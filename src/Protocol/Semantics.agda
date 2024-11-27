open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot; Honesty)
open import Protocol.Params using (Params)
open import Protocol.Block
open import Protocol.Chain
open import Protocol.Crypto using (Hashable)
open import Protocol.Message
open import Protocol.Network
open import Protocol.TreeType
open Params ⦃ ... ⦄
open Hashable ⦃ ... ⦄
open Honesty
open Envelope

module Protocol.Semantics
  ⦃ _ : Params ⦄
  ⦃ _ : Block ⦄
  ⦃ _ : Hashable Block ⦄
  ⦃ _ : Default Block ⦄
  {T : Type} ⦃ TreeType-T : TreeType T ⦄
  {AdversarialState : Type}
  {honestyOf : Party → Honesty}
  {txSelection : Slot → Party → Txs}
  -- Corrupt behavior
  {processMsgsᶜ :
      List Message
    → Slot
    → List Message
    → List Envelope
    → AdversarialState
    → List (Message × DelayMap) × AdversarialState}
  {makeBlockᶜ :
      Slot
    → List Message
    → List Envelope
    → AdversarialState
    → List (Message × DelayMap) × AdversarialState}  
  where

isHonest : Party → Type
isHonest p = honestyOf p ≡ honest

isCorrupt : Party → Type
isCorrupt p = honestyOf p ≡ corrupt

isHonestBlock : Block → Type
isHonestBlock = isHonest ∘ pid

isCorruptBlock : Block → Type
isCorruptBlock = isCorrupt ∘ pid

honestBlocks : Chain → List Block
honestBlocks = L.filter ¿ isHonestBlock ¿¹

_⊆ʰ_ : List Block → List Block → Type
_⊆ʰ_ = _⊆_ on honestBlocks

instance
  Default-T : Default T
  Default-T .def = tree₀

-- Party's local state

record LocalState : Type where
  constructor ⟪_⟫
  field
    tree : T

  addBlock : Block → LocalState
  addBlock b = record { tree = extendTree tree b }

instance
  Default-LocalState : Default LocalState
  Default-LocalState .def = record { tree = it .def }

open LocalState

-- Honest behavior

processMsgsʰ : List Message → Slot → LocalState → ⊤ × LocalState
processMsgsʰ msgs _ ls =
  _
  ,
  L.foldr (λ where (newBlock b) ls′ → addBlock ls′ b) ls msgs

makeBlockʰ : Slot → Txs → Party → LocalState → List Message × LocalState
makeBlockʰ sl txs p ls =
  ifᵈ winner p sl
    then (
      let
        bestChain = bestChain (Nat.pred sl) (ls .tree)
        hashPrev  = hash (tip bestChain)
        b         = mkBlock hashPrev sl txs p
      in
         [ newBlock b ] , addBlock ls b
      )
    else
       [] , ls
    
-- Global state

data Progress : Type where
  ready msgsDelivered blockMade : Progress

record GlobalState : Type where
  field
    clock     : Slot
    messages  : List Envelope
    states    : AssocList Party LocalState
    history   : List Message
    advState  : AdversarialState
    execOrder : List Party
    progress  : Progress

  blockHistory : List Block
  blockHistory = map (λ where (newBlock b) → b) history

open GlobalState

honestBlockHistory : GlobalState → List Block
honestBlockHistory = L.filter ¿ isHonestBlock ¿¹ ∘ blockHistory

blockPos : Block → GlobalState → ℕ
blockPos b N = length (chainFromBlock b (blockHistory N))

isCollisionFree : GlobalState → Type
isCollisionFree N =
  All
    (λ where (b , b′) → hash b ≡ hash b′ → b ≡ b′)
    (L.cartesianProduct gsBlockHistory gsBlockHistory)
  where
    open L.All using (All)
    gsBlockHistory = genesisBlock ∷ blockHistory N

updateLocalState : Party → LocalState → GlobalState → GlobalState
updateLocalState p ls N = record N { states = set p ls (N .states) }

broadcastMsgʰ : Message → GlobalState → GlobalState 
broadcastMsgʰ msg N =
  record N
    { messages = newMessages ++ N .messages
    ; history = msg ∷ N .history
    }
  where
    newMessages = map (λ party → ⦅ msg , party , 𝟙 ⦆) (N .execOrder)

broadcastMsgsʰ : List Message → GlobalState → GlobalState
broadcastMsgsʰ = flip (L.foldr broadcastMsgʰ)

broadcastMsgᶜ : Message → DelayMap → GlobalState → GlobalState
broadcastMsgᶜ msg φ N =
  record N
    { messages = newMessages ++ N .messages
    ; history = msg ∷ N .history
    }
  where
    newMessages = map (λ party → ⦅ msg , party , φ party ⦆) (N .execOrder)

broadcastMsgsᶜ : List (Message × DelayMap) → GlobalState → GlobalState
broadcastMsgsᶜ = flip $ L.foldr (λ{ (msg , φ) N′ → broadcastMsgᶜ msg φ N′ })

immediateMsgs : Party → GlobalState → List Envelope
immediateMsgs p N = L.filter ¿ flip isImmediate p ¿¹ (N .messages)

removeImmediateMsgs : Party → GlobalState → GlobalState
removeImmediateMsgs p N =
  record N { messages = L.filter ¿ ¬_ ∘ flip isImmediate p ¿¹ (N .messages) }

fetchNewMsgs : Party → GlobalState → List Message × GlobalState
fetchNewMsgs p N = map msg (immediateMsgs p N) , removeImmediateMsgs p N

executeMsgsDelivery : Party → GlobalState → GlobalState
executeMsgsDelivery p N = M.maybe′ executeMsgsDelivery′ N (N .states ⁉ p)
  where
    executeMsgsDelivery′ : LocalState → GlobalState
    executeMsgsDelivery′ ls =
      let
        (msgs , N′) = fetchNewMsgs p N
      in
        ifᵈ isHonest p
          then (
            let
              (_ , newLs) = processMsgsʰ msgs (N′ .clock) ls
            in
              updateLocalState p newLs N′
            )
          else
            let
              (newMsgs , newAs) =
                processMsgsᶜ
                  msgs
                  (N′ .clock)
                  (N′ .history)
                  (N′ .messages)
                  (N′ .advState)
            in
              record (broadcastMsgsᶜ newMsgs N′) { advState = newAs } 
  
executeBlockMaking : Party → GlobalState → GlobalState
executeBlockMaking p N = M.maybe′ executeBlockMaking′ N (N .states ⁉ p)
  where
    executeBlockMaking′ : LocalState → GlobalState
    executeBlockMaking′ ls =
      ifᵈ isHonest p
        then (
          let
            (newMsgs , newLs) = makeBlockʰ (N .clock) (txSelection (N .clock) p) p ls
          in
            broadcastMsgsʰ newMsgs (updateLocalState p newLs N)
          )
        else (
          let
            (newMsgs , newAs) =
              makeBlockᶜ
                (N .clock)
                (N .history)
                (N .messages)
                (N .advState)
          in
            broadcastMsgsᶜ newMsgs record N { advState = newAs }
          )

tick : GlobalState → GlobalState
tick N =
  record N 
    { clock    = ℕ.suc (N .clock)
    ; messages = map decreaseDelay (N .messages)
    }

-- Reachability relation

private variable
  M N O : GlobalState

data _↝_ : GlobalState → GlobalState → Type where

  deliverMsgs :
    ∙ N .progress ≡ ready
    ────────────────────────────────────
    N ↝ record (L.foldr executeMsgsDelivery N (N .execOrder)) { progress = msgsDelivered }
      
  makeBlock :
    ∙ N .progress ≡ msgsDelivered
    ────────────────────────────────────
    N ↝ record (L.foldr executeBlockMaking N (N .execOrder)) { progress = blockMade }
      
  advanceRound :
    ∙ N .progress ≡ blockMade
    ────────────────────────────────────
    N ↝ record (tick N) { progress = ready }
      
  permuteParties : ∀ {parties} →
    ∙ N .execOrder ↭ parties
    ────────────────────────────────────
    N ↝ record N { execOrder = parties }
      
  permuteMsgs : ∀ {envelopes} →
    ∙ N .messages ↭ envelopes
    ────────────────────────────────────
    N ↝ record N { messages = envelopes }

infix 2 _↝⋆_


data _↝⋆_ : GlobalState → GlobalState → Type where
  ∎ : M ↝⋆ M
  _↣_ : M ↝⋆ N → N ↝ O → M ↝⋆ O
