open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Protocol.Semantics
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot; slot₀; Honesty)
open import Protocol.Crypto ⦃ params ⦄ using (Hashable)
open import Protocol.Block ⦃ params ⦄
open import Protocol.Chain ⦃ params ⦄
open import Protocol.Message ⦃ params ⦄
open import Protocol.Network ⦃ params ⦄
open import Protocol.TreeType ⦃ params ⦄
open Hashable ⦃ ... ⦄
open Honesty
open Envelope
open import Relation.Binary.Definitions using (Reflexive)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Ext using (Starʳ)

-- Party's local state

record LocalState : Type where
  field
    tree : Tree

  addBlock : Block → LocalState
  addBlock b = record { tree = extendTree tree b }

instance
  Default-LocalState : Default LocalState
  Default-LocalState .def = record { tree = it .def }

open LocalState public

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
  blockHistory = map projBlock history

  honestParties : List Party
  honestParties = L.filter ¿ Honest ¿¹ execOrder

  blocks : Party → List Block
  blocks p = case states ⁉ p of λ where
    nothing   → []
    (just ls) → allBlocks (ls .tree)

  honestTree : Tree
  honestTree = buildTree (L.concatMap blocks honestParties)

open GlobalState public

honestBlockHistory : GlobalState → List Block
honestBlockHistory = L.filter ¿ HonestBlock ¿¹ ∘ blockHistory

blockPos : Block → GlobalState → ℕ
blockPos b N = ∣ chainFromBlock b (blockHistory N) ∣

updateLocalState : Party → LocalState → GlobalState → GlobalState
updateLocalState p ls N = record N { states = set p ls (N .states) }

broadcastMsgʰ : Message → GlobalState → GlobalState 
broadcastMsgʰ msg N =
  record N
    { messages = newMessages ++ N .messages
    ; history = msg ∷ N .history
    }
  where
    newMessages : List Envelope
    newMessages = map (λ party → ⦅ msg , party , 𝟙 ⦆) (N .execOrder)

broadcastMsgsʰ : List Message → GlobalState → GlobalState
broadcastMsgsʰ = flip (L.foldr broadcastMsgʰ)

-- Broadcast message `msg` to each party `p` with delay `φ p`.
broadcastMsgᶜ : Message → DelayMap → GlobalState → GlobalState
broadcastMsgᶜ msg φ N =
  record N
    { messages = newMessages ++ N .messages
    ; history = msg ∷ N .history
    }
  where
    newMessages : List Envelope
    newMessages = map (λ party → ⦅ msg , party , φ party ⦆) (N .execOrder)

broadcastMsgsᶜ : List (Message × DelayMap) → GlobalState → GlobalState
broadcastMsgsᶜ = flip $ L.foldr (λ{ (msg , φ) N′ → broadcastMsgᶜ msg φ N′ })

-- Get in-transit blocks in `N` addressed to `p` to be delivered within `d` rounds.
blocksDeliveredIn : Party → Delay → GlobalState → List Block
blocksDeliveredIn p d N = map (projBlock ∘ msg) $ L.filter (λ env → ¿ DeliveredIn env ¿² p d) (N .messages)

-- Get in-transit messages in `N` addressed to `p` immediately.
immediateMsgs : Party → GlobalState → List Envelope
immediateMsgs p N = L.filter ¿ flip Immediate p ¿¹ (N .messages)

-- Remove in-transit messages in `N` address to `p` immediately.
removeImmediateMsgs : Party → GlobalState → GlobalState
removeImmediateMsgs p N =
  record N { messages = L.filter ¿ ¬_ ∘ flip Immediate p ¿¹ (N .messages) }

-- Get in-transit messages in `N` addressed to `p` immediately and remove them from `N`.
fetchNewMsgs : Party → GlobalState → List Message × GlobalState
fetchNewMsgs p N = map msg (immediateMsgs p N) , removeImmediateMsgs p N

tick : GlobalState → GlobalState
tick N =
  record N 
    { clock    = ℕ.suc (N .clock)
    ; messages = map decreaseDelay (N .messages)
    }

opaque

  honestMsgsDelivery : Party → LocalState → GlobalState → GlobalState
  honestMsgsDelivery p ls N =
    let
      (msgs , N′) = fetchNewMsgs p N
      (_ , newLs) = processMsgsʰ msgs (N′ .clock) ls
    in
      updateLocalState p newLs N′

  corruptMsgsDelivery : Party → GlobalState → GlobalState
  corruptMsgsDelivery p N =
    let
      (msgs , N′) = fetchNewMsgs p N
      (newMsgs , newAs) =
        processMsgsᶜ
          msgs
          (N′ .clock)
          (N′ .history)
          (N′ .messages)
          (N′ .advState)
    in
      record (broadcastMsgsᶜ newMsgs N′) { advState = newAs }

-- The messages delivery phase for a specific party.
data _↝[_]↓_ : GlobalState → Party → GlobalState → Type where

  unknownParty↓ : ∀ {N : GlobalState} {p : Party} →
    ∙ N .states ⁉ p ≡ nothing
    ────────────────────────────────────
    N ↝[ p ]↓ N

  honestParty↓ : ∀ {N : GlobalState} {p : Party} {ls : LocalState} →
    ∙ N .states ⁉ p ≡ just ls
    ∙ Honest p
    ────────────────────────────────────
    N ↝[ p ]↓ honestMsgsDelivery p ls N

  corruptParty↓ : ∀ {N : GlobalState} {p : Party} {ls : LocalState} →
    ∙ N .states ⁉ p ≡ just ls
    ∙ Corrupt p
    ────────────────────────────────────
    N ↝[ p ]↓ corruptMsgsDelivery p N

record ↓Tag : Type where

instance
  HasTransition-↝[]↓ : HasTransition ↓Tag GlobalState Party
  HasTransition-↝[]↓ ._⊢_—[_]→_ = λ _ → _↝[_]↓_

_⊢_—[_]↓→_ : STS ↓Tag GlobalState Party
_⊢_—[_]↓→_ = _⊢_—[_]→_

_⊢_—[_]↓→∗_ : STS ↓Tag GlobalState (List Party)
_⊢_—[_]↓→∗_ = _⊢_—[_]→∗_

_⊢_—[_]↓→∗ʳ_ : STS ↓Tag GlobalState (List Party)
_⊢_—[_]↓→∗ʳ_ = _⊢_—[_]→∗ʳ_

opaque

  honestBlockMaking : Party → LocalState → GlobalState → GlobalState
  honestBlockMaking p ls N =
    let
      (newMsgs , newLs) = makeBlockʰ (N .clock) (txSelection (N .clock) p) p ls
    in
      broadcastMsgsʰ newMsgs (updateLocalState p newLs N)

  corruptBlockMaking : Party → GlobalState → GlobalState
  corruptBlockMaking p N =
    let
      (newMsgs , newAs) =
        makeBlockᶜ
          (N .clock)
          (N .history)
          (N .messages)
          (N .advState)
    in
      record (broadcastMsgsᶜ newMsgs N) { advState = newAs }

-- The block making phase for a specific party.
data _↝[_]↑_ : GlobalState → Party → GlobalState → Type where

  unknownParty↑ : ∀ {N : GlobalState} {p : Party} →
    ∙ N .states ⁉ p ≡ nothing
    ────────────────────────────────────
    N ↝[ p ]↑ N

  honestParty↑ : ∀ {N : GlobalState} {p : Party} {ls : LocalState} →
    ∙ N .states ⁉ p ≡ just ls
    ∙ Honest p
    ────────────────────────────────────
    N ↝[ p ]↑ honestBlockMaking p ls N

  corruptParty↑ : ∀ {N : GlobalState} {p : Party} {ls : LocalState} →
    ∙ N .states ⁉ p ≡ just ls
    ∙ Corrupt p
    ────────────────────────────────────
    N ↝[ p ]↑ corruptBlockMaking p N

record ↑Tag : Type where

instance
  HasTransition-↝[]↑ : HasTransition ↑Tag GlobalState Party
  HasTransition-↝[]↑ ._⊢_—[_]→_ = λ _ → _↝[_]↑_

_⊢_—[_]↑→_ : STS ↑Tag GlobalState Party
_⊢_—[_]↑→_ = _⊢_—[_]→_

_⊢_—[_]↑→∗_ : STS ↑Tag GlobalState (List Party)
_⊢_—[_]↑→∗_ = _⊢_—[_]→∗_

_⊢_—[_]↑→∗ʳ_ : STS ↑Tag GlobalState (List Party)
_⊢_—[_]↑→∗ʳ_ = _⊢_—[_]→∗ʳ_

-- The global state reachability relation.
data _↝_ : Rel GlobalState 0ℓ where

  deliverMsgs : ∀ {N N′ : GlobalState} →
    ∙ N .progress ≡ ready
    ∙ _ ⊢ N —[ N .execOrder ]↓→∗ N′
    ────────────────────────────────────
    N ↝ record N′ { progress = msgsDelivered }

  makeBlock : ∀ {N N′ : GlobalState} →
    ∙ N .progress ≡ msgsDelivered
    ∙ _ ⊢ N —[ N .execOrder ]↑→∗ N′
    ────────────────────────────────────
    N ↝ record N′ { progress = blockMade }
      
  advanceRound : ∀ {N : GlobalState} →
    ∙ N .progress ≡ blockMade
    ────────────────────────────────────
    N ↝ record (tick N) { progress = ready }
      
  permuteParties : ∀ {N : GlobalState} {parties : List Party} →
    ∙ N .execOrder ↭ parties
    ────────────────────────────────────
    N ↝ record N { execOrder = parties }
      
  permuteMsgs : ∀ {N : GlobalState} {envelopes : List Envelope} →
    ∙ N .messages ↭ envelopes
    ────────────────────────────────────
    N ↝ record N { messages = envelopes }


↝-refl : Reflexive _↝_
↝-refl = permuteParties _↭_.refl

infix 3 _↝⋆_

_↝⋆_ : Rel GlobalState 0ℓ
_↝⋆_ = RTC.Star _↝_

infix 3 _↝⋆ʳ_
_↝⋆ʳ_ = Starʳ _↝_

_⟨_⟩ : Rel GlobalState 0ℓ → Slot → Rel GlobalState 0ℓ
_⇾_ ⟨ sl ⟩ = λ N N′ → N ⇾ N′ × sl + N .clock ≡ N′ .clock

_↝⋆⟨_⟩_ : GlobalState → Slot → GlobalState → Type
N ↝⋆⟨ sl ⟩ N′ = (_↝⋆_ ⟨ sl ⟩) N N′

_↝⋆ʳ⟨_⟩_ : GlobalState → Slot → GlobalState → Type
N ↝⋆ʳ⟨ sl ⟩ N′ = (_↝⋆ʳ_ ⟨ sl ⟩) N N′

_⁺ : Rel GlobalState 0ℓ → Rel GlobalState 0ℓ
_⇾_ ⁺ = λ N N′ → N ⇾ N′ × N .clock < N′ .clock

infix 3 _↝⁺_
_↝⁺_ = _↝⋆_ ⁺

infix 3 _↝⁺ʳ_
_↝⁺ʳ_ =  _↝⋆ʳ_ ⁺

module _ where

  private variable
    N₁ N₂ : GlobalState

  -- The messages delivery phase sub-step relation.
  data _↷↓_ : Rel GlobalState 0ℓ where

    refine↓ :
      ∙ N₁ ↝⋆ N₂
      ────────────────────────────────────
      N₁ ↷↓ N₂

    progress↓ :
      ∙ record N₁ { progress = msgsDelivered } ↷↓ N₂
      ────────────────────────────────────
      N₁ ↷↓ N₂

    delivery↓ : ∀ {N′ : GlobalState} {p : Party} →
      ∙ _ ⊢ N₁ —[ p ]↓→ N′
      ∙ N′ ↷↓ N₂
      ────────────────────────────────────
      N₁ ↷↓ N₂

  ↷↓-refl : Reflexive _↷↓_
  ↷↓-refl = refine↓ ε
    where open Star

  -- The block making phase sub-step relation.
  data _↷↑_ : Rel GlobalState 0ℓ where

    refine↑ :
      ∙ N₁ ↝⋆ N₂
      ────────────────────────────────────
      N₁ ↷↑ N₂

    progress↑ :
      ∙ record N₁ { progress = blockMade } ↷↑ N₂
      ────────────────────────────────────
      N₁ ↷↑ N₂

    blockMaking↑ : ∀ {N′ : GlobalState} {p : Party} →
      ∙ _ ⊢ N₁ —[ p ]↑→ N′
      ∙ N′ ↷↑ N₂
      ────────────────────────────────────
      N₁ ↷↑ N₂

  ↷↑-refl : Reflexive _↷↑_
  ↷↑-refl = refine↑ ε
    where open Star

N₀ : GlobalState
N₀ =
  record
    { clock     = slot₀
    ; messages  = []
    ; states    = map (_, it .def) parties₀
    ; history   = []
    ; advState  = adversarialState₀
    ; execOrder = parties₀
    ; progress  = ready
    }
