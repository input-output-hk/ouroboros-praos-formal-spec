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

open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Ext using (Starʳ)

isHonest : Party → Type
isHonest p = honestyOf p ≡ honest

isCorrupt : Party → Type
isCorrupt p = honestyOf p ≡ corrupt

honest⇒¬corrupt : ∀ {p} → isHonest p → ¬ isCorrupt p
honest⇒¬corrupt {p} eq eq′ = contradiction (trans (sym eq) eq′) λ()

¬corrupt⇒honest : ∀ {p} → ¬ isCorrupt p → isHonest p
¬corrupt⇒honest {p} eq′ with honestyOf p
... | honest = refl
... | corrupt = contradiction refl eq′

corrupt⇒¬honest : ∀ {p} → isCorrupt p → ¬ isHonest p
corrupt⇒¬honest eq eq′ = contradiction (trans (sym eq) eq′) λ()

¬honest⇒corrupt : ∀ {p} → ¬ isHonest p → isCorrupt p
¬honest⇒corrupt {p} eq′ with honestyOf p
... | honest = contradiction refl eq′
... | corrupt = refl

isHonestBlock : Block → Type
isHonestBlock = isHonest ∘ pid

isCorruptBlock : Block → Type
isCorruptBlock = isCorrupt ∘ pid

honestBlocks : List Block → List Block
honestBlocks = L.filter ¿ isHonestBlock ¿¹

infix 4 _⊆ʰ_
_⊆ʰ_ : List Block → List Block → Type
_⊆ʰ_ = _⊆ˢ_ on honestBlocks

-- Set equality from BagAndSetEquality.
-- TODO: Perhaps use set theory library?

open import Data.List.Relation.Binary.BagAndSetEquality as BS hiding (set; Kind)
open import Function.Related.Propositional using (K-refl; SK-sym; K-trans; ≡⇒)
open import Function.Bundles using (mk⇔)

infix 4 _≡ˢ_
_≡ˢ_ : ∀ {a} {A : Set a} → List A → List A → Set _
_≡ˢ_ = _∼[ BS.set ]_

≡ˢ-refl = K-refl

≡ˢ-sym = SK-sym

≡ˢ-trans = K-trans

≡⇒≡ˢ : ∀ {a} {A : Set a} {xs ys : List A} → xs ≡ ys → xs ≡ˢ ys
≡⇒≡ˢ refl = ≡⇒ {k = BS.set} refl

⊆ˢ×⊇ˢ⇒≡ˢ : ∀ {a} {A : Set a} {xs ys : List A} → xs ⊆ˢ ys → ys ⊆ˢ xs → xs ≡ˢ ys
⊆ˢ×⊇ˢ⇒≡ˢ xs⊆ˢys ys⊆ˢxs = mk⇔ xs⊆ˢys ys⊆ˢxs

≡ˢ⇒⊆ˢ×⊇ˢ : ∀ {a} {A : Set a} {xs ys : List A} → xs ≡ˢ ys → xs ⊆ˢ ys × ys ⊆ˢ xs
≡ˢ⇒⊆ˢ×⊇ˢ p = to p , from p
  where open Function.Bundles.Equivalence

∷-⊆ʰ : ∀ {bs bs′ : List Block} {b : Block} → isHonestBlock b → b ∷ bs ⊆ʰ bs′ → bs ⊆ʰ bs′
∷-⊆ʰ {bs} {_} {b} bh p rewrite bh = L.SubS.⊆-trans (L.SubS.xs⊆x∷xs (honestBlocks bs) b) p

instance
  Default-T : Default T
  Default-T .def = tree₀

-- Party's local state

record LocalState : Type where
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
  blockHistory = map projBlock history

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

-- Get in-transit messages in `N` addressed to `p` immediately.
immediateMsgs : Party → GlobalState → List Envelope
immediateMsgs p N = L.filter ¿ flip isImmediate p ¿¹ (N .messages)

-- Remove in-transit messages in `N` address to `p` immediately.
removeImmediateMsgs : Party → GlobalState → GlobalState
removeImmediateMsgs p N =
  record N { messages = L.filter ¿ ¬_ ∘ flip isImmediate p ¿¹ (N .messages) }

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
    ∙ isHonest p
    ────────────────────────────────────
    N ↝[ p ]↓ honestMsgsDelivery p ls N

  corruptParty↓ : ∀ {N : GlobalState} {p : Party} {ls : LocalState} →
    ∙ N .states ⁉ p ≡ just ls
    ∙ isCorrupt p
    ────────────────────────────────────
    N ↝[ p ]↓ corruptMsgsDelivery p N

record ↓Tag : Set where

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
      broadcastMsgsᶜ newMsgs record N { advState = newAs }

-- The block making phase for a specific party.
data _↝[_]↑_ : GlobalState → Party → GlobalState → Type where

  unknownParty↑ : ∀ {N : GlobalState} {p : Party} →
    ∙ N .states ⁉ p ≡ nothing
    ────────────────────────────────────
    N ↝[ p ]↑ N

  honestParty↑ : ∀ {N : GlobalState} {p : Party} {ls : LocalState} →
    ∙ N .states ⁉ p ≡ just ls
    ∙ isHonest p
    ────────────────────────────────────
    N ↝[ p ]↑ honestBlockMaking p ls N

  corruptParty↑ : ∀ {N : GlobalState} {p : Party} {ls : LocalState} →
    ∙ N .states ⁉ p ≡ just ls
    ∙ isCorrupt p
    ────────────────────────────────────
    N ↝[ p ]↑ corruptBlockMaking p N

record ↑Tag : Set where

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
data _↝_ : GlobalState → GlobalState → Type where

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

infix 2 _↝⋆_

_↝⋆_ : GlobalState → GlobalState → Type
_↝⋆_ = RTC.Star _↝_

infix 2 _↝⋆ʳ_
_↝⋆ʳ_ = Starʳ _↝_
