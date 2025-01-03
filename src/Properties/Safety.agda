open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot; slot₀; Honesty)
open import Protocol.Params using (Params)
open import Protocol.Block
open import Protocol.Chain using (genesisBlock)
open import Protocol.Crypto using (Hashable)
open import Protocol.Message
open import Protocol.Network
open import Protocol.TreeType
open Params ⦃ ... ⦄
open Honesty
open Hashable ⦃ ... ⦄
open Envelope
open import Relation.Binary.PropositionalEquality.Properties

module Properties.Safety
  ⦃ params : Params ⦄
  ⦃ _ : Block ⦄
  ⦃ _ : Hashable Block ⦄
  ⦃ _ : Default Block ⦄
  {T : Type} ⦃ TreeType-T : TreeType T ⦄
  {AdversarialState : Type}
  {honestyOf : Party → Honesty}
  {txSelection : Slot → Party → Txs}
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
  {adversarialState₀ : AdversarialState}
  {parties₀ : List Party}
  where

open import Function.Bundles
open import Data.List.Membership.Propositional.Properties.Ext using (x∈x∷xs)
open import Data.List.Properties.Ext using (filter-∘-comm; filter-∘-×)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Ext using (Starʳ)
open import Prelude.STS.Properties.Ext using (⊢—[]→∗⇒⊢—[]→∗ʳ)
open import Protocol.BaseTypes using (slot₀)
open import Protocol.Semantics {T} {AdversarialState} {honestyOf} {txSelection} {processMsgsᶜ} {makeBlockᶜ}

open GlobalState

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

isSuperSlot : Slot → Type
isSuperSlot sl = length (filter (λ p → ¿ winner p sl × isHonest p ¿) parties₀) ≡ 1

isSuperBlock : Block → Type
isSuperBlock b = isHonest (b .pid) × isSuperSlot (b .slot)

superBlocks : GlobalState → List Block
superBlocks N = L.deduplicate _≟_ $ filter ¿ isSuperBlock ¿¹ (blockHistory N)

superBlocksAltDef : ∀ N → superBlocks N ≡ (L.deduplicate _≟_ $ filter ¿ isSuperSlot ∘ slot ¿¹ (honestBlockHistory N))
superBlocksAltDef N
  rewrite filter-∘-comm ¿ isSuperSlot ∘ slot ¿¹ ¿ isHonest ∘ pid ¿¹ (blockHistory N)
    | sym $ filter-∘-× ¿ isHonest ∘ pid ¿¹ ¿ isSuperSlot ∘ slot ¿¹ (blockHistory N)
    = refl

module _ where

  private variable
    N₁ N₂ : GlobalState

  -- The messages delivery phase sub-step relation.
  data _↷↓_ : GlobalState → GlobalState → Type where

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

  ↷↓-refl : ∀ {N} → N ↷↓ N
  ↷↓-refl = refine↓ ε
    where open Star

  -- The block making phase sub-step relation.
  data _↷↑_ : GlobalState → GlobalState → Type where

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

-- The condition `∀ {N₁} → N₁ ↷↓ N₂ → ∀ {p} → ...` forces the forging-free property
-- to hold at each previous "sub-step" within the delivery phase. A sub-step is either changing the
-- progress to `msgsDelivered` or execute the messages delivery for a party `p`.
-- Thus, an honest block can be broadcast by a corrupt party _only_ if such block was already in the
-- history at the beginning of the delivery phase. This is crucial for the proof of the lemma
-- `honestBlockHistoryMsgsDeliveryPreservation`.
isForgingFree↓ : GlobalState → Type
isForgingFree↓ N₂ = ∀ {N₁ : GlobalState} → N₁ ↷↓ N₂ → ∀ {p : Party} →
  let
    (msgs , N₁′) = fetchNewMsgs p N₁
    mds = processMsgsᶜ
      msgs
      (N₁′ .clock)
      (N₁′ .history)
      (N₁′ .messages)
      (N₁′ .advState)
      .proj₁
    nbs = map (projBlock ∘ proj₁) mds
  in
    nbs ⊆ʰ blockHistory N₁′

isForgingFree↓Prev : ∀ {N₁ N₂ : GlobalState} → isForgingFree↓ N₂ → N₁ ↝⋆ N₂ → isForgingFree↓ N₁
isForgingFree↓Prev ffD prf H = ffD (isForgingFree↓Prev′ H prf)
  where
    isForgingFree↓Prev′ : ∀ {N₁ N₂ N′ : GlobalState} → N₁ ↷↓ N′ → N′ ↝⋆ N₂ → N₁ ↷↓ N₂
    isForgingFree↓Prev′ (refine↓ x)     prf = refine↓ (x ◅◅ prf)
    isForgingFree↓Prev′ (progress↓ x)   prf = progress↓ (isForgingFree↓Prev′ x prf)
    isForgingFree↓Prev′ (delivery↓ x y) prf = delivery↓ x (isForgingFree↓Prev′ y prf)

isForgingFree↑ : GlobalState → Type
isForgingFree↑ N₂ = ∀ {N₁ : GlobalState} → N₁ ↷↑ N₂ →
  let
    mds = makeBlockᶜ (N₁ .clock) (N₁ .history) (N₁ .messages) (N₁ .advState) .proj₁
    nbs = map (projBlock ∘ proj₁) mds
  in
    nbs ⊆ʰ blockHistory N₁

isForgingFree : GlobalState → Type
isForgingFree N = isForgingFree↓ N × isForgingFree↑ N

-- the standard library version is strangely for f : A → A → A
foldr-preservesʳ' : ∀ {A B : Set} {P : B → Set} {f : A → B → B} →
  (∀ x {y} → P y → P (f x y)) → ∀ {e} → P e → ∀ xs → P (L.foldr f e xs)
foldr-preservesʳ' pres Pe []       = Pe
foldr-preservesʳ' pres Pe (_ ∷ xs) = pres _ (foldr-preservesʳ' pres Pe xs)

historyPreservation-broadcastMsgᶜ : ∀ (msg : Message) (ϕ : DelayMap) (N : GlobalState) →
  N .history ⊆ˢ broadcastMsgᶜ msg ϕ N .history
historyPreservation-broadcastMsgᶜ msg ϕ N p = there p

historyPreservation-broadcastMsgsᶜ : ∀ (mϕs : List (Message × DelayMap)) (N : GlobalState) →
  N .history ⊆ˢ broadcastMsgsᶜ mϕs N .history
historyPreservation-broadcastMsgsᶜ mϕs N {x = x} p = foldr-preservesʳ'
  {P = λ N → x ∈ N .history}
  (λ x {N} → historyPreservation-broadcastMsgᶜ (proj₁ x) (proj₂ x) N)
  p
  mϕs

private opaque

  unfolding honestMsgsDelivery honestBlockMaking

  historyPreservation-↓ : ∀ {p : Party} {N₁ N₂ : GlobalState} →
    _ ⊢ N₁ —[ p ]↓→ N₂ → N₁ .history ⊆ˢ N₂ .history
  historyPreservation-↓ (unknownParty↓ _)   = id
  historyPreservation-↓ (honestParty↓ _ _)  = id
  historyPreservation-↓ (corruptParty↓ _ _) = historyPreservation-broadcastMsgsᶜ (proj₁ (processMsgsᶜ _ _ _ _ _)) _

  historyPreservation-↓∗ : ∀ {N₁ N₂ : GlobalState} {ps : List Party} →
    _ ⊢ N₁ —[ ps ]↓→∗ N₂ → N₁ .history ⊆ˢ N₂ .history
  historyPreservation-↓∗ [] = L.SubS.⊆-refl
  historyPreservation-↓∗ (pπ ∷ psπ) = L.SubS.⊆-trans (historyPreservation-↓ pπ) (historyPreservation-↓∗ psπ)

  historyPreservation-↑ : ∀ {p : Party} {N₁ N₂ : GlobalState} →
    _ ⊢ N₁ —[ p ]↑→ N₂ → N₁ .history ⊆ˢ N₂ .history
  historyPreservation-↑ (unknownParty↑ _) = id
  historyPreservation-↑ {p} {N₁} (honestParty↑ _ _) prf
    with Params.winnerᵈ params {p} {N₁ .clock}
  ... | ⁇ (yes _) = there prf
  ... | ⁇ (no _)  = prf
  historyPreservation-↑ (corruptParty↑ _ _) prf = historyPreservation-broadcastMsgsᶜ (proj₁ (makeBlockᶜ _ _ _ _)) _ prf

  historyPreservation-↑∗ : ∀ {N₁ N₂ : GlobalState} {ps : List Party} →
    _ ⊢ N₁ —[ ps ]↑→∗ N₂ → N₁ .history ⊆ˢ N₂ .history
  historyPreservation-↑∗ [] = L.SubS.⊆-refl
  historyPreservation-↑∗ (pπ ∷ psπ) = L.SubS.⊆-trans (historyPreservation-↑ pπ) (historyPreservation-↑∗ psπ)

  historyPreservation-↝ : ∀ {N₁ N₂ : GlobalState} → N₁ ↝ N₂ → N₁ .history ⊆ˢ N₂ .history
  historyPreservation-↝ (deliverMsgs _ p)  = historyPreservation-↓∗ p
  historyPreservation-↝ (makeBlock _ p)    = historyPreservation-↑∗ p
  historyPreservation-↝ (advanceRound _)   = id
  historyPreservation-↝ (permuteParties _) = id
  historyPreservation-↝ (permuteMsgs _)    = id

  historyPreservation-↝⋆ : ∀ {N₁ N₂ : GlobalState} → N₁ ↝⋆ N₂ → N₁ .history ⊆ˢ N₂ .history
  historyPreservation-↝⋆ RTC.ε        = L.SubS.⊆-refl
  historyPreservation-↝⋆ (π RTC.◅ π⋆) = L.SubS.⊆-trans (historyPreservation-↝ π) (historyPreservation-↝⋆ π⋆)

  blockHistoryPreservation-↝⋆ : ∀ {N₁ N₂ : GlobalState} → N₁ ↝⋆ N₂ → blockHistory N₁ ⊆ˢ blockHistory N₂
  blockHistoryPreservation-↝⋆ = L.SubS.map⁺ _ ∘ historyPreservation-↝⋆

  honestBlockHistoryPreservation-↝⋆ : ∀ {N N′ : GlobalState} {ps : List Party} →
      N₀ ↝⋆ N
    → _ ⊢ N —[ ps ]↓→∗ N′
    → isForgingFree (record N′ { progress = msgsDelivered })
    → N .progress ≡ ready
    → honestBlockHistory N ≡ˢ honestBlockHistory N′
  honestBlockHistoryPreservation-↝⋆ {N} {N′} {ps} N₀↝⋆N N↝[ps]⋆N′ ff NReady = honestBlockHistoryPreservationʳ-↝⋆ {N} {N′} ps prfN₂ (⊢—[]→∗⇒⊢—[]→∗ʳ N↝[ps]⋆N′)
    where
      N₂ : GlobalState
      N₂ = record N′ { progress = msgsDelivered }

      prfN₂ : N′ ↷↓ N₂
      prfN₂ = progress↓ (↷↓-refl {N₂})

      honestBlockHistoryPreservationʳ-↝⋆ : ∀ {N N′ : GlobalState} (ps : List Party) →
          N′ ↷↓ N₂
        → _ ⊢ N —[ ps ]↓→∗ʳ N′
        → honestBlockHistory N ≡ˢ honestBlockHistory N′
      honestBlockHistoryPreservationʳ-↝⋆ {N} {.N} .[] prfN₂ [] = ≡ˢ-refl
      honestBlockHistoryPreservationʳ-↝⋆ {N} {N′} _ prfN₂ (_∷ʳ_ {is = ps} {i = p} {s′ = N″} ts⋆ ts) = step ts
        where
          ih : honestBlockHistory N ≡ˢ honestBlockHistory N″
          ih = honestBlockHistoryPreservationʳ-↝⋆ _ (delivery↓ ts prfN₂) ts⋆

          step : _ ⊢ N″ —[ p ]↓→ N′ → honestBlockHistory N ≡ˢ honestBlockHistory N′
          step (unknownParty↓ _) = ih
          -- Honest parties do not broadcast any (in particular, honest) blocks in the delivery phase.
          step (honestParty↓ _ _) = ih
          -- Corrupt parties do not broadcast new _honest_ blocks in the delivery phase (by the forging-free property).
          step (corruptParty↓ _ _) = ≡ˢ-trans ih (honestBlockHistoryPreservationᶜ {mds} sub)
            where
              mds : List (Message × DelayMap)
              mds =
                processMsgsᶜ
                  (map msg (immediateMsgs p N″))
                  (N″ .clock)
                  (N″ .history)
                  (removeImmediateMsgs p N″ .messages)
                  (N″ .advState)
                  .proj₁

              sub : map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N″
              sub = ff .proj₁ (delivery↓ ts prfN₂)

              honestBlockHistoryPreservationᶜ : ∀ {mds : List (Message × DelayMap)} →
                  map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N″
                → honestBlockHistory N″ ≡ˢ honestBlockHistory (broadcastMsgsᶜ mds (removeImmediateMsgs p N″))
              honestBlockHistoryPreservationᶜ {[]} _ = ≡ˢ-refl
              honestBlockHistoryPreservationᶜ {(newBlock b , _) ∷ mds} prf
                with ih ← honestBlockHistoryPreservationᶜ {mds} | ¿ isHonestBlock b ¿
              ... | no _   = ih prf
              ... | yes bh = goal
                where
                  π₁ : honestBlocks (b ∷ map (projBlock ∘ proj₁) mds) ≡ b ∷ honestBlocks (map (projBlock ∘ proj₁) mds)
                  π₁ rewrite bh = refl

                  π₂ : b ∷ map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N″
                  π₂ = L.SubS.⊆-trans (L.SubS.⊆-reflexive π₁) prf

                  π₃ : map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N″
                  π₃ = ∷-⊆ʰ {map (projBlock ∘ proj₁) mds} {blockHistory N″} {b} bh π₂

                  π₄ : honestBlockHistory N″ ≡ˢ honestBlockHistory (broadcastMsgsᶜ mds (removeImmediateMsgs p N″))
                  π₄ = ih π₃

                  goal : honestBlockHistory N″ ≡ˢ b ∷ honestBlockHistory (broadcastMsgsᶜ mds (removeImmediateMsgs p N″))
                  goal = ⊆ˢ×⊇ˢ⇒≡ˢ ⊆ˢπ ⊇ˢπ
                    where
                      ⊆ˢπ : honestBlockHistory N″ ⊆ˢ b ∷ honestBlockHistory (broadcastMsgsᶜ mds (removeImmediateMsgs p N″))
                      ⊆ˢπ {b′} b′∈lhs with b ≟ b′
                      ... | yes eq rewrite eq = x∈x∷xs _
                      ... | no ¬eq = L.SubS.xs⊆x∷xs _ b (to π₄ b′∈lhs)
                        where open Function.Bundles.Equivalence

                      ⊇ˢπ : b ∷ honestBlockHistory (broadcastMsgsᶜ mds (removeImmediateMsgs p N″)) ⊆ˢ honestBlockHistory N″
                      ⊇ˢπ = L.SubS.∈-∷⁺ʳ (prf {b} (x∈x∷xs _)) (≡ˢ⇒⊆ˢ×⊇ˢ π₄ .proj₂)
