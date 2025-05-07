{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled

open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Base.BlockHistory
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Properties.Base.ForgingFree ⦃ params ⦄ ⦃ assumptions ⦄
open import Protocol.Prelude
open import Protocol.BaseTypes
open import Protocol.Block ⦃ params ⦄
open import Protocol.Chain ⦃ params ⦄
open import Protocol.Message ⦃ params ⦄
open import Protocol.Network ⦃ params ⦄; open Envelope
open import Protocol.TreeType ⦃ params ⦄
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Prelude.STS.Properties using (—[]→∗⇒—[]→∗ʳ; —[]→∗ʳ⇒—[]→∗)
open import Data.List.Properties.Ext using (foldr-preservesʳ')
open import Data.List.Membership.Propositional.Properties.Ext using (x∈x∷xs {-; ∈-∷⁻; ∈-findᵇ⁻; ∈-∷-≢⁻ -})
open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_ ; ≡ˢ-refl; ≡ˢ⇒⊆×⊇; ⊆×⊇⇒≡ˢ; ≡ˢ-trans {-; ≡ˢ-sym; deduplicate-cong; filter-cong; All-resp-≡ˢ; Any-resp-≡ˢ; cartesianProduct-cong -})
open import Function.Bundles

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

blockHistoryPreservation-broadcastMsgsᶜ : ∀ (mϕs : List (Message × DelayMap)) (N : GlobalState) →
  blockHistory N ⊆ˢ blockHistory (broadcastMsgsᶜ mϕs N)
blockHistoryPreservation-broadcastMsgsᶜ mϕs N = L.SubS.map⁺ _ (historyPreservation-broadcastMsgsᶜ mϕs N)

opaque

  unfolding honestMsgsDelivery honestBlockMaking

  historyPreservation-↓ : ∀ {p : Party} {N₁ N₂ : GlobalState} →
    _ ⊢ N₁ —[ p ]↓→ N₂ → N₁ .history ⊆ˢ N₂ .history
  historyPreservation-↓ (unknownParty↓ _)   = id
  historyPreservation-↓ (honestParty↓ _ _)  = id
  historyPreservation-↓ (corruptParty↓ _ _) = historyPreservation-broadcastMsgsᶜ (proj₁ (processMsgsᶜ _ _ _ _ _)) _

  historyPreservation-↓∗ : ∀ {N₁ N₂ : GlobalState} {ps : List Party} →
    _ ⊢ N₁ —[ ps ]↓→∗ N₂ → N₁ .history ⊆ˢ N₂ .history
  historyPreservation-↓∗ = fold (const $ _⊆ˢ_ on history) (L.SubS.⊆-trans ∘ historyPreservation-↓) L.SubS.⊆-refl

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
  historyPreservation-↑∗ = fold (const $ _⊆ˢ_ on history) (L.SubS.⊆-trans ∘ historyPreservation-↑) L.SubS.⊆-refl

  historyPreservation-↝ : ∀ {N₁ N₂ : GlobalState} → N₁ ↝ N₂ → N₁ .history ⊆ˢ N₂ .history
  historyPreservation-↝ (deliverMsgs _ p)  = historyPreservation-↓∗ p
  historyPreservation-↝ (makeBlock _ p)    = historyPreservation-↑∗ p
  historyPreservation-↝ (advanceRound _)   = id
  historyPreservation-↝ (permuteParties _) = id
  historyPreservation-↝ (permuteMsgs _)    = id

  historyPreservation-↝⋆ : ∀ {N₁ N₂ : GlobalState} → N₁ ↝⋆ N₂ → N₁ .history ⊆ˢ N₂ .history
  historyPreservation-↝⋆ = RTC.fold (_⊆ˢ_ on history) (L.SubS.⊆-trans ∘ historyPreservation-↝) L.SubS.⊆-refl

  blockHistoryPreservation-↓ : ∀ {N₁ N₂ : GlobalState} {p : Party} →
    _ ⊢ N₁ —[ p ]↓→ N₂ → blockHistory N₁ ⊆ˢ blockHistory N₂
  blockHistoryPreservation-↓ = L.SubS.map⁺ _ ∘ historyPreservation-↓

  blockHistoryPreservation-↑ : ∀ {N₁ N₂ : GlobalState} {p : Party} →
    _ ⊢ N₁ —[ p ]↑→ N₂ → blockHistory N₁ ⊆ˢ blockHistory N₂
  blockHistoryPreservation-↑ = L.SubS.map⁺ _ ∘ historyPreservation-↑

  blockHistoryPreservation-↝⋆ : ∀ {N₁ N₂ : GlobalState} → N₁ ↝⋆ N₂ → blockHistory N₁ ⊆ˢ blockHistory N₂
  blockHistoryPreservation-↝⋆ = L.SubS.map⁺ _ ∘ historyPreservation-↝⋆

  blockHistoryPreservation-↑∗ : ∀ {N₁ N₂ : GlobalState} {ps : List Party} →
    _ ⊢ N₁ —[ ps ]↑→∗ N₂ → blockHistory N₁ ⊆ˢ blockHistory N₂
  blockHistoryPreservation-↑∗ = L.SubS.map⁺ _ ∘ historyPreservation-↑∗

  blockHistoryPreservation-↓∗ : ∀ {N₁ N₂ : GlobalState} {ps : List Party} →
    _ ⊢ N₁ —[ ps ]↓→∗ N₂ → blockHistory N₁ ⊆ˢ blockHistory N₂
  blockHistoryPreservation-↓∗ = L.SubS.map⁺ _ ∘ historyPreservation-↓∗

  honestBlockHistoryPreservation-broadcastMsgsᶜ : ∀ {N : GlobalState} {mds : List (Message × DelayMap)} →
      map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N
    → honestBlockHistory N ≡ˢ honestBlockHistory (broadcastMsgsᶜ mds N)
  honestBlockHistoryPreservation-broadcastMsgsᶜ {_} {[]} _ = ≡ˢ-refl
  honestBlockHistoryPreservation-broadcastMsgsᶜ {N} {(newBlock b , _) ∷ mds} prf
    with ih ← honestBlockHistoryPreservation-broadcastMsgsᶜ {N} {mds} | ¿ HonestBlock b ¿
  ... | no _   = ih prf
  ... | yes bh = goal
    where
      π₁ : honestBlocks (b ∷ map (projBlock ∘ proj₁) mds) ≡ b ∷ honestBlocks (map (projBlock ∘ proj₁) mds)
      π₁ rewrite bh = refl

      π₂ : b ∷ map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N
      π₂ = L.SubS.⊆-trans (L.SubS.⊆-reflexive π₁) prf

      π₃ : map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N
      π₃ = ∷-⊆ʰ {map (projBlock ∘ proj₁) mds} {blockHistory N} {b} bh π₂

      π₄ : honestBlockHistory N ≡ˢ honestBlockHistory (broadcastMsgsᶜ mds N)
      π₄ = ih π₃

      goal : honestBlockHistory N ≡ˢ b ∷ honestBlockHistory (broadcastMsgsᶜ mds N)
      goal = ⊆×⊇⇒≡ˢ ⊆ˢπ ⊇ˢπ
        where
          ⊆ˢπ : honestBlockHistory N ⊆ˢ b ∷ honestBlockHistory (broadcastMsgsᶜ mds N)
          ⊆ˢπ {b′} b′∈lhs with b ≟ b′
          ... | yes eq rewrite eq = x∈x∷xs _
          ... | no ¬eq = L.SubS.xs⊆x∷xs _ b (to π₄ b′∈lhs)
            where open Function.Bundles.Equivalence

          ⊇ˢπ : b ∷ honestBlockHistory (broadcastMsgsᶜ mds N) ⊆ˢ honestBlockHistory N
          ⊇ˢπ = L.SubS.∈-∷⁺ʳ (prf {b} (x∈x∷xs _)) (≡ˢ⇒⊆×⊇ π₄ .proj₂)

  honestBlockHistoryPreservation-↓∗ : ∀ {N N′ : GlobalState} {ps : List Party} →
      N₀ ↝⋆ N
    → _ ⊢ N —[ ps ]↓→∗ N′
    → ForgingFree (record N′ { progress = msgsDelivered })
    → N .progress ≡ ready
    → honestBlockHistory N ≡ˢ honestBlockHistory N′
  honestBlockHistoryPreservation-↓∗ {N} {N′} {ps} N₀↝⋆N N—[ps]↓→∗N′ ff NReady = honestBlockHistoryPreservationʳ-↓∗ {N} {N′} ps prfN₂ (—[]→∗⇒—[]→∗ʳ N—[ps]↓→∗N′)
    where
      N₂ : GlobalState
      N₂ = record N′ { progress = msgsDelivered }

      prfN₂ : N′ ↷↓ N₂
      prfN₂ = progress↓ (↷↓-refl {N₂})

      honestBlockHistoryPreservationʳ-↓∗ : ∀ {N N′ : GlobalState} (ps : List Party) →
          N′ ↷↓ N₂
        → _ ⊢ N —[ ps ]↓→∗ʳ N′
        → honestBlockHistory N ≡ˢ honestBlockHistory N′
      honestBlockHistoryPreservationʳ-↓∗ {N} {.N} .[] prfN₂ [] = ≡ˢ-refl
      honestBlockHistoryPreservationʳ-↓∗ {N} {N′} _ prfN₂ (_∷ʳ_ {is = ps} {i = p} {s′ = N″} ts⋆ ts) = step ts
        where
          ih : honestBlockHistory N ≡ˢ honestBlockHistory N″
          ih = honestBlockHistoryPreservationʳ-↓∗ _ (delivery↓ ts prfN₂) ts⋆

          step : _ ⊢ N″ —[ p ]↓→ N′ → honestBlockHistory N ≡ˢ honestBlockHistory N′
          step (unknownParty↓ _) = ih
          -- Honest parties do not broadcast any (in particular, honest) blocks in the delivery phase.
          step (honestParty↓ _ _) = ih
          -- Corrupt parties do not broadcast new _honest_ blocks in the delivery phase (by the forging-free property).
          step (corruptParty↓ _ _) = ≡ˢ-trans ih (honestBlockHistoryPreservation-broadcastMsgsᶜ {removeImmediateMsgs p N″} {mds} sub)
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

  honestBlockHistoryPreservation-↝⋆⟨0⟩ : ∀ {N N′ : GlobalState} →
      N₀ ↝⋆ N
    → N .progress ≡ ready
    → N ↝⋆⟨ 0 ⟩ N′
    → ForgingFree N′
    → N′ .progress ≡ msgsDelivered
    → honestBlockHistory N ≡ˢ honestBlockHistory N′
  honestBlockHistoryPreservation-↝⋆⟨0⟩ = {!!}

honestGlobalTreeInBlockHistory : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → allBlocks (honestTree N) ⊆ˢ genesisBlock ∷ blockHistory N
honestGlobalTreeInBlockHistory = {!!}

honestGlobalTreeButGBInBlockHistory : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → filter ¿ _≢ genesisBlock ¿¹ (allBlocks (honestTree N)) ⊆ˢ blockHistory N
honestGlobalTreeButGBInBlockHistory = {!!}

messages⊆history : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → map msg (N .messages) ⊆ˢ N .history
messages⊆history = {!!}
