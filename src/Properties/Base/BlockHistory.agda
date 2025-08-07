{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled

open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Base.BlockHistory
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Properties.Base.ForgingFree ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.Time ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.Trees ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.LocalState ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.ExecutionOrder ⦃ params ⦄ ⦃ assumptions ⦄
open import Protocol.Prelude
open import Protocol.BaseTypes
open import Protocol.Crypto ⦃ params ⦄ using (Hashable); open Hashable ⦃ ... ⦄
open import Protocol.Block ⦃ params ⦄
open import Protocol.Chain ⦃ params ⦄
open import Protocol.Message ⦃ params ⦄
open import Protocol.Network ⦃ params ⦄; open Envelope
open import Protocol.TreeType ⦃ params ⦄
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Prelude.STS.Properties using (—[]→∗⇒—[]→∗ʳ; —[]→∗ʳ⇒—[]→∗; —[[]]→∗ʳ⇒≡; —[∷ʳ]→∗-split)
open import Prelude.AssocList.Properties.Ext using (set-⁉; set-⁉-¬)
open import Data.List.Properties.Ext using (foldr-preservesʳ'; []≢∷ʳ)
open import Data.List.Membership.Propositional.Properties.Ext using (x∈x∷xs)
open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_ ; ≡ˢ-refl; ≡ˢ⇒⊆×⊇; ⊆×⊇⇒≡ˢ; ≡ˢ-trans; filter-cong)
open import Data.List.Relation.Binary.Permutation.Propositional using (↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∈-resp-↭; map⁺)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties.Ext using (filter-↭)
open import Data.List.Relation.Binary.Subset.Propositional.Properties.Ext using (∷-⊆; ∷⊆⇒∈; ⊆-++-comm; ++-absorb)
open import Data.List.Relation.Binary.BagAndSetEquality using (∷-cong; concat-cong; map-cong; bag-=⇒; ↭⇒∼bag)
open import Data.Maybe.Properties.Ext using (Is-just⇒to-witness; ≡just⇒Is-just)
open import Relation.Unary using (∁) renaming (_⊆_ to _⋐_)
open import Relation.Binary.PropositionalEquality using (≢-sym)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Ext using (Starʳ)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.Ext using (Star⇒Starʳ; Starʳ⇒Star)
open import Function.Base using (_|>_; ∣_⟩-_)
open import Function.Bundles
open import Function.Related.Propositional as Related

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

opaque

  unfolding honestMsgsDelivery corruptMsgsDelivery honestBlockMaking corruptBlockMaking

  open import Data.List.Relation.Binary.Subset.Propositional.Properties.Ext using (++-meet; map[const-x]xs⊆x∷ys)
  open import Data.List.Relation.Binary.Subset.Propositional.Properties.Ext using (∷-⊆⁺)
  open import Properties.Base.Network ⦃ params ⦄ ⦃ assumptions ⦄

  messages⊆history : ∀ {N : GlobalState} →
      N₀ ↝⋆ N
    → map msg (N .messages) ⊆ˢ N .history
  messages⊆history = messages⊆historyʳ ∘ Star⇒Starʳ
    where
      open RTC; open Starʳ
      messages⊆historyʳ : ∀ {N : GlobalState} →
          N₀ ↝⋆ʳ N
        → L.map msg (N .messages) ⊆ˢ N .history
      messages⊆historyʳ εʳ = L.SubS.⊆-refl
      messages⊆historyʳ {N} (_◅ʳ_ {j = N′} N₀↝⋆ʳN′ N′↝N) = goal N′↝N
        where
          ih : L.map msg (N′ .messages) ⊆ˢ N′ .history
          ih = messages⊆historyʳ N₀↝⋆ʳN′

          goal : N′ ↝ N → L.map msg (N .messages) ⊆ˢ N .history
          goal (deliverMsgs {N′ = N″} N′Ready N′—[eoN′]↓→∗N″) = goal* $ —[]→∗⇒—[]→∗ʳ N′—[eoN′]↓→∗N″
            where
              goal* : ∀ {N″ ps} →
                   _ ⊢ N′ —[ ps ]↓→∗ʳ N″
                 → L.map msg (N″ .messages) ⊆ˢ N″ .history
              goal* [] = ih
              goal* {N″} (_∷ʳ_ {is = ps} {i = p} {s′ = N‴} N′—[ps]↓→∗ʳN‴ N‴↝[p]↓N″) = step* N‴↝[p]↓N″
                where
                  ih* : L.map msg (N‴ .messages) ⊆ˢ N‴ .history
                  ih* = goal* N′—[ps]↓→∗ʳN‴

                  step* : _ ⊢ N‴ —[ p ]↓→ N″ → L.map msg (N″ .messages) ⊆ˢ N″ .history
                  step* (unknownParty↓ _  ) = ih*
                  step* (honestParty↓  _ _) = L.SubS.⊆-trans (L.SubS.map⁺ _ $ L.SubS.filter-⊆ _ _) ih*
                  step* (corruptParty↓ _ _) = step*′ {mds}
                    where
                      mds : List (Message × DelayMap)
                      mds =
                        processMsgsᶜ
                          (L.map msg (immediateMsgs p N‴))
                          (N‴ .clock)
                          (N‴ .history)
                          (removeImmediateMsgs p N‴ .messages)
                          (N‴ .advState)
                          .proj₁

                      Nᶜ : List (Message × DelayMap) → GlobalState
                      Nᶜ mds = broadcastMsgsᶜ mds (removeImmediateMsgs p N‴)

                      step*′ : ∀ {mds} →
                        L.map msg (Nᶜ mds .messages) ⊆ˢ Nᶜ mds .history
                      step*′ {[]} = L.SubS.⊆-trans (L.SubS.map⁺ _ $ L.SubS.filter-⊆ _ _) ih*
                      step*′ {(m , φ) ∷ mds}
                        rewrite
                          L.map-++ msg (L.map (λ party → ⦅ m , party , φ party .value ⦆) (Nᶜ mds .execOrder)) (Nᶜ mds .messages)
                        | sym $ L.map-∘ {g = msg} {f = λ party → ⦅ m , party , φ party .value ⦆} (Nᶜ mds .execOrder)
                          = ++-meet (map[const-x]xs⊆x∷ys {xs = Nᶜ mds .execOrder} {x = m}) (∷-⊆⁺ (step*′ {mds}))
          goal (makeBlock {N′ = N″} N′MsgsDelivered N′—[eoN′]↑→∗N″) = goal* $ —[]→∗⇒—[]→∗ʳ N′—[eoN′]↑→∗N″
            where
              goal* : ∀ {N″ ps} →
                  _ ⊢ N′ —[ ps ]↑→∗ʳ N″
                → L.map msg (N″ .messages) ⊆ˢ N″ .history
              goal* [] = ih
              goal* {N″} (_∷ʳ_ {is = ps} {i = p} {s′ = N‴} N′—[ps]↑→∗ʳN‴ N‴↝[p]↑N″) = step* N‴↝[p]↑N″
                where
                  ih* : L.map msg (N‴ .messages) ⊆ˢ N‴ .history
                  ih* = goal* N′—[ps]↑→∗ʳN‴

                  step* : _ ⊢ N‴ —[ p ]↑→ N″ → L.map msg (N″ .messages) ⊆ˢ N″ .history
                  step* (unknownParty↑ _  ) = ih*
                  step* (honestParty↑ {ls = ls} _ _) = step*′ {mb .proj₁}
                    where
                      mb : List Message × LocalState
                      mb = makeBlockʰ (N‴ .clock) (txSelection (N‴ .clock) p) p ls

                      N‴ʰ : List Message → GlobalState
                      N‴ʰ ms = broadcastMsgsʰ ms (updateLocalState p (mb .proj₂) N‴)

                      step*′ : ∀ {ms} →
                        L.map msg (N‴ʰ ms .messages) ⊆ˢ N‴ʰ ms .history
                      step*′ {[]} = ih*
                      step*′ {m ∷ ms}
                        rewrite
                          L.map-++ msg (L.map (λ party → ⦅ m , party , 𝟙 ⦆) (N‴ʰ ms .execOrder)) (N‴ʰ ms .messages)
                        | sym $ L.map-∘ {g = msg} {f = λ party → ⦅ m , party , 𝟙 ⦆} (N‴ʰ ms .execOrder)
                        = ++-meet (map[const-x]xs⊆x∷ys {xs = N‴ʰ ms .execOrder} {x = m}) (∷-⊆⁺ (step*′ {ms}))
                  step* (corruptParty↑ _ _) = step*′ {mds}
                    where
                      mds : List (Message × DelayMap)
                      mds = makeBlockᶜ (N‴ .clock) (N‴ .history) (N‴ .messages) (N‴ .advState) .proj₁

                      N‴ᶜ : List (Message × DelayMap) → GlobalState
                      N‴ᶜ mds = broadcastMsgsᶜ mds N‴

                      step*′ : ∀ {mds} →
                        L.map msg (N‴ᶜ mds .messages) ⊆ˢ N‴ᶜ mds .history
                      step*′ {[]} = ih*
                      step*′ {(m , φ) ∷ mds}
                        rewrite
                          L.map-++ msg (L.map (λ party → ⦅ m , party , φ party .value ⦆) (N‴ᶜ mds .execOrder)) (N‴ᶜ mds .messages)
                        | sym $ L.map-∘ {g = msg} {f = λ party → ⦅ m , party , φ party .value ⦆} (N‴ᶜ mds .execOrder)
                          = ++-meet (map[const-x]xs⊆x∷ys {xs = N‴ᶜ mds .execOrder} {x = m}) (∷-⊆⁺ (step*′ {mds}))
          goal (advanceRound   _) rewrite messagesAfterTickPreservation N′ = ih
          goal (permuteParties _) = ih
          goal (permuteMsgs    π) = L.SubS.⊆-trans (≡ˢ⇒⊆×⊇ (messagesAfterPermutationPreservation {N = N′} π) .proj₁) ih

  honestGlobalTreeButGBInBlockHistory : ∀ {N : GlobalState} →
      N₀ ↝⋆ N
    → filter ¿ _≢ genesisBlock ¿¹ (allBlocks (honestTree N)) ⊆ˢ blockHistory N
  honestGlobalTreeButGBInBlockHistory = honestGlobalTreeButGBInBlockHistoryʳ ∘ Star⇒Starʳ
    where
      open RTC; open Starʳ

      honestGlobalTreeButGBInBlockHistoryʳ :  ∀ {N : GlobalState} →
          N₀ ↝⋆ʳ N
        → filter ¿ _≢ genesisBlock ¿¹ (allBlocks (honestTree N)) ⊆ˢ blockHistory N
      honestGlobalTreeButGBInBlockHistoryʳ εʳ = subst (_⊆ˢ []) (sym allGBs) L.SubS.⊆-refl
        where
          [≡gb]⋐[∁≢gb] : (_≡ genesisBlock) ⋐ ∁ (_≢ genesisBlock)
          [≡gb]⋐[∁≢gb] = _|>_

          allGBs : filter ¿ _≢ genesisBlock ¿¹ (allBlocks (honestTree N₀)) ≡ []
          allGBs = L.filter-none _ {xs = allBlocks _} $ L.All.map [≡gb]⋐[∁≢gb] allGBsInHonestTree₀
      honestGlobalTreeButGBInBlockHistoryʳ {N} N₀↝⋆ʳN@(_◅ʳ_ {j = N′} N₀↝⋆ʳN′ N′↝N) = goal N′↝N
        where
          N₀↝⋆N : N₀ ↝⋆ N
          N₀↝⋆N = Starʳ⇒Star N₀↝⋆ʳN

          N₀↝⋆N′ : N₀ ↝⋆ N′
          N₀↝⋆N′ = Starʳ⇒Star N₀↝⋆ʳN′

          ih : filter ¿ _≢ genesisBlock ¿¹ (allBlocks (honestTree N′)) ⊆ˢ blockHistory N′
          ih = honestGlobalTreeButGBInBlockHistoryʳ N₀↝⋆ʳN′

          goal : N′ ↝ N → filter ¿ _≢ genesisBlock ¿¹ (allBlocks (honestTree N)) ⊆ˢ blockHistory N
          goal (deliverMsgs {N′ = N″} N′Ready N′—[eoN′]↓→∗N″) = L.SubS.⊆-trans goal′ bhN′⊆bhN
            where
              bhN′⊆bhN : blockHistory N′ ⊆ˢ blockHistory N
              bhN′⊆bhN = blockHistoryPreservation-↓∗ N′—[eoN′]↓→∗N″

              goal′ : filter ¿ _≢ genesisBlock ¿¹ (allBlocks (honestTree N)) ⊆ˢ blockHistory N′
              goal′ {b} b∈≢gb[htN] with L.Mem.∈-filter⁻ ¿ _≢ genesisBlock ¿¹ {xs = allBlocks _} b∈≢gb[htN]
              ... | b∈htN , b≢gb with honestGlobalTreeBlockInSomeHonestLocalTree N₀↝⋆N b∈htN
              ... | p , ls , lspN , b∈lst , hp , p∈eoN = goal* 𝟘s⊆bhN′ b∈ls′+𝟘s
                where
                  hasLspN′ : p hasStateIn N′
                  hasLspN′ = L.All.lookup (allPartiesHaveLocalState N₀↝⋆N′) p∈N′
                    where
                      p∈N : p ∈ N .execOrder
                      p∈N = hasState⇒∈execOrder N₀↝⋆N (≡just⇒Is-just lspN)

                      p∈N′ : p ∈ N′ .execOrder
                      p∈N′ = ∈-resp-↭ (↭-sym (execOrderPreservation-↭-↝ N′↝N)) p∈N

                  ls′ : LocalState
                  ls′ = M.to-witness hasLspN′

                  lspN′ : N′ .states ⁉ p ≡ just ls′
                  lspN′ = Is-just⇒to-witness hasLspN′

                  Nᵖ : GlobalState
                  Nᵖ = honestMsgsDelivery p ls′ N′

                  N′↝[p]↓Nᵖ : N′ ↝[ p ]↓ Nᵖ
                  N′↝[p]↓Nᵖ = honestParty↓ lspN′ hp

                  lspNᵖ : Nᵖ .states ⁉ p ≡ just ls
                  lspNᵖ = trans (sym lspN≡lspNᵖ) lspN
                    where
                      lspN≡lspNᵖ : N .states ⁉ p ≡ Nᵖ .states ⁉ p
                      lspN≡lspNᵖ = localStatePreservation-↓∗ N₀↝⋆N′ N′—[eoN′]↓→∗N″ N′↝[p]↓Nᵖ

                  𝟘s : List Message
                  𝟘s = L.map msg (immediateMsgs p N′)

                  ls′+𝟘s : LocalState
                  ls′+𝟘s = L.foldr (flip addBlock ∘ projBlock) ls′ 𝟘s

                  ls≡ls′+𝟘s : ls ≡ ls′+𝟘s
                  ls≡ls′+𝟘s = sym $ M.just-injective (trans (sym lspNᵖ≡ls′+𝟘s) lspNᵖ)
                    where
                      lspNᵖ≡ls′+𝟘s : Nᵖ .states ⁉ p ≡ just ls′+𝟘s
                      lspNᵖ≡ls′+𝟘s rewrite set-⁉ (N′ .states) p ls′+𝟘s = refl

                  b∈ls′+𝟘s : b ∈ allBlocks (ls′+𝟘s .tree)
                  b∈ls′+𝟘s rewrite sym ls≡ls′+𝟘s = b∈lst

                  𝟘s⊆bhN′ : 𝟘s ⊆ˢ history N′
                  𝟘s⊆bhN′ = L.SubS.⊆-trans (L.SubS.map⁺ _ $ L.SubS.filter-⊆ _ _) (messages⊆history N₀↝⋆N′)

                  goal* : ∀ {ms} →
                      ms ⊆ˢ history N′
                    → b ∈ allBlocks (L.foldr (flip addBlock ∘ projBlock) ls′ ms .tree)
                    → b ∈ blockHistory N′
                  goal* {[]} _ b∈t = ih $ L.Mem.∈-filter⁺ _ b∈htN′ b≢gb
                    where
                      b∈htN′ : b ∈ allBlocks (honestTree N′)
                      b∈htN′ = honestLocalTreeInHonestGlobalTree N₀↝⋆N′ hp lspN′ b∈t
                  goal* {m@(newBlock b′) ∷ ms} m∷ms⊆hN′ b∈tm∷ms = case L.Mem.∈-++⁻ (allBlocks _) b∈tms+b′ of λ where
                      (inj₁ b∈tms)       → goal* {ms} ms⊆hN′ b∈tms
                      (inj₂ (here b≡b′)) → b∈bhN′ b≡b′
                    where
                      m∈hN′ : m ∈ history N′
                      m∈hN′ = ∷⊆⇒∈ m∷ms⊆hN′

                      b∈bhN′ : b ≡ b′ → b ∈ blockHistory N′
                      b∈bhN′ b≡b′ rewrite b≡b′ = L.Mem.∈-map⁺ _ m∈hN′

                      ms⊆hN′ : ms ⊆ˢ history N′
                      ms⊆hN′ = ∷-⊆ m∷ms⊆hN′

                      b∈tms+b′ : b ∈ allBlocks (L.foldr (flip addBlock ∘ projBlock) ls′ ms .tree) ++ [ b′ ]
                      b∈tms+b′ =
                        b
                          ∈⟨ b∈tm∷ms ⟩
                        allBlocks (extendTree (L.foldr (flip addBlock ∘ projBlock) ls′ ms .tree) b′)
                          ⊆⟨ ≡ˢ⇒⊆×⊇ (extendable _ _) .proj₁ ⟩
                        allBlocks (L.foldr (flip addBlock ∘ projBlock) ls′ ms .tree) ++ [ b′ ] ∎
                          where open L.SubS.⊆-Reasoning Block
          goal (makeBlock {N′ = N″} N′MsgsDelivered N′—[eoN′]↑→∗N″) = goal* (—[]→∗⇒—[]→∗ʳ N′—[eoN′]↑→∗N″)
            where
              goal* : ∀ {N* ps} →
                  _ ⊢ N′ —[ ps ]↑→∗ʳ N*
                → filter ¿ _≢ genesisBlock ¿¹ (allBlocks (honestTree N*)) ⊆ˢ blockHistory N*
              goal* {N*} {[]} [] = ih
              goal* {N*} {[]} (_∷ʳ_ {eq = eq} _ _) = contradiction eq []≢∷ʳ
              goal* {N*} {p ∷ ps} (_∷ʳ_ {is = ps′} {i = p′} {s′ = N‴} {eq = eq} ts⋆ ts) = step ts
                where
                  ih* : filter ¿ _≢ genesisBlock ¿¹ (allBlocks (honestTree N‴)) ⊆ˢ blockHistory N‴
                  ih* = goal* {N‴} {ps′} ts⋆

                  step : _ ⊢ N‴ —[ p′ ]↑→ N* → filter ¿ _≢ genesisBlock ¿¹ (allBlocks (honestTree N*)) ⊆ˢ blockHistory N*
                  step (unknownParty↑ _  ) = ih*
                  step (corruptParty↑ _ _) = step′
                    where
                      mds : List (Message × DelayMap)
                      mds = makeBlockᶜ (N‴ .clock) (N‴ .history) (N‴ .messages) (N‴ .advState).proj₁

                      step′ :
                        filter ¿ _≢ genesisBlock ¿¹ (allBlocks (honestTree (broadcastMsgsᶜ mds N‴)))
                        ⊆ˢ
                        blockHistory (broadcastMsgsᶜ mds N‴)
                      step′
                        rewrite
                          localStatePreservation-broadcastMsgsᶜ {N‴} {mds}
                        | sym $ execOrderPreservation-≡-broadcastMsgsᶜ mds N‴
                          = L.SubS.⊆-trans ih* (step* {mds})
                        where
                          step* : ∀ {mds} → blockHistory N‴ ⊆ˢ blockHistory (broadcastMsgsᶜ mds N‴)
                          step* {[]}      = L.SubS.⊆-refl
                          step* {_ ∷ mds} = L.SubS.⊆-trans (step* {mds}) (L.SubS.xs⊆x∷xs _ _)
                  step (honestParty↑ {ls = ls} lsπ hp′π) with Params.winnerᵈ params {p′} {N‴ .clock}
                  ... | ⁇ (no ¬isWinner)
                    rewrite
                      dec-no ¿ winner p′ (N‴ .clock) ¿ ¬isWinner
                      = L.SubS.⊆-trans (L.SubS.filter⁺′ _ _ id (step* {N‴ .execOrder})) ih*
                    where
                      N‴⁺ : GlobalState
                      N‴⁺ = updateLocalState p′ ls N‴

                      open import Relation.Unary.Properties renaming (⊆-refl to ⋐-refl)

                      step* : ∀ {ps*} →
                        allBlocks (honestTree record N‴⁺ {execOrder = ps*})
                        ⊆ˢ
                        allBlocks (honestTree record N‴ {execOrder = ps*})
                      step* {[]} = L.SubS.⊆-refl
                      step* {p* ∷ ps*} with honestyOf p* in hp*
                      ... | corrupt = step* {ps*}
                      ... | honest rewrite hp* = let open L.SubS.⊆-Reasoning Block in begin
                        allBlocks (buildTree (blocks N‴⁺ p* ++ L.concatMap (blocks N‴⁺) (L.filter ¿ Honest ¿¹ ps*)))
                          ⊆⟨ ≡ˢ⇒⊆×⊇ (allBlocksBuildTree-++ (blocks N‴⁺ p*) _) .proj₁ ⟩
                        allBlocks (buildTree (blocks N‴⁺ p*))
                        ++
                        allBlocks (honestTree record N‴⁺ {execOrder = ps*})
                          ⊆⟨ L.SubS.++⁺ tbksN‴⁺⊆tbksN‴ (step* {ps*}) ⟩
                        allBlocks (buildTree (blocks N‴ p*))
                        ++
                        allBlocks (honestTree record N‴ {execOrder = ps*})
                          ⊆⟨ ≡ˢ⇒⊆×⊇ (allBlocksBuildTree-++ (blocks N‴ p*) _) .proj₂ ⟩
                        allBlocks (buildTree (blocks N‴ p* ++ L.concatMap (blocks N‴) (L.filter ¿ Honest ¿¹ ps*)))
                          ∎
                        where
                          eqBlocks : blocks N‴⁺ p* ≡ blocks N‴ p*
                          eqBlocks with p* ≟ p′
                          ... | yes eq rewrite eq | lsπ | set-⁉   (N‴ .states) p′    ls             = refl
                          ... | no neq rewrite      lsπ | set-⁉-¬ (N‴ .states) p′ p* ls (≢-sym neq) = refl

                          tbksN‴⁺⊆tbksN‴ : allBlocks (buildTree (blocks N‴⁺ p*)) ⊆ˢ allBlocks (buildTree (blocks N‴ p*))
                          tbksN‴⁺⊆tbksN‴ rewrite eqBlocks = L.SubS.⊆-refl

                  ... | ⁇ (yes isWinner) rewrite lsπ = let open L.SubS.⊆-Reasoning Block in begin
                    filter ¿ _≢ genesisBlock ¿¹ (allBlocks (honestTree N‴⁺))
                      ⊆⟨ L.SubS.filter⁺′ _ _ id $ step* {N‴ .execOrder} ⟩
                    filter ¿ _≢ genesisBlock ¿¹ (allBlocks (honestTree N‴) ++ [ nb ])
                      ≡⟨ L.filter-++ _ (allBlocks _) [ nb ] ⟩
                    filter ¿ _≢ genesisBlock ¿¹ (allBlocks (honestTree N‴)) ++ filter ¿ _≢ genesisBlock ¿¹ [ nb ]
                      ⊆⟨ L.SubS.++⁺ˡ _ ih* ⟩
                    blockHistory N‴ ++ filter ¿ _≢ genesisBlock ¿¹ [ nb ]
                      ⊆⟨ ⊆-++-comm (blockHistory N‴) _ ⟩
                    filter ¿ _≢ genesisBlock ¿¹ [ nb ] ++ blockHistory N‴
                      ⊆⟨ L.SubS.++⁺ˡ (blockHistory N‴) $ L.SubS.filter-⊆ ¿ _≢ genesisBlock ¿¹ [ nb ] ⟩
                    nb ∷ blockHistory N‴
                      ∎
                    where
                      best : Chain
                      best = bestChain (N‴ .clock ∸ 1) (ls .tree)

                      nb : Block
                      nb = mkBlock (hash (tip best)) (N‴ .clock) (txSelection (N‴ .clock) p′) p′

                      N‴⁺ : GlobalState
                      N‴⁺ = updateLocalState p′ (addBlock ls nb) N‴

                      tnb : Tree
                      tnb = extendTree (ls .tree) nb

                      blocksN‴⁺≡p′ : blocks N‴⁺ p′ ≡ allBlocks tnb
                      blocksN‴⁺≡p′ rewrite set-⁉ (N‴ .states) p′ (addBlock ls nb) = refl

                      blocksN‴⁺≢p′ : ∀ {p*} → p* ≢ p′ → blocks N‴ p* ≡ blocks N‴⁺ p*
                      blocksN‴⁺≢p′ {p*} p*≢p′ rewrite lsπ | set-⁉-¬ (N‴ .states) p′ p* (addBlock ls nb) (≢-sym p*≢p′) = refl

                      step* : ∀ {ps*} →
                        allBlocks (honestTree record N‴⁺ {execOrder = ps*})
                        ⊆ˢ
                        allBlocks (honestTree record N‴ {execOrder = ps*}) ++ [ nb ]
                      step* {[]} = L.SubS.xs⊆xs++ys _ _
                      step* {p* ∷ ps*} with honestyOf p* in hp*
                      ... | corrupt = step* {ps*}
                      ... | honest rewrite hp* = let open L.SubS.⊆-Reasoning Block in begin
                        allBlocks (buildTree (blocks N‴⁺ p* ++ L.concatMap (blocks N‴⁺) (L.filter ¿ Honest ¿¹ ps*)))
                          ⊆⟨ ≡ˢ⇒⊆×⊇ (allBlocksBuildTree-++ (blocks N‴⁺ p*) _) .proj₁ ⟩
                        allBlocks (buildTree (blocks N‴⁺ p*))
                        ++
                        allBlocks (honestTree record N‴⁺ {execOrder = ps*})
                          ⊆⟨ L.SubS.++⁺ tbksN‴⁺⊆tbksN‴+nb (step* {ps*}) ⟩
                        (allBlocks (buildTree (blocks N‴ p*)) ++ [ nb ])
                        ++
                        allBlocks (honestTree record N‴ {execOrder = ps*}) ++ [ nb ]
                          ⊆⟨ lemma {xs = allBlocks (buildTree (blocks N‴ p*))} {zs = [ nb ]} ⟩
                        (allBlocks (buildTree (blocks N‴ p*)) ++ allBlocks (honestTree record N‴ {execOrder = ps*})) ++ [ nb ]
                         ++ [ nb ]
                          ⊆⟨ L.SubS.++⁺ˡ _ $ ≡ˢ⇒⊆×⊇ (allBlocksBuildTree-++ (blocks N‴ p*) _) .proj₂ ⟩
                        allBlocks (buildTree (blocks N‴ p* ++ L.concatMap (blocks N‴) (L.filter ¿ Honest ¿¹ ps*))) ++ [ nb ] ++ [ nb ]
                          ⊆⟨ L.SubS.++⁺ʳ _ $ ++-absorb [ nb ] ⟩
                        allBlocks (buildTree (blocks N‴ p* ++ L.concatMap (blocks N‴) (L.filter ¿ Honest ¿¹ ps*))) ++ [ nb ]
                          ∎
                          where
                            lemma : ∀ {A : Set} {xs ys zs : List A} → (xs ++ zs) ++ ys ++ zs ⊆ˢ (xs ++ ys) ++ zs ++ zs
                            lemma {A} {xs} {ys} {zs} = let open L.SubS.⊆-Reasoning A in begin
                              (xs ++ zs) ++ ys ++ zs   ≡⟨ L.++-assoc xs zs (ys ++ zs) ⟩
                              xs ++ zs ++ ys ++ zs     ≡⟨ cong (xs ++_) $ L.++-assoc zs ys zs ⟨
                              xs ++ (zs ++ ys) ++ zs   ⊆⟨ L.SubS.++⁺ʳ xs $ L.SubS.++⁺ˡ zs $ ⊆-++-comm zs ys ⟩
                              xs ++ (ys ++ zs) ++ zs   ≡⟨ cong (xs ++_) $ L.++-assoc ys zs zs ⟩
                              xs ++ ys ++ zs ++ zs     ≡⟨ L.++-assoc xs ys (zs ++ zs) ⟨
                              (xs ++ ys) ++ zs ++ zs   ∎

                            tbksN‴⁺⊆tbksN‴+nb : allBlocks (buildTree (blocks N‴⁺ p*)) ⊆ˢ allBlocks (buildTree (blocks N‴ p*)) ++ [ nb ]
                            tbksN‴⁺⊆tbksN‴+nb  with p* ≟ p′
                            ... | yes p*≡p′ rewrite p*≡p′ | lsπ | blocksN‴⁺≡p′ = let open L.SubS.⊆-Reasoning Block in begin
                              allBlocks (buildTree (allBlocks tnb))
                                ⊆⟨ ≡ˢ⇒⊆×⊇ (buildTreeUsesAllBlocks _) .proj₁ ⟩
                              genesisBlock ∷ allBlocks tnb
                                ⊆⟨ L.SubS.∷⁺ʳ _ $ ≡ˢ⇒⊆×⊇ (extendable _ _) .proj₁ ⟩
                              genesisBlock ∷ allBlocks (ls .tree) ++ [ nb ]
                                ⊆⟨ L.SubS.++⁺ˡ _ $ ≡ˢ⇒⊆×⊇ (buildTreeUsesAllBlocks _) .proj₂ ⟩
                              allBlocks (buildTree (allBlocks (ls .tree))) ++ [ nb ]
                                ∎
                            ... | no p*≢p′ = let open L.SubS.⊆-Reasoning Block in begin
                              allBlocks (buildTree (blocks N‴⁺ p*))
                                ⊆⟨ L.SubS.⊆-reflexive $ cong (allBlocks ∘ buildTree) $ sym (blocksN‴⁺≢p′ p*≢p′) ⟩
                              allBlocks (buildTree (blocks N‴ p*))
                                ⊆⟨ L.SubS.xs⊆xs++ys _ _ ⟩
                              allBlocks (buildTree (blocks N‴ p*)) ++ [ nb ]
                                ∎

          goal (advanceRound _) = honestGlobalTreeButGBInBlockHistoryʳ N₀↝⋆ʳN′

          goal (permuteParties {parties = ps} eoN′↭ps) = let open L.SubS.⊆-Reasoning Block in begin
            filter ¿ _≢ genesisBlock ¿¹ (allBlocks (honestTree Nps))
              ⊆⟨ proj₁ $ ≡ˢ⇒⊆×⊇ (λ {b} → ∼-begin
                b ∈ filter ¿ _≢ genesisBlock ¿¹ (allBlocks (honestTree Nps))
                  ∼⟨ filter-cong (λ {b} → ∼-begin
                    b ∈ allBlocks (honestTree Nps)
                      ∼⟨ buildTreeUsesAllBlocks _ ⟩
                    b ∈ genesisBlock ∷ (L.concatMap (blocks Nps) $ L.filter ¿ Honest ¿¹ ps)
                      ∼⟨ ∷-cong refl (λ {b} → ∼-begin
                          b ∈ (L.concatMap (blocks Nps) $ L.filter ¿ Honest ¿¹ ps)
                            ∼⟨ concat-cong (λ {b} → ∼-begin
                               b ∈ (L.map (blocks Nps) $ L.filter ¿ Honest ¿¹ ps)
                                 ∼⟨ bag-=⇒ $ ↭⇒∼bag $ map⁺ _ $ filter-↭ _ $ ↭-sym eoN′↭ps ⟩
                               b ∈ (L.map (blocks N′) $ L.filter ¿ Honest ¿¹ (N′ .execOrder))
                                 ∼-∎
                               ) ⟩
                          b ∈ (L.concatMap (blocks N′) $ L.filter ¿ Honest ¿¹ (N′ .execOrder))
                            ∼-∎
                          ) ⟩
                    b ∈ genesisBlock ∷ (L.concatMap (blocks N′) $ L.filter ¿ Honest ¿¹ (N′ .execOrder))
                      ∼⟨ SK-sym $ buildTreeUsesAllBlocks _ ⟩
                    b ∈ allBlocks (honestTree N′)
                      ∼-∎ )
                    ⟩
                b ∈ filter ¿ _≢ genesisBlock ¿¹ (allBlocks (honestTree N′))
                  ∼-∎ )
               ⟩
            filter ¿ _≢ genesisBlock ¿¹ (allBlocks (honestTree N′))
              ⊆⟨ honestGlobalTreeButGBInBlockHistoryʳ N₀↝⋆ʳN′ ⟩
            blockHistory Nps
              ∎
            where
              open Related.EquationalReasoning renaming (begin_ to ∼-begin_; _∎ to _∼-∎)

              Nps : GlobalState
              Nps = record N′ { execOrder = ps }

          goal (permuteMsgs _) = honestGlobalTreeButGBInBlockHistoryʳ N₀↝⋆ʳN′

  noPrematureHonestBlocks : ∀ {N : GlobalState} →
      N₀ ↝⋆ N
    → ForgingFree N
    → L.All.All ((_≤ N .clock) ∘ slot) (honestBlockHistory N)
  noPrematureHonestBlocks = noPrematureHonestBlocksʳ ∘ Star⇒Starʳ
    where
      open RTC; open Starʳ
      noPrematureHonestBlocksʳ : ∀ {N : GlobalState} →
          N₀ ↝⋆ʳ N
        → ForgingFree N
        → L.All.All ((_≤ N .clock) ∘ slot) (honestBlockHistory N)
      noPrematureHonestBlocksʳ εʳ _ = []
      noPrematureHonestBlocksʳ {N} (_◅ʳ_ {j = N′} N₀↝⋆ʳN′ N′↝N) ffN = goal N′↝N
        where
          ffN′ : ForgingFree N′
          ffN′ = ForgingFreePrev (N′↝N ◅ ε) ffN

          ih : L.All.All ((_≤ N′ .clock) ∘ slot) (honestBlockHistory N′)
          ih = noPrematureHonestBlocksʳ N₀↝⋆ʳN′ ffN′

          goal : N′ ↝ N → L.All.All ((_≤ N .clock) ∘ slot) (honestBlockHistory N)
          goal (deliverMsgs {N′ = N″} N′Ready N′—[eoN′]↓→∗N″) =
            subst
              _
              (sym $ clockPreservation-↓∗ N′—[eoN′]↓→∗N″)
              (goal* N″↷↓N $ —[]→∗⇒—[]→∗ʳ N′—[eoN′]↓→∗N″)
            where
              N″↷↓N : N″ ↷↓ N
              N″↷↓N = progress↓ (↷↓-refl {N})

              goal* : ∀ {N″ ps} →
                   N″ ↷↓ N
                 → _ ⊢ N′ —[ ps ]↓→∗ʳ N″
                 → L.All.All ((_≤ N′ .clock) ∘ slot) (honestBlockHistory N″)
              goal* _ [] = ih
              goal* {N″} N″↷↓N (_∷ʳ_ {is = ps} {i = p} {s′ = N‴} N′—[ps]↓→∗ʳN‴ N‴↝[p]↓N″) = step* N‴↝[p]↓N″
                where
                  N‴↷↓N : N‴ ↷↓ N
                  N‴↷↓N = delivery↓ N‴↝[p]↓N″ N″↷↓N

                  ih* : L.All.All ((_≤ N′ .clock) ∘ slot) (honestBlockHistory N‴)
                  ih* = goal* N‴↷↓N N′—[ps]↓→∗ʳN‴

                  step* : _ ⊢ N‴ —[ p ]↓→ N″ → L.All.All ((_≤ N′ .clock) ∘ slot) (honestBlockHistory N″)
                  step* (unknownParty↓ _  ) = ih*
                  step* (honestParty↓  _ _) = ih*
                  step* (corruptParty↓ _ _) = step*′ {mds} sub
                    where
                      mds : List (Message × DelayMap)
                      mds =
                        processMsgsᶜ
                          (L.map msg (immediateMsgs p N‴))
                          (N‴ .clock)
                          (N‴ .history)
                          (removeImmediateMsgs p N‴ .messages)
                          (N‴ .advState)
                          .proj₁

                      sub : L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                      sub = ffN .proj₁ N‴↷↓N

                      step*′ : ∀ {mds} →
                          L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                        → L.All.All
                            ((_≤ N′ .clock) ∘ slot)
                            (honestBlockHistory (broadcastMsgsᶜ mds (removeImmediateMsgs p N‴)))
                      step*′ {[]} _ = ih*
                      step*′ {(m , _) ∷ mds} sub with bᵐ ← projBlock m | ¿ HonestBlock bᵐ ¿
                      ... | yes hbᵐ = bᵐₜ≤N′ₜ ∷ step*′ {mds} sub′
                        where
                          bᵐₜ≤N′ₜ : bᵐ .slot ≤ N′ .clock
                          bᵐₜ≤N′ₜ = L.All.lookup ih* $ ∷⊆⇒∈ sub

                          sub′ : L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                          sub′ = L.SubS.⊆-trans (L.SubS.xs⊆x∷xs _ bᵐ) sub
                      ... | no ¬hbᵐ = step*′ {mds} sub
          goal (makeBlock {N′ = N″} N′MsgsDelivered N′—[eoN′]↑→∗N″) =
            subst
              _
              (sym $ clockPreservation-↑∗ N′—[eoN′]↑→∗N″)
              (goal* N″↷↑N $ —[]→∗⇒—[]→∗ʳ N′—[eoN′]↑→∗N″)
            where
              N″↷↑N : N″ ↷↑ N
              N″↷↑N = progress↑ (↷↑-refl {N})

              goal* : ∀ {N″ ps} →
                   N″ ↷↑ N
                 → _ ⊢ N′ —[ ps ]↑→∗ʳ N″
                 → L.All.All ((_≤ N′ .clock) ∘ slot) (honestBlockHistory N″)
              goal* _ [] = ih
              goal* {N″} N″↷↑N (_∷ʳ_ {is = ps} {i = p} {s′ = N‴} N′—[ps]↑→∗ʳN‴ N‴↝[p]↑N″) = step* N‴↝[p]↑N″
                where
                  N‴↷↑N : N‴ ↷↑ N
                  N‴↷↑N = blockMaking↑ N‴↝[p]↑N″ N″↷↑N

                  ih* : L.All.All ((_≤ N′ .clock) ∘ slot) (honestBlockHistory N‴)
                  ih* = goal* N‴↷↑N N′—[ps]↑→∗ʳN‴

                  step* : _ ⊢ N‴ —[ p ]↑→ N″ → L.All.All ((_≤ N′ .clock) ∘ slot) (honestBlockHistory N″)
                  step* (unknownParty↑ _  ) = ih*
                  step* (honestParty↑ {ls = ls} lsπ hp) with Params.winnerᵈ params {p} {N‴ .clock}
                  ... | ⁇ (no ¬isWinner) = ih*
                  ... | ⁇ (yes isWinner) rewrite lsπ | hp = nbₜ≤N′ₜ ∷ ih*
                    where
                      best : Chain
                      best = bestChain (N‴ .clock  ∸ 1) (ls .tree)

                      nb : Block
                      nb = mkBlock (hash (tip best)) (N‴ .clock) (txSelection (N‴ .clock) p) p

                      nbₜ≤N′ₜ : nb .slot ≤ N′ .clock
                      nbₜ≤N′ₜ rewrite clockPreservation-↑∗ (—[]→∗ʳ⇒—[]→∗ N′—[ps]↑→∗ʳN‴) = Nat.≤-refl
                  step* (corruptParty↑ _ _) = step*′ {mds} sub
                    where
                      mds : List (Message × DelayMap)
                      mds = makeBlockᶜ (N‴ .clock) (N‴ .history) (N‴ .messages) (N‴ .advState) .proj₁

                      sub : L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                      sub = ffN .proj₂ N‴↷↑N

                      step*′ : ∀ {mds} →
                          L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                        → L.All.All ((_≤ N′ .clock) ∘ slot) (honestBlockHistory (broadcastMsgsᶜ mds N‴))
                      step*′ {[]} _ = ih*
                      step*′ {(m , _) ∷ mds} sub with bᵐ ← projBlock m | ¿ HonestBlock bᵐ ¿
                      ... | yes hbᵐ = bᵐₜ≤N′ₜ ∷ step*′ {mds} sub′
                        where
                          bᵐₜ≤N′ₜ : bᵐ .slot ≤ N′ .clock
                          bᵐₜ≤N′ₜ = L.All.lookup ih* $ ∷⊆⇒∈ sub

                          sub′ : L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                          sub′ = L.SubS.⊆-trans (L.SubS.xs⊆x∷xs _ bᵐ) sub
                      ... | no ¬hbᵐ = step*′ {mds} sub
          goal (advanceRound   _) = L.All.map Nat.m≤n⇒m≤1+n ih
          goal (permuteParties _) = ih
          goal (permuteMsgs    _) = ih

  noPrematureHonestBlocksAtReady : ∀ {N : GlobalState} →
      N₀ ↝⋆ N
    → ForgingFree N
    → N .progress ≡ ready
    → L.All.All ((_< N .clock) ∘ slot) (honestBlockHistory N)
  noPrematureHonestBlocksAtReady = noPrematureHonestBlocksAtReadyʳ ∘ Star⇒Starʳ
    where
      open RTC; open Starʳ
      noPrematureHonestBlocksAtReadyʳ : ∀ {N : GlobalState} →
          N₀ ↝⋆ʳ N
        → ForgingFree N
        → N .progress ≡ ready
        → L.All.All ((_< N .clock) ∘ slot) (honestBlockHistory N)
      noPrematureHonestBlocksAtReadyʳ εʳ _ _ = []
      noPrematureHonestBlocksAtReadyʳ {N} (_◅ʳ_ {j = N′} N₀↝⋆ʳN′ N′↝N) ffN NReady = goal N′↝N
        where
          ffN′ : ForgingFree N′
          ffN′ = ForgingFreePrev (N′↝N ◅ ε) ffN

          ih : N′ .progress ≡ ready → L.All.All ((_< N′ .clock) ∘ slot) (honestBlockHistory N′)
          ih = noPrematureHonestBlocksAtReadyʳ N₀↝⋆ʳN′ ffN′

          goal : N′ ↝ N → L.All.All ((_< N .clock) ∘ slot) (honestBlockHistory N)
          goal (advanceRound   _) = L.All.map (λ {_} → Nat.s≤s) $ noPrematureHonestBlocks (Starʳ⇒Star N₀↝⋆ʳN′) ffN′
          goal (permuteParties _) = ih NReady
          goal (permuteMsgs    _) = ih NReady

  noPrematureHonestBlocksAt↓ : ∀ {N : GlobalState} →
      N₀ ↝⋆ N
    → ForgingFree N
    → N .progress ≡ msgsDelivered
    → L.All.All ((_< N .clock) ∘ slot) (honestBlockHistory N)
  noPrematureHonestBlocksAt↓ = noPrematureHonestBlocksAt↓ʳ ∘ Star⇒Starʳ
    where
      open RTC; open Starʳ
      noPrematureHonestBlocksAt↓ʳ : ∀ {N : GlobalState} →
          N₀ ↝⋆ʳ N
        → ForgingFree N
        → N .progress ≡ msgsDelivered
        → L.All.All ((_< N .clock) ∘ slot) (honestBlockHistory N)
      noPrematureHonestBlocksAt↓ʳ εʳ _ _ = []
      noPrematureHonestBlocksAt↓ʳ {N} (_◅ʳ_ {j = N′} N₀↝⋆ʳN′ N′↝N) ffN NMsgsDelivered = goal N′↝N
        where
          ffN′ : ForgingFree N′
          ffN′ = ForgingFreePrev (N′↝N ◅ ε) ffN

          ih : N′ .progress ≡ msgsDelivered → L.All.All ((_< N′ .clock) ∘ slot) (honestBlockHistory N′)
          ih = noPrematureHonestBlocksAt↓ʳ N₀↝⋆ʳN′ ffN′

          goal : N′ ↝ N → L.All.All ((_< N .clock) ∘ slot) (honestBlockHistory N)
          goal (deliverMsgs {N′ = N″} N′Ready N′—[eoN′]↓→∗N″) =
            subst
              _
              (sym $ clockPreservation-↓∗ N′—[eoN′]↓→∗N″)
              (goal* N″↷↓N $ —[]→∗⇒—[]→∗ʳ N′—[eoN′]↓→∗N″)
            where
              N″↷↓N : N″ ↷↓ N
              N″↷↓N = progress↓ (↷↓-refl {N})

              goal* : ∀ {N″ ps} →
                   N″ ↷↓ N
                 → _ ⊢ N′ —[ ps ]↓→∗ʳ N″
                 → L.All.All ((_< N′ .clock) ∘ slot) (honestBlockHistory N″)
              goal* _ [] = noPrematureHonestBlocksAtReady (Starʳ⇒Star N₀↝⋆ʳN′) ffN′ N′Ready
              goal* {N″} N″↷↓N (_∷ʳ_ {is = ps} {i = p} {s′ = N‴} N′—[ps]↓→∗ʳN‴ N‴↝[p]↓N″) = step* N‴↝[p]↓N″
                where
                  N‴↷↓N : N‴ ↷↓ N
                  N‴↷↓N = delivery↓ N‴↝[p]↓N″ N″↷↓N

                  ih* : L.All.All ((_< N′ .clock) ∘ slot) (honestBlockHistory N‴)
                  ih* = goal* N‴↷↓N N′—[ps]↓→∗ʳN‴

                  step* : _ ⊢ N‴ —[ p ]↓→ N″ → L.All.All ((_< N′ .clock) ∘ slot) (honestBlockHistory N″)
                  step* (unknownParty↓ _  ) = ih*
                  step* (honestParty↓  _ _) = ih*
                  step* (corruptParty↓ _ _) = step*′ {mds} sub
                    where
                      mds : List (Message × DelayMap)
                      mds =
                        processMsgsᶜ
                          (L.map msg (immediateMsgs p N‴))
                          (N‴ .clock)
                          (N‴ .history)
                          (removeImmediateMsgs p N‴ .messages)
                          (N‴ .advState)
                          .proj₁

                      sub : L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                      sub = ffN .proj₁ N‴↷↓N

                      step*′ : ∀ {mds} →
                          L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                        → L.All.All
                            ((_< N′ .clock) ∘ slot)
                            (honestBlockHistory (broadcastMsgsᶜ mds (removeImmediateMsgs p N‴)))
                      step*′ {[]} _ = ih*
                      step*′ {(m , _) ∷ mds} sub with bᵐ ← projBlock m | ¿ HonestBlock bᵐ ¿
                      ... | yes hbᵐ = bᵐₜ<N′ₜ ∷ step*′ {mds} sub′
                        where
                          bᵐₜ<N′ₜ : bᵐ .slot < N′ .clock
                          bᵐₜ<N′ₜ = L.All.lookup ih* $ ∷⊆⇒∈ sub

                          sub′ : L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                          sub′ = L.SubS.⊆-trans (L.SubS.xs⊆x∷xs _ bᵐ) sub
                      ... | no ¬hbᵐ = step*′ {mds} sub
          goal (permuteParties _) = ih NMsgsDelivered
          goal (permuteMsgs    _) = ih NMsgsDelivered

  honestBlocksBelowSlotPreservation : ∀ {N N′ : GlobalState} →
      N₀ ↝⋆ N
    → N ↝⋆ N′
    → ForgingFree N′
    → filter ((_<? N .clock) ∘ slot) (honestBlockHistory N)
      ≡ˢ
      filter ((_<? N .clock) ∘ slot) (honestBlockHistory N′)
  honestBlocksBelowSlotPreservation = ∣ flip honestBlocksBelowSlotPreservationʳ ⟩- Star⇒Starʳ
    where
      open RTC; open Starʳ
      honestBlocksBelowSlotPreservationʳ :  ∀ {N N° : GlobalState} →
          N ↝⋆ʳ N°
        → N₀ ↝⋆ N
        → ForgingFree N°
        → filter ((_<? N .clock) ∘ slot) (honestBlockHistory N)
          ≡ˢ
          filter ((_<? N .clock) ∘ slot) (honestBlockHistory N°)
      honestBlocksBelowSlotPreservationʳ {N} {.N} εʳ _ _ = ≡ˢ-refl
      honestBlocksBelowSlotPreservationʳ {N} {N°} (_◅ʳ_ {j = N′} N↝⋆ʳN′ N′↝N°) N₀↝⋆N ffN° = goal N′↝N°
        where
          N₀↝⋆N′ : N₀ ↝⋆ N′
          N₀↝⋆N′ = N₀↝⋆N ◅◅ Starʳ⇒Star N↝⋆ʳN′

          ffN′ : ForgingFree N′
          ffN′ = ForgingFreePrev (N′↝N° ◅ ε) ffN°

          ih :
            filter ((_<? N .clock) ∘ slot) (honestBlockHistory N)
            ≡ˢ
            filter ((_<? N .clock) ∘ slot) (honestBlockHistory N′)
          ih = honestBlocksBelowSlotPreservationʳ N↝⋆ʳN′ N₀↝⋆N ffN′

          goal :
              N′ ↝ N°
            →
              filter ((_<? N .clock) ∘ slot) (honestBlockHistory N)
              ≡ˢ
              filter ((_<? N .clock) ∘ slot) (honestBlockHistory N°)
          goal (deliverMsgs {N′ = N″} N′Ready N′—[eoN′]↓→∗N″) {b} = begin
            b ∈ filter ((_<? N .clock) ∘ slot) (honestBlockHistory N)
              ∼⟨ ih ⟩
            b ∈ filter ((_<? N .clock) ∘ slot) (honestBlockHistory N′)
              ∼⟨ filter-cong $ honestBlockHistoryPreservation-↓∗ N₀↝⋆N′ N′—[eoN′]↓→∗N″ ffN° N′Ready ⟩
            b ∈ filter ((_<? N .clock) ∘ slot) (honestBlockHistory N°) ∎
            where open Related.EquationalReasoning
          goal (makeBlock {N′} {N″} N′MsgsDelivered N′—[eoN′]↑→∗N″) = goal* N″↷↑N″[bM] (—[]→∗⇒—[]→∗ʳ N′—[eoN′]↑→∗N″)
            where
              N″↷↑N″[bM] : N″ ↷↑ record N″ { progress = blockMade }
              N″↷↑N″[bM] = progress↑ (↷↑-refl)

              goal* : ∀ {N″ ps} →
                  N″ ↷↑ N°
                → _ ⊢ N′ —[ ps ]↑→∗ʳ N″
                →
                  filter ((_<? N .clock) ∘ slot) (honestBlockHistory N)
                  ≡ˢ
                  filter ((_<? N .clock) ∘ slot) (honestBlockHistory N″)
              goal* {N″} {[]} _ [] = ih
              goal* {N″} {[]} _ (_∷ʳ_ {eq = eq} _ _) = contradiction eq []≢∷ʳ
              goal* {N″} {p ∷ ps} N″↷↑N° (_∷ʳ_ {is = ps′} {i = p′} {s′ = N‴} {eq = eq} ts⋆ ts) = step* ts
                where
                  ih′ :
                    filter ((_<? N .clock) ∘ slot) (honestBlockHistory N)
                    ≡ˢ
                    filter ((_<? N .clock) ∘ slot) (honestBlockHistory N‴)
                  ih′ = goal* {N‴} {ps′} (blockMaking↑ ts N″↷↑N°) ts⋆

                  N‴ₜ≡N′ₜ : N‴ .clock ≡ N′ .clock
                  N‴ₜ≡N′ₜ = clockPreservation-↑∗ (—[]→∗ʳ⇒—[]→∗ ts⋆)

                  step* :
                      _ ⊢ N‴ —[ p′ ]↑→ N″
                    →
                      filter ((_<? N .clock) ∘ slot) (honestBlockHistory N)
                      ≡ˢ
                      filter ((_<? N .clock) ∘ slot) (honestBlockHistory N″)
                  step* (unknownParty↑ _) = ih′
                  step* (honestParty↑ {ls = ls} lsπ hp′π) with Params.winnerᵈ params {p′} {N‴ .clock}
                  ... | ⁇ (yes isWinner) rewrite hp′π = step*-honestParty↑
                    where
                      best : Chain
                      best = bestChain (N‴ .clock ∸ 1) (ls .tree)

                      nb : Block
                      nb = mkBlock (hash (tip best)) (N‴ .clock) (txSelection (N‴ .clock) p′) p′

                      Nₜ≤N′ₜ : N .clock ≤ N‴ .clock
                      Nₜ≤N′ₜ rewrite N‴ₜ≡N′ₜ = clockMonotonicity (Starʳ⇒Star N↝⋆ʳN′)

                      step*-honestParty↑ :
                        filter ((_<? N .clock) ∘ slot) (honestBlockHistory N)
                        ≡ˢ
                        filter ((_<? N .clock) ∘ slot) (nb ∷ honestBlockHistory N‴)
                      step*-honestParty↑
                        rewrite
                          L.filter-reject ((_<? N .clock) ∘ slot) {nb} {honestBlockHistory N‴} (Nat.≤⇒≯ Nₜ≤N′ₜ)
                          = ih′
                  ... | ⁇ (no _) = ih′
                  step* (corruptParty↑ _ _) = step*′ {mds} sub
                    where
                      mds : List (Message × DelayMap)
                      mds = makeBlockᶜ (N‴ .clock) (N‴ .history) (N‴ .messages) (N‴ .advState) .proj₁

                      sub : L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                      sub = ffN° .proj₂ (blockMaking↑ ts N″↷↑N°)

                      step*′ : ∀ {mds} →
                          L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                        →
                          filter ((_<? N .clock) ∘ slot) (honestBlockHistory N)
                          ≡ˢ
                          filter ((_<? N .clock) ∘ slot) (honestBlockHistory (broadcastMsgsᶜ mds N‴))
                      step*′ {[]} _ = ih′
                      step*′ {(m , _) ∷ mds} sub with bᵐ ← projBlock m | ¿ HonestBlock bᵐ ¿
                      ... | no ¬hbᵐ
                        rewrite
                          sym $ L.filter-reject ¿ HonestBlock ¿¹ {bᵐ} {honestBlockHistory (broadcastMsgsᶜ mds N‴)} ¬hbᵐ
                          = step*′ {mds} sub
                      ... | yes hbᵐ with bᵐ .slot <? N .clock
                      ...   | yes bᵐₜ<Nₜ
                                rewrite
                                  L.filter-accept
                                    ((_<? N .clock) ∘ slot) {bᵐ} {honestBlockHistory (broadcastMsgsᶜ mds N‴)} bᵐₜ<Nₜ
                                  = ⊆×⊇⇒≡ˢ ⊆ˢπ ⊇ˢπ
                        where
                          sub′ : L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                          sub′ = L.SubS.⊆-trans (L.SubS.xs⊆x∷xs _ bᵐ) sub

                          ⊆ˢπ :
                            filter ((_<? N .clock) ∘ slot) (honestBlockHistory N)
                            ⊆ˢ
                            bᵐ ∷ filter ((_<? N .clock) ∘ slot) (honestBlockHistory (broadcastMsgsᶜ mds N‴))
                          ⊆ˢπ {b′} b′∈lhs with bᵐ ≟ b′
                          ... | yes eq rewrite eq = x∈x∷xs _
                          ... | no ¬eq = there $ step*′ {mds} sub′ .Equivalence.to b′∈lhs
                            where open Function.Bundles.Equivalence

                          ⊇ˢπ :
                            bᵐ ∷ filter ((_<? N .clock) ∘ slot) (honestBlockHistory (broadcastMsgsᶜ mds N‴))
                            ⊆ˢ
                            filter ((_<? N .clock) ∘ slot) (honestBlockHistory N)
                          ⊇ˢπ = L.SubS.∈-∷⁺ʳ bᵐ∈fhbhN $ ≡ˢ⇒⊆×⊇ (step*′ {mds} sub′) .proj₂
                            where
                              bᵐ∈fhbhN‴ : bᵐ ∈ filter ((_<? N .clock) ∘ slot) (honestBlockHistory N‴)
                              bᵐ∈fhbhN‴ = L.Mem.∈-filter⁺ ((_<? N .clock) ∘ slot) (sub {bᵐ} (x∈x∷xs _)) bᵐₜ<Nₜ

                              bᵐ∈fhbhN : bᵐ ∈ filter ((_<? N .clock) ∘ slot) (honestBlockHistory N)
                              bᵐ∈fhbhN = ≡ˢ⇒⊆×⊇ ih′ .proj₂ bᵐ∈fhbhN‴
                      ...   | no ¬bᵐₜ<Nₜ
                                rewrite
                                  L.filter-reject
                                    ((_<? N .clock) ∘ slot) {bᵐ} {honestBlockHistory (broadcastMsgsᶜ mds N‴)} ¬bᵐₜ<Nₜ
                                  = step*′ {mds} sub′
                        where
                          sub′ : L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                          sub′ = L.SubS.⊆-trans (L.SubS.xs⊆x∷xs _ bᵐ) sub
          goal (advanceRound   _) = ih
          goal (permuteParties _) = ih
          goal (permuteMsgs    _) = ih
