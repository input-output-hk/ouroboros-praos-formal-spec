{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled

open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Base.Time
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot; Honesty)
open import Protocol.Crypto ⦃ params ⦄ using (Hashable); open Hashable ⦃ ... ⦄
open import Protocol.Block ⦃ params ⦄
open import Protocol.Chain ⦃ params ⦄
open import Protocol.TreeType ⦃ params ⦄
open import Protocol.Message ⦃ params ⦄
open import Protocol.Network ⦃ params ⦄; open Envelope
open import Properties.Base.ForgingFree ⦃ params ⦄ ⦃ assumptions ⦄
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Prelude.STS.Properties using (—[]→∗⇒—[]→∗ʳ; —[]→∗ʳ⇒—[]→∗)
open import Data.List.Properties.Ext using (foldr-preservesʳ'; []≢∷ʳ)
open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_; ≡ˢ-refl; ≡ˢ-trans; filter-cong; ⊆×⊇⇒≡ˢ; ≡ˢ⇒⊆×⊇)
open import Data.List.Relation.Binary.Subset.Propositional.Properties.Ext using (∷⊆⇒∈)
open import Data.List.Membership.Propositional.Properties.Ext using (x∈x∷xs)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Ext using (Starʳ)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.Ext using (Star⇒Starʳ; Starʳ⇒Star)
open import Relation.Binary.Core using (_Preserves_⟶_)
open import Data.Nat.Properties using (<-trans)
open import Data.Nat.Base using (z<s; s<s)
open import Function.Related.Propositional as Related
open import Function.Bundles using (Equivalence)
open import Function.Base using (∣_⟩-_)

opaque

  unfolding honestMsgsDelivery honestBlockMaking

  clockPreservation-broadcastMsgʰ : ∀ (msg : Message) (N : GlobalState) →
    broadcastMsgʰ msg N .clock ≡ N .clock
  clockPreservation-broadcastMsgʰ msg N = refl

  clockPreservation-broadcastMsgsʰ : ∀ (msgs : List Message) (N : GlobalState) →
    broadcastMsgsʰ msgs N .clock ≡ N .clock
  clockPreservation-broadcastMsgsʰ msgs N = foldr-preservesʳ'
    {P = λ N′ → N′ .clock ≡ N .clock}
    (λ msg {N′} prf → prf)
    refl
    msgs

  clockPreservation-broadcastMsgᶜ : ∀ (msg : Message) (ϕ : DelayMap) (N : GlobalState) →
    broadcastMsgᶜ msg ϕ N .clock ≡ N .clock
  clockPreservation-broadcastMsgᶜ msg ϕ N = refl

  clockPreservation-broadcastMsgsᶜ : ∀ (mϕs : List (Message × DelayMap)) (N : GlobalState) →
    broadcastMsgsᶜ mϕs N .clock ≡ N .clock
  clockPreservation-broadcastMsgsᶜ mϕs N = foldr-preservesʳ'
    {P = λ N′ → N′ .clock ≡ N .clock}
    (λ (msg , ϕ) {N′} prf → prf)
    refl
    mϕs

  clockPreservation-↓ : ∀ {N N′ : GlobalState} {p : Party} →
    _ ⊢ N —[ p ]↓→ N′ → N′ .clock ≡ N .clock
  clockPreservation-↓ (unknownParty↓ _  ) = refl
  clockPreservation-↓ (honestParty↓  _ _) = refl
  clockPreservation-↓ (corruptParty↓ _ _) = clockPreservation-broadcastMsgsᶜ (proj₁ (processMsgsᶜ _ _ _ _ _)) _

  clockPreservation-↓∗ : ∀ {N N′ : GlobalState} {ps : List Party} →
    _ ⊢ N —[ ps ]↓→∗ N′ → N′ .clock ≡ N .clock
  clockPreservation-↓∗ = fold (λ _ N N′ → N′ .clock ≡ N .clock) (λ ts π → trans π (clockPreservation-↓ ts)) refl

  clockPreservation-↑ : ∀ {N N′ : GlobalState} {p : Party} →
    _ ⊢ N —[ p ]↑→ N′ → N′ .clock ≡ N .clock
  clockPreservation-↑ (unknownParty↑ _) = refl
  clockPreservation-↑ {N} {_} {p} (honestParty↑ _ _)
    with Params.winnerᵈ params {p} {N .clock}
  ... | ⁇ (yes _) = refl
  ... | ⁇ (no _)  = refl
  clockPreservation-↑ (corruptParty↑ _ _) = clockPreservation-broadcastMsgsᶜ (proj₁ (makeBlockᶜ _ _ _ _)) _

  clockPreservation-↑∗ : ∀ {N N′ : GlobalState} {ps : List Party} →
    _ ⊢ N —[ ps ]↑→∗ N′ → N′ .clock ≡ N .clock
  clockPreservation-↑∗ = fold (λ _ N N′ → N′ .clock ≡ N .clock) (λ ts π → trans π (clockPreservation-↑ ts)) refl

  clockMonotonicity : clock Preserves _↝⋆_ ⟶ _≤_
  clockMonotonicity {N} {.N} RTC.ε = Nat.≤-refl
  clockMonotonicity {N} {N′} (RTC._◅_ {j = N″} ts↝ ts↝⋆) = Nat.≤-trans (clockMonotonicity′ ts↝) (clockMonotonicity ts↝⋆)
    where
      clockMonotonicity′ : N ↝ N″ → N .clock ≤ N″ .clock
      clockMonotonicity′ (deliverMsgs    _ ts) = Nat.≤-reflexive $ sym $ clockPreservation-↓∗ ts
      clockMonotonicity′ (makeBlock      _ ts) = Nat.≤-reflexive $ sym $ clockPreservation-↑∗ ts
      clockMonotonicity′ (advanceRound   _   ) = Nat.<⇒≤ $ Nat.n<1+n _
      clockMonotonicity′ (permuteParties _   ) = Nat.≤-refl
      clockMonotonicity′ (permuteMsgs    _   ) = Nat.≤-refl

positiveClock : ∀ {N : GlobalState} → N₀ ↝⋆ N → N .clock > 0
positiveClock = positiveClock′ ∘ Star⇒Starʳ
  where
    open Starʳ
    positiveClock′ : ∀ {N : GlobalState} → N₀ ↝⋆ʳ N → N .clock > 0
    positiveClock′ {.N₀} εʳ = Nat.z<s
    positiveClock′ {N} (ts↝⋆ ◅ʳ ts↝) with ih ← positiveClock′ ts↝⋆ | ts↝
    ... | deliverMsgs    _ ts↓∗ rewrite clockPreservation-↓∗ ts↓∗ = ih
    ... | makeBlock      _ ts↑∗ rewrite clockPreservation-↑∗ ts↑∗ = ih
    ... | advanceRound   _      = <-trans z<s (s<s ih)
    ... | permuteParties _      = ih
    ... | permuteMsgs    _      = ih

rewindToReady : ∀ {N : GlobalState} →
    N₀ ↝⁺ N
  → ∃[ N′ ]
         N₀ ↝⋆ N′
       × N′ ↝⋆ N
       × N′ .progress ≡ ready
       × N′ .clock ≡ N .clock ∸ 1
rewindToReady = {!!}

∃ReadyBeforeMsgsDelivered : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → N .progress ≡ msgsDelivered
  → ∃[ N′ ]
         N₀ ↝⋆ N′
       × N′ ↝⋆⟨ 0 ⟩ N
       × N′ .progress ≡ ready
∃ReadyBeforeMsgsDelivered = {!!}

noPrematureHonestBlocksAtReady : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → ForgingFree N
  → N .progress ≡ ready
  → L.All.All ((_< N .clock) ∘ slot) (honestBlockHistory N)
noPrematureHonestBlocksAtReady = {!!}

∃ReadyBetweenSlots : ∀ {N N′ : GlobalState} {sl : Slot} →
    N .progress ≡ ready
  → N ↝⋆ N′
  → N .clock ≤ sl × sl ≤ N′ .clock
  → ∃[ N″ ]
         N″ .progress ≡ ready
       × N″ .clock ≡ sl
       × N ↝⋆ N″
       × N″ ↝⋆ N′
∃ReadyBetweenSlots = ∣ flip ∃ReadyBetweenSlotsʳ ⟩- Star⇒Starʳ
  where
    open RTC; open Starʳ
    ∃ReadyBetweenSlotsʳ : ∀ {N N′ : GlobalState} {sl : Slot} →
        N ↝⋆ʳ N′
      → N .progress ≡ ready
      → N .clock ≤ sl × sl ≤ N′ .clock
      → ∃[ N″ ]
             N″ .progress ≡ ready
           × N″ .clock ≡ sl
           × N ↝⋆ N″
           × N″ ↝⋆ N′
    ∃ReadyBetweenSlotsʳ {N} {.N} {sl} εʳ NReady (Nₜ≤sl , sl≤Nₜ) = N , NReady , Nat.≤-antisym Nₜ≤sl sl≤Nₜ , ε , ε
    ∃ReadyBetweenSlotsʳ {N} {N′} {sl} N↝⋆ʳN′@(_◅ʳ_ {j = N°} N↝⋆ʳN° N°↝N′) NReady (Nₜ≤sl , sl≤N′ₜ) = goal N°↝N′
      where
        ih :
            sl ≤ N° .clock
          → ∃[ N″ ]
                 N″ .progress ≡ ready
               × N″ .clock ≡ sl
               × N ↝⋆ N″
               × N″ ↝⋆ N°
        ih sl≤N°ₜ = ∃ReadyBetweenSlotsʳ N↝⋆ʳN° NReady (Nₜ≤sl , sl≤N°ₜ)

        goalFromIH :
            sl ≤ N° .clock
          → ∃[ N″ ]
                 N″ .progress ≡ ready
               × N″ .clock ≡ sl
               × N ↝⋆ N″
               × N″ ↝⋆ N′
        goalFromIH sl≤N°ₜ with ih sl≤N°ₜ
        ... | N″ , N″Ready , N″ₜ≡sl , N↝⋆N″ , N″↝⋆N° = N″ , N″Ready , N″ₜ≡sl , N↝⋆N″ , N″↝⋆N° ◅◅ (N°↝N′ ◅ ε)

        goal :
            N° ↝ N′
          → ∃[ N″ ]
                 N″ .progress ≡ ready
               × N″ .clock ≡ sl
               × N ↝⋆ N″
               × N″ ↝⋆ N′
        goal (deliverMsgs {N′ = N‴} N°Ready N°—[eoN°]↓→∗N‴) =
          goalFromIH $ subst (sl ≤_) (clockPreservation-↓∗ N°—[eoN°]↓→∗N‴) sl≤N′ₜ
        goal (makeBlock {N°} {N‴} N°MsgsDelivered N°—[eoN°]↑→∗N‴) =
          goalFromIH $ subst (sl ≤_) (clockPreservation-↑∗ N°—[eoN°]↑→∗N‴) sl≤N′ₜ
        goal (advanceRound _)
          with Nat.m≤n⇒m<n∨m≡n sl≤N′ₜ
        ... | inj₂ sl≡N°ₜ+1 rewrite sl≡N°ₜ+1 = N′ , refl , refl , Starʳ⇒Star N↝⋆ʳN′ , ε
        ... | inj₁ sl<N°ₜ+1                  = goalFromIH $ Nat.≤-pred sl<N°ₜ+1
        goal (permuteParties _) = goalFromIH sl≤N′ₜ
        goal (permuteMsgs    _) = goalFromIH sl≤N′ₜ
