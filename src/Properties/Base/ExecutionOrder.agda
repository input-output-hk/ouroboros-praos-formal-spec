open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Base.ExecutionOrder
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.Message ⦃ params ⦄
open import Protocol.Network ⦃ params ⦄; open Envelope
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Data.List.Properties.Ext using (foldr-preservesʳ')
open import Data.List.Relation.Binary.Permutation.Propositional.Properties.Ext using (Unique-resp-↭)
open import Data.List.Relation.Binary.Permutation.Propositional using (↭-refl; ↭-sym; ↭-trans)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Ext using (Starʳ)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.Ext using (Star⇒Starʳ; Starʳ⇒Star)

opaque

  unfolding honestMsgsDelivery honestBlockMaking

  execOrderPreservation-≡-broadcastMsgᶜ : ∀ (msg : Message) (ϕ : DelayMap) (N : GlobalState) →
    N .execOrder ≡ broadcastMsgᶜ msg ϕ N .execOrder
  execOrderPreservation-≡-broadcastMsgᶜ msg ϕ N = refl

  execOrderPreservation-≡-broadcastMsgsᶜ : ∀ (mϕs : List (Message × DelayMap)) (N : GlobalState) →
    N .execOrder ≡ broadcastMsgsᶜ mϕs N .execOrder
  execOrderPreservation-≡-broadcastMsgsᶜ mϕs N = foldr-preservesʳ'
    {P = λ N′ → N .execOrder ≡ N′ .execOrder}
    (λ (msg , ϕ) {N′} eoN≡eoN′ → trans eoN≡eoN′ (execOrderPreservation-≡-broadcastMsgᶜ msg ϕ N′))
    refl
    mϕs

  execOrderPreservation-broadcastMsgᶜ : ∀ (msg : Message) (ϕ : DelayMap) (N : GlobalState) →
    N .execOrder ↭ broadcastMsgᶜ msg ϕ N .execOrder
  execOrderPreservation-broadcastMsgᶜ msg ϕ N = ↭-refl

  execOrderPreservation-broadcastMsgsᶜ : ∀ (mϕs : List (Message × DelayMap)) (N : GlobalState) →
    N .execOrder ↭ broadcastMsgsᶜ mϕs N .execOrder
  execOrderPreservation-broadcastMsgsᶜ mϕs N = foldr-preservesʳ'
    {P = λ N′ → N .execOrder ↭ N′ .execOrder}
    (λ (msg , ϕ) {N′} eoN↭eoN′ → ↭-trans eoN↭eoN′ (execOrderPreservation-broadcastMsgᶜ msg ϕ N′))
    ↭-refl
    mϕs

  execOrderPreservation-↭-↓ : ∀ {N N′ : GlobalState} {p : Party} →
    _ ⊢ N —[ p ]↓→ N′ → N .execOrder ↭ N′ .execOrder
  execOrderPreservation-↭-↓ (unknownParty↓ _  ) = ↭-refl
  execOrderPreservation-↭-↓ (honestParty↓  _ _) = ↭-refl
  execOrderPreservation-↭-↓ (corruptParty↓ _ _) = execOrderPreservation-broadcastMsgsᶜ (proj₁ (processMsgsᶜ _ _ _ _ _)) _

  execOrderPreservation-↭-↑ : ∀ {N N′ : GlobalState} {p : Party} →
    _ ⊢ N —[ p ]↑→ N′ → N .execOrder ↭ N′ .execOrder
  execOrderPreservation-↭-↑ (unknownParty↑ _) = ↭-refl
  execOrderPreservation-↭-↑ {N} {_} {p} (honestParty↑ _ _)
    with Params.winnerᵈ params {p} {N .clock}
  ... | ⁇ (yes _) = ↭-refl
  ... | ⁇ (no _)  = ↭-refl
  execOrderPreservation-↭-↑ (corruptParty↑ _ _) = execOrderPreservation-broadcastMsgsᶜ (proj₁ (makeBlockᶜ _ _ _ _)) _

execOrderPreservation-↭-↓∗ : ∀ {N N′ : GlobalState} {ps : List Party} →
  _ ⊢ N —[ ps ]↓→∗ N′ → N .execOrder ↭ N′ .execOrder
execOrderPreservation-↭-↓∗ = fold (const $ _↭_ on execOrder) (λ ts π → ↭-trans (execOrderPreservation-↭-↓ ts) π) ↭-refl

execOrderPreservation-↭-↑∗ : ∀ {N N′ : GlobalState} {ps : List Party} →
  _ ⊢ N —[ ps ]↑→∗ N′ → N .execOrder ↭ N′ .execOrder
execOrderPreservation-↭-↑∗ = fold (const $ _↭_ on execOrder) (λ ts π → ↭-trans (execOrderPreservation-↭-↑ ts) π) ↭-refl

execOrderPreservation-↭-↝ : ∀ {N N′ : GlobalState} → N ↝ N′ → N .execOrder ↭ N′ .execOrder
execOrderPreservation-↭-↝ (deliverMsgs    _ ts∗ ) = execOrderPreservation-↭-↓∗ ts∗
execOrderPreservation-↭-↝ (makeBlock      _ ts∗ ) = execOrderPreservation-↭-↑∗ ts∗
execOrderPreservation-↭-↝ (advanceRound   _     ) = ↭-refl
execOrderPreservation-↭-↝ (permuteParties eoN↭ps) = eoN↭ps
execOrderPreservation-↭-↝ (permuteMsgs    _     ) = ↭-refl

execOrderPreservation-↭ : ∀ {N N′ : GlobalState} → N ↝⋆ N′ → N .execOrder ↭ N′ .execOrder
execOrderPreservation-↭ = RTC.fold (_↭_ on execOrder) (λ N↝N″ eoN″↭eoN′ → ↭-trans (execOrderPreservation-↭-↝ N↝N″) eoN″↭eoN′) ↭-refl

execOrderUniqueness : ∀ {N : GlobalState} → N₀ ↝⋆ N → Unique (N .execOrder)
execOrderUniqueness N₀↝⋆N = Unique-resp-↭ (execOrderPreservation-↭ N₀↝⋆N) parties₀Uniqueness

execOrder-↭-parties₀ : ∀ {N : GlobalState} → N₀ ↝⋆ N → N .execOrder ↭ parties₀
execOrder-↭-parties₀ = execOrder-↭-parties₀′ ∘ Star⇒Starʳ
  where
    open Starʳ
    execOrder-↭-parties₀′ : ∀ {N : GlobalState} → N₀ ↝⋆ʳ N → N .execOrder ↭ parties₀
    execOrder-↭-parties₀′ εʳ        = _↭_.refl
    execOrder-↭-parties₀′ (π* ◅ʳ π) = ↭-trans (↭-sym $ execOrderPreservation-↭-↝ π) (execOrder-↭-parties₀′ π*)
