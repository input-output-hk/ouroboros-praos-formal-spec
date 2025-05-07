{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled

open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Base.LocalState
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Function.Bundles using (_⇔_)

opaque

  unfolding honestMsgsDelivery honestBlockMaking

  localStatePreservation-∉-↑∗ : ∀ {N N′ : GlobalState} {ps : List Party} {p : Party} →
    p ∉ ps → _ ⊢ N —[ ps ]↑→∗ N′ → N′ .states ⁉ p ≡ N .states ⁉ p
  localStatePreservation-∉-↑∗ = {!!}

  localStatePreservation-∈-↑∗ : ∀ {N N′ N″ : GlobalState} {p : Party} →
      N₀ ↝⋆ N
    → _ ⊢ N —[ N .execOrder ]↑→∗ N′
    → _ ⊢ N —[ p ]↑→ N″
    → N′ .states ⁉ p ≡ N″ .states ⁉ p
  localStatePreservation-∈-↑∗ = {!!}

  localStatePreservation-↓∗ : ∀ {N N′ N″ : GlobalState} {p : Party} →
      N₀ ↝⋆ N
    → _ ⊢ N —[ N .execOrder ]↓→∗ N′
    → _ ⊢ N —[ p ]↓→ N″
    → N′ .states ⁉ p ≡ N″ .states ⁉ p
  localStatePreservation-↓∗ = {!!}

  localStatePrev-↓ :  ∀ {N N′ : GlobalState} {p : Party} →
      M.Is-just (N′ .states ⁉ p)
    → _ ⊢ N —[ p ]↓→ N′
    → M.Is-just (N .states ⁉ p)
  localStatePrev-↓ = {!!}

allPartiesHaveLocalState : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → L.All.All (M.Is-just ∘ (N .states ⁉_)) (N .execOrder)
allPartiesHaveLocalState = {!!}

hasState⇔∈parties₀ : ∀ {N : GlobalState} {p : Party} →
    N₀ ↝⋆ N
  → M.Is-just (N .states ⁉ p) ⇔ p ∈ parties₀
hasState⇔∈parties₀ = {!!}

hasState⇒∈execOrder : ∀ {N : GlobalState} {p : Party} →
    N₀ ↝⋆ N
  → M.Is-just (N .states ⁉ p)
  → p ∈ N .execOrder
hasState⇒∈execOrder = {!!}
