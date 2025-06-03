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

_hasStateIn_ : REL Party GlobalState 0ℓ
p hasStateIn N = M.Is-just (N .states ⁉ p)

opaque

  unfolding honestMsgsDelivery honestBlockMaking

  localStatePreservation-∉-↑∗ : ∀ {N N′ : GlobalState} {ps : List Party} {p : Party} →
      p ∉ ps
    → _ ⊢ N —[ ps ]↑→∗ N′
    → N′ .states ⁉ p ≡ N .states ⁉ p
  localStatePreservation-∉-↑∗ = {!!}

  hasState⇔-↑∗ : ∀ {N N′ N″ : GlobalState} {ps : List Party} {p : Party} →
      _ ⊢ N —[ ps ]↑→∗ N′
    → _ ⊢ N′ —[ p ]↑→ N″
    → p hasStateIn N ⇔ p hasStateIn N″
  hasState⇔-↑∗ = {!!}

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
      p hasStateIn N′
    → _ ⊢ N —[ p ]↓→ N′
    → p hasStateIn N
  localStatePrev-↓ = {!!}

allPartiesHaveLocalState : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → L.All.All (_hasStateIn N) (N .execOrder)
allPartiesHaveLocalState = {!!}

hasState⇔∈parties₀ : ∀ {N : GlobalState} {p : Party} →
    N₀ ↝⋆ N
  → p hasStateIn N ⇔ p ∈ parties₀
hasState⇔∈parties₀ = {!!}

hasState⇒∈execOrder : ∀ {N : GlobalState} {p : Party} →
    N₀ ↝⋆ N
  → p hasStateIn N
  → p ∈ N .execOrder
hasState⇒∈execOrder = {!!}
