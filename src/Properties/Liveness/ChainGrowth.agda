{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled

open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Liveness.ChainGrowth
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.Tree ⦃ params ⦄
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.SuperBlocks ⦃ params ⦄ ⦃ assumptions ⦄

chainGrowth :  ∀ {N N′ : GlobalState} →
    N₀ ↝⋆ N
  → N ↝⁺ N′
  → N .progress ≡ ready
  → ∀ {p₁ p₂ : Party} {ls₁ ls₂ : LocalState} →
      Honest p₁
    → N .states ⁉ p₁ ≡ just ls₁
    → Honest p₂
    → N′ .states ⁉ p₂ ≡ just ls₂
    → ∀ {w : ℕ} →
        w ≤ length (luckySlotsInRange (N .clock) (N′ .clock ∸ 1))
      → length (bestChain (N .clock ∸ 1) (ls₁ .tree)) + w ≤ length (bestChain (N′ .clock ∸ 1) (ls₂ .tree))
chainGrowth = {!!}
