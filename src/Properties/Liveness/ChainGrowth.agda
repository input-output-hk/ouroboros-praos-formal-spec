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

honestGlobalTreeInHonestLocalTree : ∀ {N N′ : GlobalState} {p : Party} {ls : LocalState} →
    N₀ ↝⋆ N
  → Honest p
  → N .progress ≡ ready
  → N′ .progress ≡ msgsDelivered
  → N ↝⋆⟨ 0 ⟩ N′
  → N′ .states ⁉ p ≡ just ls
  → allBlocks (honestTree N) ⊆ˢ allBlocks (ls .tree)
honestGlobalTreeInHonestLocalTree = {!!}
