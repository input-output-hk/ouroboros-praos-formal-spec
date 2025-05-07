{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled

open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Base.Trees
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.Network ⦃ params ⦄; open Envelope
open import Protocol.TreeType ⦃ params ⦄
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_)

honestLocalTreeInHonestGlobalTree : ∀ {N : GlobalState} {p : Party} {ls : LocalState} →
    N₀ ↝⋆ N
  → Honest p
  → N .states ⁉ p ≡ just ls
  → allBlocks (ls .tree) ⊆ˢ allBlocks (honestTree N)
honestLocalTreeInHonestGlobalTree = {!!}

honestLocalTreeEvolution-↓ :  ∀ {N N′ : GlobalState} {p : Party} {ls ls′ : LocalState} →
    Honest p
  → N .states ⁉ p ≡ just ls
  → _ ⊢ N —[ p ]↓→ N′
  → N′ .states ⁉ p ≡ just ls′
  → allBlocks (ls′ .tree) ≡ˢ allBlocks (ls .tree) ++ blocksDeliveredIn p 𝟘 N -- TODO: same as immediateMsgs p N ???
honestLocalTreeEvolution-↓ = {!!}

honestGlobalTreeInHonestLocalTree : ∀ {N N′ : GlobalState} {p : Party} {ls : LocalState} →
    N₀ ↝⋆ N
  → Honest p
  → N .progress ≡ ready
  → N′ .progress ≡ msgsDelivered
  → N ↝⋆⟨ 0 ⟩ N′
  → N′ .states ⁉ p ≡ just ls
  → allBlocks (honestTree N) ⊆ˢ allBlocks (ls .tree)
honestGlobalTreeInHonestLocalTree = {!!}

honestGlobalTreeInHonestLocalTree⁺ : ∀ {N N′ : GlobalState} {p : Party} {ls : LocalState} →
    N₀ ↝⋆ N
  → Honest p
  → N .progress ≡ ready
  → N ↝⁺ N′
  → N′ .states ⁉ p ≡ just ls
  → allBlocks (honestTree N) ⊆ˢ allBlocks (ls .tree)
honestGlobalTreeInHonestLocalTree⁺ = {!!}
