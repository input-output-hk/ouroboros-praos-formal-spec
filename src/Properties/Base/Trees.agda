{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled

open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Base.Trees
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.Block ⦃ params ⦄ using (Block)
open import Protocol.Chain ⦃ params ⦄ using (genesisBlock)
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

honestGlobalTreeBlocksMonotonicity : ∀ {N N′ : GlobalState} →
    N₀ ↝⋆ N
  → N ↝ N′
  → allBlocks (honestTree N) ⊆ˢ allBlocks (honestTree N′)
honestGlobalTreeBlocksMonotonicity = {!!}

honestGlobalTreeBlocksPreservation : ∀ {N N′ : GlobalState} {pg : Progress} →
    N ↝⋆ N′
  → N .progress ≡ pg
  → N′ .progress ≡ pg
  → N .clock ≡ N′ .clock
  → allBlocks (honestTree N) ≡ˢ allBlocks (honestTree N′)
honestGlobalTreeBlocksPreservation = {!!}

allGBsInHonestTree₀ :
    L.All.All (_≡ genesisBlock) (allBlocks (honestTree N₀))
allGBsInHonestTree₀ = {!!}

honestGlobalTreeBlockInSomeHonestLocalTree :  ∀ {N : GlobalState} {b : Block} →
    N₀ ↝⋆ N
  → b ∈ allBlocks (honestTree N)
  → ∃₂[ p , ls ]
        N .states ⁉ p ≡ just ls
      × b ∈ allBlocks (ls .tree)
      × Honest p
      × p ∈ N .execOrder
honestGlobalTreeBlockInSomeHonestLocalTree = {!!}
