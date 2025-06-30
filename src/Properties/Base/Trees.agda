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
open import Properties.Base.Time ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.LocalState ⦃ params ⦄ ⦃ assumptions ⦄
open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_)
open import Function.Bundles using (_⇔_; Equivalence)

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

honestLocalTreeBlocksMonotonicity :  ∀ {N N′ : GlobalState} {p : Party} {ls ls′ : LocalState} →
    N₀ ↝⋆ N
  → Honest p
  → N .states ⁉ p ≡ just ls
  → N ↝⋆ N′
  → N′ .states ⁉ p ≡ just ls′
  → allBlocks (ls .tree) ⊆ˢ allBlocks (ls′ .tree)
honestLocalTreeBlocksMonotonicity = {!!}

honestGlobalTreeInHonestLocalTree : ∀ {N N′ : GlobalState} {p : Party} {ls : LocalState} →
    N₀ ↝⋆ N
  → Honest p
  → N .progress ≡ ready
  → N′ .progress ≡ msgsDelivered
  → N ↝⋆⟨ 0 ⟩ N′
  → N′ .states ⁉ p ≡ just ls
  → allBlocks (honestTree N) ⊆ˢ allBlocks (ls .tree)
honestGlobalTreeInHonestLocalTree = {!!}

honestGlobalTreeInHonestLocalTree-↝⋆⟨1⟩ :  ∀ {N N′ : GlobalState} {p : Party} {ls′ : LocalState} →
    N₀ ↝⋆ N
  → Honest p
  → N .progress ≡ ready
  → N ↝⋆⟨ 1 ⟩ N′
  → N′ .progress ≡ ready
  → N′ .states ⁉ p ≡ just ls′
  → allBlocks (honestTree N) ⊆ˢ allBlocks (ls′ .tree)
honestGlobalTreeInHonestLocalTree-↝⋆⟨1⟩ = {!!}

honestGlobalTreeInHonestLocalTree-↝⁺ : ∀ {N N′ : GlobalState} {p : Party} {ls′ : LocalState} →
    N₀ ↝⋆ N
  → Honest p
  → N .progress ≡ ready
  → N ↝⁺ N′
  → N′ .states ⁉ p ≡ just ls′
  → allBlocks (honestTree N) ⊆ˢ allBlocks (ls′ .tree)
honestGlobalTreeInHonestLocalTree-↝⁺ {N} {N′} {p} {ls′} N₀↝⋆N hp NReady (N↝⋆N′ , Nₜ<N′ₜ) lsN′p
  with ∃ReadyBetweenSlots NReady N↝⋆N′ (Nat.n≤1+n _ , Nₜ<N′ₜ)
... | N″ , N″Ready , N″ₜ≡Nₜ+1 , N↝⋆N″ , N″↝⋆N′
  with
      pHasInN″ ← hasState⇔-↝⋆ N″↝⋆N′ .Equivalence.from $ subst M.Is-just (sym lsN′p) (M.Any.just tt)
    | hasStateInAltDef {N″} .Equivalence.from pHasInN″
... | ls″ , lsN″p = L.SubS.⊆-trans htN⊆tls″ tls″⊆tls′
  where
    N₀↝⋆N″ : N₀ ↝⋆ N″
    N₀↝⋆N″ = N₀↝⋆N ◅◅ N↝⋆N″

    tls″⊆tls′ : allBlocks (ls″ .tree) ⊆ˢ allBlocks (ls′ .tree)
    tls″⊆tls′ = honestLocalTreeBlocksMonotonicity N₀↝⋆N″ hp lsN″p N″↝⋆N′ lsN′p

    htN⊆tls″ : allBlocks (honestTree N) ⊆ˢ allBlocks (ls″ .tree)
    htN⊆tls″ = honestGlobalTreeInHonestLocalTree-↝⋆⟨1⟩ N₀↝⋆N hp NReady (N↝⋆N″ , sym N″ₜ≡Nₜ+1) N″Ready lsN″p

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
