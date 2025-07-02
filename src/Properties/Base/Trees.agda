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
open import Properties.Base.ExecutionOrder ⦃ params ⦄ ⦃ assumptions ⦄
open import Data.Maybe.Properties.Ext using (Is-just⇒to-witness; ≡just⇒Is-just)
open import Data.List.Relation.Binary.Permutation.Propositional using (↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∈-resp-↭)
open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_; ≡ˢ⇒⊇)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Ext using (Starʳ)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.Ext using (Star⇒Starʳ; Starʳ⇒Star)
open import Function.Bundles using (_⇔_; Equivalence)

honestLocalTreeEvolution-↑ : ∀ {N N′ N″ : GlobalState} {ps : List Party} {p : Party} {ls₁ ls₂ : LocalState} →
    N₀ ↝⋆ N
  → _ ⊢ N —[ ps ]↑→∗ N″
  → _ ⊢ N —[ p ]↑→ N′
  → Honest p
  → N .states ⁉ p ≡ just ls₁
  → N′ .states ⁉ p ≡ just ls₂
  → ∃[ bs ]
        allBlocks (ls₂ .tree) ≡ˢ allBlocks (ls₁ .tree) ++ bs
      × (∀ {p′} →
            p′ ∈ N .execOrder
          → bs ⊆ˢ blocksDeliveredIn p′ 𝟙 N″)
honestLocalTreeEvolution-↑ = {!!}

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

honestGlobalTreeInHonestLocalTree-↝⋆⟨1⟩ : ∀ {N N′ : GlobalState} {p : Party} {ls′ : LocalState} →
    N₀ ↝⋆ N
  → Honest p
  → N .progress ≡ ready
  → N ↝⋆⟨ 1 ⟩ N′
  → N′ .progress ≡ ready
  → N′ .states ⁉ p ≡ just ls′
  → allBlocks (honestTree N) ⊆ˢ allBlocks (ls′ .tree)
honestGlobalTreeInHonestLocalTree-↝⋆⟨1⟩ N₀↝⋆ʳN hp NReady (N↝⋆N′ , Nₜ+1≡N′ₜ) = honestGlobalTreeInHonestLocalTree-↝⋆⟨1⟩ʳ N₀↝⋆ʳN hp NReady (Star⇒Starʳ N↝⋆N′) Nₜ+1≡N′ₜ
  where
    open RTC; open Starʳ
    honestGlobalTreeInHonestLocalTree-↝⋆⟨1⟩ʳ : ∀ {N N′ : GlobalState} {p : Party} {ls′ : LocalState} →
        N₀ ↝⋆ N
      → Honest p
      → N .progress ≡ ready
      → N ↝⋆ʳ N′
      → 1 + N .clock ≡ N′ .clock
      → N′ .progress ≡ ready
      → N′ .states ⁉ p ≡ just ls′
      → allBlocks (honestTree N) ⊆ˢ allBlocks (ls′ .tree)
    honestGlobalTreeInHonestLocalTree-↝⋆⟨1⟩ʳ {N} {N′} {p} {ls′} N₀↝⋆N hp NReady (_◅ʳ_ {j = N″} N↝⋆ʳN″ N″↝N′) Nₜ+1≡N′ₜ N′Ready lspN′ with N″↝N′
    ... | advanceRound N″BlockMade = goal N↝⋆ʳN″ (Nat.suc-injective Nₜ+1≡N′ₜ) N″BlockMade lspN′
      where
        goal : ∀ {N*} →
             N ↝⋆ʳ N*
           → N .clock ≡ N* .clock
           → N* .progress ≡ blockMade
           → ∀ {ls′} →
               N* .states ⁉ p ≡ just ls′
             → allBlocks (honestTree N) ⊆ˢ allBlocks (ls′ .tree)
        goal εʳ _ N*BlockMade _ = contradiction (subst (_≡ blockMade) NReady N*BlockMade) λ ()
        goal {N*} (_◅ʳ_ {j = N‴} N↝⋆ʳN‴ N‴↝N*) Nₜ≡N*ₜ N*BlockMade {ls*} lspN*
          with N‴↝N*
        ... | makeBlock {N′ = N⁺} N‴MsgsDelivered N‴—[eoN‴]↑→∗N⁺ = L.SubS.⊆-trans htN⊆tls‴ tsl‴⊆tls*
          where
            N₀↝⋆N‴ : N₀ ↝⋆ N‴
            N₀↝⋆N‴ = N₀↝⋆N ◅◅ Starʳ⇒Star N↝⋆ʳN‴

            pHasInN‴ : p hasStateIn N‴
            pHasInN‴ = L.All.lookup (allPartiesHaveLocalState N₀↝⋆N‴) p∈N‴
              where
                p∈N‴ : p ∈ N‴ .execOrder
                p∈N‴ = ∈-resp-↭ (↭-sym (execOrderPreservation-↭-↝ N‴↝N*)) p∈N*
                  where
                    N₀↝⋆N* : N₀ ↝⋆ N*
                    N₀↝⋆N* = N₀↝⋆N‴ ◅◅ (N‴↝N* ◅ ε)

                    p∈N* : p ∈ N* .execOrder
                    p∈N* = hasState⇒∈execOrder N₀↝⋆N* (≡just⇒Is-just lspN*)

            ls‴ = LocalState ∋ M.to-witness pHasInN‴

            lspN‴ : N‴ .states ⁉ p ≡ just ls‴
            lspN‴ = Is-just⇒to-witness pHasInN‴

            Nₚ = GlobalState ∋ honestBlockMaking p ls‴ N‴

            N‴↝[p]↑Nₚ : N‴ ↝[ p ]↑ Nₚ
            N‴↝[p]↑Nₚ = honestParty↑ lspN‴ hp

            lspNₚ : Nₚ .states ⁉ p ≡ just ls*
            lspNₚ = trans (sym lspN⁺≡lspNₚ) lspN*
              where
                lspN⁺≡lspNₚ : N⁺ .states ⁉ p ≡ Nₚ .states ⁉ p
                lspN⁺≡lspNₚ = localStatePreservation-∈-↑∗ N₀↝⋆N‴ N‴—[eoN‴]↑→∗N⁺ N‴↝[p]↑Nₚ

            htN⊆tls‴ : allBlocks (honestTree N) ⊆ˢ allBlocks (ls‴ .tree)
            htN⊆tls‴ = honestGlobalTreeInHonestLocalTree N₀↝⋆N hp NReady N‴MsgsDelivered (Starʳ⇒Star N↝⋆ʳN‴ , Nₜ≡N‴ₜ) lspN‴
              where
                Nₜ≡N‴ₜ : N .clock ≡ N‴ .clock
                Nₜ≡N‴ₜ rewrite Nₜ≡N*ₜ = clockPreservation-↑∗ N‴—[eoN‴]↑→∗N⁺

            tsl‴⊆tls* : allBlocks (ls‴ .tree) ⊆ˢ allBlocks (ls* .tree)
            tsl‴⊆tls* with honestLocalTreeEvolution-↑ N₀↝⋆N‴ N‴—[eoN‴]↑→∗N⁺ N‴↝[p]↑Nₚ hp lspN‴ lspNₚ
            ... | bs , tls*≡tls‴+bs , _ = let open L.SubS.⊆-Reasoning Block in begin
              allBlocks (ls‴ .tree)       ⊆⟨ L.SubS.xs⊆xs++ys _ _ ⟩
              allBlocks (ls‴ .tree) ++ bs ⊆⟨ ≡ˢ⇒⊇ tls*≡tls‴+bs ⟩
              allBlocks (ls* .tree)       ∎

        ... | permuteParties _ = goal N↝⋆ʳN‴ Nₜ≡N*ₜ N*BlockMade lspN*
        ... | permuteMsgs    _ = goal N↝⋆ʳN‴ Nₜ≡N*ₜ N*BlockMade lspN*

    ... | permuteParties _ = honestGlobalTreeInHonestLocalTree-↝⋆⟨1⟩ʳ N₀↝⋆N hp NReady N↝⋆ʳN″ Nₜ+1≡N′ₜ N′Ready lspN′
    ... | permuteMsgs    _ = honestGlobalTreeInHonestLocalTree-↝⋆⟨1⟩ʳ N₀↝⋆N hp NReady N↝⋆ʳN″ Nₜ+1≡N′ₜ N′Ready lspN′

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
