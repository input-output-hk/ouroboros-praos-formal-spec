{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled

open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Liveness.ChainQuality.Properties
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot)
open import Protocol.Crypto ⦃ params ⦄ using (Hashable); open Hashable ⦃ ... ⦄
open import Protocol.Block ⦃ params ⦄
open import Protocol.Chain ⦃ params ⦄
open import Protocol.Tree ⦃ params ⦄
open import Protocol.Message ⦃ params ⦄
open import Protocol.Network ⦃ params ⦄
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Safety.BlockPositions ⦃ params ⦄ ⦃ assumptions ⦄
open import Protocol.Tree.Properties ⦃ params ⦄
open import Protocol.Chain.Properties ⦃ params ⦄
open import Properties.Base.Trees ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.LocalState ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.BlockHistory ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.ExecutionOrder ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.ForgingFree ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.CollisionFree ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.Time ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.SuperBlocks ⦃ params ⦄ ⦃ assumptions ⦄
open import Data.Nat.Properties.Ext using (n>0⇒pred[n]<n)
open import Data.Maybe.Properties.Ext using (Is-just⇒to-witness)
open import Data.List.Properties.Ext using (count-partition; ∈-ι⁺)
open import Data.List.Relation.Unary.All.Properties.Ext using (All-filter)
open import Data.List.Relation.Unary.AllPairs.Properties.Ext using (headʳ)
open import Data.List.Relation.Unary.Unique.Propositional.Properties.Ext using (Unique[xs∷ʳx]⇒x∉xs; Unique-⊆-#≤)
open import Data.List.Relation.Unary.Linked.Properties using (filter⁺)
open import Data.List.Relation.Binary.SetEquality using (≡ˢ⇒⊇)
open import Data.List.Relation.Binary.Permutation.Propositional using (↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∈-resp-↭)
open import Data.List.Relation.Binary.Subset.Propositional.Properties.Ext using (∷⊆⇒∈)
open import Data.List.Membership.Propositional.Properties.Ext using (∈-∷ʳ-≢⁻; ∉-filter⁺; ∉-filter⁻)
open import Data.List.Ext using (count; ι)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Ext using (Starʳ)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.Ext using (Star⇒Starʳ; Starʳ⇒Star)
open import Prelude.STS.Properties using (—[]→∗⇒—[]→∗ʳ; —[]→∗ʳ⇒—[]→∗; —[∷ʳ]→∗-split; —[[]]→∗ʳ⇒≡)
open import Prelude.AssocList.Properties.Ext using (set-⁉)
open import Function.Bundles using (Equivalence; Inverse)
open import Relation.Unary.Properties using (∁?)

private

  opaque
    unfolding honestBlockMaking

    open import Data.List.Reverse

    -- NOTE: Auxiliary lemma. Added because `opaque` does not seem to work within a few nested levels.
    -- Try to isolate the issue and report it.
    pastBestChainLength† : ∀ {N N⁺ b N⁼ Nᵖ cₕ ls⁼ p ls cₜ} →
        N₀ ↝⋆ N
      → CollisionFree N
      → N₀ ↝⋆ N⁼
      → N⁼ ↝[ b .pid ]↑ Nᵖ
      → (b ∷ cₕ) ✓
      → b ∉ blockHistory N⁼
      → Nᵖ ≡ honestBlockMaking (b .pid) ls⁼ N⁼
      → Honest p
      → N .states ⁉ p ≡ just ls
      → cₜ ++ b ∷ cₕ ≡ bestChain (N .clock ∸ 1) (ls .tree)
      → N⁼ ↝⋆ N
      → ForgingFree N⁺
      → HonestBlock b →
      ∀ {N† ps} →
        Reverse ps
      → N† ↷↑ N⁺
      → Unique ps
      → b ∈ blockHistory N†
      → _ ⊢ N⁼ —[ ps ]↑→∗ʳ N†
      → ∃[ ls′ ] (Nᵖ .states ⁉ b .pid) ≡ just ls′ × length (bestChain (N⁼ .clock) (ls′ .tree)) ≡ length (b ∷ cₕ)
    pastBestChainLength† {b = b} {N⁼ = N⁼} _ _ _ _ _ b∉bhN⁼ _ _ _ _ _ _ _ {N† = N†} [] _ _ b∈bhN† ts =
      case ¿ b ∈ blockHistory N⁼ ¿ of λ where
        (yes b∈bhN⁼) → contradiction b∈bhN⁼ b∉bhN⁼
        (no  b∉bhN⁼) → contradiction (subst ((b ∈_) ∘ blockHistory) (sym $ —[[]]→∗ʳ⇒≡ ts) b∈bhN†) b∉bhN⁼
    pastBestChainLength† {N} {N⁺} {b} {N⁼} {Nᵖ} {cₕ} {ls⁼} {p} {ls} {cₜ}
      N₀↝⋆N cfN N₀↝⋆N⁼ tsbₚ [b+cₕ]✓ b∉bhN⁼ Nᵖeq hp lspN cₜ+b+cₕ≡bcN N⁼↝⋆N ffN⁺ hb
      {N† = N†} (ps′ ∶ ps′r ∶ʳ p′) N†↷↑N⁺ ps′∷ʳp′Uniq b∈bhN† ts* with —[∷ʳ]→∗-split (—[]→∗ʳ⇒—[]→∗ ts*)
    ... | N⁰ , ts⁺′ , ts = goal b∈bhN† ts
      where
        ts⁺ : _ ⊢ N⁼ —[ ps′ ]↑→∗ʳ N⁰
        ts⁺ = —[]→∗⇒—[]→∗ʳ ts⁺′

        ps′Uniq : Unique ps′
        ps′Uniq = headʳ ps′∷ʳp′Uniq

        p′∉ps′ : p′ ∉ ps′
        p′∉ps′ = Unique[xs∷ʳx]⇒x∉xs ps′∷ʳp′Uniq

        N⁰↷↑N⁺ : N⁰ ↷↑ N⁺
        N⁰↷↑N⁺ = blockMaking↑ ts N†↷↑N⁺

        ih :
            b ∈ blockHistory N⁰
          → ∃[ ls′ ] (Nᵖ .states ⁉ b .pid) ≡ just ls′ × length (bestChain (N⁼ .clock) (ls′ .tree)) ≡ length (b ∷ cₕ)
        ih b∈bhN⁰ = pastBestChainLength† N₀↝⋆N cfN N₀↝⋆N⁼ tsbₚ [b+cₕ]✓ b∉bhN⁼ Nᵖeq hp lspN cₜ+b+cₕ≡bcN N⁼↝⋆N ffN⁺ hb ps′r
                      N⁰↷↑N⁺ ps′Uniq b∈bhN⁰ ts⁺

        goal :
            b ∈ blockHistory N†
          → _ ⊢ N⁰ —[ p′ ]↑→ N†
          → ∃[ ls′ ] (Nᵖ .states ⁉ b .pid) ≡ just ls′ × length (bestChain (N⁼ .clock) (ls′ .tree)) ≡ length (b ∷ cₕ)
        goal _ (unknownParty↑ _) = ih b∈bhN†
        goal b∈bhN† (honestParty↑ {ls = ls′} ls′π hp′π)
          with Params.winnerᵈ params {p′} {N⁰ .clock}
        ... | ⁇ (no ¬isWinner) = ih b∈bhN†
        ... | ⁇ (yes isWinner) rewrite hp′π with b∈bhN†
        ...   | here b≡nb = addBlock ls′ nb , eq₁ tsbₚ , eq₂
          where
            best : Chain
            best = bestChain (N⁰ .clock ∸ 1) (ls′ .tree)

            nb : Block
            nb = mkBlock (hash (tip best)) (N⁰ .clock) (txSelection (N⁰ .clock) p′) p′

            ls′N⁼ : N⁼ .states ⁉ p′ ≡ just ls′
            ls′N⁼ rewrite localStatePreservation-∉-↑∗ p′∉ps′ (—[]→∗ʳ⇒—[]→∗ ts⁺) = ls′π

            eq₁ : N⁼ ↝[ b .pid ]↑ Nᵖ → Nᵖ .states ⁉ b .pid ≡ just (addBlock ls′ nb)
            eq₁ tsbₚ rewrite b≡nb with tsbₚ
            ... | unknownParty↑ ls≡◇ = contradiction ls≡◇ ((subst (_≢ nothing) (sym ls′N⁼) λ ()))
            ... | honestParty↑ {ls = ls} lsπ _ = eq₁hp
              where
                ls≡ls′ : ls ≡ ls′
                ls≡ls′ = M.just-injective (subst₂ (_≡_) lsπ ls′N⁼ refl)

                eq₁hp : Nᵖ .states ⁉ p′ ≡ just (addBlock ls′ nb)
                eq₁hp
                  rewrite
                      sym $ clockPreservation-↑∗ (—[]→∗ʳ⇒—[]→∗ ts⁺)
                    | dec-yes ¿ winner p′ (N⁰ .clock) ¿ isWinner .proj₂
                    | ls≡ls′
                    | set-⁉ (N⁼ .states) p′ (addBlock ls′ nb)
                    = refl
            ... | corruptParty↑ _ cp′π = contradiction hp′π (corrupt⇒¬honest cp′π)

            eq₂ : length (bestChain (N⁼ .clock) (addBlock ls′ nb .tree)) ≡ suc (length cₕ)
            eq₂ with ✓-∃-∷ (valid (ls′ .tree) (N⁰ .clock ∸ 1))
            ... | b′ , cₕ′ , b′+cₕ′≡best = Nat.≤-antisym leq geq
              where
                N⁰ₜ>0 : N⁰ .clock > 0
                N⁰ₜ>0 rewrite (clockPreservation-↑∗ (—[]→∗ʳ⇒—[]→∗ ts⁺)) = positiveClock N₀↝⋆N⁼

                bc′ : Chain
                bc′ = b′ ∷ cₕ′

                [b+bc′]✓ : (b ∷ bc′) ✓
                [b+bc′]✓ rewrite b≡nb =
                  ✓-∷ .Equivalence.to (
                      isWinner
                    , subst (λ ◆ → hash (tip ◆) ≡ hash b′) b′+cₕ′≡best refl
                    , nb>ˢb′
                    , subst _✓ (sym b′+cₕ′≡best) (valid (ls′. tree) (N⁰ .clock ∸ 1)))
                  where
                    nb>ˢb′ : nb >ˢ b′
                    nb>ˢb′ = Nat.≤-<-trans b′ₜ≤N⁰ₜ-1 (n>0⇒pred[n]<n N⁰ₜ>0)
                      where
                        b′ₜ≤N⁰ₜ-1 : b′ .slot ≤ N⁰ .clock ∸ 1
                        b′ₜ≤N⁰ₜ-1 = L.All.lookup (bestChainSlotBounded (ls′ .tree) (N⁰ .clock ∸ 1))
                          (subst (b′ ∈_) b′+cₕ′≡best (here refl))

                best≡cₕ : best ≡ cₕ
                best≡cₕ rewrite sym b′+cₕ′≡best = ≡tips⇒≡chains N₀↝⋆N cfN [b+bc′]✓ [b+cₕ]✓ b′+cₕ′⊆gb+bhN cₕ⊆gb+bhN
                  where
                    open L.SubS.⊆-Reasoning Block

                    b′+cₕ′⊆gb+bhN : b′ ∷ cₕ′ ⊆ˢ genesisBlock ∷ blockHistory N
                    b′+cₕ′⊆gb+bhN rewrite sym b′+cₕ′≡best = begin
                      b′ ∷ cₕ′
                        ≡⟨ b′+cₕ′≡best ⟩
                      best
                        ⊆⟨ selfContained (ls′ .tree) (N⁰ .clock ∸ 1) ⟩
                      filter ((_≤? N⁰ .clock ∸ 1) ∘ slot) (allBlocks (ls′ .tree))
                        ⊆⟨ L.SubS.filter-⊆ _ _ ⟩
                      allBlocks (ls′ .tree)
                        ⊆⟨ honestLocalTreeInHonestGlobalTree N₀↝⋆N⁼ hp′π ls′N⁼ ⟩
                      allBlocks (honestTree N⁼)
                        ⊆⟨ honestGlobalTreeInBlockHistory N₀↝⋆N⁼ ⟩
                      genesisBlock ∷ blockHistory N⁼
                        ⊆⟨ L.SubS.∷⁺ʳ genesisBlock (blockHistoryPreservation-↝⋆ N⁼↝⋆N) ⟩
                      genesisBlock ∷ blockHistory N
                        ∎

                    cₕ⊆gb+bhN : cₕ ⊆ˢ genesisBlock ∷ blockHistory N
                    cₕ⊆gb+bhN = begin
                      cₕ
                        ⊆⟨ L.SubS.xs⊆ys++xs _ _ ⟩
                      (cₜ L.∷ʳ b) ++ cₕ
                        ≡⟨ L.++-assoc _ [ b ] _ ⟩
                      cₜ ++ b ∷ cₕ
                        ≡⟨ cₜ+b+cₕ≡bcN ⟩
                      bestChain (N .clock ∸ 1) (ls .tree)
                        ⊆⟨ selfContained (ls .tree) (N .clock ∸ 1) ⟩
                      filter ((_≤? N .clock ∸ 1) ∘ slot) (allBlocks (ls .tree))
                        ⊆⟨ L.SubS.filter-⊆ _ _ ⟩
                      allBlocks (ls .tree)
                        ⊆⟨ honestLocalTreeInHonestGlobalTree N₀↝⋆N hp lspN ⟩
                      allBlocks (honestTree N)
                        ⊆⟨ honestGlobalTreeInBlockHistory N₀↝⋆N ⟩
                      genesisBlock ∷ blockHistory N
                        ∎

                leq : length (bestChain (N⁼ .clock) (addBlock ls′ nb .tree)) ≤ suc (length cₕ)
                leq rewrite sym best≡cₕ | sym $ clockPreservation-↑∗ (—[]→∗ʳ⇒—[]→∗ ts⁺) =
                  Nat.≤-reflexive $ extendTreeLength (ls′ .tree) nb

                geq : length cₕ < length (bestChain (N⁼ .clock) (addBlock ls′ nb .tree))
                geq = Nat.<-≤-trans {j = length (b ∷ cₕ)} Nat.≤-refl geq′
                  where
                    geq′ : length (b ∷ cₕ) ≤ length (bestChain (N⁼ .clock) (addBlock ls′ nb .tree))
                    geq′ = optimal (b ∷ cₕ) (addBlock ls′ nb .tree) (N⁼ .clock) [b+cₕ]✓ b+cₕ⊆ft
                      where
                        open import Function.Reasoning

                        N⁰ₜ≤N⁼ₜ : N⁰ .clock ≤ N⁼ .clock
                        N⁰ₜ≤N⁼ₜ = Nat.≤-reflexive $ clockPreservation-↑∗ (—[]→∗ʳ⇒—[]→∗ ts⁺)

                        b+cₕ⊆ft : b ∷ cₕ ⊆ˢ filter ((_≤? N⁼ .clock) ∘ slot) (allBlocks (extendTree (ls′ .tree) nb))
                        b+cₕ⊆ft {b″} (here b″≡b) rewrite trans b″≡b b≡nb =
                          L.Mem.∈-filter⁺ ((_≤? N⁼ .clock) ∘ slot) {xs = allBlocks (extendTree (ls′ .tree) nb)} nb∈ab N⁰ₜ≤N⁼ₜ
                          where
                            nb∈ab : nb ∈ allBlocks (extendTree (ls′ .tree) nb)
                            nb∈ab =
                                                                         here refl ∶
                              nb ∈ [ nb ]                                |> L.SubS.xs⊆ys++xs _ _ ∶
                              nb ∈ allBlocks (ls′ .tree) ++ [ nb ]       |> ≡ˢ⇒⊇ (extendable (ls′ .tree) nb) ∶                                  
                              nb ∈ allBlocks (extendTree (ls′ .tree) nb)
                        b+cₕ⊆ft {b″} (there b″∈cₕ) =
                          L.Mem.∈-filter⁺ ((_≤? N⁼ .clock) ∘ slot) {xs = allBlocks (extendTree (ls′ .tree) nb)} b″∈ab b″ₜ≤N⁼ₜ
                          where
                            b″∈best : b″ ∈ best
                            b″∈best rewrite best≡cₕ = b″∈cₕ

                            b″ₜ≤N⁼ₜ : b″ .slot ≤ N⁼ .clock
                            b″ₜ≤N⁼ₜ = Nat.≤-trans b″ₜ≤N⁰ₜ-1 N⁰ₜ-1≤N⁼ₜ
                              where
                                b″ₜ≤N⁰ₜ-1 : b″ .slot ≤ N⁰ .clock ∸ 1
                                b″ₜ≤N⁰ₜ-1 = L.All.lookup (bestChainSlotBounded (ls′ .tree) (N⁰ .clock ∸ 1)) b″∈best

                                N⁰ₜ-1≤N⁼ₜ : N⁰ .clock ∸ 1 ≤ N⁼ .clock
                                N⁰ₜ-1≤N⁼ₜ = Nat.<⇒≤ $ Nat.<-≤-trans (n>0⇒pred[n]<n N⁰ₜ>0) N⁰ₜ≤N⁼ₜ

                            b″∈ab : b″ ∈ allBlocks (extendTree (ls′ .tree) nb)
                            b″∈ab =
                                b″∈best ∶
                              b″ ∈ best
                                |> selfContained (ls′ .tree) (N⁰ .clock ∸ 1) ∶
                              b″ ∈ filter ((_≤? N⁰ .clock ∸ 1) ∘ slot) (allBlocks (ls′ .tree))
                                |> L.SubS.filter-⊆ _ _ ∶
                              b″ ∈ allBlocks (ls′ .tree)
                                |> L.SubS.xs⊆xs++ys _ _ ∶
                              b″ ∈ allBlocks (ls′ .tree) ++ [ nb ]
                                |> ≡ˢ⇒⊇ (extendable (ls′ .tree) nb) ∶
                              b″ ∈ allBlocks (extendTree (ls′ .tree) nb)
        ...   | there b∈bhN⁰ = ih b∈bhN⁰

        goal _ (corruptParty↑ _ _) = step-cp {mds} (ffN⁺ .proj₂ N⁰↷↑N⁺) b∈bhN†
          where
            mds : List (Message × DelayMap)
            mds = makeBlockᶜ (N⁰ .clock) (N⁰ .history) (N⁰ .messages) (N⁰ .advState) .proj₁

            step-cp : ∀ {mds} →
                map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N⁰
              → b ∈ blockHistory (broadcastMsgsᶜ mds N⁰)
              → ∃[ ls′ ] (Nᵖ .states ⁉ b .pid) ≡ just ls′ × length (bestChain (N⁼ .clock) (ls′ .tree)) ≡ length (b ∷ cₕ)
            step-cp {[]} sub b∈bh = ih b∈bh
            step-cp {(newBlock b* , _) ∷ mds} sub b∈bh with b∈bh
            ... | here b≡b* rewrite sym b≡b* = ih b∈bhN⁰
              where
                b∈bhN⁰ : b ∈ blockHistory N⁰
                b∈bhN⁰ rewrite L.filter-accept ¿ HonestBlock ¿¹ {x = b} {xs = map (projBlock ∘ proj₁) mds} hb =
                  L.SubS.filter-⊆ _ _ $ sub {b} (here refl)
            ... | there b*∈mds = step-cp {mds} sub′ b*∈mds
              where
                sub′ : map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N⁰
                sub′ with ¿ HonestBlock b* ¿
                ... | yes hb* = λ b∈mds → sub (there b∈mds)
                ... | no ¬hb* = sub

  open RTC; open Starʳ

  pastBestChainLength‡ : ∀ {N N′ b cₕ cₜ p ls N◆ N*} →
      N◆ ↝⋆ʳ N*
    → N* ↝⋆ N
    → N′ ↝⋆ N◆
    → N₀ ↝⋆ N′
    → ForgingFree N
    → CollisionFree N
    → HonestBlock b
    → N₀ ↝⋆ N
    → (b ∷ cₕ) ✓
    → Honest p
    → N .states ⁉ p ≡ just ls
    → cₜ ++ b ∷ cₕ ≡ bestChain (N .clock ∸ 1) (ls .tree)
    → N◆ .clock ≡ b .slot
    → N* .clock ≡ suc (b .slot)
    → N◆ .progress ≡ ready
    → N* .progress ≡ ready
    → b ∈ blockHistory N*
    → ∃[ ls′ ] N* .states ⁉ b .pid ≡ just ls′ × length (bestChain (N* .clock ∸ 1) (ls′ .tree)) ≡ length (b ∷ cₕ)
  pastBestChainLength‡ εʳ _ _ _ _ _ _ _ _ _ _ _ N◆ₜ≡bₜ N◆ₜ≡bₜ+1 = contradiction (trans (sym N◆ₜ≡bₜ) N◆ₜ≡bₜ+1) λ ()
  pastBestChainLength‡ {N} {N′} {b} {cₕ} {cₜ} {p} {ls} {N◆} {N*}
    (_◅ʳ_ {j = N°} N◆↝⋆ʳN° N°↝N*) N*↝⋆N N′↝⋆N◆ N₀↝⋆N′ ffN cfN hb N₀↝⋆N [b+cₕ]✓ hp lspN cₜ+b+cₕ≡bcN
    N◆ₜ≡bₜ N*ₜ≡bₜ+1 N◆Ready N*Ready b∈bhN* = goal′ N°↝N*
    where
      N°↝⋆N : N° ↝⋆ N
      N°↝⋆N = N°↝N* ◅ N*↝⋆N

      ih : N° .clock ≡ suc (b .slot) → N° .progress ≡ ready → b ∈ blockHistory N° → _
      ih N°ₜ≡bₜ+1 N°Ready b∈bhN° =
        pastBestChainLength‡ N◆↝⋆ʳN° N°↝⋆N N′↝⋆N◆ N₀↝⋆N′ ffN cfN hb N₀↝⋆N [b+cₕ]✓ hp lspN cₜ+b+cₕ≡bcN
          N◆ₜ≡bₜ N°ₜ≡bₜ+1 N◆Ready N°Ready b∈bhN°

      goal′ : N° ↝ N* → _
      goal′ (permuteParties _) = ih N*ₜ≡bₜ+1 N*Ready b∈bhN*
      goal′ (permuteMsgs    _) = ih N*ₜ≡bₜ+1 N*Ready b∈bhN*
      goal′ (advanceRound N°BlockMade) = goal″ N◆↝⋆ʳN° N°↝⋆N N◆ₜ≡bₜ N°ₜ≡bₜ N◆Ready N°BlockMade b∈bhN*
        where
          N°ₜ≡bₜ : N° .clock ≡ b .slot
          N°ₜ≡bₜ = Nat.suc-injective N*ₜ≡bₜ+1

          goal″ : ∀ {N⁺} →
              N◆ ↝⋆ʳ N⁺
            → N⁺ ↝⋆ N
            → N◆ .clock ≡ b .slot
            → N⁺ .clock ≡ b .slot
            → N◆ .progress ≡ ready
            → N⁺ .progress ≡ blockMade
            → b ∈ blockHistory N⁺
            → ∃[ ls′ ] N⁺ .states ⁉ b .pid ≡ just ls′ × length (bestChain (N⁺ .clock) (ls′ .tree)) ≡ length (b ∷ cₕ)
          goal″ εʳ _ _ _ N◆Ready N◆BlockMade _ = contradiction (trans (sym N◆Ready) N◆BlockMade) λ ()
          goal″ {N⁺} (_◅ʳ_ {j = N⁼} N◆↝⋆ʳN⁼ N⁼↝N⁺) Ṇ⁺↝⋆N N◆ₜ≡bₜ N⁺ₜ≡bₜ N◆Ready N⁺BlockMade b∈bhN⁺ = goal‴ N⁼↝N⁺
            where
              N⁼↝⋆N : N⁼ ↝⋆ N
              N⁼↝⋆N = N⁼↝N⁺ ◅ Ṇ⁺↝⋆N

              goal‴ : N⁼ ↝ N⁺ → _
              goal‴ (permuteParties _) = goal″ N◆↝⋆ʳN⁼ N⁼↝⋆N N◆ₜ≡bₜ N⁺ₜ≡bₜ N◆Ready N⁺BlockMade b∈bhN⁺
              goal‴ (permuteMsgs    _) = goal″ N◆↝⋆ʳN⁼ N⁼↝⋆N N◆ₜ≡bₜ N⁺ₜ≡bₜ N◆Ready N⁺BlockMade b∈bhN⁺
              goal‴ (makeBlock {N′ = N‴} N⁼MsgsDelivered N⁼—[eoN⁼]↑→∗N‴) = goal′*″
                where
                  N⁼ₜ≡bₜ : N⁼ .clock ≡ b .slot
                  N⁼ₜ≡bₜ = trans (sym $ clockPreservation-↑∗ N⁼—[eoN⁼]↑→∗N‴) N⁺ₜ≡bₜ

                  N₀↝⋆N⁼ : N₀ ↝⋆ N⁼
                  N₀↝⋆N⁼ = N₀↝⋆N′ ◅◅ N′↝⋆N◆ ◅◅ (Starʳ⇒Star N◆↝⋆ʳN⁼)

                  ffN⁼ : ForgingFree N⁼
                  ffN⁼ = ForgingFreePrev N⁼↝⋆N ffN

                  ffN⁺ : ForgingFree N⁺
                  ffN⁺ = ForgingFreePrev Ṇ⁺↝⋆N ffN

                  hasLspN⁼ : b .pid hasStateIn N⁼
                  hasLspN⁼ = L.All.lookup (allPartiesHaveLocalState N₀↝⋆N⁼) bₚ∈N⁼
                    where
                      b∈hbhN⁺ : b ∈ honestBlockHistory N⁺
                      b∈hbhN⁺ = L.Mem.∈-filter⁺ _ b∈bhN⁺ hb

                      bₚ∈N⁺ : b .pid ∈ N⁺ .execOrder
                      bₚ∈N⁺ = honestBlockPidInExecOrder (N₀↝⋆N⁼ ◅◅ N⁼↝N⁺ ◅ ε) ffN⁺ b∈hbhN⁺

                      bₚ∈N⁼ : b .pid ∈ N⁼ .execOrder
                      bₚ∈N⁼ = ∈-resp-↭ (↭-sym (execOrderPreservation-↭-↝ N⁼↝N⁺)) bₚ∈N⁺

                  ls⁼ : LocalState
                  ls⁼ = M.to-witness hasLspN⁼

                  lsbₚN⁼ : N⁼ .states ⁉ b .pid ≡ just ls⁼
                  lsbₚN⁼ = Is-just⇒to-witness hasLspN⁼

                  b∉bhN⁼ : b ∉ blockHistory N⁼
                  b∉bhN⁼ = ∉-filter⁻ _ b∉hbhN⁼ hb
                    where
                      <N⁼ₜ[hbhN⁼] : L.All.All ((_< N⁼ .clock) ∘ slot) (honestBlockHistory N⁼)
                      <N⁼ₜ[hbhN⁼] = noPrematureHonestBlocksAt↓ N₀↝⋆N⁼ ffN⁼ N⁼MsgsDelivered

                      b∉hbhN⁼ : b ∉ honestBlockHistory N⁼
                      b∉hbhN⁼ rewrite sym $ All-filter {P? = (_<? N⁼ .clock) ∘ slot} <N⁼ₜ[hbhN⁼] = b∉<N⁼ₜ[hbhN⁼]
                        where
                          b∉<N⁼ₜ[hbhN⁼] : b ∉ filter ((_<? N⁼ .clock) ∘ slot) (honestBlockHistory N⁼)
                          b∉<N⁼ₜ[hbhN⁼] = ∉-filter⁺ (honestBlockHistory N⁼) bₜ≮N⁼ₜ
                            where
                              bₜ≮N⁼ₜ : ¬ (b. slot < N⁼ .clock)
                              bₜ≮N⁼ₜ rewrite N⁼ₜ≡bₜ = Nat.<-irrefl refl

                  Nᵖ : GlobalState
                  Nᵖ = honestBlockMaking (b .pid) ls⁼ N⁼

                  ts : N⁼ ↝[ b .pid ]↑ Nᵖ
                  ts = honestParty↑ lsbₚN⁼ hb

                  lsN‴≡lsNᵖ  : N‴ .states ⁉ b .pid ≡ Nᵖ .states ⁉ b .pid
                  lsN‴≡lsNᵖ = localStatePreservation-∈-↑∗ N₀↝⋆N⁼ N⁼—[eoN⁼]↑→∗N‴ ts

                  goal′*″ : ∃[ ls′ ] (N‴ .states ⁉ b .pid) ≡ just ls′ × length
                    (bestChain (N‴ .clock) (ls′ .tree)) ≡ length (b ∷ cₕ)
                  goal′*″ rewrite N⁺ₜ≡bₜ | sym N⁼ₜ≡bₜ =
                    subst (λ ◆ → ∃[ ls′ ] (◆ ≡ just ls′ × length (bestChain (N⁼ .clock) (ls′ .tree)) ≡ length (b ∷ cₕ)))
                      (sym lsN‴≡lsNᵖ)
                      (pastBestChainLength†
                        N₀↝⋆N cfN N₀↝⋆N⁼ ts [b+cₕ]✓ b∉bhN⁼ refl hp lspN cₜ+b+cₕ≡bcN N⁼↝⋆N ffN⁺ hb
                        (reverseView (N⁼ .execOrder)) N‴↷↑N‴[bM] N⁼Uniq b∈bhN⁺ ((—[]→∗⇒—[]→∗ʳ N⁼—[eoN⁼]↑→∗N‴)))
                    where
                      N‴↷↑N‴[bM] : N‴ ↷↑ record N‴ { progress = blockMade }
                      N‴↷↑N‴[bM] = progress↑ (↷↑-refl)

                      N⁼Uniq : Unique (N⁼ .execOrder)
                      N⁼Uniq = execOrderUniqueness N₀↝⋆N⁼

pastBestChainLength : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → ForgingFree N
  → CollisionFree N
  → ∀ {p : Party} {ls : LocalState}
    → Honest p
    → N .states ⁉ p ≡ just ls
    → ∀ {b : Block} {cₕ cₜ : Chain}
      → HonestBlock b
      → cₕ ++ b ∷ cₜ ≡ bestChain (N .clock ∸ 1) (ls .tree)
      → ∃₂[ N′ , p′ ]
          N₀ ↝⋆ N′
        × N′ ↝⋆ N
        × N′ .clock ≡ suc (b .slot)
        × N′ .progress ≡ ready
        × Honest p′
        × ∃[ ls′ ]
            N′ .states ⁉ p′ ≡ just ls′
          × length (bestChain (N′ .clock ∸ 1) (ls′ .tree)) ≡ length (b ∷ cₜ)
pastBestChainLength {N} N₀↝⋆N ffN cfN {p} {ls} hp lspN {b} {cₜ} {cₕ} hb cₜ+b+cₕ≡bcN
  with b ≟ genesisBlock
... | yes b≡gb rewrite b≡gb | genesisBlockSlot =
    case ∃ls′∈N₀ of λ where
      (ls′ , lspN₀) → N₀ , p , RTC.ε , N₀↝⋆N , refl , refl , hp , ls′ , lspN₀ , (|bcls′|≡|cₕ|+1 $ tree₀InN₀ lspN₀)
  where
    ∃ls′∈N₀ : ∃[ ls′ ] N₀ .states ⁉ p ≡ just ls′
    ∃ls′∈N₀ = hasStateInAltDef {N₀} .Equivalence.from $ L.All.lookup (allPartiesHaveLocalState RTC.ε) p∈ps₀
      where
        p∈ps₀ : p ∈ parties₀
        p∈ps₀ = hasState⇔∈parties₀ N₀↝⋆N .Equivalence.to pHasInN
          where
            pHasInN : p hasStateIn N
            pHasInN = hasStateInAltDef {N} {p} .Equivalence.to (ls , lspN)

    cₕ≡[] : cₕ ≡ []
    cₕ≡[] = [gb+c]✓⇔c≡[] .Equivalence.to [gb+cₕ]✓
      where
        [gb+cₕ]✓ : (genesisBlock ∷ cₕ) ✓
        [gb+cₕ]✓ rewrite sym b≡gb = ✓-++ʳ $ subst _✓ (sym cₜ+b+cₕ≡bcN) (valid (ls .tree) (N .clock ∸ 1))

    |bcls′|≡|cₕ|+1 : ∀ {ls′} → ls′ .tree ≡ tree₀ → length (bestChain 0 (ls′ .tree)) ≡ suc (length cₕ)
    |bcls′|≡|cₕ|+1 tls′≡t₀ rewrite tls′≡t₀ | bestChain[t₀]≡gb 0 | cₕ≡[] = refl

... | no  b≢gb = goal
  where
    open import Function.Reasoning

    bcN : Chain
    bcN = bestChain (N .clock ∸ 1) (ls .tree)

    bcN✓ : bcN ✓
    bcN✓ = valid (ls .tree) (N .clock ∸ 1)

    b∈bcN : b ∈ bcN
    b∈bcN rewrite sym cₜ+b+cₕ≡bcN = L.Mem.∈-++⁺ʳ cₜ (here refl)

    [b+cₕ]✓ : (b ∷ cₕ) ✓
    [b+cₕ]✓ = ✓-++ʳ $ subst _✓ (sym cₜ+b+cₕ≡bcN) bcN✓

    N₀ₜ≤bₜ : N₀ .clock ≤ b .slot
    N₀ₜ≤bₜ with ✓⇒gbIsHead bcN✓
    ... | c , c+gb≡bcN = 1≤bₜ b∈c [c+gb]✓
      where
        [c+gb]✓ : (c L.∷ʳ genesisBlock) ✓
        [c+gb]✓ rewrite c+gb≡bcN = bcN✓

        b∈c : b ∈ c
        b∈c = ∈-∷ʳ-≢⁻ (subst (b ∈_) (sym c+gb≡bcN) b∈bcN) b≢gb

        1≤bₜ : ∀ {c*} → b ∈ c* → (c* L.∷ʳ genesisBlock) ✓ → 1 ≤ b .slot
        1≤bₜ {[]} () _
        1≤bₜ {b′ ∷ c*} (here b≡b′) [b′+c*+gb]✓ rewrite b≡b′ =
          subst
            ((_≤ b′ .slot) ∘ suc)
            genesisBlockSlot $
            nonAdjacentBlocksDecreasingSlots {cₕ = []} {cₘ = c*} {cₜ = []} (✓⇒ds [b′+c*+gb]✓)
        1≤bₜ {b′ ∷ b″ ∷ c*} (there b∈b″+c*) [b′+b″+c*+gb]✓ = 1≤bₜ {b″ ∷ c*} b∈b″+c* $ ✓-++ʳ {c = [ b′ ]} [b′+b″+c*+gb]✓

    bₜ≤Nₜ-1 : b .slot ≤ N .clock ∸ 1
    bₜ≤Nₜ-1 = L.Mem.∈-filter⁻ _ {xs = allBlocks (ls .tree)} (selfContained (ls .tree) (N .clock ∸ 1) b∈bcN) .proj₂

    N₀ₜ≤bₜ+1 : N₀ .clock ≤ suc (b .slot)
    N₀ₜ≤bₜ+1 = Nat.s≤s Nat.z≤n

    bₜ+1≤Nₜ : suc (b .slot) ≤ N .clock
    bₜ+1≤Nₜ = subst (suc (b .slot) ≤_) (Nat.suc-pred _ ⦃ Nat.>-nonZero $ positiveClock N₀↝⋆N ⦄) $ Nat.s≤s bₜ≤Nₜ-1

    bₜ≤bₜ+1 : b .slot ≤ suc (b .slot)
    bₜ≤bₜ+1 = Nat.n≤1+n _

    open RTC; open Starʳ

    goal : _
    goal
      with ∃ReadyBetweenSlots refl N₀↝⋆N (N₀ₜ≤bₜ+1 , bₜ+1≤Nₜ)
    ... | N″ , N″Ready , N″ₜ≡bₜ+1 , N₀↝⋆N″ , N″↝⋆N
      with ∃ReadyBetweenSlots refl N₀↝⋆N″ (N₀ₜ≤bₜ , subst (b .slot ≤_) (sym N″ₜ≡bₜ+1) bₜ≤bₜ+1)
    ... | N′ , N′Ready , N′ₜ≡bₜ , N₀↝⋆N′ , N′↝⋆N″ =
      N″ , b .pid , N₀↝⋆N″ , N″↝⋆N , subst (_≡ suc (b .slot)) (sym N″ₜ≡bₜ+1) refl , N″Ready , hb ,
      pastBestChainLength‡
        (Star⇒Starʳ N′↝⋆N″) N″↝⋆N ε N₀↝⋆N′ ffN cfN hb N₀↝⋆N [b+cₕ]✓ hp lspN cₜ+b+cₕ≡bcN N′ₜ≡bₜ N″ₜ≡bₜ+1 N′Ready N″Ready b∈bhN″
      where
        b∈bhN : b ∈ blockHistory N
        b∈bhN =
            b∈bcN ∶
          b ∈ bcN
            |> selfContained (ls .tree) (N .clock ∸ 1) ∶
          b ∈ filter ((_≤? N .clock ∸ 1) ∘ slot) (allBlocks (ls .tree))
            |> L.SubS.filter-⊆ _ _ ∶
          b ∈ allBlocks (ls .tree)
            |> honestLocalTreeInHonestGlobalTree N₀↝⋆N hp lspN ∶
          b ∈ allBlocks (honestTree N)
            |> flip (L.Mem.∈-filter⁺ _) b≢gb ∶
          b ∈ filter ¿ _≢ genesisBlock ¿¹ (allBlocks (honestTree N))
            |> honestGlobalTreeButGBInBlockHistory N₀↝⋆N ∶
          b ∈ blockHistory N

        bₜ<N″ₜ : b .slot < N″ .clock
        bₜ<N″ₜ rewrite N″ₜ≡bₜ+1 = Nat.≤-refl

        b∈bhN″ : b ∈ blockHistory N″
        b∈bhN″ =
            L.Mem.∈-filter⁺ _ b∈bhN hb ∶
          b ∈ honestBlockHistory N
            |> flip (L.Mem.∈-filter⁺ _) bₜ<N″ₜ ∶
          b ∈ filter ((_<? N″ .clock) ∘ slot) (honestBlockHistory N)
            |> ≡ˢ⇒⊇ (honestBlocksBelowSlotPreservation N₀↝⋆N″ N″↝⋆N ffN) ∶
          b ∈ filter ((_<? N″ .clock) ∘ slot) (honestBlockHistory N″)
            |> L.SubS.filter-⊆ _ _ ∶
          b ∈ honestBlockHistory N″
            |> L.SubS.filter-⊆ _ _ ∶
          b ∈ blockHistory N″

        goal* : ∀ {N*} →
            N′ ↝⋆ʳ N*
          → N* ↝⋆ N
          → N′ .clock ≡ b .slot
          → N* .clock ≡ suc (b .slot)
          → N′ .progress ≡ ready
          → N* .progress ≡ ready
          → b ∈ blockHistory N*
          → ∃[ ls′ ] N* .states ⁉ b .pid ≡ just ls′ × length (bestChain (N* .clock ∸ 1) (ls′ .tree)) ≡ length (b ∷ cₕ)
        goal* εʳ _ N′ₜ≡bₜ N′ₜ≡bₜ+1 = contradiction (trans (sym N′ₜ≡bₜ) N′ₜ≡bₜ+1) λ ()
        goal* {N*} (_◅ʳ_ {j = N°} N′↝⋆ʳN° N°↝N*) N*↝⋆N N′ₜ≡bₜ N*ₜ≡bₜ+1 N′Ready N*Ready b∈bhN* = goal′ N°↝N*
          where
            N°↝⋆N : N° ↝⋆ N
            N°↝⋆N = N°↝N* ◅ N*↝⋆N

            ih : N° .clock ≡ suc (b .slot) → N° .progress ≡ ready → b ∈ blockHistory N° → _
            ih N°ₜ≡bₜ+1 N°Ready b∈bhN° = goal* {N°} N′↝⋆ʳN° N°↝⋆N N′ₜ≡bₜ N°ₜ≡bₜ+1 N′Ready N°Ready b∈bhN°

            goal′ : N° ↝ N* → _
            goal′ (permuteParties _) = ih N*ₜ≡bₜ+1 N*Ready b∈bhN*
            goal′ (permuteMsgs    _) = ih N*ₜ≡bₜ+1 N*Ready b∈bhN*
            goal′ (advanceRound N°BlockMade) = goal″ N′↝⋆ʳN° N°↝⋆N N′ₜ≡bₜ N°ₜ≡bₜ N′Ready N°BlockMade b∈bhN*
              where
                N°ₜ≡bₜ : N° .clock ≡ b .slot
                N°ₜ≡bₜ = Nat.suc-injective N*ₜ≡bₜ+1

                goal″ : ∀ {N⁺} →
                    N′ ↝⋆ʳ N⁺
                  → N⁺ ↝⋆ N
                  → N′ .clock ≡ b .slot
                  → N⁺ .clock ≡ b .slot
                  → N′ .progress ≡ ready
                  → N⁺ .progress ≡ blockMade
                  → b ∈ blockHistory N⁺
                  → ∃[ ls′ ] N⁺ .states ⁉ b .pid ≡ just ls′ × length (bestChain (N⁺ .clock) (ls′ .tree)) ≡ length (b ∷ cₕ)
                goal″ εʳ _ _ _ N′Ready N′BlockMade _ = contradiction (trans (sym N′Ready) N′BlockMade) λ ()
                goal″ {N⁺} (_◅ʳ_ {j = N⁼} N′↝⋆ʳN⁼ N⁼↝N⁺) Ṇ⁺↝⋆N N′ₜ≡bₜ N⁺ₜ≡bₜ N′Ready N⁺BlockMade b∈bhN⁺ = goal‴ N⁼↝N⁺
                  where
                    N⁼↝⋆N : N⁼ ↝⋆ N
                    N⁼↝⋆N = N⁼↝N⁺ ◅ Ṇ⁺↝⋆N

                    goal‴ : N⁼ ↝ N⁺ → _
                    goal‴ (permuteParties _) = goal″ N′↝⋆ʳN⁼ N⁼↝⋆N N′ₜ≡bₜ N⁺ₜ≡bₜ N′Ready N⁺BlockMade b∈bhN⁺
                    goal‴ (permuteMsgs    _) = goal″ N′↝⋆ʳN⁼ N⁼↝⋆N N′ₜ≡bₜ N⁺ₜ≡bₜ N′Ready N⁺BlockMade b∈bhN⁺
                    goal‴ (makeBlock {N′ = N‴} N⁼MsgsDelivered N⁼—[eoN⁼]↑→∗N‴) = goal′*″
                      where
                        N⁼ₜ≡bₜ : N⁼ .clock ≡ b .slot
                        N⁼ₜ≡bₜ = trans (sym $ clockPreservation-↑∗ N⁼—[eoN⁼]↑→∗N‴) N⁺ₜ≡bₜ

                        N₀↝⋆N⁼ : N₀ ↝⋆ N⁼
                        N₀↝⋆N⁼ = N₀↝⋆N′ ◅◅ (Starʳ⇒Star N′↝⋆ʳN⁼)

                        ffN⁼ : ForgingFree N⁼
                        ffN⁼ = ForgingFreePrev N⁼↝⋆N ffN

                        ffN⁺ : ForgingFree N⁺
                        ffN⁺ = ForgingFreePrev Ṇ⁺↝⋆N ffN

                        hasLspN⁼ : b .pid hasStateIn N⁼
                        hasLspN⁼ = L.All.lookup (allPartiesHaveLocalState N₀↝⋆N⁼) bₚ∈N⁼
                          where
                            b∈hbhN⁺ : b ∈ honestBlockHistory N⁺
                            b∈hbhN⁺ = L.Mem.∈-filter⁺ _ b∈bhN⁺ hb

                            bₚ∈N⁺ : b .pid ∈ N⁺ .execOrder
                            bₚ∈N⁺ = honestBlockPidInExecOrder (N₀↝⋆N⁼ ◅◅ N⁼↝N⁺ ◅ ε) ffN⁺ b∈hbhN⁺

                            bₚ∈N⁼ : b .pid ∈ N⁼ .execOrder
                            bₚ∈N⁼ = ∈-resp-↭ (↭-sym (execOrderPreservation-↭-↝ N⁼↝N⁺)) bₚ∈N⁺

                        ls⁼ : LocalState
                        ls⁼ = M.to-witness hasLspN⁼

                        lsbₚN⁼ : N⁼ .states ⁉ b .pid ≡ just ls⁼
                        lsbₚN⁼ = Is-just⇒to-witness hasLspN⁼

                        b∉bhN⁼ : b ∉ blockHistory N⁼
                        b∉bhN⁼ = ∉-filter⁻ _ b∉hbhN⁼ hb
                          where
                            <N⁼ₜ[hbhN⁼] : L.All.All ((_< N⁼ .clock) ∘ slot) (honestBlockHistory N⁼)
                            <N⁼ₜ[hbhN⁼] = noPrematureHonestBlocksAt↓ N₀↝⋆N⁼ ffN⁼ N⁼MsgsDelivered

                            b∉hbhN⁼ : b ∉ honestBlockHistory N⁼
                            b∉hbhN⁼ rewrite sym $ All-filter {P? = (_<? N⁼ .clock) ∘ slot} <N⁼ₜ[hbhN⁼] = b∉<N⁼ₜ[hbhN⁼]
                              where
                                b∉<N⁼ₜ[hbhN⁼] : b ∉ filter ((_<? N⁼ .clock) ∘ slot) (honestBlockHistory N⁼)
                                b∉<N⁼ₜ[hbhN⁼] = ∉-filter⁺ (honestBlockHistory N⁼) bₜ≮N⁼ₜ
                                  where
                                    bₜ≮N⁼ₜ : ¬ (b. slot < N⁼ .clock)
                                    bₜ≮N⁼ₜ rewrite N⁼ₜ≡bₜ = Nat.<-irrefl refl

                        Nᵖ : GlobalState
                        Nᵖ = honestBlockMaking (b .pid) ls⁼ N⁼

                        ts : N⁼ ↝[ b .pid ]↑ Nᵖ
                        ts = honestParty↑ lsbₚN⁼ hb

                        lsN‴≡lsNᵖ  : N‴ .states ⁉ b .pid ≡ Nᵖ .states ⁉ b .pid
                        lsN‴≡lsNᵖ = localStatePreservation-∈-↑∗ N₀↝⋆N⁼ N⁼—[eoN⁼]↑→∗N‴ ts

                        goal′*″ : ∃[ ls′ ] (N‴ .states ⁉ b .pid) ≡ just ls′ × length
                          (bestChain (N‴ .clock) (ls′ .tree)) ≡ length (b ∷ cₕ)
                        goal′*″ rewrite N⁺ₜ≡bₜ | sym N⁼ₜ≡bₜ =
                          subst (λ ◆ → ∃[ ls′ ] (◆ ≡ just ls′ × length (bestChain (N⁼ .clock) (ls′ .tree)) ≡ length (b ∷ cₕ)))
                            (sym lsN‴≡lsNᵖ)
                            (pastBestChainLength†
                              N₀↝⋆N cfN N₀↝⋆N⁼ ts [b+cₕ]✓ b∉bhN⁼ refl hp lspN cₜ+b+cₕ≡bcN N⁼↝⋆N ffN⁺ hb
                              (reverseView (N⁼ .execOrder)) N‴↷↑N‴[bM] N⁼Uniq b∈bhN⁺ ((—[]→∗⇒—[]→∗ʳ N⁼—[eoN⁼]↑→∗N‴)))
                          where
                            N‴↷↑N‴[bM] : N‴ ↷↑ record N‴ { progress = blockMade }
                            N‴↷↑N‴[bM] = progress↑ (↷↑-refl)

                            N⁼Uniq : Unique (N⁼ .execOrder)
                            N⁼Uniq = execOrderUniqueness N₀↝⋆N⁼

pastBestChainLength′ : ∀ {N N′ : GlobalState} →
    N₀ ↝⋆ N′
  → N′ ↝⋆ N
  → ForgingFree N
  → CollisionFree N
  → N′ .progress ≡ ready
  → ∀ {p : Party} {ls : LocalState}
    → Honest p
    → N .states ⁉ p ≡ just ls
    → ∀ {b : Block} {cₕ cₜ : Chain}
      → HonestBlock b
      → N′ .clock ≤ b .slot
      → cₕ ++ b ∷ cₜ ≡ bestChain (N .clock ∸ 1) (ls .tree)
      → ∃₂[ N″ , p′ ]
          N′ ↝⋆ N″
        × N″ ↝⋆ N
        × N″ .clock ≡ suc (b .slot)
        × N″ .progress ≡ ready
        × Honest p′
        × ∃[ ls′ ]
            N″ .states ⁉ p′ ≡ just ls′
          × length (bestChain (N″ .clock ∸ 1) (ls′ .tree)) ≡ length (b ∷ cₜ)
pastBestChainLength′ {N} {N′} N₀↝⋆N′ N′↝⋆N ffN cfN N′Ready {p} {ls} hp lspN {b} {cₜ} {cₕ} hb N′ₜ≤bₜ cₜ+b+cₕ≡bcN = goal
  where
    open import Function.Reasoning

    bcN : Chain
    bcN = bestChain (N .clock ∸ 1) (ls .tree)

    _ : ∃₂[ cₕ′ , cₜ′ ] bcN ≡ cₜ′ ++ b ∷ cₕ′
    _ = cₕ , cₜ , sym cₜ+b+cₕ≡bcN

    bcN✓ : bcN ✓
    bcN✓ = valid (ls .tree) (N .clock ∸ 1)

    b∈bcN : b ∈ bcN
    b∈bcN rewrite sym cₜ+b+cₕ≡bcN = L.Mem.∈-++⁺ʳ cₜ (here refl)

    [b+cₕ]✓ : (b ∷ cₕ) ✓
    [b+cₕ]✓ = ✓-++ʳ $ subst _✓ (sym cₜ+b+cₕ≡bcN) bcN✓

    b≢gb : b ≢ genesisBlock
    b≢gb b≡gb = contradiction (positiveClock N₀↝⋆N′) (Nat.≤⇒≯ N′ₜ≤0)
      where
        N′ₜ≤0 : N′ .clock ≤ 0
        N′ₜ≤0 = subst (N′ .clock ≤_) genesisBlockSlot (subst ((N′ .clock ≤_) ∘ slot) b≡gb N′ₜ≤bₜ)

    bₜ≤Nₜ-1 : b .slot ≤ N .clock ∸ 1
    bₜ≤Nₜ-1 = L.All.lookup (bestChainSlotBounded (ls .tree) (N .clock ∸ 1)) b∈bcN

    N₀↝⋆N : N₀ ↝⋆ N
    N₀↝⋆N = N₀↝⋆N′ ◅◅ N′↝⋆N

    N′ₜ≤bₜ+1 : N′ .clock ≤ suc (b .slot)
    N′ₜ≤bₜ+1 = Nat.≤-trans N′ₜ≤bₜ (Nat.n≤1+n _)

    bₜ+1≤Nₜ : suc (b .slot) ≤ N .clock
    bₜ+1≤Nₜ = subst (suc (b .slot) ≤_) (Nat.suc-pred _ ⦃ Nat.>-nonZero $ positiveClock N₀↝⋆N ⦄) $ Nat.s≤s bₜ≤Nₜ-1

    bₜ≤bₜ+1 : b .slot ≤ suc (b .slot)
    bₜ≤bₜ+1 = Nat.n≤1+n _

    open RTC; open Starʳ

    goal : _
    goal
      with ∃ReadyBetweenSlots N′Ready N′↝⋆N (N′ₜ≤bₜ+1 , bₜ+1≤Nₜ)
    ... | N″ , N″Ready , N″ₜ≡bₜ+1 , N′↝⋆N″ , N″↝⋆N
      with ∃ReadyBetweenSlots N′Ready N′↝⋆N″ (N′ₜ≤bₜ , subst (b .slot ≤_) (sym N″ₜ≡bₜ+1) bₜ≤bₜ+1)
    ... | N‴ , N‴Ready , N‴ₜ≡bₜ , N′↝⋆N‴ , N‴↝⋆N″ = N″ , b .pid , N′↝⋆N″ , N″↝⋆N , subst (_≡ suc (b .slot)) (sym N″ₜ≡bₜ+1) refl , N″Ready , hb ,
      pastBestChainLength‡
        (Star⇒Starʳ N‴↝⋆N″) N″↝⋆N N′↝⋆N‴ N₀↝⋆N′ ffN cfN hb N₀↝⋆N [b+cₕ]✓ hp lspN cₜ+b+cₕ≡bcN
        N‴ₜ≡bₜ N″ₜ≡bₜ+1 N‴Ready N″Ready b∈bhN″
      where
        b∈bhN : b ∈ blockHistory N
        b∈bhN =
            b∈bcN ∶
          b ∈ bcN
            |> selfContained (ls .tree) (N .clock ∸ 1) ∶
          b ∈ filter ((_≤? N .clock ∸ 1) ∘ slot) (allBlocks (ls .tree))
            |> L.SubS.filter-⊆ _ _ ∶
          b ∈ allBlocks (ls .tree)
            |> honestLocalTreeInHonestGlobalTree N₀↝⋆N hp lspN ∶
          b ∈ allBlocks (honestTree N)
            |> flip (L.Mem.∈-filter⁺ _) b≢gb ∶
          b ∈ filter ¿ _≢ genesisBlock ¿¹ (allBlocks (honestTree N))
            |> honestGlobalTreeButGBInBlockHistory N₀↝⋆N ∶
          b ∈ blockHistory N

        bₜ<N″ₜ : b .slot < N″ .clock
        bₜ<N″ₜ rewrite N″ₜ≡bₜ+1 = Nat.≤-refl

        N₀↝⋆N″ : N₀ ↝⋆ N″
        N₀↝⋆N″ = N₀↝⋆N′ ◅◅ N′↝⋆N″

        b∈bhN″ : b ∈ blockHistory N″
        b∈bhN″ =
            L.Mem.∈-filter⁺ _ b∈bhN hb ∶
          b ∈ honestBlockHistory N
            |> flip (L.Mem.∈-filter⁺ _) bₜ<N″ₜ ∶
          b ∈ filter ((_<? N″ .clock) ∘ slot) (honestBlockHistory N)
            |> ≡ˢ⇒⊇ (honestBlocksBelowSlotPreservation N₀↝⋆N″ N″↝⋆N ffN) ∶
          b ∈ filter ((_<? N″ .clock) ∘ slot) (honestBlockHistory N″)
            |> L.SubS.filter-⊆ _ _ ∶
          b ∈ honestBlockHistory N″
            |> L.SubS.filter-⊆ _ _ ∶
          b ∈ blockHistory N″

opaque
  unfolding count

  corruptBlocksUpperBound : ∀ {sl₁ sl₂ : Slot} {bs : List Block} →
      L.All.All (λ b → sl₁ ≤ b .slot × b .slot < sl₂) bs
    → CorrectBlocks bs
    → DecreasingSlots bs
    → count (∁? ¿ HonestBlock ¿¹) bs ≤ length (corruptSlotsInRange sl₁ sl₂)
  corruptBlocksUpperBound {sl₁} {sl₂} {bs} bs:[sl₁:sl₂] cb[bs] ds[bs] with sl₁ <? sl₂
  ... | no sl₁≮sl₂ = goal-sl₁≮sl₂ bs:[sl₁:sl₂]
    where
      goal-sl₁≮sl₂ : ∀ {bs*} →
          L.All.All (λ b → sl₁ ≤ b .slot × b .slot < sl₂) bs*
        → count (∁? ¿ HonestBlock ¿¹) bs* ≤ length (corruptSlotsInRange sl₁ sl₂)
      goal-sl₁≮sl₂ {[]} _ rewrite Nat.m≤n⇒m∸n≡0 (Nat.≮⇒≥ sl₁≮sl₂) = Nat.z≤n
      goal-sl₁≮sl₂ {b* ∷ bs*} [b*+bs*]:[sl₁:sl₂] with L.All.lookup [b*+bs*]:[sl₁:sl₂] (here refl)
      ... | sl₁≤b*ₜ , b*ₜ<sl₂ = contradiction (Nat.≤-<-trans sl₁≤b*ₜ b*ₜ<sl₂) sl₁≮sl₂
  ... | yes sl₁<sl₂ rewrite sym $ L.length-map slot (filter (∁? ¿ HonestBlock ¿¹) bs) =
    Unique-⊆-#≤ cbs[bs]! (cbs[bs*]⊆cs[sl₁:sl₂] ss[bs]⊆cs[sl₁:sl₂] bs:[sl₁:sl₂] cb[bs])
    where
      ss[bs]⊆cs[sl₁:sl₂] : L.map slot bs ⊆ˢ slotsInRange sl₁ sl₂
      ss[bs]⊆cs[sl₁:sl₂] {sl} sl∈m with L.Mem.∈-map⁻ _ sl∈m
      ... | b , b∈bs , sl≡bₜ with L.All.lookup bs:[sl₁:sl₂] b∈bs
      ...   | sl₁≤bₜ , bₜ<sl₂ rewrite sl≡bₜ = ∈-ι⁺ sl₁≤bₜ (subst (b .slot <_) (sym $ Nat.m+[n∸m]≡n (Nat.<⇒≤ sl₁<sl₂)) bₜ<sl₂)

      cbs[bs]! : Unique (L.map slot (filter (∁? ¿ HonestBlock ¿¹) bs))
      cbs[bs]! = DecreasingSlots⇒UniqueSlots (filter⁺ (∁? ¿ HonestBlock ¿¹) (λ {b b′ b″} → >ˢ-trans {b} {b′} {b″}) ds[bs])

      cbs[bs*]⊆cs[sl₁:sl₂] : ∀ {bs*} →
          L.map slot bs* ⊆ˢ slotsInRange sl₁ sl₂
        → L.All.All (λ b → sl₁ ≤ b .slot × b .slot < sl₂) bs*
        → CorrectBlocks bs*
        → L.map slot (filter (∁? ¿ HonestBlock ¿¹) bs*) ⊆ˢ corruptSlotsInRange sl₁ sl₂
      cbs[bs*]⊆cs[sl₁:sl₂] {[]} _ _ _ = λ ()
      cbs[bs*]⊆cs[sl₁:sl₂] {b* ∷ bs*} ss[b*+bs*]⊆cs [b*+bs*]:[sl₁:sl₂] cb[b*+bs*] {sl} with ¿ HonestBlock b* ¿
      ... | yes hb* =
        cbs[bs*]⊆cs[sl₁:sl₂] (λ {_} → ss[b*+bs*]⊆cs ∘ there) (L.All.tail [b*+bs*]:[sl₁:sl₂]) (L.All.tail cb[b*+bs*])
      ... | no ¬hb* = λ where
        (here sl≡b*ₜ) →
          L.Mem.∈-filter⁺
            ¿ CorruptSlot ¿¹
            (subst (_∈ slotsInRange sl₁ sl₂) (sym sl≡b*ₜ) $ ∷⊆⇒∈ ss[b*+bs*]⊆cs)
            (L.Mem.Any↔ .Inverse.to
              (b* .pid ,
               L.Mem.∈-allFin (b* .pid) ,
               (subst (winner (b* .pid)) (sym sl≡b*ₜ) $ L.All.head cb[b*+bs*]) ,
               ¬honest⇒corrupt ¬hb*))
        (there sl∈scs[bs*]) →
          cbs[bs*]⊆cs[sl₁:sl₂]
            (λ {_} → ss[b*+bs*]⊆cs ∘ there) ((L.All.tail [b*+bs*]:[sl₁:sl₂])) ((L.All.tail cb[b*+bs*])) sl∈scs[bs*]

  honestBlocksLowerBound : ∀ {sl₁ sl₂ : Slot} {bs : List Block} {w : ℕ} →
      L.All.All (λ b → sl₁ ≤ b .slot × b .slot < sl₂) bs
    → CorrectBlocks bs
    → DecreasingSlots bs
    → length (corruptSlotsInRange sl₁ sl₂) + w ≤ length bs
    → w ≤ length (honestBlocks bs)
  honestBlocksLowerBound {sl₁} {sl₂} {bs} {w} bs:[sl₁:sl₂] cb[bs] ds[bs] |cs[sl₁:sl₂]|+w≤|bs| =
      subst (length (corruptSlotsInRange sl₁ sl₂) + w ≤_) (sym $ count-partition ¿ HonestBlock ¿¹ bs) |cs[sl₁:sl₂]|+w≤|bs| ∶
    length (corruptSlotsInRange sl₁ sl₂) + w ≤ count ¿ HonestBlock ¿¹ bs + count (∁? ¿ HonestBlock ¿¹) bs
      |> subst (_≤ count ¿ HonestBlock ¿¹ bs + count (∁? ¿ HonestBlock ¿¹) bs) (sym $ Nat.+-comm w _) ∶
    w + length (corruptSlotsInRange sl₁ sl₂) ≤ count ¿ HonestBlock ¿¹ bs + count (∁? ¿ HonestBlock ¿¹) bs
      |> flip Nat.≤-trans (Nat.+-monoʳ-≤ (count ¿ HonestBlock ¿¹ bs) (corruptBlocksUpperBound bs:[sl₁:sl₂] cb[bs] ds[bs])) ∶
    w + length (corruptSlotsInRange sl₁ sl₂) ≤ count ¿ HonestBlock ¿¹ bs + length (corruptSlotsInRange sl₁ sl₂)
      |> Nat.+-cancelʳ-≤ _ _ _ ∶
    w ≤ length (honestBlocks bs)
      where open import Function.Reasoning
