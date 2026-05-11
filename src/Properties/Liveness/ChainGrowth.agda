open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Liveness.ChainGrowth
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.Tree ⦃ params ⦄
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Protocol.Tree.Properties ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Liveness.ChainGrowth.Properties ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.SuperBlocks ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.Time ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.Trees ⦃ params ⦄ ⦃ assumptions ⦄

chainGrowth : ∀ {N N′ : GlobalState} →
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
chainGrowth {N} {N′} N₀↝⋆N (N↝⋆N′ , Nₜ<N′ₜ) NReady {p₁} {p₂} {ls₁} {ls₂} hp₁ lsp₁N hp₂ lsp₂N′ {w} w≤|ls[Nₜ:N′⦈|
  with ∃ReadyBetweenSlots NReady N↝⋆N′ (Nat.<⇒≤pred Nₜ<N′ₜ , Nat.pred[n]≤n)
... | N″ , N″Ready , N″ₜ≡Nₜ-1 , N↝⋆N″ , N″↝⋆N′ = Nat.≤-trans |bcp₁N|+w≤|htc[N″]| |htc[N″]|≤|bcp₂N′|
  where
    bcp₁N  = bestChain (N  .clock ∸ 1) (ls₁ .tree)
    bcp₂N′ = bestChain (N′ .clock ∸ 1) (ls₂ .tree)

    w≤|ls[Nₜ:N″]| : w ≤ length (luckySlotsInRange (N .clock) (N″ .clock))
    w≤|ls[Nₜ:N″]| rewrite N″ₜ≡Nₜ-1 = w≤|ls[Nₜ:N′⦈|

    |bcp₁N|+w≤|htc[N″]| : length bcp₁N + w ≤ length (honestTreeChain N″)
    |bcp₁N|+w≤|htc[N″]| = Nat.≤-trans |bcp₁N|+w≤|htc[N]|+w |htc[N]|+w≤|htc[N″]|
      where
        |bcp₁N|+w≤|htc[N]|+w : length bcp₁N + w ≤ length (honestTreeChain N) + w
        |bcp₁N|+w≤|htc[N]|+w = Nat.+-monoˡ-≤ w (allBlocks⊆⇒|bestChain|≤ _ (honestLocalTreeInHonestGlobalTree N₀↝⋆N hp₁ lsp₁N))

        |htc[N]|+w≤|htc[N″]| : length (honestTreeChain N) + w ≤ length (honestTreeChain N″)
        |htc[N]|+w≤|htc[N″]| = honestTreeChainGrowth N₀↝⋆N N↝⋆N″ NReady {w} w≤|ls[Nₜ:N″]|

    |htc[N″]|≤|bcp₂N′| : length (honestTreeChain N″) ≤ length bcp₂N′
    |htc[N″]|≤|bcp₂N′| =
      allBlocks⊆×≤ˢ⇒|bestChain|≤
        (honestGlobalTreeInHonestLocalTree-↝⁺ (N₀↝⋆N ◅◅ N↝⋆N″) hp₂ N″Ready (N″↝⋆N′ , N″ₜ<N′ₜ) lsp₂N′)
        N″ₜ-1≤N′ₜ-1
      where
        N″ₜ<N′ₜ : N″ .clock < N′ .clock
        N″ₜ<N′ₜ rewrite N″ₜ≡Nₜ-1 | Nat.suc-pred (N′ .clock) ⦃ Nat.>-nonZero $ positiveClock (N₀↝⋆N ◅◅ N↝⋆N′) ⦄ = Nat.≤-refl

        N″ₜ-1≤N′ₜ-1 : N″ .clock ∸ 1 ≤ N′ .clock ∸ 1
        N″ₜ-1≤N′ₜ-1 = Nat.∸-monoˡ-≤ 1 $ subst (_≤ N′ .clock) (sym N″ₜ≡Nₜ-1) Nat.pred[n]≤n
