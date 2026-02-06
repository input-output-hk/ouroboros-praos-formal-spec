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
open import Protocol.Tree.Properties ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.SuperBlocks ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.Time ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.Trees ⦃ params ⦄ ⦃ assumptions ⦄
open import Data.Nat.Properties.Ext using (suc≗+1)

honestTreeChainGrowth : ∀ {N N′ : GlobalState} →
    N₀ ↝⋆ N
  → N ↝⋆ N′
  → N .progress ≡ ready
  → ∀ {w : ℕ} →
      w ≤ length (luckySlotsInRange (N .clock) (N′ .clock))
    → length (honestTreeChain N) + w ≤ length (honestTreeChain N′)
honestTreeChainGrowth {N} N₀↝⋆N N↝⋆N′ _ {0} _
  rewrite Nat.+-identityʳ (length (honestTreeChain N)) = honestTreeChainLengthMonotonicity N₀↝⋆N N↝⋆N′
honestTreeChainGrowth {N} {N′} N₀↝⋆N N↝⋆N′ NReady {suc w} w+1≤|ls[Nₜ:N′ₜ]|
  with ∃LessLuckySlotsBetweenStates
         N₀↝⋆N
         N↝⋆N′
         NReady
         $ subst (_≤ length (luckySlotsInRange (N .clock) (N′ .clock))) (suc≗+1 w) w+1≤|ls[Nₜ:N′ₜ]|
... | N″ , N″Ready , N₀↝⋆N″ , N″↝⋆N′ , |htc[N]|+1≤|htc[N″]| , w≤|ls[N″ₜ:N′ₜ]| =
  Nat.≤-trans |htc[N]|+[w+1]≤w+|htc[N″]| w+|htc[N″]|≤|htc[N′]|
  where
    |htc[N]|+[w+1]≤w+|htc[N″]| : length (honestTreeChain N) + suc w ≤ w + length (honestTreeChain N″)
    |htc[N]|+[w+1]≤w+|htc[N″]|
      rewrite
        sym $ Nat.+-assoc (length (honestTreeChain N)) 1 w
      | Nat.+-comm w (length (honestTreeChain N″))
      = Nat.+-monoˡ-≤ w |htc[N]|+1≤|htc[N″]|

    w+|htc[N″]|≤|htc[N′]| : w + length (honestTreeChain N″) ≤ length (honestTreeChain N′)
    w+|htc[N″]|≤|htc[N′]| rewrite Nat.+-comm w (length (honestTreeChain N″)) =
      honestTreeChainGrowth N₀↝⋆N″ N″↝⋆N′ N″Ready w≤|ls[N″ₜ:N′ₜ]|

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
