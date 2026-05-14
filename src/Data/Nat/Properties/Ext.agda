module Data.Nat.Properties.Ext where

open import Function.Base using (_∘_; flip)
open import Data.Nat.Base
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; suc-pred; ≤-<-trans; +-suc; +-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; _≗_; refl; cong; subst)

pred[n]<n : ∀ {n} .⦃ _ : NonZero n ⦄ → pred n < n
pred[n]<n {n} = ≤-reflexive (suc-pred n)

suc-≢-injective : ∀ {i j : ℕ} → suc i ≢ suc j → i ≢ j
suc-≢-injective = _∘ cong suc

n≤pred[m]⇒n<m : ∀ {n m} .⦃ _ : NonZero m ⦄ → n ≤ pred m → n < m
n≤pred[m]⇒n<m = flip ≤-<-trans pred[n]<n

n>0⇒pred[n]<n : ∀ {n} → n > 0 → pred n < n
n>0⇒pred[n]<n {zero}    = λ ()
n>0⇒pred[n]<n {suc n} _ = ≤-refl

suc≗+1 : suc ≗ _+ 1
suc≗+1 n rewrite +-suc n 0 | +-identityʳ n = refl

-- TODO: Remove when upgrading stdlib to the next version.
∸-suc : ∀ {m n} → .(m ≤ n) → suc n ∸ m ≡ suc (n ∸ m)
∸-suc {m = zero}              _   = refl
∸-suc {m = suc _} {n = suc _} m≤n = ∸-suc (s≤s⁻¹ m≤n)

0<n∸m⇒m<n : ∀ {n m} → 0 < n ∸ m → m < n
0<n∸m⇒m<n {suc n} {zero} p = p
0<n∸m⇒m<n {suc n} {suc m} p = s≤s (0<n∸m⇒m<n p)
