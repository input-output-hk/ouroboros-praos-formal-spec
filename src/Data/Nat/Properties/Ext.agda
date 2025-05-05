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
