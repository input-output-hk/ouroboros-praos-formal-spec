module Data.Fin.Properties.Ext where

open import Function.Base using (_∘_)
open import Data.Nat using (ℕ; z≤n; _≤_)
open import Data.Nat.Properties using (n≤1+n)
open import Data.Fin using (Fin; zero; suc; pred; _≤_; toℕ)
open import Data.Fin.Properties using (toℕ-inject₁)
open import Relation.Binary.PropositionalEquality using (refl; _≢_; cong; subst; sym)
open import Relation.Nullary.Negation using (contradiction)

suc-≢-injective : ∀ {n : ℕ} {i j : Fin n} → suc i ≢ suc j → i ≢ j
suc-≢-injective = _∘ cong suc

pred-≤ : ∀ {n} (i : Fin n) → pred i Data.Fin.≤ i
pred-≤ zero    = z≤n
pred-≤ (suc i) = subst (Data.Nat._≤ toℕ (suc i)) (sym (toℕ-inject₁ i)) (n≤1+n (toℕ i))
