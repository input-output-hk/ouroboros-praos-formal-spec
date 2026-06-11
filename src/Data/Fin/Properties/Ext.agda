module Data.Fin.Properties.Ext where

open import Function.Base using (_∘_; _∋_)
open import Data.Nat using (ℕ; z≤n; s≤s; _≤_)
open import Data.Nat.Properties using (n≤1+n)
open import Data.Fin using (Fin; zero; suc; pred; _≤_; _<_; _>_; toℕ; inject₁)
open import Data.Fin.Properties using (toℕ-inject₁; inject₁-injective; ≤-trans; i<1+i)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_; cong; subst; sym)
open import Relation.Nullary.Negation using (contradiction)

suc-≢-injective : ∀ {n : ℕ} {i j : Fin n} → suc i ≢ suc j → i ≢ j
suc-≢-injective = _∘ cong suc

pred-≤ : ∀ {n} (i : Fin n) → pred i Data.Fin.≤ i
pred-≤ zero    = z≤n
pred-≤ (suc i) = subst (Data.Nat._≤ toℕ (suc i)) (sym (toℕ-inject₁ i)) (n≤1+n (toℕ i))

pred-injective : ∀ {n : ℕ} {i j : Fin (Data.Nat.suc n)} → i ≢ zero → j ≢ zero → pred i ≡ pred j → i ≡ j
pred-injective {i = suc i} {j = suc j} _ _ eq = cong suc (inject₁-injective eq)
pred-injective {i = zero}  {j = _}     i≢0 _   _ = contradiction refl i≢0
pred-injective {i = _}     {j = zero}  _   j≢0 _ = contradiction refl j≢0

>0⇒≢0 : ∀ {n : ℕ} {i : Fin (Data.Nat.suc n)} → i > (Fin (Data.Nat.suc n) ∋ zero) → i ≢ zero
>0⇒≢0 {n} i>0 i≡0 = contradiction (subst (_> (Fin (Data.Nat.suc n) ∋ zero)) i≡0 i>0) λ ()

pred< : ∀ {n : ℕ} {i j : Fin (Data.Nat.suc n)} → i Data.Fin.≤ j → j > (Fin (Data.Nat.suc n) ∋ zero) → pred i < j
pred< {_} {zero}  {suc _} _          pj = pj
pred< {_} {suc i} {suc j} (s≤s i≤j)  _  =
  subst (λ k → Data.Nat._<_ k (toℕ (Data.Fin.suc j)))
    (sym (toℕ-inject₁ i))
    (Data.Nat.s≤s i≤j)
