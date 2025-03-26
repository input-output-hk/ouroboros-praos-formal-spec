module Prelude.DecEq.Properties.Ext where

open import Data.Bool using (true)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (isYes; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Class.DecEq using (DecEq)
open DecEq ⦃...⦄

≟-refl : ∀ {A : Set} ⦃ _ : DecEq A ⦄ (x : A) → (x ≟ x) ≡ yes refl
≟-refl x with x ≟ x
... | yes p rewrite p = refl
... | no ¬p = contradiction refl ¬p

==-refl : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {x : A} → (x == x) ≡ true
==-refl {x = x} = cong isYes (≟-refl x)
