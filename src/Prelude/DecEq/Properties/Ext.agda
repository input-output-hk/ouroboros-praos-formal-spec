module Prelude.DecEq.Properties.Ext where

open import Data.Bool using (true)
open import Relation.Nullary.Decidable using (isYes)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)
open import Prelude.DecEq using (DecEq)
open DecEq ⦃...⦄

==-refl : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {x : A} → x == x ≡ true
==-refl {x = x} = cong isYes (≟-refl x)
