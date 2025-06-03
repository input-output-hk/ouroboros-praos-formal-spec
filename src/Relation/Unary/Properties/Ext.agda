module Relation.Unary.Properties.Ext where

open import Relation.Unary using (∅; U; ∁) renaming (_⊆_ to _⋐_)

U⊆∁∅ : ∀ {a} {A : Set a} → _⋐_ {A = A} U (∁ ∅)
U⊆∁∅ {_} _ = λ ()
