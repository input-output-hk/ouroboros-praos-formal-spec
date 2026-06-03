module Relation.Unary.Properties.Ext where

open import Relation.Unary using (Pred; Empty; ∅; U; ∁; _∩_; Decidable) renaming (_⊆_ to _⋐_)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (no)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

U⊆∁∅ : ∀ {a} {A : Set a} → _⋐_ {A = A} U (∁ ∅)
U⊆∁∅ {_} _ = λ ()

P∩∁P≐∅ : ∀ {a ℓ} {A : Set a} {P : Pred A ℓ} → Empty (P ∩ ∁ P)
P∩∁P≐∅ x = λ z → z .proj₂ (z .proj₁)

P∩∁P? : ∀ {a ℓ} {A : Set a} {P : Pred A ℓ} → Decidable (P ∩ ∁ P)
P∩∁P? {P = P} x = no (P∩∁P≐∅ {P = P} x)
