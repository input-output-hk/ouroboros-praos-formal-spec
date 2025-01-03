module Data.List.Membership.Propositional.Properties.Ext where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

x∈x∷xs : ∀ {A : Set} (xs : List A) {x} → x ∈ x ∷ xs
x∈x∷xs xs = here refl

∈-∷⁻ : ∀ {A : Set} (xs : List A) {x y} → y ∈ x ∷ xs → (y ≡ x) ⊎ (y ∈ xs)
∈-∷⁻ xs {x} {y} (here px) = inj₁ px
∈-∷⁻ xs {x} {y} (there p) = inj₂ p
