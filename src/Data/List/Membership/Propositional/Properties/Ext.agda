module Data.List.Membership.Propositional.Properties.Ext where

open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Bool using (Bool; false; true)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; _∷_; findᵇ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Relation.Nullary.Negation using (contradiction)
open import Prelude.DecEq using (DecEq)

x∈x∷xs : ∀ {A : Set} (xs : List A) {x} → x ∈ x ∷ xs
x∈x∷xs xs = here refl

∈-∷⁻ : ∀ {A : Set} {xs : List A} {x y} → y ∈ x ∷ xs → (y ≡ x) ⊎ (y ∈ xs)
∈-∷⁻ (here px) = inj₁ px
∈-∷⁻ (there p) = inj₂ p

∈-findᵇ⁻ : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {P : A → Bool} {xs : List A} {x : A} → findᵇ P xs ≡ just x → x ∈ xs
∈-findᵇ⁻ {P = P} {xs = x′ ∷ xs′} eqf with P x′
... | false = there (∈-findᵇ⁻ {xs = xs′} eqf)
... | true  = here (sym (just-injective eqf))

∈-∷-≢⁻ : ∀ {A : Set} {xs : List A} {x y : A} → y ∈ x ∷ xs → y ≢ x → y ∈ xs
∈-∷-≢⁻ y∈x∷xs y≢x with ∈-∷⁻ y∈x∷xs
... | inj₁ y≡x  = contradiction y≡x y≢x
... | inj₂ y∈xs = y∈xs
