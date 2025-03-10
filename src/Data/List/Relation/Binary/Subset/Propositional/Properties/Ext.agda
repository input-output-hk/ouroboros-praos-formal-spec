module Data.List.Relation.Binary.Subset.Propositional.Properties.Ext where

open import Function.Base using (id; _∘_; _|>_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; cartesianProduct; filterᵇ; deduplicate)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-trans; xs⊆x∷xs; filter⁺′; ∷⁺ʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-cartesianProduct⁺; ∈-cartesianProduct⁻; ∈-deduplicate⁻; ∈-deduplicate⁺)
open import Data.List.Membership.Propositional.Properties.Ext using (x∈x∷xs)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.Any.Properties using (¬Any[])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Negation using (contradiction)
open import Prelude.DecEq using (DecEq; _≟_)

∷-⊆ : ∀ {A : Set} {xs ys : List A} {x} → x ∷ xs ⊆ ys → xs ⊆ ys
∷-⊆ {_} {xs} {_} {x} p = ⊆-trans (xs⊆x∷xs xs x) p

∷-⊆⁺ : ∀ {A : Set} {xs ys : List A} {y} → xs ⊆ ys → xs ⊆ y ∷ ys
∷-⊆⁺ {y = y} = ∷-⊆ ∘ ∷⁺ʳ y

∷⊆⇒∈ : ∀ {A : Set} {xs ys : List A} {x} → x ∷ xs ⊆ ys → x ∈ ys
∷⊆⇒∈ {xs = xs} = (x∈x∷xs xs) |>_

cartesianProduct-⊆-Mono : ∀ {A B : Set} {xs xs′ : List A} {ys ys′ : List B} → xs ⊆ xs′ → ys ⊆ ys′ → cartesianProduct xs ys ⊆ cartesianProduct xs′ ys′
cartesianProduct-⊆-Mono {_} {_} {xs} {xs′} {ys} {ys′} xs⊆xs′ ys⊆ys′ {x , y} [x,y]∈xs×ys
  with ∈-cartesianProduct⁻ xs ys [x,y]∈xs×ys
... | x∈xs , y∈ys = ∈-cartesianProduct⁺ (xs⊆xs′ x∈xs) (ys⊆ys′ y∈ys)

⊆[]⇒≡[] : ∀ {A : Set} {xs : List A} → xs ⊆ [] → xs ≡ []
⊆[]⇒≡[] {xs = []} ⊆[] = refl
⊆[]⇒≡[] {xs = x ∷ xs} ⊆[] = contradiction (⊆[] {x} (here refl)) ¬Any[]

filterᵇ-mono : ∀ {A : Set} {P : A → Bool} {xs ys : List A} → xs ⊆ ys → filterᵇ P xs ⊆ filterᵇ P ys
filterᵇ-mono {P = P} xs⊆ys = filter⁺′ (T? ∘ P) (T? ∘ P) id xs⊆ys
  where open import Relation.Nullary.Decidable.Core using (T?)

deduplicate⁺′ : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {xs ys : List A} → xs ⊆ ys → deduplicate _≟_ xs ⊆ deduplicate _≟_ ys
deduplicate⁺′ {xs = xs} xs⊆ys v∈ddxs with ∈-deduplicate⁻ _≟_ xs v∈ddxs
... | v∈xs = ∈-deduplicate⁺ _≟_ (xs⊆ys v∈xs)

deduplicate-⊆ : ∀ {A : Set} ⦃ _ : DecEq A ⦄ (xs : List A) → deduplicate _≟_ xs ⊆ xs
deduplicate-⊆ xs {x} x∈ddxs = ∈-deduplicate⁻ _≟_ xs {x} x∈ddxs
