module Data.List.Relation.Binary.Subset.Propositional.Properties.Ext where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; cartesianProduct)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-trans; xs⊆x∷xs)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-cartesianProduct⁺; ∈-cartesianProduct⁻)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.Any.Properties using (¬Any[])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Negation using (contradiction)

∷-⊆ : ∀ {A : Set} {xs ys : List A} {x} → x ∷ xs ⊆ ys → xs ⊆ ys
∷-⊆ {_} {xs} {_} {x} p = ⊆-trans (xs⊆x∷xs xs x) p

cartesianProduct-⊆-Mono : ∀ {A B : Set} {xs xs′ : List A} {ys ys′ : List B} → xs ⊆ xs′ → ys ⊆ ys′ → cartesianProduct xs ys ⊆ cartesianProduct xs′ ys′
cartesianProduct-⊆-Mono {_} {_} {xs} {xs′} {ys} {ys′} xs⊆xs′ ys⊆ys′ {x , y} [x,y]∈xs×ys
  with ∈-cartesianProduct⁻ xs ys [x,y]∈xs×ys
... | x∈xs , y∈ys = ∈-cartesianProduct⁺ (xs⊆xs′ x∈xs) (ys⊆ys′ y∈ys)

⊆[]⇒≡[] : ∀ {A : Set} {xs : List A} → xs ⊆ [] → xs ≡ []
⊆[]⇒≡[] {xs = []} ⊆[] = refl
⊆[]⇒≡[] {xs = x ∷ xs} ⊆[] = contradiction (⊆[] {x} (here refl)) ¬Any[]
