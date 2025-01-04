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

cartesianProduct-⊆-Mono : ∀ {A : Set} {xs ys : List A} → xs ⊆ ys → cartesianProduct xs xs ⊆ cartesianProduct ys ys
cartesianProduct-⊆-Mono {xs = xs} {ys = ys} xs⊆ys {x₁ , x₂} [x₁,x₂]∈xs×xs = ∈-cartesianProduct⁺ (proj₁ prf) (proj₂ prf)
  where
    prf : x₁ ∈ ys × x₂ ∈ ys
    prf = let (x₁∈xs , x₂∈xs) = ∈-cartesianProduct⁻ xs xs [x₁,x₂]∈xs×xs in xs⊆ys x₁∈xs , xs⊆ys x₂∈xs

⊆[]⇒≡[] : ∀ {A : Set} {xs : List A} → xs ⊆ [] → xs ≡ []
⊆[]⇒≡[] {xs = []} ⊆[] = refl
⊆[]⇒≡[] {xs = x ∷ xs} ⊆[] = contradiction (⊆[] {x} (here refl)) ¬Any[]
