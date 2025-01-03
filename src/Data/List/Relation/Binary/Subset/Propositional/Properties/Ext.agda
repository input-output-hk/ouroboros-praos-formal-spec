module Data.List.Relation.Binary.Subset.Propositional.Properties.Ext where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; _∷_; cartesianProduct)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-trans; xs⊆x∷xs)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-cartesianProduct⁺; ∈-cartesianProduct⁻)

∷-⊆ : ∀ {A : Set} {xs ys : List A} {x} → x ∷ xs ⊆ ys → xs ⊆ ys
∷-⊆ {_} {xs} {_} {x} p = ⊆-trans (xs⊆x∷xs xs x) p

cartesianProduct-⊆ˢ-Mono : ∀ {A : Set} {xs ys : List A} → xs ⊆ ys → cartesianProduct xs xs ⊆ cartesianProduct ys ys
cartesianProduct-⊆ˢ-Mono {xs = xs} {ys = ys} xs⊆ys {x₁ , x₂} [x₁,x₂]∈xs×xs = ∈-cartesianProduct⁺ (proj₁ prf) (proj₂ prf)
  where
    prf : x₁ ∈ ys × x₂ ∈ ys
    prf = let (x₁∈xs , x₂∈xs) = ∈-cartesianProduct⁻ xs xs [x₁,x₂]∈xs×xs in xs⊆ys x₁∈xs , xs⊆ys x₂∈xs
