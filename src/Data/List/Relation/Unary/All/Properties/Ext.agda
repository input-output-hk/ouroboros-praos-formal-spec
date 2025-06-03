module Data.List.Relation.Unary.All.Properties.Ext where

open import Function.Base using (_∘_)
open import Relation.Unary using (Pred; U; ∁; ∅)
open import Relation.Unary.Properties.Ext using (U⊆∁∅)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; cartesianProduct)
open import Data.List.Relation.Unary.All using (All; lookup; tabulate; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-cartesianProduct⁺)

-- TODO: Perhaps move to Data.List.Relation.Unary.All.Properties in stdlib.
cartesianProduct⁻ : ∀ {ℓ} {A B : Set} {P : Pred (A × B) ℓ} {xs : List A} {ys : List B} →
                      All P (cartesianProduct xs ys) →
                      (∀ {x y} → x ∈ xs → y ∈ ys → P (x , y))
cartesianProduct⁻ Pxs×ys {x} {y} x∈xs y∈ys = lookup Pxs×ys {x , y} (∈-cartesianProduct⁺ x∈xs y∈ys)

All-U : ∀ {ℓ} {A : Set ℓ} (xs : List A) → All U xs
All-U _ = tabulate λ {_} _ → tt

All-∁∅ : ∀ {ℓ} {A : Set ℓ} (xs : List A) → All (∁ ∅) xs
All-∁∅ {A = A} = map (λ {x} → U⊆∁∅ {A = A} {x}) ∘ All-U
