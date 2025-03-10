module Data.List.Relation.Unary.All.Properties.Ext where

open import Relation.Unary using (Pred)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; cartesianProduct)
open import Data.List.Relation.Unary.All using (All; lookup)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-cartesianProduct⁺)

-- TODO: Perhaps move to Data.List.Relation.Unary.All.Properties in stdlib.
cartesianProduct⁻ : ∀ {ℓ} {A B : Set} {P : Pred (A × B) ℓ} {xs : List A} {ys : List B} →
                      All P (cartesianProduct xs ys) →
                      (∀ {x y} → x ∈ xs → y ∈ ys → P (x , y))
cartesianProduct⁻ Pxs×ys {x} {y} x∈xs y∈ys = lookup Pxs×ys {x , y} (∈-cartesianProduct⁺ x∈xs y∈ys)
