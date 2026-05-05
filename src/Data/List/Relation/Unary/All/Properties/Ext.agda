module Data.List.Relation.Unary.All.Properties.Ext where

open import Function.Base using (_∘_; _$_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Unary using (Pred; U; ∁; ∅; Decidable)
open import Relation.Unary.Properties.Ext using (U⊆∁∅)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_; _++_; cartesianProduct; filter; reverse)
open import Data.List.Relation.Unary.All using (All; lookup; tabulate; map)
open import Data.List.Relation.Unary.All.Properties using (singleton⁻; ++⁺; ++⁻)
open import Data.List.Properties using (filter-reject; unfold-reverse)
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

All-∁-filter : ∀ {ℓ ℓ′} {A : Set ℓ} {P : Pred A ℓ′} {P? : Decidable P} {xs : List A} → All (∁ P) xs → filter P? xs ≡ []
All-∁-filter           {xs = []}     All.[] = refl
All-∁-filter {P? = P?} {xs = x ∷ xs} (∁Px All.∷ ∁Pxs) rewrite filter-reject P? {xs = xs} ∁Px = All-∁-filter ∁Pxs

All-filter : ∀ {ℓ ℓ′} {A : Set ℓ} {P : Pred A ℓ′} {P? : Decidable P} {xs : List A} → All P xs → filter P? xs ≡ xs
All-filter {xs = []} All.[] = refl
All-filter {P? = P?} {xs = x ∷ xs} (Px All.∷ Pxs) with P? x
... | no ¬Px = contradiction Px ¬Px
... | yes Px = cong (x ∷_) (All-filter Pxs)

All-reverse⁺ : ∀ {ℓ ℓ′} {A : Set ℓ} {P : Pred A ℓ′} {xs : List A} → All P xs → All P (reverse xs)
All-reverse⁺ {xs = []}     All.[] = All.[]
All-reverse⁺ {xs = x ∷ xs} (Px All.∷ Pxs) rewrite unfold-reverse x xs = ++⁺ (All-reverse⁺ Pxs)  (Px All.∷ All.[])

All-reverse⁻ : ∀ {ℓ ℓ′} {A : Set ℓ} {P : Pred A ℓ′} {xs : List A} → All P (reverse xs) → All P xs
All-reverse⁻ {xs = []} p = p
All-reverse⁻ {P = P} {xs = x ∷ xs} p with ++⁻ (reverse xs) (subst (All P) (unfold-reverse x xs) p)
... | Prxs , P[x] = singleton⁻ P[x] All.∷ All-reverse⁻ Prxs
