module Data.List.Relation.Binary.Permutation.Propositional.Properties.Ext where

open import Function.Base using (_∘_)
open import Relation.Nullary using (yes; no)
open import Relation.Unary using (Decidable; Pred)
open import Relation.Binary.Core using (_Preserves_⟶_)
open import Relation.Binary.Definitions using (_Respects_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; ≢-sym) renaming (trans to ≡-trans)
open import Data.Nat.Base using (suc)
open import Data.List using (List; _∷_; length; filter)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique) renaming (_∷_ to _∷ᵘ_)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; refl; prep; swap; trans; ↭-trans)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (All-resp-↭)

-- TODO: Use Data.List.Relation.Binary.Permutation.Setoid.Properties.Unique-resp-↭.
-- TODO: Perhaps add to stdlib (Data.List.Relation.Binary.Permutation.Propositional.Properties)
Unique-resp-↭ : ∀ {a} {A : Set a} → _Respects_ {A = List A} Unique _↭_
Unique-resp-↭ refl         wit                       = wit
Unique-resp-↭ (prep x p)   (px ∷ᵘ wit)               = All-resp-↭ p px ∷ᵘ Unique-resp-↭ p wit
Unique-resp-↭ (swap x y p) ((x≢y ∷ px) ∷ᵘ py ∷ᵘ wit) = py′ ∷ᵘ All-resp-↭ p px ∷ᵘ Unique-resp-↭ p wit
  where py′ = ≢-sym x≢y ∷ All-resp-↭ p py
Unique-resp-↭ (trans p₁ p₂) wit                      = Unique-resp-↭ p₂ (Unique-resp-↭ p₁ wit)

-- TODO: Remove when update stdlib to master (use ↭-length).
length-cong : ∀ {a} {A : Set a} → length {A = A} Preserves _↭_ ⟶ _≡_
length-cong refl          = refl
length-cong (prep x p)    = cong suc (length-cong p)
length-cong (swap x y p)  = cong (suc ∘ suc) (length-cong p)
length-cong (trans p₁ p₂) = ≡-trans (length-cong p₁) (length-cong p₂)

-- TODO: Remove when update stdlib to master (use filter-↭).
filter-↭ : ∀ {a} {A : Set a} {P : Pred A a} (P? : Decidable P) → (filter {A = A} P?) Preserves _↭_ ⟶ _↭_
filter-↭ P? refl = refl
filter-↭ P? (prep x xs↭ys) with P? x
... | yes _ = prep x (filter-↭ P? xs↭ys)
... | no _  = filter-↭ P? xs↭ys
filter-↭ P? (swap x y xs↭ys) with P? x in eqˣ | P? y in eqʸ
... | yes _ | yes _ rewrite eqˣ rewrite eqʸ = swap x y (filter-↭ P? xs↭ys)
... | yes _ | no  _ rewrite eqˣ rewrite eqʸ = prep x (filter-↭ P? xs↭ys)
... | no _  | yes _ rewrite eqˣ rewrite eqʸ = prep y (filter-↭ P? xs↭ys)
... | no _  | no _  rewrite eqˣ rewrite eqʸ = filter-↭ P? xs↭ys
filter-↭ P? (trans xs↭ys ys↭zs) = ↭-trans (filter-↭ P? xs↭ys) (filter-↭ P? ys↭zs)
