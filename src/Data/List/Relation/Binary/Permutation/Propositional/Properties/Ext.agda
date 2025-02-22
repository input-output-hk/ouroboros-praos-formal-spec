module Data.List.Relation.Binary.Permutation.Propositional.Properties.Ext where

open import Relation.Binary.Definitions using (_Respects_)
open import Relation.Binary.PropositionalEquality using (≢-sym)
open import Data.List using (List)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique) renaming (_∷_ to _∷ᵘ_)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; refl; prep; swap; trans)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (All-resp-↭)

-- TODO: Perhaps add to stdlib (Data.List.Relation.Binary.Permutation.Propositional.Properties)
Unique-resp-↭ : ∀ {a} {A : Set a} → _Respects_ {A = List A} Unique _↭_
Unique-resp-↭ refl         wit                       = wit
Unique-resp-↭ (prep x p)   (px ∷ᵘ wit)               = All-resp-↭ p px ∷ᵘ Unique-resp-↭ p wit
Unique-resp-↭ (swap x y p) ((x≢y ∷ px) ∷ᵘ py ∷ᵘ wit) = py′ ∷ᵘ All-resp-↭ p px ∷ᵘ Unique-resp-↭ p wit
  where py′ = ≢-sym x≢y ∷ All-resp-↭ p py
Unique-resp-↭ (trans p₁ p₂) wit                      = Unique-resp-↭ p₂ (Unique-resp-↭ p₁ wit)
