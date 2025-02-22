module Data.List.Relation.Unary.Unique.Propositional.Properties.Ext where

open import Level using (Level)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)
open import Data.Product.Base using (_×_)
open import Data.List.Base using (List; []; _∷_; _∷ʳ_; _++_)
open import Data.List.Membership.Propositional using (_∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs.Core
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
import Data.List.Relation.Unary.Unique.Setoid.Properties.Ext as Setoid
open import Data.List.Relation.Binary.Permutation.Propositional using (↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∷↭∷ʳ)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties.Ext using (Unique-resp-↭)

private
  variable
    a : Level
    A : Set a
    x : A
    xs ys : List A

module _ {A : Set a} {xs ys} where

  ++⁻ : Unique (xs ++ ys) → Unique xs × Unique ys × Disjoint xs ys
  ++⁻ = Setoid.++⁻ (setoid A)

-- TODO: Remove when upgrading the stdlib to version 2.2
Unique[x∷xs]⇒x∉xs : Unique (x ∷ xs) → x ∉ xs
Unique[x∷xs]⇒x∉xs ((x≢ ∷ x∉) ∷ _ ∷ uniq) = λ where
  (here x≡)  → x≢ x≡
  (there x∈) → Unique[x∷xs]⇒x∉xs (x∉ AllPairs.∷ uniq) x∈

Unique[xs∷ʳx]⇒x∉xs : Unique (xs ∷ʳ x) → x ∉ xs
Unique[xs∷ʳx]⇒x∉xs {xs = xs} {x = x} = Unique[x∷xs]⇒x∉xs ∘ Unique-resp-↭ (↭-sym (∷↭∷ʳ x xs))
