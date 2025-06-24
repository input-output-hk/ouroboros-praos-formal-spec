module Data.List.Relation.Unary.Unique.Setoid.Properties.Ext where

open import Level using (Level)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Nullary.Negation using (contraposition)
open import Data.Product.Base using (_×_; _,_)
open import Data.List.Base using (map; _++_)
open import Data.List.Relation.Unary.Unique.Setoid
open import Data.List.Relation.Binary.Disjoint.Setoid
import Data.List.Relation.Unary.AllPairs as AllPairs using (AllPairs; map)
import Data.List.Relation.Unary.AllPairs.Properties.Ext as AllPairs using (map⁻; ++⁻)
open import Data.List.Relation.Binary.Disjoint.Setoid.Properties.Ext using (AllAll⇒Disjoint)
open import Function.Definitions using (Congruent)

private
  variable
    a b ℓ ℓ₁ ℓ₂ : Level

-- TODO: Remove when upgrading to stdlib 2.3.
module _ (S : Setoid a ℓ₁) (R : Setoid b ℓ₂) where

  open Setoid S renaming (_≈_ to _≈₁_)
  open Setoid R renaming (_≈_ to _≈₂_)

  map⁻ : ∀ {f} → Congruent _≈₁_ _≈₂_ f →
         ∀ {xs} → Unique R (map f xs) → Unique S xs
  map⁻ cong fxs! = AllPairs.map (contraposition cong) (AllPairs.map⁻ fxs!)

module _ (S : Setoid a ℓ) where

  ++⁻ : ∀ {xs ys} → Unique S (xs ++ ys) → Unique S xs × Unique S ys × Disjoint S xs ys
  ++⁻ xs++ys! with AllPairs.++⁻ xs++ys!
  ... | xs! , ys! , AAysxs = xs! , ys! , AllAll⇒Disjoint S AAysxs
