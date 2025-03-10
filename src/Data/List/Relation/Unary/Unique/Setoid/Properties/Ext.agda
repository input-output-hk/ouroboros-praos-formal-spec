module Data.List.Relation.Unary.Unique.Setoid.Properties.Ext where

open import Level using (Level)
open import Relation.Binary.Bundles using (Setoid)
open import Data.Product.Base using (_×_; _,_)
open import Data.List.Base using (_++_)
open import Data.List.Relation.Unary.Unique.Setoid
open import Data.List.Relation.Binary.Disjoint.Setoid
import Data.List.Relation.Unary.AllPairs.Properties.Ext as AllPairsP using (++⁻)
open import Data.List.Relation.Binary.Disjoint.Setoid.Properties.Ext using (AllAll⇒Disjoint)

private
  variable
    a ℓ : Level

module _ (S : Setoid a ℓ) where

  ++⁻ : ∀ {xs ys} → Unique S (xs ++ ys) → Unique S xs × Unique S ys × Disjoint S xs ys
  ++⁻ xs++ys! with AllPairsP.++⁻ xs++ys!
  ... | xs! , ys! , AAysxs = xs! , ys! , AllAll⇒Disjoint S AAysxs
