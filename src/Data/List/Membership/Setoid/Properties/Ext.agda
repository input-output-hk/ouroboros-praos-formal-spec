module Data.List.Membership.Setoid.Properties.Ext where

open import Level using (Level)
open import Relation.Binary.Bundles using (Setoid)
open import Data.List using ([_])
open import Data.List.Relation.Unary.Any as Any using (here)
import Data.List.Relation.Binary.Equality.Setoid as Equality
import Data.List.Membership.Setoid as Membership

private
  variable
    c ℓ : Level

module _ (S : Setoid c ℓ) where

  open Setoid S
  open Equality S
  open Membership S

  ∈-[-]⁻ : ∀ {x y} → y ∈ [ x ] → y ≈ x
  ∈-[-]⁻ (here px) = px
