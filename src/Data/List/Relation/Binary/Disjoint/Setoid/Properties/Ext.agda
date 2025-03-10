module Data.List.Relation.Binary.Disjoint.Setoid.Properties.Ext where

open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.List using (_∷_; [_])
open import Data.List.Relation.Binary.Disjoint.Setoid
open import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties using (All¬⇒¬Any)
open import Data.List.Relation.Unary.Any.Properties using (++⁻)
open import Data.List.Membership.Setoid.Properties using (∈-resp-≈)
open import Data.List.Membership.Setoid.Properties.Ext using (∈-[-]⁻)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Nullary.Negation.Core using (contradiction)

module _ {c ℓ} (S : Setoid c ℓ) where

  open Setoid S

  AllAll⇒Disjoint : ∀ {xs ys} → All (λ x → All (x ≉_) ys) xs → Disjoint S xs ys
  AllAll⇒Disjoint {x ∷ xs} {y ∷ ys} (A≉x[y∷ys] ∷ AA≉x′[y∷ys][xs]) (v∈x∷xs , v∈y∷ys)
    with ++⁻ [ x ] v∈x∷xs
  ... | inj₁ v∈[x] = contradiction (∈-resp-≈ S (∈-[-]⁻ S v∈[x]) v∈y∷ys) (All¬⇒¬Any A≉x[y∷ys])
  ... | inj₂ v∈xs  = AllAll⇒Disjoint AA≉x′[y∷ys][xs] (v∈xs , v∈y∷ys)
