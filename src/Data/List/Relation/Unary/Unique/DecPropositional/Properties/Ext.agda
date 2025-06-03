module Data.List.Relation.Unary.Unique.DecPropositional.Properties.Ext where

open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Nullary.Negation using (contraposition)
open import Data.List using (List; []; _∷_)
open import Data.List.Ext using (undup)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties.Ext using (∈-undup⁻)
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.List.Relation.Unary.All.Properties.Core using (¬Any⇒All¬)
open import Data.List.Relation.Unary.AllPairs.Core as AP using (AllPairs)
open import Class.DecEq using (DecEq)
open DecEq ⦃...⦄

module _ {a} {A : Set a} ⦃ _ : DecEq A ⦄ where

  open import Data.List.Membership.DecPropositional (_≟_ {A = A}) using (_∈?_)

  undup-! : ∀ {xs : List A} → Unique (undup xs)
  undup-! {[]} = AP.[]
  undup-! {x ∷ xs} with x ∈? xs
  ... | yes x∈xs = undup-! {xs}
  ... | no x∉xs  = ¬Any⇒All¬ (undup xs) x∉udxs AP.∷ undup-! {xs}
    where
      x∉udxs : x ∉ undup xs
      x∉udxs = contraposition (∈-undup⁻ xs) x∉xs
