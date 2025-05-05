{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled

module Data.List.Relation.Binary.Sublist.Propositional.Properties.Ext where

open import Level
open import Function.Bundles using (Bijection)
open import Function.Base using (_$_; _∘_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (_Respects_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)
open import Data.List using (List; []; _∷_; filter)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
import Data.List.Relation.Binary.Sublist.Setoid as SetoidSublist
import Data.List.Relation.Binary.Sublist.Setoid.Properties as SetoidProperties
open import Data.List.Relation.Binary.Sublist.Propositional hiding (map)
open import Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.Ext

private variable
  a ℓ p : Level
  A : Set a
  x y : A
  xs ys : List A
  P : Pred A p

module _ {A : Set a} where
  open SetoidProperties (setoid A) public hiding (filter-⊆)

module _ (P? : Decidable P) where

  -- TODO: Perhaps add to Data.List.Relation.Binary.Sublist.Propositional.Properties
  filter-⊆ : ∀ xs → filter P? xs ⊆ xs
  filter-⊆ = SetoidProperties.filter-⊆ (setoid _) P?

⊆∷⇒∈ : x ∷ xs ⊆ ys → x ∈ ys
⊆∷⇒∈ {xs = []} p = to [x]⊆xs⤖x∈xs p
  where open Bijection
⊆∷⇒∈ {xs = x′ ∷ xs} {ys = ys} p = {!⊆∷⇒∈ {xs = xs} {ys = ys}!}

⊆∷⇒∈∨⊆ : xs ⊆ y ∷ ys → y ∈ xs ⊎ xs ⊆ ys
⊆∷⇒∈∨⊆ {xs = []} {ys = ys} _ = inj₂ $ []⊆-universal ys
⊆∷⇒∈∨⊆ {xs = x ∷ xs} {y = y} {ys = ys} x∷xs⊆y∷ys with ⊆∷⇒∈∨⊆ $ ∷ˡ⁻ x∷xs⊆y∷ys
... | inj₁ y∈xs = inj₁ $ there y∈xs
... | inj₂ xs⊆ys with ⊆∷⇒∈ x∷xs⊆y∷ys
... |  here x≡y = inj₁ $ here (sym x≡y)
... |  there x∈ys = inj₂ {![x]⊆ys  xs⊆ys!}

Unique-resp-⊇ : Unique {A = A} Respects _⊇_
Unique-resp-⊇ = {!!}
