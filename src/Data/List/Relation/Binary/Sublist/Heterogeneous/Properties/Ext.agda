module Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.Ext where

open import Level
open import Relation.Binary.Core using (REL)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List using ([])
open import Data.List.Relation.Binary.Suffix.Heterogeneous
open import Data.List.Relation.Binary.Sublist.Heterogeneous
open import Data.List.Relation.Binary.Sublist.Heterogeneous.Properties using (fromPointwise)

module _ {a b r} {A : Set a} {B : Set b} (R : REL A B r) where

  ⊆[]⇒≡[] : ∀ {xs} → Sublist R xs [] → xs ≡ []
  ⊆[]⇒≡[] {xs = []} p = refl

  Suffix⇒Sublist : ∀ {xs ys} → Suffix R xs ys → Sublist R xs ys
  Suffix⇒Sublist (here xs≐ys)  = fromPointwise xs≐ys
  Suffix⇒Sublist (there {y} p) = y ∷ʳ Suffix⇒Sublist p
