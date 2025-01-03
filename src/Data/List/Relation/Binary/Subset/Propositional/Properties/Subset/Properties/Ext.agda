module Data.List.Relation.Binary.Subset.Propositional.Properties.Ext where

open import Data.List using (List)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)

⊆[]⇒≡[] : ∀ {A : Set} {xs : List A} → xs ⊆ [] → xs ≡ []
⊆[]⇒≡[] {xs = []} ⊆[] = refl
⊆[]⇒≡[] {xs = x ∷ xs} ⊆[] = contradiction (⊆[] {x} (here refl)) L.Any.¬Any[]
