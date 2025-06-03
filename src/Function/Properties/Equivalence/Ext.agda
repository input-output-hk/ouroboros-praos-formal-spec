module Function.Properties.Equivalence.Ext where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Structures using (IsEquivalence)
open import Function.Bundles using (_⇔_; Equivalence)
open import Function.Properties.Equivalence using (⇔-isEquivalence)

≡⇒⇔ : ∀ {a} {A B : Set a} → A ≡ B → A ⇔ B
≡⇒⇔ {a = a} A≡B rewrite A≡B = ⇔-refl
  where open IsEquivalence {ℓ = a} ⇔-isEquivalence renaming (refl to ⇔-refl)
