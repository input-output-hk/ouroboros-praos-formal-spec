module Function.Properties.Equivalence.Ext where

open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Structures using (IsEquivalence)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Function.Properties.Equivalence using (⇔-isEquivalence)
open import Function.Base using (const; _$_; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

≡⇒⇔ : ∀ {a} {A B : Set a} → A ≡ B → A ⇔ B
≡⇒⇔ {a = a} A≡B rewrite A≡B = ⇔-refl
  where open IsEquivalence {ℓ = a} ⇔-isEquivalence renaming (refl to ⇔-refl)

⊤⇔⊤ : ⊤ ⇔ ⊤
⊤⇔⊤ = mk⇔ (const tt) (const tt)

⊥⇔⊥ : ⊥ ⇔ ⊥
⊥⇔⊥ = mk⇔ (λ ()) λ ()

⊥⇎⊤ : ¬ (⊥ ⇔ ⊤)
⊥⇎⊤ = (_$ tt) ∘ Equivalence.from

⊤⇎⊥ : ¬ (⊤ ⇔ ⊥)
⊤⇎⊥ = (_$ tt) ∘ Equivalence.to
