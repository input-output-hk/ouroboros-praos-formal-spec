module Relation.Binary.PropositionalEquality.Properties.Ext where

open import Data.Bool using (false; true)
open import Data.Bool.Properties using (¬-not; not-¬)
open import Function.Base using (_∘_)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Class.DecEq using (DecEq)
open DecEq ⦃...⦄
open import Prelude.DecEq.Properties.Ext using (==-refl)

≡×≢⇒≢ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≢ z → x ≢ z
≡×≢⇒≢ p q = subst _ (sym p) q

==⇔≡ : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {x y : A} → (x == y) ≡ true ⇔ x ≡ y
==⇔≡ = mk⇔ to from
  where
    to : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {x y : A} → (x == y) ≡ true → x ≡ y
    to {x = x} {y = y} x==y with x ≟ y
    ... | yes x≡y = x≡y
    ... | no x≢y = contradiction x==y λ ()

    from : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {x y : A} → x ≡ y → (x == y) ≡ true
    from refl = ==-refl

=/=⇔≢ : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {x y : A} → (x == y) ≡ false ⇔ x ≢ y
=/=⇔≢ = mk⇔ to from
  where
    to : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {x y : A} → (x == y) ≡ false → x ≢ y
    to = contraposition (Equivalence.from ==⇔≡) ∘ not-¬

    from : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {x y : A} → x ≢ y → (x == y) ≡ false
    from = ¬-not ∘ contraposition (Equivalence.to ==⇔≡)
