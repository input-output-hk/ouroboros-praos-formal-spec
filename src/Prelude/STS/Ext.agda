-- TODO: Remove this as everything here is already available in iog-prelude.

module Prelude.STS.Ext where

open import Prelude.Init hiding (map)
open import Prelude.InferenceRules
open import Prelude.STS
open import Relation.Binary.Definitions using (Trans; Reflexive)
open import Relation.Binary.Core using (_⇒_)

private variable Γ S I : Type

-- *Reverse* reflexive transitive closure of a state transition system.
module _ {Γ S I : Type} (_⊢_—[_]→_ : STS Γ S I) where mutual

  private variable
    γ : Γ
    s s′ s″ : S
    i : I
    is is′ : List I

  private
    _⊢_—[_]→∗ʳ_ : STS Γ S (List I)
    _⊢_—[_]→∗ʳ_ = _∗ʳ

  data _∗ʳ : STS Γ S (List I) where
    [] :
       ─────────────────
       γ ⊢ s —[ [] ]→∗ʳ s

    _∷ʳ_ : ∀ { eq : is′ ≡ is L.∷ʳ i } →
      ∙ γ ⊢ s —[ is ]→∗ʳ s′
      ∙ γ ⊢ s′ —[ i ]→ s″
        ───────────────────────
        γ ⊢ s —[ is′ ]→∗ʳ s″

_⊢_—[_]→∗ʳ_ : ⦃ HasTransition Γ S I ⦄ → STS Γ S (List I)
_⊢_—[_]→∗ʳ_ = _⊢_—[_]→_ ∗ʳ

module _ ⦃ _ : HasTransition Γ S I ⦄ where

  -- The type of `fold` establishes an induction rule for STS's,
  -- namely, if a relation holds both for no steps and for a single
  -- step, then it holds for arbitrarily many steps using the
  -- reflexive-transitive closure relation.
  fold : ∀ {ℓ} {γ : Γ} (P : List I → Rel S ℓ) →
    (∀ {i is} → Trans (γ ⊢_—[ i ]→_) (P is) (P (i ∷ is))) →
    Reflexive (P []) →
    (∀ {is} → γ ⊢_—[ is ]→∗_ ⇒ P is)
  fold P _⊕_ ∅ []         = ∅
  fold P _⊕_ ∅ (ts ∷ ts∗) = ts ⊕ fold P _⊕_ ∅ ts∗

module _ ⦃ ht₁ : HasTransition Γ S I ⦄ ⦃ ht₂ : HasTransition Γ S I ⦄ where

  open HasTransition ht₁ renaming (_⊢_—[_]→_ to _⊢_—[_]¹→_; _⊢_—[_]→∗_ to _⊢_—[_]¹→∗_)
  open HasTransition ht₂ renaming (_⊢_—[_]→_ to _⊢_—[_]²→_; _⊢_—[_]→∗_ to _⊢_—[_]²→∗_)

  map : ∀ {γ : Γ} →
    (∀ {i}  → _⊢_—[ i  ]¹→_  γ ⇒ _⊢_—[ i  ]²→_  γ) →
    (∀ {is} → _⊢_—[ is ]¹→∗_ γ ⇒ _⊢_—[ is ]²→∗_ γ)
  map f [] = []
  map f (ts ∷ ts∗) = f ts ∷ map f ts∗

-- Specializations for no environment.
⊢_—[_]→_ : ⦃ HasTransition ⊤ S I ⦄ → STS ⊤ S I
⊢_—[_]→_ = _⊢_—[_]→_

⊢_—[_]→∗_ : ⦃ HasTransition ⊤ S I ⦄ → STS ⊤ S (List I)
⊢_—[_]→∗_ = _⊢_—[_]→∗_

⊢_—[_]→∗ʳ_ : ⦃ HasTransition ⊤ S I ⦄ → STS ⊤ S (List I)
⊢_—[_]→∗ʳ_ = _⊢_—[_]→∗ʳ_
