module Prelude.STS.Ext where

open import Prelude.Init
open import Prelude.InferenceRules
open import Prelude.STS

private variable Γ S I : Type

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

-- Specializations for no environment.
⊢_—[_]→_ : ⦃ HasTransition ⊤ S I ⦄ → STS ⊤ S I
⊢_—[_]→_ = _⊢_—[_]→_

⊢_—[_]→∗_ : ⦃ HasTransition ⊤ S I ⦄ → STS ⊤ S (List I)
⊢_—[_]→∗_ = _⊢_—[_]→∗_

⊢_—[_]→∗ʳ_ : ⦃ HasTransition ⊤ S I ⦄ → STS ⊤ S (List I)
⊢_—[_]→∗ʳ_ = _⊢_—[_]→∗ʳ_
