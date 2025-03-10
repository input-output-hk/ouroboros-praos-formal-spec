module Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.Ext where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; _,_; ∃-syntax)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary using (_⇒_; _⇔_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; _◅◅_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Ext
open Star

Star⇒≡⊎∃ : ∀ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} {i k} → Star T i k → i ≡ k ⊎ (∃[ j ] Star T i j × T j k)
Star⇒≡⊎∃ ε = inj₁ refl
Star⇒≡⊎∃ {i = i} (iTj ◅ jT⋆k) with Star⇒≡⊎∃ jT⋆k
... | inj₁ j≡k                 = inj₂ (i , ε , subst _ j≡k iTj)
... | inj₂ (k′ , jT⋆k′ , k′Tk) = inj₂ (k′ , iTj ◅ jT⋆k′ , k′Tk)

Star⇒Starᵈ : ∀ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} → Star T ⇒ Starᵈ T
Star⇒Starᵈ ε            = εᵈ
Star⇒Starᵈ (iTj ◅ jT⋆k) = ⟨ iTj ⟩ᵈ ◅ᵈ Star⇒Starᵈ jT⋆k

Starᵈ⇒Star : ∀ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} → Starᵈ T ⇒ Star T
Starᵈ⇒Star ⟨ iTj ⟩ᵈ       = iTj ◅ ε
Starᵈ⇒Star εᵈ             = ε
Starᵈ⇒Star (iT⋆j ◅ᵈ jT⋆k) = Starᵈ⇒Star iT⋆j ◅◅ Starᵈ⇒Star jT⋆k

Starᵈ⇔Star : ∀ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} → Starᵈ T ⇔ Star T
Starᵈ⇔Star = Starᵈ⇒Star , Star⇒Starᵈ

Starʳ⇒Starᵈ : ∀ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} → Starʳ T ⇒ Starᵈ T
Starʳ⇒Starᵈ εʳ            = εᵈ
Starʳ⇒Starᵈ (iT⋆j ◅ʳ jTk) = Starʳ⇒Starᵈ iT⋆j ◅ᵈ ⟨ jTk ⟩ᵈ

Starᵈ⇒Starʳ : ∀ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} → Starᵈ T ⇒ Starʳ T
Starᵈ⇒Starʳ ⟨ iTk ⟩ᵈ       = εʳ ◅ʳ iTk
Starᵈ⇒Starʳ εᵈ             = εʳ
Starᵈ⇒Starʳ (iT⋆j ◅ᵈ jT⋆k) = Starᵈ⇒Starʳ iT⋆j ◅◅ʳ Starᵈ⇒Starʳ jT⋆k

Starᵈ⇔Starʳ : ∀ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} → Starᵈ T ⇔ Starʳ T
Starᵈ⇔Starʳ = Starᵈ⇒Starʳ , Starʳ⇒Starᵈ

Star⇒Starʳ : ∀ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} → Star T ⇒ Starʳ T
Star⇒Starʳ {x = x} {y = y} = proj₁ Starᵈ⇔Starʳ {x} {y} ∘ proj₂ Starᵈ⇔Star {x} {y}

Starʳ⇒Star : ∀ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} → Starʳ T ⇒ Star T
Starʳ⇒Star {x = x} {y = y} = proj₁ Starᵈ⇔Star {x} {y} ∘ proj₂ Starᵈ⇔Starʳ {x} {y}

Star⇔Starʳ : ∀ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} → Star T ⇔ Starʳ T
Star⇔Starʳ = Star⇒Starʳ , Starʳ⇒Star
