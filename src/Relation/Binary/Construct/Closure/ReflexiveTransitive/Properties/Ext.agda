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

module _ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} where

  private variable i j k : I

  Star⇒≡⊎∃ : Star T i k → i ≡ k ⊎ (∃[ j ] Star T i j × T j k)
  Star⇒≡⊎∃ ε = inj₁ refl
  Star⇒≡⊎∃ {i = i} (iTj ◅ jT⋆k) with Star⇒≡⊎∃ jT⋆k
  ... | inj₁ j≡k                 = inj₂ (i , ε , subst _ j≡k iTj)
  ... | inj₂ (k′ , jT⋆k′ , k′Tk) = inj₂ (k′ , iTj ◅ jT⋆k′ , k′Tk)

  Star⇒Starᵈ : Star T ⇒ Starᵈ T
  Star⇒Starᵈ ε            = εᵈ
  Star⇒Starᵈ (iTj ◅ jT⋆k) = ⟨ iTj ⟩ᵈ ◅ᵈ Star⇒Starᵈ jT⋆k

  Starᵈ⇒Star : Starᵈ T ⇒ Star T
  Starᵈ⇒Star ⟨ iTj ⟩ᵈ       = iTj ◅ ε
  Starᵈ⇒Star εᵈ             = ε
  Starᵈ⇒Star (iT⋆j ◅ᵈ jT⋆k) = Starᵈ⇒Star iT⋆j ◅◅ Starᵈ⇒Star jT⋆k

  Starᵈ⇔Star : Starᵈ T ⇔ Star T
  Starᵈ⇔Star = Starᵈ⇒Star , Star⇒Starᵈ

  Starʳ⇒Starᵈ : Starʳ T ⇒ Starᵈ T
  Starʳ⇒Starᵈ εʳ            = εᵈ
  Starʳ⇒Starᵈ (iT⋆j ◅ʳ jTk) = Starʳ⇒Starᵈ iT⋆j ◅ᵈ ⟨ jTk ⟩ᵈ

  Starᵈ⇒Starʳ : Starᵈ T ⇒ Starʳ T
  Starᵈ⇒Starʳ ⟨ iTk ⟩ᵈ       = εʳ ◅ʳ iTk
  Starᵈ⇒Starʳ εᵈ             = εʳ
  Starᵈ⇒Starʳ (iT⋆j ◅ᵈ jT⋆k) = Starᵈ⇒Starʳ iT⋆j ◅◅ʳ Starᵈ⇒Starʳ jT⋆k

  Starᵈ⇔Starʳ : Starᵈ T ⇔ Starʳ T
  Starᵈ⇔Starʳ = Starᵈ⇒Starʳ , Starʳ⇒Starᵈ

  Star⇒Starʳ : Star T ⇒ Starʳ T
  Star⇒Starʳ {x = x} {y = y} = proj₁ Starᵈ⇔Starʳ {x} {y} ∘ proj₂ Starᵈ⇔Star {x} {y}

  Starʳ⇒Star : Starʳ T ⇒ Star T
  Starʳ⇒Star {x = x} {y = y} = proj₁ Starᵈ⇔Star {x} {y} ∘ proj₂ Starᵈ⇔Starʳ {x} {y}

  Star⇔Starʳ : Star T ⇔ Starʳ T
  Star⇔Starʳ = Star⇒Starʳ , Starʳ⇒Star

  infixr 2 _▻′_ _▻ʳ_
  _▻′_ : Star T i j → T j k → Star T i k
  ε         ▻′ ij = ij ◅ ε
  (il ◅ lj) ▻′ jk = il ◅ (lj ▻′ jk)

  _▻ʳ_ : T i j → Starʳ T j k → Starʳ T i k
  ij ▻ʳ εʳ         = εʳ         ◅ʳ ij
  ij ▻ʳ (jl ◅ʳ lk) = (ij ▻ʳ jl) ◅ʳ lk

  Star⇒Starʳ′ : Star T ⇒ Starʳ T
  Star⇒Starʳ′ ε         = εʳ
  Star⇒Starʳ′ (ik ◅ kj) = ik ▻ʳ Star⇒Starʳ′ kj

  Starʳ⇒Star′ : Starʳ T ⇒ Star T
  Starʳ⇒Star′ εʳ         = ε
  Starʳ⇒Star′ (ik ◅ʳ kj) = Starʳ⇒Star′ ik ▻′ kj

  Star⇒Starʳ-▻ : ∀ (ik : Star T i k) (kj : T k j) → Star⇒Starʳ′ (ik ▻′ kj) ≡ Star⇒Starʳ′ ik ◅ʳ kj
  Star⇒Starʳ-▻ ε         kj                            = refl
  Star⇒Starʳ-▻ (il ◅ lk) kj rewrite Star⇒Starʳ-▻ lk kj = refl

  Starʳ⇒Star-▻ʳ : ∀ (ik : T i k) (kj : Starʳ T k j) → Starʳ⇒Star′ (ik ▻ʳ kj) ≡ ik ◅ Starʳ⇒Star′ kj
  Starʳ⇒Star-▻ʳ ik εʳ                                     = refl
  Starʳ⇒Star-▻ʳ ik (kl ◅ʳ lj) rewrite Starʳ⇒Star-▻ʳ ik kl = refl

  Star⇒Starʳ-Starʳ⇒Star : ∀ (ij : Starʳ T i j) → Star⇒Starʳ′ (Starʳ⇒Star′ ij) ≡ ij
  Star⇒Starʳ-Starʳ⇒Star εʳ = refl
  Star⇒Starʳ-Starʳ⇒Star (ik ◅ʳ kj) rewrite Star⇒Starʳ-▻ (Starʳ⇒Star′ ik) kj | Star⇒Starʳ-Starʳ⇒Star ik = refl

  Starʳ⇒Star-Star⇒Starʳ : ∀ (ij : Star T i j) → Starʳ⇒Star′ (Star⇒Starʳ′ ij) ≡ ij
  Starʳ⇒Star-Star⇒Starʳ ε = refl
  Starʳ⇒Star-Star⇒Starʳ (ik ◅ kj) rewrite Starʳ⇒Star-▻ʳ ik (Star⇒Starʳ′ kj) | Starʳ⇒Star-Star⇒Starʳ kj = refl
