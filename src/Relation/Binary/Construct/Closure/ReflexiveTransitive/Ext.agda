module Relation.Binary.Construct.Closure.ReflexiveTransitive.Ext where

open import Level using (_⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary using (_⇒_)
open import Relation.Binary.Definitions using (Reflexive; RightTrans; Transitive)

data Starᵈ {ℓ ℓ′} {I : Set ℓ} (T : Rel I ℓ′) : Rel I (ℓ ⊔ ℓ′) where
  ⟨_⟩ᵈ : T ⇒ Starᵈ T
  εᵈ   : Reflexive  (Starᵈ T)
  _◅ᵈ_ : Transitive (Starᵈ T)

data Starʳ {ℓ ℓ′} {I : Set ℓ} (T : Rel I ℓ′) : Rel I (ℓ ⊔ ℓ′) where
  εʳ   : Reflexive  (Starʳ T)
  _◅ʳ_ : RightTrans (Starʳ T) T

infixr 5 _◅◅ʳ_

_◅◅ʳ_ : ∀ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} → Transitive (Starʳ T)
xs ◅◅ʳ εʳ        = xs
xs ◅◅ʳ (ys ◅ʳ y) = (xs ◅◅ʳ ys) ◅ʳ y
