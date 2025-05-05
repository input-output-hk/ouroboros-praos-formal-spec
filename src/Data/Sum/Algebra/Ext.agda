module Data.Sum.Algebra.Ext where

open import Level
open import Function.Base using (_$_)
open import Relation.Nullary.Indexed renaming (¬ to ¬ⁱ)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; map₁)
open import Data.Sum.Algebra using (⊎-identityˡ)
open import Data.Product.Base using (_×_; _,_)

[B⊎C]×A⇒[AxB]⊎C : ∀ {ℓ ℓ′ ℓ″} {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″} → B ⊎ C → A → (A × B) ⊎ C
[B⊎C]×A⇒[AxB]⊎C (inj₁ b) a = inj₁ (a , b)
[B⊎C]×A⇒[AxB]⊎C (inj₂ c) a = inj₂ c

[A⊎B]×¬ⁱA⇒B : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} → A ⊎ B → ¬ⁱ ℓ′ A → B
[A⊎B]×¬ⁱA⇒B a⊎b ¬a = ⊎-identityˡ _ _ .Inverse.to $ map₁ ¬a a⊎b
  where open import Function.Bundles

[A⊎B]×¬A⇒B : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} → A ⊎ B → ¬ A → B
[A⊎B]×¬A⇒B (inj₁ a) ¬a = contradiction a ¬a
[A⊎B]×¬A⇒B (inj₂ b) ¬a = b
