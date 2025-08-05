module Data.Sum.Algebra.Ext where

open import Level
open import Function.Base using (_$_; flip)
open import Relation.Nullary.Indexed renaming (¬ to ¬ⁱ)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; map₁)
open import Data.Sum.Algebra using (⊎-identityˡ)
open import Data.Product.Base using (_×_; _,_)

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Set ℓ
  B : Set ℓ′
  C : Set ℓ″

[B⊎C]×A⇒[AxB]⊎C : B ⊎ C → A → (A × B) ⊎ C
[B⊎C]×A⇒[AxB]⊎C (inj₁ b) a = inj₁ (a , b)
[B⊎C]×A⇒[AxB]⊎C (inj₂ c) a = inj₂ c

[A⊎B]×¬ⁱA⇒B : A ⊎ B → ¬ⁱ _ A → B
[A⊎B]×¬ⁱA⇒B a⊎b ¬a = ⊎-identityˡ _ _ .Inverse.to $ map₁ ¬a a⊎b
  where open import Function.Bundles

[A⊎B]×¬A⇒B : A ⊎ B → ¬ A → B
[A⊎B]×¬A⇒B (inj₁ a)   = contradiction a
[A⊎B]×¬A⇒B (inj₂ b) _ = b

¬A⊎B⇒A→B : ¬ A ⊎ B → A → B
¬A⊎B⇒A→B (inj₁ ¬a)   = flip contradiction ¬a
¬A⊎B⇒A→B (inj₂  b) _ = b
