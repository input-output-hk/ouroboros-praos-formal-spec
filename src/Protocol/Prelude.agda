module Protocol.Prelude where

open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_) public
open import Relation.Binary.Construct.Composition using (_;_) public
module RTC where
  open import Relation.Binary.Construct.Closure.ReflexiveTransitive public
open RTC public using (Star; _◅◅_; foldl)
open import Relation.Binary.PropositionalEquality using (_≗_) public
open import Relation.Nullary.Decidable.Core using (does) public
open import Data.Fin.Patterns using (0F; 1F; 2F) public
open import Prelude.Init public
open import Prelude.DecEq public
open import Prelude.Decidable public
open Nat using (_≤?_) public
open import Prelude.AssocList public
open import Prelude.Default using (Default) public
open Default ⦃ ... ⦄ public
open import Prelude.LiteralSequences public
open import Prelude.Irrelevance using (cofirst?) public
open import Prelude.InferenceRules public

cong₄ : ∀ {a} {A B C D E : Set a} (f : A → B → C → D → E) {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄}
  → x₁ ≡ y₁
  → x₂ ≡ y₂
  → x₃ ≡ y₃
  → x₄ ≡ y₄
  → f x₁ x₂ x₃ x₄ ≡ f y₁ y₂ y₃ y₄
cong₄ f refl refl refl refl = refl

-- NOTE: The following is copied from Class.Decidable in agda-stdlib-classes.
¿_¿ᵇ : (P : Type ℓ) → ⦃ P ⁇ ⦄ → Bool
¿ P ¿ᵇ = ⌊ ¿ P ¿ ⌋

infix 0 ifᵈ_then_else_
ifᵈ_then_else_ : ∀ {X : Type ℓ} (P : Type ℓ′)
  → ⦃ P ⁇ ⦄ → ({_ : P} → X) → ({_ : ¬ P} → X) → X
ifᵈ P then t else f with ¿ P ¿
... | yes p = t {p}
... | no ¬p = f {¬p}
