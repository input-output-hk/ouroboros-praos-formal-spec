module Protocol.Prelude where

open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_) public
open import Relation.Binary.Construct.Composition using (_;_) public
module RTC where
  open import Relation.Binary.Construct.Closure.ReflexiveTransitive public
open RTC public using (Star; _◅◅_; foldl)
open import Relation.Binary.PropositionalEquality using (_≗_; trans; subst₂) public
open import Relation.Nullary.Decidable.Core using (does) public
open import Data.Fin.Patterns using (0F; 1F; 2F) public
open import Prelude.Init public
open import Prelude.DecEq public
open import Prelude.Decidable public
open import Prelude.Irrelevance public
open Nat using (_≤?_; _<?_) public
open import Prelude.AssocList public
open import Prelude.Default using (Default) public
open Default ⦃ ... ⦄ public
open import Prelude.LiteralSequences public
open import Prelude.Irrelevance using (cofirst?) public
open import Prelude.InferenceRules public
open import Prelude.STS public
open import Prelude.STS.Ext renaming (map to STS-map) public

-- NOTE: The following is copied from Class.Decidable in agda-stdlib-classes.
¿_¿ᵇ : (P : Type ℓ) → ⦃ P ⁇ ⦄ → Bool
¿ P ¿ᵇ = ⌊ ¿ P ¿ ⌋

infix 0 ifᵈ_then_else_
ifᵈ_then_else_ : ∀ {X : Type ℓ} (P : Type ℓ′)
  → ⦃ P ⁇ ⦄ → ({_ : P} → X) → ({_ : ¬ P} → X) → X
ifᵈ P then t else f with ¿ P ¿
... | yes p = t {p}
... | no ¬p = f {¬p}

dec-de-morgan₂ : ∀ {P Q : Type} → ⦃ P ⁇ ⦄ → ¬ P ⊎ ¬ Q → ¬ (P × Q)
dec-de-morgan₂ (inj₁ ¬p) (p , _) = ¬p p
dec-de-morgan₂ (inj₂ ¬q) (_ , q) = ¬q q
