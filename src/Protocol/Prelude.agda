module Protocol.Prelude where

open import Data.Product using (∃₂) public
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_) public
open import Relation.Binary.Construct.Composition using (_;_) public
module RTC where
  open import Relation.Binary.Construct.Closure.ReflexiveTransitive public
open RTC public using (Star; _◅◅_; foldl)
open import Relation.Binary.PropositionalEquality using (_≗_; trans; subst₂) public
open import Relation.Nullary.Decidable.Core using (does) public
open import Data.Fin.Patterns using (0F; 1F; 2F) public
open import Prelude.Init public
open import Class.DecEq public
open import Class.Decidable public
open import Prelude.Irrelevance public
open Nat using (_≤?_; _<?_) public
open import Prelude.AssocList public
open import Class.Default using (Default) public
open Default ⦃ ... ⦄ public
open import Prelude.LiteralSequences public
open import Prelude.Irrelevance using (cofirst?) public
open import Prelude.InferenceRules public
open import Prelude.STS public

dec-de-morgan₂ : ∀ {P Q : Type} → ⦃ P ⁇ ⦄ → ¬ P ⊎ ¬ Q → ¬ (P × Q)
dec-de-morgan₂ (inj₁ ¬p) (p , _) = ¬p p
dec-de-morgan₂ (inj₂ ¬q) (_ , q) = ¬q q
