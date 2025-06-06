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
open import Data.Sum.Base using () renaming (map₁ to ⊎-map₁; map₂ to ⊎-map₂) public
open import Data.Product.Base using (uncurry′) renaming (swap to ×-swap) public
open import Data.List.Base using (_ʳ++_) public
open L.SubL public using () renaming (_⊆_ to _⊑_)
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

¬-×-comm : ∀ {P Q : Type} → ¬ (P × Q) → ¬ (Q × P)
¬-×-comm ¬[p×q] q×p = ¬[p×q] $ ×-comm _ _ .Inverse.to q×p
  where
    open import Data.Product.Algebra using (×-comm)
    open import Function.Bundles using (Inverse)

¬-distrib-×-dec : ∀ {P Q : Type} → ⦃ P ⁇ ⦄ → ¬ (P × Q) → ¬ P ⊎ ¬ Q
¬-distrib-×-dec {P} ¬[p×q] with ¿ P ¿
... | yes p = inj₂ λ q → ¬[p×q] (p , q)
... | no ¬p = inj₁ ¬p

¬[p×q]×p⇒¬q : ∀ {P Q : Type} → ⦃ P ⁇ ⦄ → ¬ (P × Q) → P → ¬ Q
¬[p×q]×p⇒¬q ¬[p×q] p with ¬-distrib-×-dec ¬[p×q]
... | inj₁ ¬p = contradiction p ¬p
... | inj₂ ¬q = ¬q

¬[p×q]×q⇒¬p : ∀ {P Q : Type} → ⦃ Q ⁇ ⦄ → ¬ (P × Q) → Q → ¬ P
¬[p×q]×q⇒¬p = ¬[p×q]×p⇒¬q ∘ ¬-×-comm
