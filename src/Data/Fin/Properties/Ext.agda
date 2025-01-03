module Data.Fin.Properties.Ext where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (refl; _≢_; cong)
open import Relation.Nullary.Negation using (contradiction)

suc-≢-injective : ∀ {n : ℕ} {i j : Fin n} → suc i ≢ suc j → i ≢ j
suc-≢-injective {i = zero} {j = zero} p = contradiction refl p
suc-≢-injective {_} {_} p = λ q → contradiction (cong suc q) p
