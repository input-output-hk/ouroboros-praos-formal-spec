module Data.Nat.Properties.Ext where

open import Function.Base using (_∘_)
open import Data.Nat.Base
open import Data.Nat.Properties using (≤-reflexive; suc-pred)
open import Relation.Binary.PropositionalEquality using (_≢_; cong)

pred[n]<n : ∀ {n} .{{_ : NonZero n}} → pred n < n
pred[n]<n {n} = ≤-reflexive (suc-pred n)

suc-≢-injective : ∀ {i j : ℕ} → suc i ≢ suc j → i ≢ j
suc-≢-injective = _∘ cong suc
