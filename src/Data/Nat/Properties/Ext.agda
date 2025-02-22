module Data.Nat.Properties.Ext where

open import Data.Nat.Base
open import Data.Nat.Properties using (≤-reflexive; suc-pred)

pred[n]<n : ∀ {n} .{{_ : NonZero n}} → pred n < n
pred[n]<n {n} = ≤-reflexive (suc-pred n)
