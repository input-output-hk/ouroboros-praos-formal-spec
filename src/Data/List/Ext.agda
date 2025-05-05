module Data.List.Ext where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)

-- The list of the `m` consecutive natural numbers starting from `n`
ι : ℕ → ℕ → List ℕ
ι n 0       = []
ι n (suc m) = n ∷ ι (suc n) m
--ι n m = map (_+ n) $ upTo m
