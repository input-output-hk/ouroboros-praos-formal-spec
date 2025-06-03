module Data.List.Ext where

open import Class.DecEq using (DecEq)
open DecEq ⦃...⦄
open import Function.Base using (_∘_)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Unary using (Pred; Decidable)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; length; filter)

-- The list of the `m` consecutive natural numbers starting from `n`
ι : ℕ → ℕ → List ℕ
ι n 0       = []
ι n (suc m) = n ∷ ι (suc n) m
--ι n m = map (_+ n) $ upTo m

opaque

  count : ∀ {a p} {A : Set a} {P : Pred A p} → Decidable P → List A → ℕ
  count P? = length ∘ (filter P?)

module _ {a} {A : Set a} ⦃ _ : DecEq A ⦄ where

  open import Data.List.Membership.DecPropositional (_≟_ {A = A}) using (_∈?_)

--
-- Like deduplicate _≟_ but keeps the last occurrence instead of the first, e.g.
--   deduplicate (1 ∷ 2 ∷ 1 ∷ []) == 1 ∷ 2 ∷ []
-- whereas
--   undup (1 ∷ 2 ∷ 1 ∷ []) == 2 ∷ 1 ∷ []
--
  undup : List A → List A
  undup [] = []
  undup (x ∷ xs) with x ∈? xs
  ... | yes _ = undup xs
  ... | no _  = x ∷ undup xs
