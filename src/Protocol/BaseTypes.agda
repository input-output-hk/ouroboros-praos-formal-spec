module Protocol.BaseTypes where

open import Protocol.Prelude

-- Slots

Slot : Type
Slot = ℕ

slot₀ : Slot
slot₀ = 1

-- Party honesty

data Honesty : Type where
  honest corrupt : Honesty

instance
  DecEq-Honesty : DecEq Honesty
  DecEq-Honesty ._≟_ honest  honest  = yes refl
  DecEq-Honesty ._≟_ corrupt corrupt = yes refl
  DecEq-Honesty ._≟_ honest  corrupt = no λ()
  DecEq-Honesty ._≟_ corrupt honest  = no λ()
