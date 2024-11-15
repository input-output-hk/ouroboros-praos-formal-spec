module Protocol.Params where

open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot)

record Params : Type₁ where
  field
    numParties : ℕ

  Party : Type
  Party = Fin numParties

  field
    Txs    : Type
    Hash   : Type
    winner : Party → Slot → Type

    ⦃ DecEq-Txs   ⦄ : DecEq Txs
    ⦃ DecEq-Hash  ⦄ : DecEq Hash
    ⦃ winnerᵈ     ⦄ : winner ⁇²

open Params ⦃ ... ⦄ public
