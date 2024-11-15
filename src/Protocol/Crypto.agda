open import Protocol.Params

module Protocol.Crypto
  ⦃ _ : Params ⦄
  where

open import Protocol.Prelude

record Hashable (T : Type) : Type where
  field
    hash : T → Hash

open Hashable ⦃ ... ⦄ public
