open import Protocol.Params using (Params)

module Protocol.Crypto
  ⦃ _ : Params ⦄
  where

open import Protocol.Prelude
open import Protocol.Params using (Hash)

record Hashable (T : Type) : Type where
  field
    hash : T → Hash

open Hashable ⦃ ... ⦄ public
