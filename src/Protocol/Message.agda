open import Protocol.Params using (Params)

module Protocol.Message
  ⦃ params : _ ⦄ (open Params params)
  where

open import Protocol.Prelude
open import Protocol.Block ⦃ params ⦄

data Message : Type where
  newBlock : Block → Message

projBlock : Message → Block
projBlock (newBlock b) = b
