open import Protocol.Params using (Params)
open import Protocol.Block using (Block)

module Protocol.Message
  ⦃ _ : Params ⦄
  ⦃ _ : Block  ⦄  
  where

open import Protocol.Prelude

data Message : Type where
  newBlock : Block → Message
