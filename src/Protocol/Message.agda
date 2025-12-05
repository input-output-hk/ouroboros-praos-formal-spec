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

instance
  DecEq-Message : DecEq Message
  DecEq-Message ._≟_ (newBlock b) (newBlock b′)
    with b ≟ b′
  ... | no  b≢b′ = no λ m≡m′ → contradiction (cong projBlock m≡m′) b≢b′
  ... | yes b≡b′ = yes $ cong newBlock b≡b′
