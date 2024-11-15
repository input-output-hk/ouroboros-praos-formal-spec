open import Protocol.Params using (Params)
open import Protocol.Block using (Block)

module Protocol.Network
  ⦃ _ : Params ⦄
  ⦃ _ : Block ⦄
  where

open import Protocol.Prelude
open import Protocol.Message
open Params ⦃ ... ⦄

Delay : Type
Delay = Fin 3

pattern 𝟘 = 0F -- immediate
pattern 𝟙 = 1F -- delayed 1 round
pattern 𝟚 = 2F -- delayed 2 rounds

record Envelope : Type where
  constructor
    ⦅_,_,_⦆
  field
    msg : Message
    rcv : Party
    cd  : Delay

  isImmediate : Party → Type
  isImmediate p = (cd ≡ 𝟘) × (rcv ≡ p)

open Envelope ⦃ ... ⦄

decreaseDelay : Envelope → Envelope
decreaseDelay ev = record ev { cd = Fi.pred (ev .cd) }

DelayMap : Type
DelayMap = Party → Delay
