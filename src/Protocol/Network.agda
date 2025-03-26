open import Protocol.Params using (Params)

module Protocol.Network
  ⦃ params : _ ⦄ (open Params params)
  where

open import Protocol.Prelude
open import Protocol.Message ⦃ params ⦄

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

  DeliveredIn : Party → Delay → Type
  DeliveredIn p d = (cd ≡ d) × (rcv ≡ p)

  Immediate : Pred Party 0ℓ
  Immediate = flip DeliveredIn 𝟘

open Envelope ⦃ ... ⦄

decreaseDelay : Envelope → Envelope
decreaseDelay ev = record ev { cd = Fi.pred (ev .cd) }

DelayMap : Type
DelayMap = Party → Delay
