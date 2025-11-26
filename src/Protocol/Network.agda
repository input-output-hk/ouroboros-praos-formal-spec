open import Protocol.Params using (Params)

module Protocol.Network
  ⦃ params : _ ⦄ (open Params params)
  where

open import Protocol.Prelude
open import Protocol.Message ⦃ params ⦄

Delay : Type
Delay = Fin 3

pattern 𝟘 = 0F -- to be delivered at round t
pattern 𝟙 = 1F -- to be delivered at round t + 1
pattern 𝟚 = 2F -- to be delivered at round t + 2

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

open Envelope

open import Function.Nary.NonDependent using (congₙ)

instance
  DecEq-Envelope : DecEq Envelope
  DecEq-Envelope ._≟_ e e′
    with e .msg ≟ e′ .msg | e .rcv ≟ e′ .rcv | e .cd ≟ e′ .cd
  ... | yes msg≡ | yes rcv≡ | yes cd≡ = yes $ congₙ 3 ⦅_,_,_⦆ msg≡ rcv≡ cd≡
  ... | no ¬msg≡ | _        | _       = no λ e≡e′ → contradiction (cong msg e≡e′) ¬msg≡
  ... | _        | no ¬rcv≡ | _       = no λ e≡e′ → contradiction (cong rcv e≡e′) ¬rcv≡
  ... | _        | _        | no ¬cd≡ = no λ e≡e′ → contradiction (cong cd  e≡e′) ¬cd≡

decreaseDelay : Envelope → Envelope
decreaseDelay ev = record ev { cd = Fi.pred (ev .cd) }

DelayMap : Type
DelayMap = Party → [ d ∈ Delay ∣ d Fi.> (Delay ∋ 𝟘) ]
