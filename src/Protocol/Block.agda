open import Protocol.Params using (Params)
open import Protocol.Params using (Params)

module Protocol.Block
  ⦃ _ : Params ⦄
  where

open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot)
open import Protocol.Params using (Hash; Txs; Party; winner)
open import Data.Nat.Properties using (≤-trans; n≤1+n)

record Block : Type where
  constructor mkBlock
  field
    prev : Hash
    slot : Slot
    txs  : Txs
    pid  : Party

  CorrectBlock : Type
  CorrectBlock = winner pid slot

open Block public

_>ˢ_ : Rel Block _
_>ˢ_ = _>_ on slot

>ˢ-trans : Transitive _>ˢ_
>ˢ-trans {_} {b′} {_} b>ˢb′ b′>ˢb″ = ≤-trans (≤-trans b′>ˢb″ (n≤1+n (b′ .slot))) b>ˢb′

open import Function.Nary.NonDependent using (congₙ)

instance  
  DecEq-Block : DecEq Block
  DecEq-Block ._≟_ b b′
    with b .prev ≟ b′ .prev | b .slot ≟ b′ .slot | b .txs ≟ b′ .txs | b .pid ≟ b′ .pid
  ... | yes prev≡ | yes slot≡ | yes txs≡ | yes pid≡ = yes (congₙ 4 mkBlock prev≡ slot≡ txs≡ pid≡)
  ... | no ¬prev≡ | _         | _        | _        = no λ b≢b′ → contradiction (cong prev b≢b′) ¬prev≡
  ... | _         | no ¬slot≡ | _        | _        = no λ b≢b′ → contradiction (cong slot b≢b′) ¬slot≡
  ... | _         | _         | no ¬txs≡ | _        = no λ b≢b′ → contradiction (cong txs  b≢b′) ¬txs≡
  ... | _         | _         | _        | no ¬pid≡ = no λ b≢b′ → contradiction (cong pid  b≢b′) ¬pid≡

open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)

instance
  Block-≡-isDecEquivalence = isDecEquivalence {A = Block} _≟_
