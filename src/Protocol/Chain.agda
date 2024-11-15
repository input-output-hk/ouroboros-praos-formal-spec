open import Protocol.Prelude using (Default)
open import Protocol.Params using (Params)
open import Protocol.Block using (Block)
open import Protocol.Crypto using (Hashable)

module Protocol.Chain
  ⦃ _ : Params ⦄
  ⦃ _ : Block ⦄
  ⦃ _ : Hashable Block ⦄
  ⦃ _ : Default Block ⦄
  where

open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot)
open import Protocol.Block
open Hashable ⦃ ... ⦄

genesisBlock : Block
genesisBlock = it .def

Chain : Type
Chain = List Block

tip : Chain → Block
tip []      = genesisBlock
tip (b ∷ _) = b

correctBlocks : Chain → Type
correctBlocks = All correctBlock
  where
    open L.All using (All)

prune : Slot → Chain → Chain
prune sl c = filter ((_≤? sl) ∘ slot) c

_⪯_ : Chain → Chain → Type
c₁ ⪯ c₂ = ∃[ c₃ ] c₁ ++ c₃ ≡ c₂

linked : Block → Block → Type
linked b b′ = prev b ≡ hash b′

-- NOTE: Very similar to Data.List.Relation.Unary.Linked
properlyLinked : Chain → Type
properlyLinked []            = ⊥
properlyLinked (b ∷ [])      = b ≡ genesisBlock
properlyLinked (b ∷ b′ ∷ bs) = linked b b′ × properlyLinked bs

-- NOTE: Similar to instantiating Data.List.Relation.Unary.Sorted.TotalOrder
-- with ≤-isTotalOrder from from Data.Nat.Properties, but in our case we need
-- < instead of ≤.
decreasingSlots : Chain → Type
decreasingSlots []            = ⊤
decreasingSlots (b ∷ [])      = ⊤
decreasingSlots (b ∷ b′ ∷ bs) = b′ .slot < b .slot × decreasingSlots bs

validChain : Chain → Type
validChain c = correctBlocks c × properlyLinked c × decreasingSlots c

chainFromBlock : Block → List Block → Chain
chainFromBlock b bs = chainFromBlock′ (length bs) b bs
  where
    chainFromBlock′ : ℕ → Block → List Block → Chain
    chainFromBlock′ 0       _ _  = []
    chainFromBlock′ (suc n) b bs =
      if b == genesisBlock
        then
          [ b ]
        else
          if (b .prev == hash genesisBlock)
            then
              [ b ⨾ genesisBlock ]
            else
              case L.findᵇ ((b .prev ==_) ∘ hash) bs of λ where
                nothing   → []
                (just b′) →
                  case chainFromBlock′ n b′ (L.filterᵇ (not ∘ (_== b′)) bs) of
                    λ where
                    []          → []
                    (b′′ ∷ bs′) → b ∷ b′′ ∷ bs′
