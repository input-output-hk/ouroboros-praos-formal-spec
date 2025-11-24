open import Protocol.Prelude using (Default)
open import Protocol.Params using (Params)
open import Protocol.Crypto using (Hashable)
open import Protocol.Block using (Block)

module Protocol.Chain
  ⦃ params : _ ⦄ (open Params params)
  ⦃ _ : Hashable Block ⦄
  ⦃ _ : Default Block ⦄
  where

open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot)
open import Protocol.Block ⦃ params ⦄ hiding (Block)
open Hashable ⦃ ... ⦄
open import Data.List.Relation.Binary.Suffix.Heterogeneous using (Suffix)

genesisBlock : Block
genesisBlock = it .def

Chain : Type
Chain = List Block

tip : Chain → Block
tip []      = genesisBlock
tip (b ∷ _) = b

CorrectBlocks : Pred Chain _
CorrectBlocks = L.All.All CorrectBlock

prune : Slot → Chain → Chain
prune sl c = filter ((_≤? sl) ∘ slot) c

_⪯_ : Rel Chain _
_⪯_ = Suffix _≡_

_⟵_ : Rel Block _
b ⟵ b′ = prev b ≡ hash b′

-- NOTE: Very similar to Data.List.Relation.Unary.Linked. Also, perhaps we can use Data.List.Relation.Unary.AllPairs.
ProperlyLinked : Chain → Type
ProperlyLinked []            = ⊥
ProperlyLinked (b ∷ [])      = b ≡ genesisBlock
ProperlyLinked (b ∷ b′ ∷ bs) = b ⟵ b′ × ProperlyLinked (b′ ∷ bs)

-- NOTE: Similar to instantiating Data.List.Relation.Unary.Sorted.TotalOrder
-- with ≤-isTotalOrder from from Data.Nat.Properties, but in our case we need
-- < instead of ≤.
open import Data.List.Relation.Unary.Linked
DecreasingSlots = Linked _>ˢ_

opaque
  _✓ : Pred Chain 0ℓ
  c ✓ = CorrectBlocks c × ProperlyLinked c × DecreasingSlots c

{-# TERMINATING #-}
-- TODO: Prove termination using `WellFounded`.
chainFromBlock : Block → List Block → Chain
chainFromBlock b bs =
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
              case chainFromBlock b′ (L.filterᵇ (not ∘ (_== b′)) bs) of
                λ where
                []          → []
                (b′′ ∷ bs′) → b ∷ b′′ ∷ bs′
{----
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

chainFromBlock : Block → List Block → Chain
chainFromBlock b bs = chainFromBlock′ (length bs) b bs
--------}
