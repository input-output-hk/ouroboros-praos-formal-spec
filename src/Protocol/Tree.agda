open import Protocol.Prelude using (Default)
open import Protocol.Params using (Params)
open import Protocol.Crypto using (Hashable)
open import Protocol.Block using (Block)

module Protocol.Tree
  ⦃ params : _ ⦄ (open Params params)
  ⦃ _ : Hashable Block ⦄
  ⦃ _ : Default Block ⦄
  where

open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot)
open import Protocol.Block ⦃ params ⦄ hiding (Block)
open import Protocol.Chain ⦃ params ⦄
open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_)

∣_∣ : List Block → ℕ
∣_∣ = length

record Tree (T : Type) : Type₁ where
  field
    tree₀      : T
    extendTree : T → Block → T
    allBlocks  : T → List Block
    bestChain  : Slot → T → Chain

    instantiated :
      allBlocks tree₀ ≡ [ genesisBlock ]

    extendable : ∀ (t : T) (b : Block) →
      allBlocks (extendTree t b) ≡ˢ allBlocks t ++ [ b ]

    valid : ∀ (t : T) (sl : Slot) →
      bestChain sl t ✓

    optimal : ∀ (c : Chain) (t : T) (sl : Slot) →
        c ✓
      → c ⊆ˢ filter ((_≤? sl) ∘ slot) (allBlocks t)
      → ∣ c ∣ ≤ ∣ bestChain sl t ∣

    selfContained : ∀ (t : T) (sl : Slot) →
      bestChain sl t ⊆ˢ filter ((_≤? sl) ∘ slot) (allBlocks t)

open Tree ⦃ ... ⦄ public
