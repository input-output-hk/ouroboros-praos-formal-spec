open import Protocol.Prelude using (Default)
open import Protocol.Params using (Params)
open import Protocol.Block using (Block)
open import Protocol.Crypto using (Hashable)

module Protocol.TreeType
  ⦃ _ : Params ⦄
  ⦃ _ : Block ⦄
  ⦃ _ : Hashable Block ⦄
  ⦃ _ : Default Block ⦄
  where

open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot)
open import Protocol.Block
open import Protocol.Chain

record TreeType (T : Type) : Type₁ where
  field
    tree₀      : T
    extendTree : T → Block → T
    allBlocks  : T → List Block
    bestChain  : Slot → T → Chain

    instantiated :
      allBlocks tree₀ ≡ [ genesisBlock ]

    extendable : ∀ (t : T) (b : Block) →
      allBlocks (extendTree t b) ≡ allBlocks t ++ [ b ]

    valid : ∀ (t : T) (sl : Slot) →
      validChain (bestChain sl t)

    optimal : ∀ (c : Chain) (t : T) (sl : Slot) →
        validChain c
      → c ⊆ filter (λ b → slot b ≤? sl) (allBlocks t)
      → length c ≤ length (bestChain sl t)

    selfContained : ∀ (t : T) (sl : Slot) →
      bestChain sl t ⊆ filter (λ b → slot b ≤? sl) (allBlocks t)

open TreeType ⦃ ... ⦄ public
