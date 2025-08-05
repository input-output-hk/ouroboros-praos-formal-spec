{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled

open import Protocol.Prelude using (Default)
open import Protocol.Params using (Params)
open import Protocol.Crypto using (Hashable)
open import Protocol.Block using (Block)

module Protocol.TreeType
  ⦃ params : _ ⦄ (open Params params)
  ⦃ _ : Hashable Block ⦄
  ⦃ _ : Default Block ⦄
  where

open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_; ⊆×⊇⇒≡ˢ; ≡⇒≡ˢ; Any-resp-≡ˢ; ≡ˢ-refl)
open import Data.List.Relation.Binary.BagAndSetEquality using (++-cong; ↭⇒∼bag; bag-=⇒)
open import Function.Related.Propositional as Related
open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot)
open import Protocol.Block ⦃ params ⦄ hiding (Block)
open import Protocol.Chain ⦃ params ⦄

∣_∣ : List Block → ℕ
∣_∣ = length

record TreeType (T : Type) : Type₁ where
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

  buildTree : List Block → T
  buildTree = L.foldr (flip extendTree) tree₀

  buildTreeUsesAllBlocks : ∀ (bs : List Block) → allBlocks (buildTree bs) ≡ˢ genesisBlock ∷ bs
  buildTreeUsesAllBlocks [] = ≡⇒≡ˢ instantiated
  buildTreeUsesAllBlocks (b ∷ bs) {b′} = begin
    b′ ∈ allBlocks (buildTree (b ∷ bs))          ≡⟨⟩
    b′ ∈ allBlocks (extendTree (buildTree bs) b) ∼⟨ extendable _ _ ⟩
    b′ ∈ allBlocks (buildTree bs) ++ [ b ]       ∼⟨ ++-cong (buildTreeUsesAllBlocks bs) ≡ˢ-refl ⟩
    b′ ∈ genesisBlock ∷ bs ++ [ b ]              ∼⟨ bag-=⇒ (↭⇒∼bag g∷bs∷b↭g∷b∷bs) ⟩
    b′ ∈ genesisBlock ∷ b ∷ bs
   ∎
    where
      open Related.EquationalReasoning
      open import Data.List.Relation.Binary.Permutation.Propositional using (prep; ↭-sym)
      open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∷↭∷ʳ)
      g∷bs∷b↭g∷b∷bs : genesisBlock ∷ bs ++ [ b ] ↭ genesisBlock ∷ b ∷ bs
      g∷bs∷b↭g∷b∷bs = prep _ (↭-sym $ ∷↭∷ʳ _ _)

  bestChainSlotBounded : ∀ (t : T) (sl : Slot) → L.All.All ((_≤ sl) ∘ slot) (bestChain sl t)
  bestChainSlotBounded t sl = L.All.tabulate $
    λ {b} b∈best → L.Mem.∈-filter⁻ _ {xs = allBlocks t} (selfContained t sl b∈best) .proj₂

  allBlocksBuildTree-++ : ∀ (bs bs′ : List Block) → allBlocks (buildTree (bs ++ bs′)) ≡ˢ allBlocks (buildTree bs) ++ allBlocks (buildTree bs′)
  allBlocksBuildTree-++ = {!!}

  genesisBlockInAllBlocks : ∀ (t : T) → genesisBlock ∈ allBlocks t
  genesisBlockInAllBlocks = {!!}

open TreeType ⦃ ... ⦄ public
