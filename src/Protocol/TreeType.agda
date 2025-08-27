open import Protocol.Prelude using (Default)
open import Protocol.Params using (Params)
open import Protocol.Crypto using (Hashable)
open import Protocol.Block using (Block)

module Protocol.TreeType
  ⦃ params : _ ⦄ (open Params params)
  ⦃ _ : Hashable Block ⦄
  ⦃ _ : Default Block ⦄
  where

open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_; ⊆×⊇⇒≡ˢ; ≡⇒≡ˢ; Any-resp-≡ˢ; ≡ˢ-refl; ≡ˢ-sym)
open import Data.List.Relation.Binary.BagAndSetEquality using (++-cong; ↭⇒∼bag; bag-=⇒)
open import Data.List.Relation.Binary.Permutation.Propositional using (prep; ↭-sym; module PermutationReasoning)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∷↭∷ʳ; ++⁺ˡ; ++-comm)
open import Function.Related.Propositional as Related
open import Function.Bundles using (mk⇔)
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
      g∷bs∷b↭g∷b∷bs : genesisBlock ∷ bs ++ [ b ] ↭ genesisBlock ∷ b ∷ bs
      g∷bs∷b↭g∷b∷bs = prep _ (↭-sym $ ∷↭∷ʳ _ _)

  bestChainSlotBounded : ∀ (t : T) (sl : Slot) → L.All.All ((_≤ sl) ∘ slot) (bestChain sl t)
  bestChainSlotBounded t sl = L.All.tabulate $
    λ {b} b∈best → L.Mem.∈-filter⁻ _ {xs = allBlocks t} (selfContained t sl b∈best) .proj₂

  genesisBlockInAllBlocks : ∀ (t : T) → genesisBlock ∈ allBlocks t
  genesisBlockInAllBlocks t = L.SubS.⊆-trans (selfContained t 0) (L.SubS.filter-⊆ _ _) $ gb∈bc
    where
      gb∈bc : genesisBlock ∈ bestChain 0 t
      gb∈bc with ✓⇒gbIsHead (valid t 0)
      ... | c , c+gb≡bc rewrite sym c+gb≡bc = L.Mem.∈-++⁺ʳ c (here refl)

  allBlocksBuildTree-++ : ∀ (bs bs′ : List Block) → allBlocks (buildTree (bs ++ bs′)) ≡ˢ allBlocks (buildTree bs) ++ allBlocks (buildTree bs′)
  allBlocksBuildTree-++ [] bs′ {b} = let open Related.EquationalReasoning in begin
    b ∈ allBlocks (buildTree bs′)                      ∼⟨ mk⇔
                                                           (L.SubS.xs⊆x∷xs _ _)
                                                           (L.SubS.∈-∷⁺ʳ (genesisBlockInAllBlocks _) L.SubS.⊆-refl) ⟩
    b ∈ [ genesisBlock ] ++ allBlocks (buildTree bs′)  ∼⟨ ++-cong (≡⇒≡ˢ $ sym instantiated) ≡ˢ-refl ⟩
    b ∈ allBlocks tree₀ ++ allBlocks (buildTree bs′)   ∎
  allBlocksBuildTree-++ (b ∷ bs) bs′ {b′} = let open Related.EquationalReasoning in begin
    b′ ∈ allBlocks (buildTree ((b ∷ bs) ++ bs′))                              ≡⟨⟩
    b′ ∈ allBlocks (extendTree (buildTree (bs ++ bs′)) b)                     ∼⟨ extendable _ _ ⟩
    b′ ∈ allBlocks (buildTree (bs ++ bs′)) ++ [ b ]                           ∼⟨ ++-cong
                                                                                   (allBlocksBuildTree-++ bs bs′) ≡ˢ-refl ⟩
    b′ ∈ (allBlocks (buildTree bs) ++ allBlocks (buildTree bs′)) ++ [ b ]     ∼⟨ bag-=⇒ $ ↭⇒∼bag $
                                                                                   lemma (allBlocks (buildTree bs)) _ _ ⟩
    b′ ∈ (allBlocks (buildTree bs) ++ [ b ]) ++ allBlocks (buildTree bs′)     ∼⟨ ++-cong (≡ˢ-sym $ extendable _ _) ≡ˢ-refl ⟩
    b′ ∈ allBlocks (extendTree (buildTree bs) b) ++ allBlocks (buildTree bs′) ≡⟨⟩
    b′ ∈ allBlocks (buildTree (b ∷ bs)) ++ allBlocks (buildTree bs′)          ∎
    where
      lemma : ∀ {a} {A : Set a} (xs ys : List A) (x : A) → (xs ++ ys) ++ [ x ] ↭ (xs ++ [ x ]) ++ ys
      lemma xs ys x = let open PermutationReasoning in begin
        (xs ++ ys) ++ [ x ]  ≡⟨ L.++-assoc xs ys [ x ] ⟩
        xs ++ ys ++ [ x ]    ↭⟨ ++⁺ˡ xs $ ++-comm ys _ ⟩
        xs ++ [ x ] ++ ys    ≡⟨ L.++-assoc xs [ x ] ys ⟨
        (xs ++ [ x ]) ++ ys  ∎

open TreeType ⦃ ... ⦄ public
