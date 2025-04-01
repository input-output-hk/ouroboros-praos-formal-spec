{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled

open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Safety.SingleRoundCommonPrefix
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot)
open import Protocol.Crypto ⦃ params ⦄ using (Hashable); open Hashable ⦃ ... ⦄
open import Protocol.Block ⦃ params ⦄
open import Protocol.Chain ⦃ params ⦄
open import Protocol.Message ⦃ params ⦄
open import Protocol.Network ⦃ params ⦄; open Envelope
open import Protocol.TreeType ⦃ params ⦄
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.ForgingFree ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.CollisionFree ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.SuperBlocks ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Safety ⦃ params ⦄ ⦃ assumptions ⦄

lcs : Chain → Chain → Chain
lcs (b ∷ c) (b′ ∷ c′) with b ≟ b′
... | yes _ = b ∷ lcs c c′
... | no  _ = []
lcs _       _         = []

singlePartyCommonPrefix-⪯ : ∀ {N : GlobalState} {k : Slot} →
    N₀ ↝⋆ N
  → ForgingFree N
  → CollisionFree N
  → ∀ {p : Party} {ls : LocalState}
    → Honest p
    → N .states ⁉ p ≡ just ls
    → let bc = bestChain (N .clock ∸ 1) (ls .tree)
      in ∀ {c : Chain} {sl : Slot} →
          c ⊆ˢ filter ((_≤? N .clock ∸ 1 + sl) ∘ slot) (genesisBlock ∷ blockHistory N)
        → c ✓
        → ∣ bc ∣ ≤ ∣ c ∣
        → prune k bc ⪯ c
          ⊎
          ∃[ sl′ ]
              sl′ ≤ k
            × length (superSlotsInRange (sl′ + 1) (N .clock ∸ 1))
              ≤
              2 * length (corruptSlotsInRange (sl′ + 1) (N .clock + sl))
singlePartyCommonPrefix-⪯ = {!!}

singlePartyCommonPrefix-⪰ : ∀ {N : GlobalState} {k : Slot} →
    N₀ ↝⋆ N
  → ForgingFree N
  → CollisionFree N
  → ∀ {p : Party} {ls : LocalState}
    → Honest p
    → N .states ⁉ p ≡ just ls
    → let bc = bestChain (N .clock ∸ 1) (ls .tree)
      in ∀ {c : Chain} {sl : Slot} →
          c ⊆ˢ filter ((_≤? N .clock ∸ 1 + sl) ∘ slot) (genesisBlock ∷ blockHistory N)
        → c ✓
        → ∣ bc ∣ ≤ ∣ c ∣
        → prune k c ⪯ bc
          ⊎
          ∃[ sl′ ]
              sl′ ≤ k
            × length (superSlotsInRange (sl′ + 1) (N .clock ∸ 1))
              ≤
              2 * length (corruptSlotsInRange (sl′ + 1) (N .clock + sl))
singlePartyCommonPrefix-⪰ = {!!}

singleRoundCommonPrefix : ∀ {N : GlobalState} {k : Slot} →
    N₀ ↝⋆ N
  → ForgingFree N
  → CollisionFree N
  → ∀ {p₁ p₂ : Party} {ls₁ ls₂ : LocalState}
  → Honest p₁
  → Honest p₂
  → N .states ⁉ p₁ ≡ just ls₁
  → N .states ⁉ p₂ ≡ just ls₂
  → let bc₁ = bestChain (N .clock ∸ 1) (ls₁ .tree)
        bc₂ = bestChain (N .clock ∸ 1) (ls₂ .tree)
    in prune k bc₁ ⪯ bc₂
       ⊎
       ∃[ sl′ ]
           sl′ ≤ k
         × length (superSlotsInRange (sl′ + 1) (N .clock ∸ 1))
           ≤
           2 * length (corruptSlotsInRange (sl′ + 1) (N .clock))
singleRoundCommonPrefix {N} {k} N₀↝⋆N ffN cfN {p₁} {p₂} {ls₁} {ls₂} hp₁ hp₂ lsp₁ lsp₂ = goal
  where
    bc₁ = bestChain (N .clock ∸ 1) (ls₁ .tree)
    bc₂ = bestChain (N .clock ∸ 1) (ls₂ .tree)

    bc⊆fg∷bhN : ∀ ls p hp lsp → bestChain (N .clock ∸ 1) (ls .tree) ⊆ˢ filter ((_≤? N .clock ∸ 1 + 0) ∘ slot) (genesisBlock ∷ blockHistory N)
    bc⊆fg∷bhN ls p hp lsp {b} b∈bc = L.Mem.∈-filter⁺ ((_≤? N .clock ∸ 1 + 0) ∘ slot) (π1 b∈bc) π2
      where
        π1 : bestChain (N .clock ∸ 1) (ls .tree) ⊆ˢ genesisBlock ∷ blockHistory N
        π1 = begin
          bestChain (N .clock ∸ 1) (ls .tree)
            ⊆⟨ selfContained (ls .tree) (N .clock ∸ 1) ⟩
          filter ((_≤? N .clock ∸ 1) ∘ slot) (allBlocks (ls .tree))
            ⊆⟨ L.SubS.filter-⊆ _ _ ⟩
          allBlocks (ls .tree)
            ⊆⟨ honestLocalTreeInHonestGlobalTree {p = p} N₀↝⋆N hp lsp ⟩
          allBlocks (honestTree N)
            ⊆⟨ honestGlobalTreeInBlockHistory N₀↝⋆N ⟩
          genesisBlock ∷ blockHistory N ∎
          where open L.SubS.⊆-Reasoning Block

        π2 : b .slot ≤ N .clock ∸ 1 + 0
        π2
          rewrite
            Nat.+-suc (N .clock ∸ 1) 0
          | Nat.+-identityʳ (N .clock ∸ 1)
          = L.All.lookup (bestChainSlotBounded (ls .tree) (N .clock ∸ 1)) b∈bc

    Goal-◆ = λ ◆ →
      prune k bc₁ ⪯ bc₂
      ⊎
      ∃[ sl′ ]
          sl′ ≤ k
        × length (superSlotsInRange (sl′ + 1) (N .clock ∸ 1))
          ≤
          2 * length (corruptSlotsInRange (sl′ + 1) ◆)

    goal : Goal-◆ (N .clock)
    goal with Nat.≤-total ∣ bc₁ ∣ ∣ bc₂ ∣
    ... | inj₁ ∣bc₁∣≤∣bc₂∣ = subst Goal-◆ (Nat.+-identityʳ _) $ singlePartyCommonPrefix-⪯ {k = k} N₀↝⋆N ffN cfN {p₁} {ls₁} hp₁ lsp₁ {bc₂} {0} (bc⊆fg∷bhN ls₂ p₂ hp₂ lsp₂) bc₂✓ ∣bc₁∣≤∣bc₂∣
      where
        bc₂✓ : bc₂ ✓
        bc₂✓ = valid (ls₂ .tree) (N .clock ∸ 1)

    ... | inj₂ ∣bc₂∣≤∣bc₁∣ = subst Goal-◆ (Nat.+-identityʳ _) $ singlePartyCommonPrefix-⪰ {k = k} N₀↝⋆N ffN cfN {p₂} {ls₂} hp₂ lsp₂ {bc₁} {0} (bc⊆fg∷bhN ls₁ p₁ hp₁ lsp₁) bc₁✓ ∣bc₂∣≤∣bc₁∣
      where
        bc₁✓ : bc₁ ✓
        bc₁✓ = valid (ls₁ .tree) (N .clock ∸ 1)
