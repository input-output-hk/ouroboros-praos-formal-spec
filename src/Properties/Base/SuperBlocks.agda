{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled

open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Base.SuperBlocks
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot; Honesty)
open import Protocol.Block ⦃ params ⦄
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.ForgingFree ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.CollisionFree ⦃ params ⦄ ⦃ assumptions ⦄
open import Data.List.Ext using (ι)
open import Data.List.Properties.Ext using (filter-∘-comm; filter-∘-×; ∈-ι⁺)

SuperSlot : Pred Slot 0ℓ
SuperSlot sl = length (filter (λ p → ¿ winner p sl × Honest p ¿) parties₀) ≡ 1

SuperBlock : Pred Block 0ℓ
SuperBlock b = Honest (b .pid) × SuperSlot (b .slot)

superBlocks : GlobalState → List Block
superBlocks N = L.deduplicate _≟_ $ filter ¿ SuperBlock ¿¹ (blockHistory N)

∈-superBlocks⁻ : ∀ {N : GlobalState} {b : Block} → b ∈ superBlocks N → b ∈ blockHistory N × SuperBlock b
∈-superBlocks⁻ = L.Mem.∈-filter⁻ _ ∘ L.Mem.∈-deduplicate⁻ _ _

∈-superBlocks⁺ : ∀ {N : GlobalState} {b : Block} → b ∈ blockHistory N → SuperBlock b → b ∈ superBlocks N
∈-superBlocks⁺ = L.Mem.∈-deduplicate⁺ _ ∘₂ L.Mem.∈-filter⁺ _

superBlocksAltDef : ∀ N → superBlocks N ≡ (L.deduplicate _≟_ $ filter ¿ SuperSlot ∘ slot ¿¹ (honestBlockHistory N))
superBlocksAltDef N
  rewrite filter-∘-comm ¿ SuperSlot ∘ slot ¿¹ ¿ Honest ∘ pid ¿¹ (blockHistory N)
    | sym $ filter-∘-× ¿ Honest ∘ pid ¿¹ ¿ SuperSlot ∘ slot ¿¹ (blockHistory N)
    = refl

{--------
-- NOTE: In Coq this is defined as:
-- length (filter (λ p → ¿ winner p sl × Corrupt p ¿) $ L.allFin numParties) > 1
-- Is it actually the same?
CorruptSlot : Pred Slot 0ℓ
CorruptSlot sl = length (filter (λ p → ¿ winner p sl × Corrupt p ¿) parties₀) > 1
--------}

-- Corrupt slots: Slots where there are at least one corrupt winner.

CorruptSlotIn : REL (List Party) Slot 0ℓ
CorruptSlotIn ps sl = L.Any.Any (λ p → winner p sl × Corrupt p) ps

CorruptSlot : Pred Slot 0ℓ
CorruptSlot sl = CorruptSlotIn (L.allFin numParties) sl

CorruptSlotW : Pred Slot 0ℓ
CorruptSlotW sl = CorruptSlotIn parties₀ sl

-- The list of slots in the range [sl₁, sl₂)
slotsInRange : Slot → Slot → List Slot
slotsInRange sl₁ sl₂ = ι sl₁ (sl₂ ∸ sl₁)
--map (_+ sl₁) $ L.upTo (sl₂ ∸ sl₁)

superSlotsInRange : Slot → Slot → List Slot
superSlotsInRange = filter ¿ SuperSlot ¿¹ ∘₂ slotsInRange

superBlocksInRange : GlobalState → Slot → Slot → List Block
superBlocksInRange N sl₁ sl₂ = filter (λ b → ¿ sl₁ ≤ b .slot × b .slot < sl₂ ¿) (superBlocks N)

corruptSlotsInRange : Slot → Slot → List Slot
corruptSlotsInRange = filter ¿ CorruptSlot ¿¹ ∘₂ slotsInRange

slotsInRange-≤-+ : ∀ {P : Pred Slot 0ℓ} (P? : Decidable¹ P) (sl₁ sl₂ sl₃ : Slot) →
  length (filter P? (slotsInRange sl₁ sl₂)) ≤ length (filter P? (slotsInRange sl₁ (sl₂ + sl₃)))
slotsInRange-≤-+ = {!!}

slotsInRange-++ : ∀ {P : Pred Slot 0ℓ} (P? : Decidable¹ P) {sl₁ sl₂ sl₃ : Slot} →
  sl₁ ≤ sl₂ → sl₂ ≤ sl₃ → filter P? (slotsInRange sl₁ sl₃) ≡ filter P? (slotsInRange sl₁ sl₂) ++ filter P? (slotsInRange sl₂ sl₃)
slotsInRange-++ = {!!}

slotsInRange-∈ : ∀ {sl₁ sl₂ sl : Slot} → sl₁ ≤ sl → sl < sl₂ → sl ∈ slotsInRange sl₁ sl₂
slotsInRange-∈ {sl₁} {sl₂} {sl} sl₁≤sl sl<sl₂ = ∈-ι⁺ sl₁≤sl $
  begin-strict
    sl                ≡⟨ Nat.m∸n+n≡m sl₁≤sl ⟨
    (sl ∸ sl₁) + sl₁  ≡⟨ Nat.+-comm _ sl₁ ⟩
    sl₁ + (sl ∸ sl₁)  <⟨ Nat.+-monoʳ-< sl₁ $ Nat.∸-monoˡ-< sl<sl₂ sl₁≤sl ⟩
    sl₁ + (sl₂ ∸ sl₁) ∎
  where open Nat.≤-Reasoning

superSlots≡superBlocks : ∀ {N : GlobalState} {sl₁ sl₂ : Slot} →
    N₀ ↝⋆ N
  → ForgingFree N
  → 0 < sl₁
  → sl₂ ≤ N .clock
  → length (superSlotsInRange sl₁ sl₂) ≡ length (superBlocksInRange N sl₁ sl₂)
superSlots≡superBlocks = {!!}

superBlockPositionsUniqueness : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → ForgingFree N
  → CollisionFree N
  → Unique (map (flip blockPos N) (superBlocks N))
superBlockPositionsUniqueness = {!!}

superBlocksInHonestBlockHistory :  ∀ {N} → superBlocks N ⊆ˢ honestBlockHistory N
superBlocksInHonestBlockHistory {N} {b} b∈sbsN = L.Mem.∈-filter⁺ ¿ HonestBlock ¿¹ b∈bhN bIsHonest
  where
    b∈bhN : b ∈ blockHistory N
    b∈bhN = ∈-superBlocks⁻ {N} b∈sbsN .proj₁

    bIsHonest : Honest (b .pid)
    bIsHonest = ∈-superBlocks⁻ {N} b∈sbsN .proj₂ .proj₁
