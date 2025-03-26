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
open import Data.List.Properties.Ext using (filter-∘-comm; filter-∘-×)

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

-- NOTE: In Coq this is defined as:
-- length (filter (λ p → ¿ winner p sl × Corrupt p ¿) $ L.allFin numParties) > 1
-- Is it actually the same?
CorruptSlot : Pred Slot 0ℓ
CorruptSlot sl = length (filter (λ p → ¿ winner p sl × Corrupt p ¿) parties₀) > 1

slotsInRange : Slot → Slot → List Slot
slotsInRange sl₁ sl₂ = map (_+ sl₁) $ L.upTo (sl₂ ∸ sl₁)

superSlotsInRange : Slot → Slot → List Slot
superSlotsInRange = filter ¿ SuperSlot ¿¹ ∘₂ slotsInRange

corruptSlotsInRange : Slot → Slot → List Slot
corruptSlotsInRange = filter ¿ CorruptSlot ¿¹ ∘₂ slotsInRange

slotsInRange-≤-+ : ∀ {P : Pred Slot 0ℓ} (P? : Decidable¹ P) (sl₁ sl₂ sl₃ : Slot) →
  length (filter P? (slotsInRange sl₁ sl₂)) ≤ length (filter P? (slotsInRange sl₁ (sl₂ + sl₃)))
slotsInRange-≤-+ = {!!}
