open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Base.ForgingFree
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.Message ⦃ params ⦄
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄

-- The condition `∀ {N₁} → N₁ ↷↓ N₂ → ∀ {p} → ...` forces the forging-free property to hold at each
-- previous "sub-step" within the delivery/minting phase. A sub-step is either starting a
-- new round, changing the progress to `msgsDelivered`/‵blockMade` or executing the messages
-- delivery/block minting for a party `p`.
--
-- Thus, an honest block can be broadcast by a corrupt party _only_ if such block was already in the
-- history at the beginning of the delivery/minting phase.
ForgingFree↓ : Pred GlobalState 0ℓ
ForgingFree↓ N₂ = ∀ {N₁ : GlobalState} → N₁ ↷↓ N₂ → ∀ {p : Party} →
  let
    (msgs , N₁′) = fetchNewMsgs p N₁
    mds = processMsgsᶜ
      msgs
      (N₁′ .clock)
      (N₁′ .history)
      (N₁′ .messages)
      (N₁′ .advState)
      .proj₁
    nbs = map (projBlock ∘ proj₁) mds
  in
    nbs ⊆ʰ blockHistory N₁′

ForgingFree↑ : Pred GlobalState 0ℓ
ForgingFree↑ N₂ = ∀ {N₁ : GlobalState} → N₁ ↷↑ N₂ →
  let
    mds = makeBlockᶜ (N₁ .clock) (N₁ .history) (N₁ .messages) (N₁ .advState) .proj₁
    nbs = map (projBlock ∘ proj₁) mds
  in
    nbs ⊆ʰ blockHistory N₁

ForgingFree : Pred GlobalState 0ℓ
ForgingFree N = ForgingFree↓ N × ForgingFree↑ N

ForgingFree↓Prev : ∀ {N₁ N₂ : GlobalState} → ForgingFree↓ N₂ → N₁ ↝⋆ N₂ → ForgingFree↓ N₁
ForgingFree↓Prev ff↓ ts↝⋆ ts↷↓ = ff↓ (ForgingFree↓Prev′ ts↷↓ ts↝⋆)
  where
    ForgingFree↓Prev′ : ∀ {N₁ N₂ N′ : GlobalState} → N₁ ↷↓ N′ → N′ ↝⋆ N₂ → N₁ ↷↓ N₂
    ForgingFree↓Prev′ (refine↓ x)     ts↝⋆ = refine↓ (x ◅◅ ts↝⋆)
    ForgingFree↓Prev′ (progress↓ x)   ts↝⋆ = progress↓ (ForgingFree↓Prev′ x ts↝⋆)
    ForgingFree↓Prev′ (delivery↓ x y) ts↝⋆ = delivery↓ x (ForgingFree↓Prev′ y ts↝⋆)

ForgingFree↑Prev : ∀ {N₁ N₂ : GlobalState} → ForgingFree↑ N₂ → N₁ ↝⋆ N₂ → ForgingFree↑ N₁
ForgingFree↑Prev ff↑ ts↝⋆ ts↷↑ = ff↑ (ForgingFree↑Prev′ ts↷↑ ts↝⋆)
  where
    ForgingFree↑Prev′ : ∀ {N₁ N₂ N′ : GlobalState} → N₁ ↷↑ N′ → N′ ↝⋆ N₂ → N₁ ↷↑ N₂
    ForgingFree↑Prev′ (refine↑ x)        ts↝⋆ = refine↑ (x ◅◅ ts↝⋆)
    ForgingFree↑Prev′ (progress↑ x)      ts↝⋆ = progress↑ (ForgingFree↑Prev′ x ts↝⋆)
    ForgingFree↑Prev′ (blockMaking↑ x y) ts↝⋆ = blockMaking↑ x (ForgingFree↑Prev′ y ts↝⋆)

ForgingFreePrev : ∀ {N₁ N₂} → N₁ ↝⋆ N₂ → ForgingFree N₂ → ForgingFree N₁
ForgingFreePrev N₁↝⋆N₂ (ffN₂↓ , ffN₂↑) = ForgingFree↓Prev ffN₂↓ N₁↝⋆N₂ , ForgingFree↑Prev ffN₂↑ N₁↝⋆N₂
