{-# OPTIONS --allow-unsolved-metas #-} -- FIXME: Remove later

open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot; slot₀; Honesty)
open import Protocol.Params using (Params)
open import Protocol.Block
open import Protocol.Crypto using (Hashable)
open import Protocol.Message
open import Protocol.Network
open import Protocol.TreeType
open Params ⦃ ... ⦄
open Honesty
open Hashable ⦃ ... ⦄
open Envelope

module Properties.Safety
  ⦃ _ : Params ⦄
  ⦃ _ : Block ⦄
  ⦃ _ : Hashable Block ⦄
  ⦃ _ : Default Block ⦄
  {T : Type} ⦃ TreeType-T : TreeType T ⦄
  {AdversarialState : Type}
  {honestyOf : Party → Honesty}
  {txSelection : Slot → Party → Txs}
  {processMsgsᶜ :
      List Message
    → Slot
    → List Message
    → List Envelope
    → AdversarialState
    → List (Message × DelayMap) × AdversarialState}
  {makeBlockᶜ :
      Slot
    → List Message
    → List Envelope
    → AdversarialState
    → List (Message × DelayMap) × AdversarialState}
  {adversarialState₀ : AdversarialState}
  {parties₀ : List Party}
  where

open import Protocol.Semantics {T} {AdversarialState} {honestyOf} {txSelection} {processMsgsᶜ} {makeBlockᶜ}
open GlobalState

N₀ : GlobalState
N₀ =
  record
    { clock     = slot₀
    ; messages  = []
    ; states    = L.foldr (λ p states → set p (it .def) states) [] parties₀
    ; history   = []
    ; advState  = adversarialState₀
    ; execOrder = parties₀
    ; progress  = ready
    }

isSuperSlot : Slot → Type
isSuperSlot sl = length (filter (λ p → ¿ winner p sl × isHonest p ¿) parties₀) ≡ 1

isSuperBlock : Block → Type
isSuperBlock b = isHonest (b .pid) × isSuperSlot (b .slot)

superBlocks : GlobalState → List Block
superBlocks N = L.deduplicate _≟_ $ filter ¿ isSuperBlock ¿¹ (blockHistory N)

private variable
  N₁ N₂ : GlobalState

data MsgsDeliverySteps : GlobalState → GlobalState → Type₁ where

  refineStepR :
    ∙ N₁ ↝⋆ N₂
    ────────────────────────────────────
    MsgsDeliverySteps N₁ N₂

  progressR :
    ∙ MsgsDeliverySteps (record N₁ { progress = msgsDelivered }) N₂
    ────────────────────────────────────
    MsgsDeliverySteps N₁ N₂

  deliveryStep : ∀ {p} →
    ∙ MsgsDeliverySteps (executeMsgsDelivery p N₁) N₂
    ────────────────────────────────────
    MsgsDeliverySteps N₁ N₂

data BlockMakingSteps : GlobalState → GlobalState → Type₁ where

  refineStepB :
    ∙ N₁ ↝⋆ N₂
    ────────────────────────────────────
    BlockMakingSteps N₁ N₂

  progressB :
    ∙ BlockMakingSteps (record N₁ { progress = blockMade }) N₂
    ────────────────────────────────────
    BlockMakingSteps N₁ N₂

  blockMakingStep : ∀ {p} →
    ∙ BlockMakingSteps (executeBlockMaking p N₁) N₂
    ────────────────────────────────────
    BlockMakingSteps N₁ N₂

isForgingFreeD : GlobalState → Type₁
isForgingFreeD N₂ = ∀ {N₁} → MsgsDeliverySteps N₁ N₂ → ∀ {p} →
  let
    (msgs , N₁′) = fetchNewMsgs p N₁
    mds = processMsgsᶜ
      msgs
      (N₁′ .clock)
      (N₁′ .history)
      (N₁′ .messages)
      (N₁′ .advState)
      .proj₁
    nbs = map (λ where (newBlock b , _) → b) mds
  in
    nbs ⊆ʰ blockHistory N₁′

isForgingFreeB : GlobalState → Type₁
isForgingFreeB N₂ = ∀ {N₁} → BlockMakingSteps N₁ N₂ →
  let
    mds = makeBlockᶜ (N₁ .clock) (N₁ .history) (N₁ .messages) (N₁ .advState) .proj₁
    nbs = map (λ where (newBlock b , _) → b) mds
  in
    nbs ⊆ʰ blockHistory N₁

isForgingFree : GlobalState → Type₁
isForgingFree N = isForgingFreeD N × isForgingFreeB N

-- Main lemma for proving the Common Prefix property

module LA = L.All

superBlockPositions : ∀ {N : GlobalState} {sb b : Block} →
    N₀ ↝⋆ N
  → isCollisionFree N
  → isForgingFree N
  → LA.All
      (λ where (sb , b) → blockPos sb N ≢ blockPos b N ⊎ sb ≡ b)
      (L.cartesianProduct (superBlocks N) (honestBlockHistory N))
superBlockPositions = {!!}
