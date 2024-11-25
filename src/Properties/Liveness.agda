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

module Properties.Liveness
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
  {parties₀ : List Party} -- TODO: Use numParties instead
  where

open import Protocol.Semantics {T} {AdversarialState} {honestyOf} {txSelection} {processMsgsᶜ} {makeBlockᶜ}
open import Properties.Common {T} {AdversarialState} {honestyOf} {txSelection} {processMsgsᶜ} {makeBlockᶜ} {adversarialState₀} {parties₀}

knowledgePropagation : ∀ {N₁ N₂ : GlobalState} {p₁ p₂ : Party} {t₁ t₂ : T} →
    honestyOf p₁ ≡ honest
  → honestyOf p₂ ≡ honest
  → p₁ ∈ parties₀
  → p₂ ∈ parties₀
  → N₀ ↝⋆ N₁
  → N₁ ↝⋆ N₂
  → (p₁ , ⟪ t₁ ⟫) ∈ N₁ .states
  → (p₂ , ⟪ t₂ ⟫) ∈ N₂ .states
  → N₁ .progress ≡ ready
  → N₂ .progress ≡ msgsDelivered
  → N₁ .clock ≡ N₂ .clock
  → allBlocks t₁ ⊆ allBlocks t₂
knowledgePropagation = {!!}
  
  
