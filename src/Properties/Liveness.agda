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

open import Data.List.Membership.DecPropositional {A = Block} _≟_ renaming (_∈_ to _∈ˢ_)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties


lemma-permutation : ∀ {N : GlobalState} →
  states (L.foldr executeMsgsDelivery N (N .execOrder)) ↭ N .states
lemma-permutation = {!!}

lemma2-permutation : ∀ {N : GlobalState} → clock
      (L.foldr executeMsgsDelivery N
       (N .execOrder))
      ≡ N .clock
lemma2-permutation = {!!}

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
  → allBlocks t₁ ⊆ˢ allBlocks t₂
knowledgePropagation h₁ h₂ p₁∈p p₂∈p N₀↝⋆N ∎ p₁∈N p₂∈N r d _ = {!!}
  -- let x = trans (sym r) d in ⊥-elim (ready≢delivered x) -- contradiction ready and delivered
knowledgePropagation h₁ h₂ p₁∈p p₂∈p N₀↝⋆N₁ (N₁↝⋆N ↣ permuteParties _) p₁∈N₁ p₂∈N₂ refl refl refl =
  knowledgePropagation h₁ h₂ p₁∈p p₂∈p N₀↝⋆N₁ N₁↝⋆N p₁∈N₁ p₂∈N₂ refl refl refl
knowledgePropagation h₁ h₂ p₁∈p p₂∈p N₀↝⋆N₁ (N₁↝⋆N ↣ permuteMsgs _) p₁∈N₁ p₂∈N₂ refl refl refl =
  knowledgePropagation h₁ h₂ p₁∈p p₂∈p N₀↝⋆N₁ N₁↝⋆N p₁∈N₁ p₂∈N₂ refl refl refl
knowledgePropagation {N₁} {N₂} {p₁} {p₂} {t₁} {t₂} h₁ h₂ p₁∈p p₂∈p N₀↝⋆N₁ (N₁↝⋆N ↣ deliverMsgs {N} refl) p₁∈N₁ p₂∈N₂ refl refl refl {x} b
  with L.foldr executeMsgsDelivery N (N .execOrder) | executeMsgsDelivery p₂ N
... | xx | yy = {!!}

{-
  with x ∈? allBlocks t₂
... | yes p = p
... | no ¬p = {!!}
-}
