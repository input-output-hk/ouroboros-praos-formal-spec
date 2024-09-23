module Praos.Chain where

open import Prelude.Init
open Nat using (_≤?_)

open import Praos.Block
open import Praos.Crypto

module _ ⦃ _ : Config ⦄ where

  open Config ⦃...⦄

  record Network : Set₁ where
    field
      Δ : ℕ
      honest? : ∀ (p : PartyId) → Honesty p

  record Postulates : Set₁ where
    field
      IsSlotLeader : PartyId → Slot → LeadershipProof → Set
      IsBlockSignature : Block → Signature → Set

  -- Chain
  Chain = List Block

  data _⪯_ : Chain → Chain → Set where

    Prefix : ∀ {c₁ c₂ c₃ : Chain}
      → c₁ ++ c₃ ≡ c₂
      → c₁ ⪯ c₂

  prune : Slot → Chain → Chain
  prune sl = filter ((_≤? sl) ∘ slotNumber)

module _ ⦃ _ : Config ⦄
         ⦃ _ : Hashable Block ⦄
         ⦃ _ : Postulates ⦄
         where

  open Config ⦃...⦄
  open Hashable ⦃...⦄
  open Postulates ⦃...⦄

  -- Validity of a chain

  data ValidChain : Chain → Set where

    Genesis : ValidChain []

    Cons : ∀ {c : Chain} {b : Block}
      → IsBlockSignature b (signature b)
      → IsSlotLeader (creatorId b) (slotNumber b) (leadershipProof b)
      → parentBlock b ≡ tipHash c
      → ValidChain c
      → ValidChain (b ∷ c)
