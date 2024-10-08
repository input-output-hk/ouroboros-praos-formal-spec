module Praos.Chain where

open import Prelude.Init
open Nat using (_≤?_)

open import Praos.Block
open import Praos.Crypto

record Network : Type₁ where
  field
    Δ : ℕ

module _ ⦃ _ : Config ⦄ where

  open Config ⦃...⦄

  record Postulates : Type₁ where
    field
      IsSlotLeader : PartyId → Slot → LeadershipProof → Type
      IsBlockSignature : Block → Signature → Type

  -- Chain
  Chain = List Block

  data _⪯_ : Chain → Chain → Type where

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

  data ValidChain : Chain → Type where

    Genesis : ValidChain []

    Cons : ∀ {c : Chain} {b : Block}
      → IsBlockSignature b (signature b)
      → IsSlotLeader (creatorId b) (slotNumber b) (leadershipProof b)
      → parentBlock b ≡ tipHash c
      → ValidChain c
      → ValidChain (b ∷ c)
