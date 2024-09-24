module Praos.Block where

open import Prelude.Init
open import Praos.Crypto

Slot = ℕ

Tx = ⊤
Payload = List Tx

record Config : Type where
  field
    numParties : ℕ

module _ ⦃ _ : Config ⦄ where

  open Config ⦃...⦄

  -- Finite number of parties
  PartyId = Fin numParties

  record Party : Type where
    constructor MkParty
    field
      partyId : PartyId
      vkey : VerificationKey

  open Party public

  data Honesty : PartyId → Type where
    Honest : ∀ {p : PartyId}  → Honesty p
    Corrupt : ∀ {p : PartyId} → Honesty p

  record Block : Type
  record BlockBody : Type

  record Block where
    field
      slotNumber : Slot
      creatorId : PartyId
      parentBlock : Hash Block
      leadershipProof : LeadershipProof
      signature : Signature
      bodyHash : Hash Payload

  open Block public

  record BlockBody where
    constructor MkBlockBody
    field
      blockHash : Hash Payload
      payload : Payload

  open BlockBody public

module _ {a : Type} ⦃ _ : Hashable a ⦄
  where

  open Hashable ⦃...⦄

  tipHash : List a → Hash a
  tipHash [] = MkHash emptyBS
  tipHash (x ∷ _) = hash x
