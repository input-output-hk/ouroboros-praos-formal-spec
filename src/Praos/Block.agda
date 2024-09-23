module Praos.Block where

open import Prelude.Init
open import Praos.Crypto

Slot = ℕ

Tx = ⊤
Payload = List Tx

PartyId = ℕ -- TODO: Data.Fin ?

record Party : Set where
  constructor MkParty
  field partyId : PartyId
        vkey : VerificationKey

open Party public

data Honesty : PartyId → Set where

  Honest : ∀ {p : PartyId}
    → Honesty p

  Corrupt : ∀ {p : PartyId}
    → Honesty p

PartyTup = ∃[ p ] (Honesty p)
Parties = List PartyTup

record Block : Set
record BlockBody : Set

record Block where
  field slotNumber : Slot
        creatorId : PartyId
        parentBlock : Hash Block
        leadershipProof : LeadershipProof
        signature : Signature
        bodyHash : Hash Payload

open Block public

record BlockBody where
  constructor MkBlockBody
  field blockHash : Hash Payload
        payload : Payload

open BlockBody public

module _ {a : Set} ⦃ _ : Hashable a ⦄
  where

  open Hashable ⦃...⦄

  tipHash : List a → Hash a
  tipHash [] = MkHash emptyBS
  tipHash (x ∷ _) = hash x
