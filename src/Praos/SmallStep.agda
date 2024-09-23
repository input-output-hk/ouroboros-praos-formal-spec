module Praos.SmallStep where

open import Prelude.AssocList
open import Prelude.DecEq using (DecEq)
open import Prelude.Default using (Default)
open Default ⦃...⦄
open import Prelude.InferenceRules
open import Prelude.Init

open import Praos.Block
open import Praos.Chain
open import Praos.Crypto

module _ ⦃ _ : Config ⦄
         ⦃ _ : Hashable Block ⦄
         ⦃ _ : Hashable (List Tx) ⦄
         ⦃ _ : Network ⦄
         ⦃ _ : Postulates ⦄
         where

  open Config ⦃...⦄
  open Hashable ⦃...⦄
  open Network ⦃...⦄
  open Postulates ⦃...⦄

  data Message : Type where
    ChainMsg : {c : Chain} → ValidChain c → Message

  Delay = Fin (suc (suc Δ))

  pattern 𝟘 = fzero
  pattern 𝟙 = fsuc fzero
  pattern 𝟚 = fsuc (fsuc fzero)

  record Envelope : Type where
    constructor ⦅_,_,_,_⦆
    field
      partyId : PartyId
      honesty : Honesty partyId
      message : Message
      delay : Delay

  open Envelope

  -- Tree type

  record IsTreeType {T : Type}
                    (tree₀ : T)
                    (chains : T → List Chain)
                    (addChain : T → {c : Chain} → ValidChain c → T)
                    (preferredChain : T → Chain)
         : Type₁ where
    field
      instantiated :
        preferredChain tree₀ ≡ []

      valid : ∀ (t : T)
        → ValidChain (preferredChain t)

      optimal : ∀ (c : Chain) (t : T)
        → ValidChain c
        → c ∈ chains t
        → length c ≤ length (preferredChain t)

      self-contained : ∀ (t : T)
        → preferredChain t ∈ chains t

  record TreeType (T : Type) : Type₁ where
    field
      tree₀ : T
      chains : T → List Chain
      addChain : T → {c : Chain} → ValidChain c → T
      preferredChain : T → Chain
      is-TreeType : IsTreeType tree₀ chains addChain preferredChain

  -- Semantics

  module Semantics
           {T : Type} {blockTree : TreeType T}
           {S : Type} {adversarialState₀ : S}
           {txSelection : Slot → PartyId → List Tx}
           where

    open TreeType blockTree

    private
      instance
        Default-T : Default T
        Default-T .def = tree₀

    -- Global state

    record State : Type where
      constructor ⟦_,_,_,_,_⟧
      field
        clock : Slot
        blockTrees : AssocList PartyId T
        messages : List Envelope
        history : List Message
        adversarialState : S

    -- Updating a local block-tree upon receiving a message

    data _[_]→_ : T → Message → T → Type where

      ChainReceived : ∀ {c vc t} →
          ────────────────────────────────────
          t [ ChainMsg {c} vc ]→ addChain t vc

    Fetched : State → Type
    Fetched = All (λ { z → delay z ≢ 𝟘 }) ∘ messages
      where
        open State
        open L.All using (All)

    tick : State → State
    tick M =
      record M
        { clock = suc clock
        ; messages =
            map (λ where e → record e { delay = pred (delay e) })
              messages
        }
      where open State M

    delay_by_update_ : Message → (PartyId → Delay) → State → State
    delay m by fᵈ update M =
      record M
        { messages =
            map (λ { p → ⦅ p , honest? p , m , fᵈ p ⦆}) (L.allFin numParties)
            ++ messages
        ; history = m ∷ history
        }
      where open State M

    -- Fetching of messages

    data _⊢_[_]⇀_ : {p : PartyId} → Honesty p → State → Message → State → Type
      where

      honest : ∀ {p} {t t′} {m} {N} → let open State N in
          (m∈ms : ⦅ p , Honest , m , 𝟘 ⦆ ∈ messages) →
        ∙ blockTrees ⁉ p ≡ just t
        ∙ t [ m ]→ t′
          ────────────────────────────────────────────
          Honest {p} ⊢
          N [ m ]⇀ record N
            { blockTrees = set p t′ blockTrees
            ; messages = messages ─ m∈ms
            }

    -- Block creation / chain propagation

    createBlock : Slot → PartyId → LeadershipProof → Signature → T → Block
    createBlock s p π σ t =
      record
        { slotNumber = s
        ; creatorId = p
        ; parentBlock =
            let open IsTreeType
            in tipHash (preferredChain t)
        ; leadershipProof = π
        ; bodyHash =
            let txs = txSelection s p
            in blockHash
                 record
                   { blockHash = hash txs
                   ; payload = txs
                   }
        ; signature = σ
        }

    infix 2 _⊢_↷_

    data _⊢_↷_ : {p : PartyId} → Honesty p → State → State → Type where

      honest : ∀ {p} {t} {M} {π} {σ}
        → let
            open State M
            b = createBlock clock p π σ t
            pref = preferredChain t
          in
          (vc : ValidChain (b ∷ pref))
          (fᵈ : PartyId → Delay) →
        ∙ blockTrees ⁉ p ≡ just t
          ──────────────────────────────
          Honest {p} ⊢
            M ↷ delay ChainMsg vc by fᵈ
                 update M

    -- Small-step semantics
    -- The small-step semantics describe the evolution of the global state

    variable
      M N O : State
      p : PartyId
      h : Honesty p

    data _↝_ : State → State → Type where

      Fetch : ∀ {m} →
        ∙ h ⊢ M [ m ]⇀ N
          ──────────────
          M ↝ N

      CreateBlock :
        ∙ Fetched M
        ∙ h ⊢ M ↷ N
          ─────────
          M ↝ N

      NextSlot :
        ∙ Fetched M
          ──────────
          M ↝ tick M

    -- Reflexive, transitive closure

    infix  2 _↝⋆_
    infixr 2 _↣_
    infix  3 ∎

    data _↝⋆_ : State → State → Type where
      ∎ : M ↝⋆ M
      _↣_ : M ↝ N → N ↝⋆ O → M ↝⋆ O

  open Semantics public
