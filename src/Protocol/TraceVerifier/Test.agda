{-# OPTIONS --erasure #-}

module Protocol.TraceVerifier.Test where

open import Examples.Praos
open import Protocol.TraceVerifier ⦃ praosParams ⦄ ⦃ praosAssumptions ⦄
open import Protocol.Semantics     ⦃ praosParams ⦄ ⦃ praosAssumptions ⦄
open import Protocol.Chain         ⦃ praosParams ⦄
open import Protocol.Tree          ⦃ praosParams ⦄
open import Protocol.Block         ⦃ praosParams ⦄
open import Protocol.Network       ⦃ praosParams ⦄
open import Protocol.Message       ⦃ praosParams ⦄
open import Protocol.Assumptions   ⦃ praosParams ⦄
open import Protocol.Prelude
open import Prelude.Closures _—→_ hiding (Trace; states)
open import Irrelevance.List.Permutation using (_·↭_; ·↭-refl; ·↭-swap; module ·↭-Reasoning)
open Envelope
open Assumptions praosAssumptions

opaque
  unfolding honestMsgsDelivery corruptMsgsDelivery

  --
  -- An example of a derivation
  --

  b₀ b₁ : Block
  b₀ = genesisBlock
  b₁ = mkBlock 1 10 _ 𝕃

  c₀ c₁ : Chain
  c₀ = [ b₀ ]
  c₁ = [ b₁ ⨾ b₀ ]

  m₁ : Message
  m₁ = newBlock b₁

  e₁ : Envelope
  e₁ = ⦅ m₁ , ℍ , 𝟘 ⦆

  _ : record N₀
      { messages  = [ e₁ ] }
      —↠
      record N₀
      { progress  = ready
      ; execOrder = [ ℍ ⨾ 𝕃 ⨾ ℂ ]
      ; clock     = 2
      }
  _ = begin
        record N₀
        { messages = [ e₁ ] }
      —→⟨ deliverMsgs
            refl
            ( honestParty↓  refl refl
            ∷ honestParty↓  refl refl
            ∷ corruptParty↓ refl refl
            ∷ []
            )
        ⟩
        record N₀
        { progress  = msgsDelivered
        ; messages  = []
        ; states    = [ (𝕃 , record { tree = [ c₀ ] })
                      ⨾ (ℍ , record { tree = [ c₁ ] })
                      ⨾ (ℂ , record { tree = [ c₀ ] })
                      ]
        }
      —→⟨ {!!} ⟩ -- TODO: Replace by a `makeBlock` transition
        record N₀
        { progress  = blockMade }
      —→⟨ permuteParties (·↭-swap 𝕃 ℍ (·↭-refl [ ℂ ])) ⟩
        record N₀
        { progress  = blockMade
        ; execOrder = [ ℍ ⨾ 𝕃 ⨾ ℂ ] }
      —→⟨ advanceRound refl ⟩
        record N₀
        { progress  = ready
        ; execOrder = [ ℍ ⨾ 𝕃 ⨾ ℂ ]
        ; clock     = 2 }
      ∎

--
-- Tests of valid and invalid traces
--

-- A valid trace:
testTrace₁ : Trace
testTrace₁ = L.reverse $
  [ PermuteParties [ ℍ ⨾ 𝕃 ⨾ ℂ ]
  ⨾ PermuteParties [ ℂ ⨾ ℍ ⨾ 𝕃 ]
  ⨾ DeliverMsgs
  ]

_ : ¿ ValidTrace testTrace₁ ¿ᵇ ≡ true
_ = refl

-- An invalid trace; `AdvanceRound` can only be executed when `progress` is `blockMade`:
testTrace₂ : Trace
testTrace₂ = L.reverse $
  [ PermuteParties [ ℍ ⨾ 𝕃 ⨾ ℂ ]
  ⨾ AdvanceRound
  ]

_ : ¿ ValidTrace testTrace₂ ¿ᵇ ≡ false
_ = refl
