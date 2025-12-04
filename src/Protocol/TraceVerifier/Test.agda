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
open import Irrelevance.List.Permutation using (_·↭_; ·↭-refl; ·↭-swap)
open Envelope
open Assumptions praosAssumptions

opaque
  unfolding honestMsgsDelivery corruptMsgsDelivery honestBlockMaking corruptBlockMaking

  --
  -- An example of a derivation
  --

  b₀ b₁ b₂ : Block
  b₀ = genesisBlock
  b₁ = mkBlock 1 10 _ 𝕃
  b₂ = mkBlock 1  1 _ 𝕃

  mb₁ mb₂ : Message
  mb₁ = newBlock b₁
  mb₂ = newBlock b₂

  _ : record N₀
      { messages  = [ ⦅ mb₁ , ℍ , 𝟘 ⦆ ] }
      —↠
      record N₀
      { progress  = ready
      ; messages  = [ ⦅ mb₂ , 𝕃 , 𝟘 ⦆
                    ⨾ ⦅ mb₂ , ℍ , 𝟘 ⦆
                    ⨾ ⦅ mb₂ , ℂ , 𝟘 ⦆
                    ]
      ; history   = [ mb₂ ]
      ; states    = [ (𝕃 , record { tree = [ [ b₂ ⨾ b₀ ] ] })
                    ⨾ (ℍ , record { tree = [ [ b₁ ⨾ b₀ ] ] })
                    ⨾ (ℂ , record { tree = [ [ b₀ ] ] })
                    ]
      ; execOrder = [ ℍ ⨾ 𝕃 ⨾ ℂ ]
      ; clock     = 2
      }
  _ = begin
        record N₀
        { messages = [ ⦅ mb₁ , ℍ , 𝟘 ⦆ ] }
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
        ; states    = [ (𝕃 , record { tree = [ [ b₀ ] ] })
                      ⨾ (ℍ , record { tree = [ [ b₁ ⨾ b₀ ] ] })
                      ⨾ (ℂ , record { tree = [ [ b₀ ] ] })
                      ]
        }
      —→⟨ makeBlock
            refl
            ( honestParty↑ {ls = record { tree = [ [ b₀ ] ] }} refl refl
            ∷ honestParty↑ refl refl
            ∷ corruptParty↑ refl refl
            ∷ []
            )
        ⟩
        record N₀
        { progress  = blockMade
        ; messages  = [ ⦅ mb₂ , 𝕃 , 𝟙 ⦆
                      ⨾ ⦅ mb₂ , ℍ , 𝟙 ⦆
                      ⨾ ⦅ mb₂ , ℂ , 𝟙 ⦆
                      ]
        ; history   = [ mb₂ ]
        ; states    = [ (𝕃 , record { tree = [ [ b₂ ⨾ b₀ ] ] })
                      ⨾ (ℍ , record { tree = [ [ b₁ ⨾ b₀ ] ] })
                      ⨾ (ℂ , record { tree = [ [ b₀ ] ] })
                      ]
        }
      —→⟨ permuteParties (·↭-swap 𝕃 ℍ (·↭-refl [ ℂ ])) ⟩
        record N₀
        { progress  = blockMade
        ; messages  = [ ⦅ mb₂ , 𝕃 , 𝟙 ⦆
                      ⨾ ⦅ mb₂ , ℍ , 𝟙 ⦆
                      ⨾ ⦅ mb₂ , ℂ , 𝟙 ⦆
                      ]
        ; history   = [ mb₂ ]
        ; states    = [ (𝕃 , record { tree = [ [ b₂ ⨾ b₀ ] ] })
                      ⨾ (ℍ , record { tree = [ [ b₁ ⨾ b₀ ] ] })
                      ⨾ (ℂ , record { tree = [ [ b₀ ] ] })
                      ]
        ; execOrder = [ ℍ ⨾ 𝕃 ⨾ ℂ ]
        }
      —→⟨ advanceRound refl ⟩
        record N₀
        { progress  = ready
        ; messages  = [ ⦅ mb₂ , 𝕃 , 𝟘 ⦆
                      ⨾ ⦅ mb₂ , ℍ , 𝟘 ⦆
                      ⨾ ⦅ mb₂ , ℂ , 𝟘 ⦆
                      ]
        ; history   = [ mb₂ ]
        ; states    = [ (𝕃 , record { tree = [ [ b₂ ⨾ b₀ ] ] })
                      ⨾ (ℍ , record { tree = [ [ b₁ ⨾ b₀ ] ] })
                      ⨾ (ℂ , record { tree = [ [ b₀ ] ] })
                      ]
        ; execOrder = [ ℍ ⨾ 𝕃 ⨾ ℂ ]
        ; clock     = 2
        }
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
  ⨾ MakeBlock
  ⨾ AdvanceRound
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
