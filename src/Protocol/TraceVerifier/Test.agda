{-# OPTIONS --erasure #-}

module Protocol.TraceVerifier.Test where

open import Examples.Praos
open import Protocol.TraceVerifier ⦃ praosParams ⦄ ⦃ praosAssumptions ⦄
open import Protocol.Semantics     ⦃ praosParams ⦄ ⦃ praosAssumptions ⦄
open import Protocol.Prelude
open import Prelude.Closures _—→_
open import Irrelevance.List.Permutation using (_·↭_; ·↭-refl; ·↭-swap; module ·↭-Reasoning)

--
-- An example of a derivation
--

_ = begin
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
