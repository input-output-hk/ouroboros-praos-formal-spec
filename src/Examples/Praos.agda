{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled in

module Examples.Praos where

open import Protocol.Prelude
open import Protocol.BaseTypes

open import Protocol.Params

VerKey = ℕ
Seed   = ℕ

pattern 𝕃 = fzero             -- honest leader
pattern ℍ = fsuc fzero        -- honest
pattern ℂ = fsuc (fsuc fzero) -- corrupt

-- NOTE: The VRF verifies only for the vk 0 ≡ Fi.toℕ 𝕃 
vrf : REL VerKey Seed 0ℓ
vrf 0 _ = ⊤
vrf _ _ = ⊥

instance
  Dec-vrf : vrf ⁇²
  Dec-vrf {0}     {_} .dec = yes tt
  Dec-vrf {suc _} {_} .dec = no (λ ())

instance
  praosParams : Params
  praosParams = record
    { numParties = 3
    ; Txs        = ⊤
    ; Hash       = ℕ
    ; winner     = λ  p   sl  →     vrf (Fi.toℕ p) sl
    ; winnerᵈ    = λ {p} {sl} → ⁇ ¿ vrf (Fi.toℕ p) sl ¿
    }

open import Protocol.Block  ⦃ praosParams ⦄
open import Protocol.Crypto ⦃ praosParams ⦄

instance
  praosHashableBlock : Hashable Block
  praosHashableBlock .hash = suc ∘ prev -- i.e., if b .prev ≡ h then hash b ≡ suc h

instance
  praosDefaultBlock : Default Block
  praosDefaultBlock = record { def = mkBlock 0 0 tt 𝕃 } -- i.e., the genesis block

open import Protocol.Tree  ⦃ praosParams ⦄ ⦃ praosHashableBlock ⦄
open import Protocol.Chain ⦃ praosParams ⦄ ⦃ praosHashableBlock ⦄

-- NOTE: Implementation as described in the Praos paper
PraosTreeImpl : Type
PraosTreeImpl = List Chain -- chains received so far in the slot

_fitsIn_ : Block → Op₁ Chain
b fitsIn [] = []
b fitsIn c′@(b′ ∷ c) = if b .prev == hash b′ then b ∷ c′ else c

maxLength : PraosTreeImpl → ℕ
maxLength cs = (case L.reverse $ sort $ map length cs of λ where
  [] → 0
  (l ∷ _) → l)
  where
    open import Data.Nat.Properties using (≤-decTotalOrder)
    open import Data.List.Sort.InsertionSort ≤-decTotalOrder

maxChain : PraosTreeImpl → Chain
maxChain cs = case L.findᵇ ((_== maxLength cs) ∘ length) cs of λ where
  nothing → []
  (just c) → c

instance
  praosTree : Tree PraosTreeImpl
  praosTree = record
    { -- Operations
      tree₀         = [ [ genesisBlock ] ]
    ; extendTree    = λ cs b → map (b fitsIn_) cs
    ; allBlocks     = L.deduplicateᵇ (_==_) ∘ L.concat
    ; bestChain     = λ sl cs → maxChain cs
      -- Axioms
    ; instantiated  = {!!}
    ; extendable    = {!!}
    ; valid         = {!!}
    ; optimal       = {!!}
    ; selfContained = {!!}
    }

open import Protocol.Assumptions ⦃ praosParams ⦄

instance
  praosAssumptions : Assumptions
  praosAssumptions = record
    { -- Types/data/functions
      TreeImpl           = PraosTreeImpl
    ; AdversarialState   = ⊤
    ; honestyOf          = λ where 𝕃 → honest; ℍ → honest; ℂ → corrupt
    ; txSelection        = λ _ _ → _
    ; adversarialState₀  = _
    ; parties₀           = [ 𝕃 ⨾ ℍ ⨾ ℂ ]
    ; processMsgsᶜ       = λ _ _ _ _ _ → [] , _
    ; makeBlockᶜ         = λ _ _ _ _   → [] , _
      -- Axioms
    ; Hashable-Block     = praosHashableBlock
    ; Default-Block      = praosDefaultBlock
    ; Tree-TreeImpl      = it
    ; parties₀HasHonest  = here refl
    ; parties₀Uniqueness = ((λ ()) L.All.∷ (λ ()) L.All.∷ []) L.Unique.∷ ((λ ()) L.All.∷ []) L.Unique.∷ [] L.Unique.∷ L.Unique.[]
    ; genesisBlockSlot   = refl
    ; genesisHonesty     = refl
    ; genesisWinner      = tt
    }
