{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled

open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Base.LocalState
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.Message ⦃ params ⦄
open import Protocol.Network ⦃ params ⦄; open Envelope
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Data.Maybe.Properties.Ext using (Is-just⇒to-witness)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.Structures using (IsEquivalence)
open import Function.Properties.Equivalence using (⇔-isEquivalence)
open IsEquivalence {ℓ = 0ℓ} ⇔-isEquivalence renaming (trans to ⇔-trans) hiding (refl)

_hasStateIn_ : REL Party GlobalState 0ℓ
p hasStateIn N = M.Is-just (N .states ⁉ p)

hasStateInAltDef : ∀ {N : GlobalState} {p : Party} →
  (∃[ ls ] N .states ⁉ p ≡ just ls) ⇔ p hasStateIn N
hasStateInAltDef {N} {p} = mk⇔ to from
  where
    to : (∃[ ls ] N .states ⁉ p ≡ just ls) → p hasStateIn N
    to (_ , lsNp) rewrite lsNp = M.Any.just tt

    from : p hasStateIn N → (∃[ ls ] N .states ⁉ p ≡ just ls)
    from pHasN = M.to-witness pHasN , Is-just⇒to-witness pHasN

opaque

  unfolding honestMsgsDelivery honestBlockMaking

  localStatePreservation-broadcastMsgsᶜ : ∀ {N : GlobalState} {mds : List (Message × DelayMap)} →
    broadcastMsgsᶜ mds N .states ≡ N .states
  localStatePreservation-broadcastMsgsᶜ {_} {[]} = refl
  localStatePreservation-broadcastMsgsᶜ {N} {md ∷ mds} rewrite localStatePreservation-broadcastMsgsᶜ {N} {mds} = refl

  localStatePreservation-∉-↑∗ : ∀ {N N′ : GlobalState} {ps : List Party} {p : Party} →
      p ∉ ps
    → _ ⊢ N —[ ps ]↑→∗ N′
    → N′ .states ⁉ p ≡ N .states ⁉ p
  localStatePreservation-∉-↑∗ = {!!}

  hasState⇔-↑ : ∀ {N N′ : GlobalState} {p p′ : Party} →
      _ ⊢ N —[ p′ ]↑→ N′
    → p hasStateIn N ⇔ p hasStateIn N′
  hasState⇔-↑ = {!!}

  hasState⇔-↑∗ : ∀ {N N′ N″ : GlobalState} {ps : List Party} {p : Party} →
      _ ⊢ N —[ ps ]↑→∗ N′
    → _ ⊢ N′ —[ p ]↑→ N″
    → p hasStateIn N ⇔ p hasStateIn N″
  hasState⇔-↑∗         []          ts = hasState⇔-↑ ts
  hasState⇔-↑∗ {p = p} (ts′ ∷ ts*) ts = ⇔-trans (hasState⇔-↑ {p = p} ts′) (hasState⇔-↑∗ ts* ts)

  hasState⇔-↝⋆ :  ∀ {N N′ : GlobalState} {p : Party} →
      N ↝⋆ N′
    → p hasStateIn N ⇔ p hasStateIn N′
  hasState⇔-↝⋆ = {!!}

  localStatePreservation-∈-↑∗ : ∀ {N N′ N″ : GlobalState} {p : Party} →
      N₀ ↝⋆ N
    → _ ⊢ N —[ N .execOrder ]↑→∗ N′
    → _ ⊢ N —[ p ]↑→ N″
    → N′ .states ⁉ p ≡ N″ .states ⁉ p
  localStatePreservation-∈-↑∗ = {!!}

  localStatePreservation-↓∗ : ∀ {N N′ N″ : GlobalState} {p : Party} →
      N₀ ↝⋆ N
    → _ ⊢ N —[ N .execOrder ]↓→∗ N′
    → _ ⊢ N —[ p ]↓→ N″
    → N′ .states ⁉ p ≡ N″ .states ⁉ p
  localStatePreservation-↓∗ = {!!}

  localStatePrev-↓ :  ∀ {N N′ : GlobalState} {p : Party} →
      p hasStateIn N′
    → _ ⊢ N —[ p ]↓→ N′
    → p hasStateIn N
  localStatePrev-↓ = {!!}

allPartiesHaveLocalState : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → L.All.All (_hasStateIn N) (N .execOrder)
allPartiesHaveLocalState = {!!}

hasState⇔∈parties₀ : ∀ {N : GlobalState} {p : Party} →
    N₀ ↝⋆ N
  → p hasStateIn N ⇔ p ∈ parties₀
hasState⇔∈parties₀ = {!!}

hasState⇒∈execOrder : ∀ {N : GlobalState} {p : Party} →
    N₀ ↝⋆ N
  → p hasStateIn N
  → p ∈ N .execOrder
hasState⇒∈execOrder = {!!}
