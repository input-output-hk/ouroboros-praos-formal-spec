{-# OPTIONS --allow-unsolved-metas #-} -- FIXME: Remove later

open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot; slot₀; Honesty)
open import Protocol.Params using (Params)
open import Protocol.Block
open import Protocol.Crypto using (Hashable)
open import Protocol.Message
open import Protocol.Network
open import Protocol.TreeType
open import Data.Nat using (s≤s; z≤n)
open import Data.Nat.Properties using (<⇒≤)
open import Relation.Nullary.Decidable using (_because_)
open import Relation.Nullary.Reflects using (ofʸ)


open Params ⦃ ... ⦄
open Honesty
open Hashable ⦃ ... ⦄
open Envelope


module Properties.Liveness
  ⦃ _ : Params ⦄
  ⦃ _ : Block ⦄
  ⦃ _ : Hashable Block ⦄
  ⦃ _ : Default Block ⦄
  {T : Type} ⦃ TreeType-T : TreeType T ⦄
  {AdversarialState : Type}
  {honestyOf : Party → Honesty}
  {txSelection : Slot → Party → Txs}
  {processMsgsᶜ :
      List Message
    → Slot
    → List Message
    → List Envelope
    → AdversarialState
    → List (Message × DelayMap) × AdversarialState}
  {makeBlockᶜ :
      Slot
    → List Message
    → List Envelope
    → AdversarialState
    → List (Message × DelayMap) × AdversarialState}
  {adversarialState₀ : AdversarialState}
  {parties₀ : List Party} -- TODO: Use numParties instead
  where


open import Protocol.Semantics {T} {AdversarialState} {honestyOf} {txSelection} {processMsgsᶜ} {makeBlockᶜ}
open import Properties.Common {T} {AdversarialState} {honestyOf} {txSelection} {processMsgsᶜ} {makeBlockᶜ} {adversarialState₀} {parties₀}

open import Data.List.Membership.DecPropositional {A = Block} _≟_ renaming (_∈_ to _∈ˢ_)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties


lemma-permutation : ∀ {N : GlobalState} →
  states (L.foldr executeMsgsDelivery N (N .execOrder)) ↭ N .states
lemma-permutation = {!!}

lemma2-permutation : ∀ {N : GlobalState} → clock
      (L.foldr executeMsgsDelivery N
       (N .execOrder))
      ≡ N .clock
lemma2-permutation = {!!}

knowledgePropagation : ∀ {N₁ N₂ : GlobalState} {p₁ p₂ : Party} {t₁ t₂ : T} →
    honestyOf p₁ ≡ honest
  → honestyOf p₂ ≡ honest
  → p₁ ∈ parties₀
  → p₂ ∈ parties₀
  → N₀ ↝⋆ N₁
  → N₁ ↝⋆ N₂
  → (p₁ , ⟪ t₁ ⟫) ∈ N₁ .states
  → (p₂ , ⟪ t₂ ⟫) ∈ N₂ .states
  → N₁ .progress ≡ ready
  → N₂ .progress ≡ msgsDelivered
  → N₁ .clock ≡ N₂ .clock
  → allBlocks t₁ ⊆ˢ allBlocks t₂
knowledgePropagation h₁ h₂ p₁∈p p₂∈p N₀↝⋆N ∎ p₁∈N p₂∈N r d _ = {!!}
  -- let x = trans (sym r) d in ⊥-elim (ready≢delivered x) -- contradiction ready and delivered
knowledgePropagation h₁ h₂ p₁∈p p₂∈p N₀↝⋆N₁ (N₁↝⋆N ↣ permuteParties _) p₁∈N₁ p₂∈N₂ refl refl refl =
  knowledgePropagation h₁ h₂ p₁∈p p₂∈p N₀↝⋆N₁ N₁↝⋆N p₁∈N₁ p₂∈N₂ refl refl refl
knowledgePropagation h₁ h₂ p₁∈p p₂∈p N₀↝⋆N₁ (N₁↝⋆N ↣ permuteMsgs _) p₁∈N₁ p₂∈N₂ refl refl refl =
  knowledgePropagation h₁ h₂ p₁∈p p₂∈p N₀↝⋆N₁ N₁↝⋆N p₁∈N₁ p₂∈N₂ refl refl refl
knowledgePropagation {N₁} {N₂} {p₁} {p₂} {t₁} {t₂} h₁ h₂ p₁∈p p₂∈p N₀↝⋆N₁ (N₁↝⋆N ↣ deliverMsgs {N} refl) p₁∈N₁ p₂∈N₂ refl refl refl {x} b
  with L.foldr executeMsgsDelivery N (N .execOrder) | executeMsgsDelivery p₂ N
... | xx | yy = {!!}

{-
  with x ∈? allBlocks t₂
... | yes p = p
... | no ¬p = {!!}
-}



-- Theorem 1 (Chain Growth) --------------------------------------------------

module _ {isLucky   : Slot → Bool}
         {isLucky?  : (s : Slot) → Dec (isLucky s ≡ true)}
         {N₁ N₂     : GlobalState}
         {p₁ p₂     : Party}
         {t₁ t₂     : T}
         {sl₁ sl₂   : Slot}
  where


  -- For s₁ sₙ : ℕ, s₁ ≤ sₙ, return list [s₁, suc s₁, ..., sₙ].
  rangeTo : (s₁ sₙ : Slot) → s₁ ≤ sₙ → List Slot
  rangeTo 0 0 s₁≤sₙ = [ 0 ]
  rangeTo s₁ (suc sₙ) s₁≤sₙ with s₁ ≟ sₙ
  ... | yes _ = s₁ ∷ [ suc sₙ ]
  ... | no ¬p = rangeAux s₁ sₙ ¬p [ suc sₙ ]
    where
    rangeAux : (s₁ s₂ : Slot) → ¬ (s₁ ≡ s₂) → List Slot → List Slot
    rangeAux _       0   _ acc = acc
    rangeAux s₁ (suc s₂) p acc with s₁ ≟ s₂
    ... | yes _ = s₁ ∷ (suc s₂) ∷ acc
    ... | no ¬p = rangeAux s₁ s₂ ¬p ((suc s₂) ∷ acc)

  -- test rangeTo
  _ : rangeTo 5 7 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) ≡ 5 ∷ 6 ∷ [ 7 ]
  _ = refl


  -- Return list of lucky numbers between s₁ and sₙ (inclusive)
  luckyBetween : (s₁ sₙ : Slot) → (s₁ ≤ sₙ) → List Slot
  luckyBetween s₁ sₙ s₁≤sₙ = filter isLucky? (rangeTo s₁ sₙ s₁≤sₙ)

  {-
  Let
    N₀, N₁, N₂ : GlobalState,
    p₁, p₂ : Party,
    sl₁, sl₂ : Slot and
    w : ℕ.
    If
      + N₀ ⇓ N₁,
      + N₁ ⇓ N₂,
      + p₁ is a party in N₁ with tree t₁,
      + p₂ is a party in N₂ with tree t₂,
      + the round of N₁ is sl₁,
      + the round of N₂ is sl₂, and
      + ∃ at least w lucky slots between N₁ and N₂ then

    Then
      | bestChain (sl₁ - 1) t₁ | + w ≤ | bestChain (sl₂ − 1) t₂ |.
  -}

  Theorem1-ChainGrowth :  {w         : ℕ}  -- min number of lucky slots between N₁ and N₂
    →                     honestyOf p₁ ≡ honest
    →                     honestyOf p₂ ≡ honest
    →                     {N₁≤N₂ : N₁ .clock ≤ N₂ .clock}
    →                     p₁ ∈ parties₀
    →                     p₂ ∈ parties₀
    →                     N₀ ↝⋆ N₁
    →                     N₁ ↝⋆ N₂
    →                     (p₁ , ⟪ t₁ ⟫) ∈ N₁ .states
    →                     (p₂ , ⟪ t₂ ⟫) ∈ N₂ .states
    →                     N₁ .progress ≡ ready
    →                     N₂ .progress ≡ msgsDelivered
    →                     N₁ .clock ≡ suc sl₁
    →                     N₂ .clock ≡ suc sl₂
    →                     w ≤ length (luckyBetween (N₁ .clock) (N₂ .clock) (N₁≤N₂))
    →                     length (bestChain sl₁ t₁) + w ≤ length (bestChain sl₂ t₂)

  Theorem1-ChainGrowth {0} h₁ h₂ x x₁ x₂ x₃ x₄ x₅ prog₁ prog₂ x₆ x₇ x₈ = goal
    where
    N₁≡N₂ : N₁ .clock ≡ N₂ .clock
    N₁≡N₂ = {!!}

    kp : allBlocks t₁ ⊆ˢ allBlocks t₂
    kp = knowledgePropagation {N₁ = N₁}{N₂} h₁ h₂ x x₁ x₂ x₃ x₄ x₅ prog₁ prog₂ N₁≡N₂

    goal : length (bestChain sl₁ t₁) + 0 ≤ length (bestChain sl₂ t₂)
    goal = {!!}

  Theorem1-ChainGrowth {w = suc w} h₁ h₂ {N₁≤N₂} x x₁ x₂ x₃ x₄ x₅ prog₁ prog₂ x₆ x₇ x₈ = {!!}

{-
  Proof (by induction on the number of lucky slots, w).

  In the induction case we identify the global state N with the lowest slot number sl s.t.,
  N1 ⇓ N, N ⇓ N2, and lucky_slot sl.  In the global state N, we establish that the honest party
  who wins the slot creates a new chain that is strictly longer than any chain of an honest party
  in N₁, as they knew what was there before by Lemma 1.

  We complete the proof by applying the induction hypothesis to N.
-}
