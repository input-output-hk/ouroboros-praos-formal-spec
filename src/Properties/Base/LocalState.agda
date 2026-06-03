{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled

open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Base.LocalState
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Properties.Base.Network ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.ExecutionOrder ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.Time ⦃ params ⦄ ⦃ assumptions ⦄
open import Protocol.Prelude
open import Protocol.Crypto ⦃ params ⦄ using (Hashable); open Hashable ⦃ ... ⦄
open import Protocol.Block ⦃ params ⦄
open import Protocol.Chain ⦃ params ⦄
open import Protocol.Tree ⦃ params ⦄
open import Protocol.Message ⦃ params ⦄
open import Protocol.Network ⦃ params ⦄; open Envelope
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Prelude.STS.Properties using (—[]→∗⇒—[]→∗ʳ; —[]→∗ʳ⇒—[]→∗; —[∷ʳ]→∗-split; —[[]]→∗ʳ⇒≡)
open import Prelude.AssocList.Properties.Ext using (set-⁉; set-⁉-¬; map-just⇔∈)
open import Data.List.Membership.Propositional.Properties.Ext using (∈-∷ʳ-≢⁻; ∈-∷ʳ⁻; ∉-∷ʳ⁻)
open import Data.List.Relation.Unary.AllPairs.Properties.Ext using (headʳ)
open import Data.List.Relation.Unary.Unique.Propositional.Properties.Ext using (Unique[xs∷ʳx]⇒x∉xs)
open import Data.List.Relation.Binary.Permutation.Propositional using (↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∈-resp-↭; map⁺; All-resp-↭; Any-resp-↭)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties.Ext using (filter-↭)
open import Data.Maybe.Properties.Ext using (Is-just⇒to-witness)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using (≢-sym)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Ext using (Starʳ)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.Ext using (Star⇒Starʳ)
open import Function.Base using (∣_⟩-_)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Function.Construct.Symmetry using (⇔-sym)
open import Function.Properties.Equivalence using (⇔-isEquivalence)
open import Function.Properties.Equivalence.Ext using (⊤⇎⊥)
open IsEquivalence {ℓ = 0ℓ} ⇔-isEquivalence renaming (refl to ⇔-refl; trans to ⇔-trans) hiding (sym)

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

  unfolding honestMsgsDelivery corruptMsgsDelivery honestBlockMaking

  localStatePreservation-broadcastMsgsʰ : ∀ {N : GlobalState} {ms : List Message} →
    broadcastMsgsʰ ms N .states ≡ N .states
  localStatePreservation-broadcastMsgsʰ {N} {[]} = refl
  localStatePreservation-broadcastMsgsʰ {N} {m ∷ ms} = localStatePreservation-broadcastMsgsʰ {N} {ms}

  localStatePreservation-broadcastMsgsᶜ : ∀ {N : GlobalState} {mds : List (Message × DelayMap)} →
    broadcastMsgsᶜ mds N .states ≡ N .states
  localStatePreservation-broadcastMsgsᶜ {_} {[]} = refl
  localStatePreservation-broadcastMsgsᶜ {N} {md ∷ mds} rewrite localStatePreservation-broadcastMsgsᶜ {N} {mds} = refl

  localStatePreservation-↓² : ∀ {N₁ N₁′ N₂ N₂′ : GlobalState} {p : Party} →
      Honest p
    → _ ⊢ N₁  —[ p ]↓→ N₂
    → _ ⊢ N₁′ —[ p ]↓→ N₂′
    → N₁ .states ⁉ p ≡ N₁′ .states ⁉ p
    → immediateMsgs p N₁ ≡ immediateMsgs p N₁′
    → N₂ .states ⁉ p ≡ N₂′ .states ⁉ p
  localStatePreservation-↓² hp (corruptParty↓ _ cp) _ _ _
    = contradiction hp $ corrupt⇒¬honest cp
  localStatePreservation-↓² hp _ (corruptParty↓ _ cp) _ _
    = contradiction hp $ corrupt⇒¬honest cp
  localStatePreservation-↓² _ (unknownParty↓ _) (unknownParty↓ _) eq _
    rewrite eq = refl
  localStatePreservation-↓² _ (unknownParty↓ π) (honestParty↓ π′ _) eq _
    rewrite eq = contradiction π (subst (_≢ nothing) (sym π′) λ ())
  localStatePreservation-↓² _  (honestParty↓ π _) (unknownParty↓ π′) eq _
    rewrite eq = contradiction π′ (subst (_≢ nothing) (sym π) λ ())
  localStatePreservation-↓² {N₁} {N₁′} {p = p} _ (honestParty↓ {ls = ls}  π _) (honestParty↓ π′ _) eq 𝟘seq
    rewrite sym eq | sym 𝟘seq | M.just-injective (trans (sym π′) π)
      | set-⁉ (N₁ .states) p (L.foldr (λ m ls″ → addBlock ls″ (projBlock m)) ls (map msg (immediateMsgs p N₁)))
      | set-⁉ (N₁′ .states) p (L.foldr (λ m ls″ → addBlock ls″ (projBlock m)) ls (map msg (immediateMsgs p N₁)))
      = refl

  localStatePreservation-↑² : ∀ {N₁ N₁′ N₂ N₂′ : GlobalState} {p : Party} →
      Honest p
    → _ ⊢ N₁  —[ p ]↑→ N₂
    → _ ⊢ N₁′ —[ p ]↑→ N₂′
    → N₁ .states ⁉ p ≡ N₁′ .states ⁉ p
    → N₁ .clock ≡ N₁′ .clock
    → N₂ .states ⁉ p ≡ N₂′ .states ⁉ p
  localStatePreservation-↑² hp (corruptParty↑ _ cp) _ _ _
    = contradiction hp $ corrupt⇒¬honest cp
  localStatePreservation-↑² hp _ (corruptParty↑ _ cp) _  _
    = contradiction hp $ corrupt⇒¬honest cp
  localStatePreservation-↑² _ (unknownParty↑ _) (unknownParty↑ _) eq _
    rewrite eq = refl
  localStatePreservation-↑² _ (unknownParty↑ π) (honestParty↑ π′ _) eq _
    rewrite eq = contradiction π (subst (_≢ nothing) (sym π′) λ ())
  localStatePreservation-↑² _  (honestParty↑ π _) (unknownParty↑ π′) eq _
    rewrite eq = contradiction π′ (subst (_≢ nothing) (sym π) λ ())
  localStatePreservation-↑² {N₁} {N₁′} {p = p} _ (honestParty↑ {ls = ls}  π _) (honestParty↑ π′ _) eq ceq
    rewrite sym eq | sym ceq | M.just-injective (trans (sym π′) π)
    with
        nb ← mkBlock (hash (tip (bestChain (N₁ .clock ∸ 1) (ls .tree)))) (N₁ .clock) (txSelection (N₁ .clock) p) p
      | Params.winnerᵈ params {p} {N₁ .clock}
  ... | ⁇ (no _)
          rewrite set-⁉ (N₁ .states) p ls | set-⁉ (N₁′ .states) p ls = refl
  ... | ⁇ (yes _)
          rewrite set-⁉ (N₁ .states) p (addBlock ls nb) | set-⁉ (N₁′ .states) p (addBlock ls nb) = refl

  localStatePreservation-∉-↓∗ : ∀ {N N′ : GlobalState} {ps : List Party} {p : Party} →
      p ∉ ps
    → _ ⊢ N —[ ps ]↓→∗ N′
    → N′ .states ⁉ p ≡ N .states ⁉ p
  localStatePreservation-∉-↓∗ {ps = ps} = ∣ flip (localStatePreservation-∉-↓∗ʳ (reverseView ps)) ⟩- —[]→∗⇒—[]→∗ʳ
    where
      open import Data.List.Reverse

      localStatePreservation-∉-↓∗ʳ : ∀ {N N′ : GlobalState} {ps : List Party} {p : Party} →
          Reverse ps
        → _ ⊢ N —[ ps ]↓→∗ʳ N′
        → p ∉ ps
        → N′ .states ⁉ p ≡ N .states ⁉ p
      localStatePreservation-∉-↓∗ʳ [] N—[ps]↓→∗ʳN′ _ rewrite sym $ —[[]]→∗ʳ⇒≡ N—[ps]↓→∗ʳN′ = refl
      localStatePreservation-∉-↓∗ʳ {N} {N′} {_} {p} (ps′ ∶ ps′r ∶ʳ p′) N—[ps′∷ʳp′]↓→∗ʳN′ p∉ps′∷ʳp′
        with —[∷ʳ]→∗-split (—[]→∗ʳ⇒—[]→∗ N—[ps′∷ʳp′]↓→∗ʳN′) | ∉-∷ʳ⁻ p∉ps′∷ʳp′
      ... | N″ , N—[ps′]↓→∗N″ , N″—[p′]↓→N′ | p≢p′ , p∉ps′ =  goal N″—[p′]↓→N′
        where
          ih : N″ .states ⁉ p ≡ N .states ⁉ p
          ih = localStatePreservation-∉-↓∗ʳ ps′r (—[]→∗⇒—[]→∗ʳ N—[ps′]↓→∗N″) p∉ps′

          goal : _ ⊢ N″ —[ p′ ]↓→ N′ → N′ .states ⁉ p ≡ N .states ⁉ p
          goal (unknownParty↓ _) = ih
          goal (corruptParty↓ _ _)
            rewrite
              localStatePreservation-broadcastMsgsᶜ
                {fetchNewMsgs p′ N″ .proj₂}
                {processMsgsᶜ
                  (fetchNewMsgs p′ N″ .proj₁)
                  (fetchNewMsgs p′ N″ .proj₂ .clock)
                  (fetchNewMsgs p′ N″ .proj₂ .history)
                  (fetchNewMsgs p′ N″ .proj₂ .messages)
                  (fetchNewMsgs p′ N″ .proj₂ .advState)
                  .proj₁
                 }
              = ih
          goal (honestParty↓ {ls = ls} lsN″p′ hp′) = trans goal′ ih
            where
              goal′ : honestMsgsDelivery p′ ls N″ .states ⁉ p ≡ N″ .states ⁉ p
              goal′ with p ≟ p′
              ... | yes p≡p′ = contradiction p≡p′ p≢p′
              ... | no _
                   rewrite
                     set-⁉-¬ (N″ .states) p′ p
                       (L.foldr (λ m ls″ → addBlock ls″ (projBlock m)) ls (map msg (immediateMsgs p′ N″))) (≢-sym p≢p′)
                     = refl

  localStatePreservation-∉-↑∗ : ∀ {N N′ : GlobalState} {ps : List Party} {p : Party} →
      p ∉ ps
    → _ ⊢ N —[ ps ]↑→∗ N′
    → N′ .states ⁉ p ≡ N .states ⁉ p
  localStatePreservation-∉-↑∗ {ps = ps} = ∣ flip (localStatePreservation-∉-↑∗ʳ (reverseView ps)) ⟩- —[]→∗⇒—[]→∗ʳ
    where
      open import Data.List.Reverse

      localStatePreservation-∉-↑∗ʳ : ∀ {N N′ : GlobalState} {ps : List Party} {p : Party} →
          Reverse ps
        → _ ⊢ N —[ ps ]↑→∗ʳ N′
        → p ∉ ps
        → N′ .states ⁉ p ≡ N .states ⁉ p
      localStatePreservation-∉-↑∗ʳ [] N—[ps]↑→∗ʳN′ _ rewrite sym $ —[[]]→∗ʳ⇒≡ N—[ps]↑→∗ʳN′ = refl
      localStatePreservation-∉-↑∗ʳ {N} {N′} {_} {p} (ps′ ∶ ps′r ∶ʳ p′) N—[ps′∷ʳp′]↑→∗ʳN′ p∉ps′∷ʳp′
        with —[∷ʳ]→∗-split (—[]→∗ʳ⇒—[]→∗ N—[ps′∷ʳp′]↑→∗ʳN′) | ∉-∷ʳ⁻ p∉ps′∷ʳp′
      ... | N″ , N—[ps′]↑→∗N″ , N″—[p′]↑→N′ | p≢p′ , p∉ps′ = goal N″—[p′]↑→N′
        where
          ih : N″ .states ⁉ p ≡ N .states ⁉ p
          ih = localStatePreservation-∉-↑∗ʳ ps′r (—[]→∗⇒—[]→∗ʳ N—[ps′]↑→∗N″) p∉ps′

          goal : _ ⊢ N″ —[ p′ ]↑→ N′ → N′ .states ⁉ p ≡ N .states ⁉ p
          goal (unknownParty↑ _) = ih
          goal (corruptParty↑ _ _)
            with makeBlockᶜ (N″ .clock) (N″ .history) (N″ .messages) (N″ .advState)
          ...   | newMds , _ rewrite localStatePreservation-broadcastMsgsᶜ {N″} {newMds} = ih
          goal (honestParty↑ {ls = ls} _ _)
            with makeBlockʰ (N″ .clock) (txSelection (N″ .clock) p′) p′ ls
          ...   | newMsgs , newLs rewrite localStatePreservation-broadcastMsgsʰ {updateLocalState p′ newLs N″} {newMsgs}
              with p ≟ p′
          ...     | yes p≡p′ = contradiction p≡p′ p≢p′
          ...     | no _ rewrite set-⁉-¬ (N″ .states) p′ p newLs (≢-sym p≢p′) = ih

  hasState⇔-↓∗ : ∀ {N N′ : GlobalState} {ps : List Party} {p : Party} →
      _ ⊢ N —[ ps ]↓→∗ N′
    → p hasStateIn N ⇔ p hasStateIn N′
  hasState⇔-↓∗ = {!!}

  hasState⇔-↑ : ∀ {N N′ : GlobalState} {p p′ : Party} →
      _ ⊢ N —[ p′ ]↑→ N′
    → p hasStateIn N ⇔ p hasStateIn N′
  hasState⇔-↑ (unknownParty↑ _) = ⇔-refl
  hasState⇔-↑ {N} {_} {p} {p′} (honestParty↑ {ls = ls} lsp′N _)
    with makeBlockʰ (N .clock) (txSelection (N .clock) p′) p′ ls
  ...   | newMsgs , newLs rewrite localStatePreservation-broadcastMsgsʰ {updateLocalState p′ newLs N} {newMsgs}
      with p ≟ p′
  ...     | yes p≡p′
    rewrite sym p≡p′ | set-⁉ (N .states) p newLs | lsp′N
      = mk⇔ (const $ M.Any.just tt) (const $ M.Any.just tt)
  ...     | no p≢p′ rewrite set-⁉-¬ (N .states) p′ p newLs (≢-sym p≢p′) = ⇔-refl
  hasState⇔-↑ {N} (corruptParty↑ _ _)
    rewrite
      localStatePreservation-broadcastMsgsᶜ
        {N} {makeBlockᶜ (N .clock) (N .history) (N .messages) (N .advState) .proj₁} = ⇔-refl

  hasState⇔-↑∗ : ∀ {N N′ : GlobalState} {ps : List Party} {p : Party} →
      _ ⊢ N —[ ps ]↑→∗ N′
    → p hasStateIn N ⇔ p hasStateIn N′
  hasState⇔-↑∗ [] = ⇔-refl
  hasState⇔-↑∗ {p = p} (ts ∷ ts*) = ⇔-trans (hasState⇔-↑ {p = p} ts) (hasState⇔-↑∗ ts*)

  hasState⇔-↑∗-↑ : ∀ {N N′ N″ : GlobalState} {ps : List Party} {p : Party} →
      _ ⊢ N —[ ps ]↑→∗ N′
    → _ ⊢ N′ —[ p ]↑→ N″
    → p hasStateIn N ⇔ p hasStateIn N″
  hasState⇔-↑∗-↑         []          ts = hasState⇔-↑ ts
  hasState⇔-↑∗-↑ {p = p} (ts′ ∷ ts*) ts = ⇔-trans (hasState⇔-↑ {p = p} ts′) (hasState⇔-↑∗-↑ ts* ts)

  hasState⇔-↝⋆ :  ∀ {N N′ : GlobalState} {p : Party} →
      N ↝⋆ N′
    → p hasStateIn N ⇔ p hasStateIn N′
  hasState⇔-↝⋆ {N} {N′} {p} = hasState⇔-↝⋆ʳ ∘ Star⇒Starʳ
    where
      open RTC; open Starʳ
      hasState⇔-↝⋆ʳ : ∀ {N′ : GlobalState} → N ↝⋆ʳ N′ → p hasStateIn N ⇔ p hasStateIn N′
      hasState⇔-↝⋆ʳ εʳ = ⇔-refl
      hasState⇔-↝⋆ʳ {N′} (_◅ʳ_ {j = N″} N↝⋆ʳN″ N″↝N′) = goal N″↝N′
        where
          ih : p hasStateIn N ⇔ p hasStateIn N″
          ih = hasState⇔-↝⋆ʳ N↝⋆ʳN″

          goal : N″ ↝ N′ → p hasStateIn N ⇔ p hasStateIn N′
          goal (deliverMsgs {N′ = N‴} N″Ready N″—[eoN″]↓→∗N‴) = goal* $ —[]→∗⇒—[]→∗ʳ N″—[eoN″]↓→∗N‴
            where
              goal* : ∀ {N* ps} → _ ⊢ N″ —[ ps ]↓→∗ʳ N* → p hasStateIn N ⇔ p hasStateIn N*
              goal* [] = ih
              goal* {N*} (_∷ʳ_ {is = ps*} {i = p*} {s′ = N°} N″—[ps*]↓→∗ʳN° N°↝[p*]↓N*) = step* N°↝[p*]↓N*
                where
                  ih* : p hasStateIn N ⇔ p hasStateIn N°
                  ih* = goal* N″—[ps*]↓→∗ʳN°

                  step* : _ ⊢ N° —[ p* ]↓→ N* → p hasStateIn N ⇔ p hasStateIn N*
                  step* (unknownParty↓ _) = ih*
                  step* (honestParty↓ {ls = ls} lsN°p* hp*) = ⇔-trans ih* step-hp*
                    where
                      step-hp* : p hasStateIn N° ⇔ p hasStateIn (honestMsgsDelivery p* ls N°)
                      step-hp* with p ≟ p*
                      ... | yes p≡p*
                        rewrite
                            sym p≡p*
                          | set-⁉
                              (N° .states)
                              p
                              (L.foldr (λ m ls″ → addBlock ls″ (projBlock m)) ls (L.map msg (immediateMsgs p N°)))
                          | lsN°p*
                          = mk⇔ (const $ M.Any.just tt) (const $ M.Any.just tt)
                      ... | no p≢p*
                        rewrite
                          set-⁉-¬
                            (N° .states)
                            p*
                            p
                            (L.foldr (λ m ls″ → addBlock ls″ (projBlock m)) ls (L.map msg (immediateMsgs p* N°)))
                            (≢-sym p≢p*)
                          = ⇔-refl
                  step* (corruptParty↓ _ _)
                    rewrite
                      localStatePreservation-broadcastMsgsᶜ
                        {fetchNewMsgs p* N° .proj₂}
                        {processMsgsᶜ
                          (fetchNewMsgs p* N° .proj₁)
                          (fetchNewMsgs p* N° .proj₂ .clock)
                          (fetchNewMsgs p* N° .proj₂ .history)
                          (fetchNewMsgs p* N° .proj₂ .messages)
                          (fetchNewMsgs p* N° .proj₂ .advState)
                          .proj₁
                         }
                      = ih*
          goal (makeBlock {N″} {N‴} N″MsgsDelivered N″—[eoN″]↑→∗N‴) = goal* $ —[]→∗⇒—[]→∗ʳ N″—[eoN″]↑→∗N‴
            where
              goal* : ∀ {N* ps} → _ ⊢ N″ —[ ps ]↑→∗ʳ N* → p hasStateIn N ⇔ p hasStateIn N*
              goal* [] = ih
              goal* {N*} (_∷ʳ_ {is = ps*} {i = p*} {s′ = N°} N″—[ps*]↑→∗ʳN° N°↝[p*]↑N*) = step* N°↝[p*]↑N*
                where
                  ih* : p hasStateIn N ⇔ p hasStateIn N°
                  ih* = goal* N″—[ps*]↑→∗ʳN°

                  step* : _ ⊢ N° —[ p* ]↑→ N* → p hasStateIn N ⇔ p hasStateIn N*
                  step* (unknownParty↑ _) = ih*
                  step* (honestParty↑ {ls = ls} lsN°p* hp*) = ⇔-trans ih* step-hp*
                    where
                      step-hp* : p hasStateIn N° ⇔ p hasStateIn (honestBlockMaking p* ls N°)
                      step-hp* with makeBlockʰ (N° .clock) (txSelection (N° .clock) p*) p* ls
                      ... | newMsgs , newLs
                        rewrite
                          localStatePreservation-broadcastMsgsʰ {updateLocalState p* newLs N°} {newMsgs}
                        with p ≟ p*
                      ...   | yes p≡p*
                          rewrite sym p≡p* | set-⁉ (N° .states) p newLs | lsN°p*
                            = mk⇔ (const $ M.Any.just tt) (const $ M.Any.just tt)
                      ...   | no p≢p*
                          rewrite set-⁉-¬ (N° .states) p* p newLs (≢-sym p≢p*) = ⇔-refl
                  step* (corruptParty↑ _ _)
                    rewrite
                      localStatePreservation-broadcastMsgsᶜ
                        {N°} {makeBlockᶜ (N° .clock) (N° .history) (N° .messages) (N° .advState) .proj₁}
                      = ih*
          goal (advanceRound   _) = ih
          goal (permuteParties _) = ih
          goal (permuteMsgs    _) = ih

  localStatePrev-↓ :  ∀ {N N′ : GlobalState} {p : Party} →
      p hasStateIn N′
    → _ ⊢ N —[ p ]↓→ N′
    → p hasStateIn N
  localStatePrev-↓     pHasLsInN′ (unknownParty↓ _)                = pHasLsInN′
  localStatePrev-↓ {N} _          (honestParty↓  {ls = ls} lspN _) = hasStateInAltDef {N} .Equivalence.to (ls , lspN)
  localStatePrev-↓ {N} _          (corruptParty↓ {ls = ls} lspN _) = hasStateInAltDef {N} .Equivalence.to (ls , lspN)

hasState⇔∈parties₀ : ∀ {N : GlobalState} {p : Party} →
    N₀ ↝⋆ N
  → p hasStateIn N ⇔ p ∈ parties₀
hasState⇔∈parties₀ {N} {p} N₀↝⋆N = ⇔-trans (⇔-sym $ hasState⇔-↝⋆ N₀↝⋆N) (map-just⇔∈ parties₀ p (it .def))

allPartiesHaveLocalState : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → L.All.All (_hasStateIn N) (N .execOrder)
allPartiesHaveLocalState N₀↝⋆N =
  All-resp-↭
    (↭-sym $ execOrder-↭-parties₀ N₀↝⋆N)
    (L.All.tabulate $ hasState⇔∈parties₀ N₀↝⋆N .Equivalence.from)

hasState⇒∈execOrder : ∀ {N : GlobalState} {p : Party} →
    N₀ ↝⋆ N
  → p hasStateIn N
  → p ∈ N .execOrder
hasState⇒∈execOrder N₀↝⋆N pHasLsInN =
  Any-resp-↭
    (execOrderPreservation-↭ N₀↝⋆N)
    (hasState⇔∈parties₀ N₀↝⋆N .Equivalence.to pHasLsInN)

opaque

  unfolding honestBlockMaking corruptBlockMaking

  blocksDeliveredInEvolution-↑′ : ∀ {N N′ : GlobalState} {p : Party} →
      _ ⊢ N —[ p ]↑→ N′
    → ∀ {p′ : Party} {d : Delay} →
        blocksDeliveredIn p′ d N ⊆ˢ blocksDeliveredIn p′ d N′
  blocksDeliveredInEvolution-↑′ {N} {N′} {p} ts {p′} {d} with ts
  ... | unknownParty↑ _ = L.SubS.⊆-refl
  ... | corruptParty↑ _ _
    with makeBlockᶜ (N .clock) (N .history) (N .messages) (N .advState)
  ...   | newMds , _ = goal newMds
    where
      goal : ∀ (mds* : List (Message × DelayMap)) →
        blocksDeliveredIn p′ d N ⊆ˢ blocksDeliveredIn p′ d (broadcastMsgsᶜ mds* N)
      goal [] = L.SubS.⊆-refl
      goal ((m , ϕ) ∷ mds*) = goal′
        where
          Nᶜ : GlobalState
          Nᶜ = broadcastMsgsᶜ mds* N

          dlv? : Decidable¹ λ e → DeliveredIn e p′ d
          dlv? = λ e → ¿ DeliveredIn e ¿² p′ d

          mkenv : Party → Envelope
          mkenv = λ party → ⦅ m , party , ϕ party .value ⦆

          goal′ : blocksDeliveredIn p′ d N ⊆ˢ L.map (projBlock ∘ msg) (filter dlv? (L.map mkenv (Nᶜ .execOrder) ++ Nᶜ .messages))
          goal′
            rewrite
              L.filter-++ dlv? (map mkenv (Nᶜ .execOrder)) (Nᶜ .messages)
            | L.map-++ (projBlock ∘ msg) (filter dlv? (map mkenv (Nᶜ .execOrder))) (filter dlv? (Nᶜ .messages))
              = L.SubS.⊆-trans (goal mds*) $ L.SubS.xs⊆ys++xs _ _
  blocksDeliveredInEvolution-↑′ {N} {N′} {p} ts {p′} {d}
      | honestParty↑ {ls = ls} lspN hp with Params.winnerᵈ params {p} {N .clock}
  ...   | ⁇ (no  _) = L.SubS.⊆-refl
  ...   | ⁇ (yes _) = goal
    where
      nb : Block
      nb = mkBlock (hash (tip (bestChain (N .clock ∸ 1) (ls .tree)))) (N .clock) (txSelection (N .clock) p) p

      dlv? : Decidable¹ λ e → DeliveredIn e p′ d
      dlv? = λ e → ¿ DeliveredIn e ¿² p′ d

      mkenv : Party → Envelope
      mkenv = λ party → ⦅ newBlock nb , party , 𝟙 ⦆

      goal :
        blocksDeliveredIn p′ d N
        ⊆ˢ
        map (projBlock ∘ msg) (filter dlv? (map mkenv (N .execOrder) ++ N .messages))
      goal
       rewrite
         L.filter-++ dlv? (map mkenv (N .execOrder)) (N .messages)
       | L.map-++ (projBlock ∘ msg) (filter dlv? (map mkenv (N .execOrder))) (filter dlv? (N .messages))
         = L.SubS.xs⊆ys++xs _ _

blocksDeliveredInEvolution-↑∗ : ∀ {N N′ : GlobalState} {ps : List Party} →
    _ ⊢ N —[ ps ]↑→∗ N′
  → ∀ {p′ : Party} {d : Delay} →
      blocksDeliveredIn p′ d N ⊆ˢ blocksDeliveredIn p′ d N′
blocksDeliveredInEvolution-↑∗ []         = L.SubS.⊆-refl
blocksDeliveredInEvolution-↑∗ (ts ∷ ts*) = L.SubS.⊆-trans (blocksDeliveredInEvolution-↑′ ts) (blocksDeliveredInEvolution-↑∗ ts*)

opaque

  unfolding honestMsgsDelivery honestBlockMaking corruptBlockMaking

  localStatePreservation-↓∗ : ∀ {N N′ N″ : GlobalState} {p : Party} →
      N₀ ↝⋆ N
    → _ ⊢ N —[ N .execOrder ]↓→∗ N′
    → _ ⊢ N —[ p ]↓→ N″
    → N′ .states ⁉ p ≡ N″ .states ⁉ p
  localStatePreservation-↓∗ {N} {N′} {N″} {p} N₀↝⋆N N—[eoN]↓→∗N′ N—[p]↓→N″ =
    localStatePreservation-↓∗ʳ (reverseView (N .execOrder)) NUniq pHasInN⇔p∈eoN N—[p]↓→N″ (—[]→∗⇒—[]→∗ʳ N—[eoN]↓→∗N′)
    where
      pHasInN⇔p∈eoN : p hasStateIn N ⇔ p ∈ N .execOrder
      pHasInN⇔p∈eoN =
        mk⇔
          (∈-resp-↭ ps₀↭eoN ∘ pHasInN⇔p∈ps₀ .Equivalence.to)
          (pHasInN⇔p∈ps₀ .Equivalence.from ∘ ∈-resp-↭ (↭-sym ps₀↭eoN))
        where
          pHasInN⇔p∈ps₀ : p hasStateIn N ⇔ p ∈ parties₀
          pHasInN⇔p∈ps₀ = hasState⇔∈parties₀ N₀↝⋆N

          ps₀↭eoN : parties₀ ↭ N .execOrder
          ps₀↭eoN = execOrderPreservation-↭ N₀↝⋆N

      NUniq : Unique (N .execOrder)
      NUniq = execOrderUniqueness N₀↝⋆N

      open import Data.List.Reverse

      ⊤⇔isJust  : ∀ {ls : LocalState} → ⊤ ⇔ M.Is-just (just ls)
      ⊤⇔isJust = M.Any.just-equivalence

      p∈[]⇔⊥ : p ∈ [] ⇔ ⊥
      p∈[]⇔⊥ = mk⇔ (λ ()) λ ()

      ⊤⇔⊥ : ∀ {ls : LocalState} → M.Is-just (just ls) ⇔ p ∈ [] → ⊤ ⇔ ⊥
      ⊤⇔⊥ isJust⇔p∈[] = ⇔-trans (⇔-trans ⊤⇔isJust isJust⇔p∈[]) p∈[]⇔⊥

      localStatePreservation-↓∗ʳ : ∀ {N* ps} →
          Reverse ps
        → Unique ps
        → p hasStateIn N ⇔ p ∈ ps
        → _ ⊢ N —[ p ]↓→ N″
        → _ ⊢ N —[ ps ]↓→∗ʳ N*
        → N* .states ⁉ p ≡ N″ .states ⁉ p
      localStatePreservation-↓∗ʳ [] _ isJust⇔p∈[] N—[p]↓→N″ N—[ps]↓→∗ʳN* rewrite sym $ —[[]]→∗ʳ⇒≡ N—[ps]↓→∗ʳN*
        with N—[p]↓→N″
      ... | unknownParty↓ _ = refl
      ... | honestParty↓ _ _
          with N .states ⁉ p
      ...   | just ls = contradiction (⊤⇔⊥ isJust⇔p∈[]) ⊤⇎⊥
      localStatePreservation-↓∗ʳ [] _ isJust⇔p∈[] _ _
          | corruptParty↓ _ _
          with N .states ⁉ p
      ...   | just ls = contradiction (⊤⇔⊥ isJust⇔p∈[]) ⊤⇎⊥
      localStatePreservation-↓∗ʳ {N* = N*} (ps′ ∶ ps′r ∶ʳ p′) ps′∷ʳp′Uniq pHasInN⇔p∈ps′∷ʳp′ N—[p]↓→N″ N—[ps′∷ʳp′]↓→∗ʳN*
        with —[∷ʳ]→∗-split (—[]→∗ʳ⇒—[]→∗ N—[ps′∷ʳp′]↓→∗ʳN*)
      ... | N‴ , N—[ps′]↓→∗N‴ , N‴—[p′]↓→N*
          with p ≟ p′
      ...   | yes p≡p′ rewrite p≡p′ = goal N‴—[p′]↓→N* N—[p]↓→N″
        where
          p′∉ps′ : p′ ∉ ps′
          p′∉ps′ = Unique[xs∷ʳx]⇒x∉xs ps′∷ʳp′Uniq

          lsp′N‴≡lsp′N : N‴ .states ⁉ p′ ≡ N .states ⁉ p′
          lsp′N‴≡lsp′N = localStatePreservation-∉-↓∗ p′∉ps′ N—[ps′]↓→∗N‴

          p′HasInN : p′ hasStateIn N
          p′HasInN = pHasInN⇔p∈ps′∷ʳp′ .Equivalence.from $ L.Mem.∈-++⁺ʳ ps′ {[ p′ ]} (here refl)

          goal : _ ⊢ N‴ —[ p′ ]↓→ N* → _ ⊢ N —[ p′ ]↓→ N″ → N* .states ⁉ p′ ≡ N″ .states ⁉ p′
          goal (unknownParty↓ lsp′N*≡◇) _ = contradiction lsp′N*≡◇ lsp′N*≢◇
            where
              lsp′N*≢◇ : N* .states ⁉ p′ ≢ nothing
              lsp′N*≢◇ with hasStateInAltDef {N} .Equivalence.from p′HasInN
              ... | _ , lspN rewrite sym lsp′N‴≡lsp′N | lspN = flip contradiction λ ()
          goal (honestParty↓ {ls = ls} lsp′N‴ hp′) N—[p′]↓→N″ =
            localStatePreservation-↓²
              hp′ N‴—[p′]↓→N* N—[p′]↓→N″ lsp′N‴≡lsp′N (immediateMessagesPreservation-∉-↓∗ p′∉ps′ N—[ps′]↓→∗N‴)
          goal (corruptParty↓ {ls = ls} lsp′N‴ cp′) N—[p′]↓→N″
            rewrite
              localStatePreservation-broadcastMsgsᶜ
                {fetchNewMsgs p′ N‴ .proj₂}
                {processMsgsᶜ
                  (fetchNewMsgs p′ N‴ .proj₁)
                  (fetchNewMsgs p′ N‴ .proj₂ .clock)
                  (fetchNewMsgs p′ N‴ .proj₂ .history)
                  (fetchNewMsgs p′ N‴ .proj₂ .messages)
                  (fetchNewMsgs p′ N‴ .proj₂ .advState)
                  .proj₁
                 }
              with N—[p′]↓→N″
          ... | unknownParty↓ _ = lsp′N‴≡lsp′N
          ... | honestParty↓ _ hp′ = contradiction hp′ $ corrupt⇒¬honest cp′
          ... | corruptParty↓ _ _
            rewrite
              localStatePreservation-broadcastMsgsᶜ
                {fetchNewMsgs p′ N .proj₂}
                {processMsgsᶜ
                  (fetchNewMsgs p′ N .proj₁)
                  (fetchNewMsgs p′ N .proj₂ .clock)
                  (fetchNewMsgs p′ N .proj₂ .history)
                  (fetchNewMsgs p′ N .proj₂ .messages)
                  (fetchNewMsgs p′ N .proj₂ .advState)
                  .proj₁
                 }
                 = lsp′N‴≡lsp′N
      ...   | no p≢p′ = goal N‴—[p′]↓→N*
        where
          ps′Uniq : Unique ps′
          ps′Uniq = headʳ ps′∷ʳp′Uniq

          p′∉ps′ : p′ ∉ ps′
          p′∉ps′ = Unique[xs∷ʳx]⇒x∉xs ps′∷ʳp′Uniq

          lsp′N‴≡lsp′N : N‴ .states ⁉ p′ ≡ N .states ⁉ p′
          lsp′N‴≡lsp′N = localStatePreservation-∉-↓∗ p′∉ps′ N—[ps′]↓→∗N‴

          pHasInN⇔p∈ps′ : p hasStateIn N ⇔ p ∈ ps′
          pHasInN⇔p∈ps′ =
            mk⇔
              (λ pHasInN → ∈-∷ʳ-≢⁻ (pHasInN⇔p∈ps′∷ʳp′ .Equivalence.to pHasInN) p≢p′)
              (λ p∈ps′ → pHasInN⇔p∈ps′∷ʳp′ .Equivalence.from $ L.Mem.∈-++⁺ˡ p∈ps′)

          ih : ∀ {N*} → _ ⊢ N —[ ps′ ]↓→∗ N* → N* .states ⁉ p ≡ N″ .states ⁉ p
          ih = localStatePreservation-↓∗ʳ ps′r ps′Uniq pHasInN⇔p∈ps′ N—[p]↓→N″ ∘ —[]→∗⇒—[]→∗ʳ

          goal : _ ⊢ N‴ —[ p′ ]↓→ N* → N* .states ⁉ p ≡ N″ .states ⁉ p
          goal (unknownParty↓ _) = ih N—[ps′]↓→∗N‴
          goal (honestParty↓ {ls = ls} _ _)
            with p ≟ p′
          ...   | yes p≡p′ = contradiction p≡p′ p≢p′
          ...   | no _
                   rewrite
                     set-⁉-¬ (N‴ .states) p′ p
                       (L.foldr (λ m ls″ → addBlock ls″ (projBlock m)) ls (map msg (immediateMsgs p′ N‴))) (≢-sym p≢p′)
                     = ih N—[ps′]↓→∗N‴
          goal (corruptParty↓ _ _)
            rewrite
              localStatePreservation-broadcastMsgsᶜ
                {fetchNewMsgs p′ N‴ .proj₂}
                {processMsgsᶜ
                  (fetchNewMsgs p′ N‴ .proj₁)
                  (fetchNewMsgs p′ N‴ .proj₂ .clock)
                  (fetchNewMsgs p′ N‴ .proj₂ .history)
                  (fetchNewMsgs p′ N‴ .proj₂ .messages)
                  (fetchNewMsgs p′ N‴ .proj₂ .advState)
                  .proj₁
                 }
                 = ih N—[ps′]↓→∗N‴

  localStatePreservation-∈-↑∗ : ∀ {N N′ N″ : GlobalState} {p : Party} →
      N₀ ↝⋆ N
    → _ ⊢ N —[ N .execOrder ]↑→∗ N′
    → _ ⊢ N —[ p ]↑→ N″
    → N′ .states ⁉ p ≡ N″ .states ⁉ p
  localStatePreservation-∈-↑∗ {N} {N′} {N″} {p} N₀↝⋆N N—[eoN]↑→∗N′ N—[p]↑→N″ =
    localStatePreservation-∈-↑∗ʳ (reverseView (N .execOrder)) NUniq pHasInN⇔p∈eoN N—[p]↑→N″ (—[]→∗⇒—[]→∗ʳ N—[eoN]↑→∗N′)
    where
      pHasInN⇔p∈eoN : p hasStateIn N ⇔ p ∈ N .execOrder
      pHasInN⇔p∈eoN =
        mk⇔
          (∈-resp-↭ ps₀↭eoN ∘ pHasInN⇔p∈ps₀ .Equivalence.to)
          (pHasInN⇔p∈ps₀ .Equivalence.from ∘ ∈-resp-↭ (↭-sym ps₀↭eoN))
        where
          pHasInN⇔p∈ps₀ : p hasStateIn N ⇔ p ∈ parties₀
          pHasInN⇔p∈ps₀ = hasState⇔∈parties₀ N₀↝⋆N

          ps₀↭eoN : parties₀ ↭ N .execOrder
          ps₀↭eoN = execOrderPreservation-↭ N₀↝⋆N

      NUniq : Unique (N .execOrder)
      NUniq = execOrderUniqueness N₀↝⋆N

      open import Data.List.Reverse

      ⊤⇔isJust  : ∀ {ls : LocalState} → ⊤ ⇔ M.Is-just (just ls)
      ⊤⇔isJust = M.Any.just-equivalence

      p∈[]⇔⊥ : p ∈ [] ⇔ ⊥
      p∈[]⇔⊥ = mk⇔ (λ ()) λ ()

      ⊤⇔⊥ : ∀ {ls : LocalState} → M.Is-just (just ls) ⇔ p ∈ [] → ⊤ ⇔ ⊥
      ⊤⇔⊥ isJust⇔p∈[] = ⇔-trans (⇔-trans ⊤⇔isJust isJust⇔p∈[]) p∈[]⇔⊥

      localStatePreservation-∈-↑∗ʳ : ∀ {N* ps} →
          Reverse ps
        → Unique ps
        → p hasStateIn N ⇔ p ∈ ps
        → _ ⊢ N —[ p ]↑→ N″
        → _ ⊢ N —[ ps ]↑→∗ʳ N*
        → N* .states ⁉ p ≡ N″ .states ⁉ p
      localStatePreservation-∈-↑∗ʳ [] _ isJust⇔p∈[] N—[p]↑→N″ N—[ps]↑→∗ʳN* rewrite sym $ —[[]]→∗ʳ⇒≡ N—[ps]↑→∗ʳN*
        with N—[p]↑→N″
      ... | unknownParty↑ _ = refl
      ... | honestParty↑ _ _
          with N .states ⁉ p
      ...   | just ls = contradiction (⊤⇔⊥ isJust⇔p∈[]) ⊤⇎⊥
      localStatePreservation-∈-↑∗ʳ [] _ isJust⇔p∈[] _ _
          | corruptParty↑ _ _
          with N .states ⁉ p
      ...   | just ls = contradiction (⊤⇔⊥ isJust⇔p∈[]) ⊤⇎⊥
      localStatePreservation-∈-↑∗ʳ {N* = N*} (ps′ ∶ ps′r ∶ʳ p′) ps′∷ʳp′Uniq pHasInN⇔p∈ps′∷ʳp′ N—[p]↑→N″ N—[ps′∷ʳp′]↑→∗ʳN*
        with —[∷ʳ]→∗-split (—[]→∗ʳ⇒—[]→∗ N—[ps′∷ʳp′]↑→∗ʳN*)
      ... | N‴ , N—[ps′]↑→∗N‴ , N‴—[p′]↑→N*
          with p ≟ p′
      ...   | yes p≡p′ rewrite p≡p′ = goal N‴—[p′]↑→N* N—[p]↑→N″
        where
          p′∉ps′ : p′ ∉ ps′
          p′∉ps′ = Unique[xs∷ʳx]⇒x∉xs ps′∷ʳp′Uniq

          lsp′N‴≡lsp′N : N‴ .states ⁉ p′ ≡ N .states ⁉ p′
          lsp′N‴≡lsp′N = localStatePreservation-∉-↑∗ p′∉ps′ N—[ps′]↑→∗N‴

          p′HasInN : p′ hasStateIn N
          p′HasInN = pHasInN⇔p∈ps′∷ʳp′ .Equivalence.from $ L.Mem.∈-++⁺ʳ ps′ {[ p′ ]} (here refl)

          goal : _ ⊢ N‴ —[ p′ ]↑→ N* → _ ⊢ N —[ p′ ]↑→ N″ → N* .states ⁉ p′ ≡ N″ .states ⁉ p′
          goal (unknownParty↑ lsp′N*≡◇) _ = contradiction lsp′N*≡◇ lsp′N*≢◇
            where
              lsp′N*≢◇ : N* .states ⁉ p′ ≢ nothing
              lsp′N*≢◇ with hasStateInAltDef {N} .Equivalence.from p′HasInN
              ... | _ , lspN rewrite sym lsp′N‴≡lsp′N | lspN = flip contradiction λ ()
          goal (honestParty↑ {ls = ls} lsp′N‴ hp′) N—[p′]↑→N″
            = localStatePreservation-↑² hp′ N‴—[p′]↑→N* N—[p′]↑→N″ lsp′N‴≡lsp′N (clockPreservation-↑∗ N—[ps′]↑→∗N‴)
          goal (corruptParty↑ {ls = ls} lsp′N‴ cp′) N—[p′]↑→N″
            rewrite
              localStatePreservation-broadcastMsgsᶜ
                {N‴} {makeBlockᶜ (clock N‴) (history N‴) (messages N‴) (advState N‴) .proj₁}
            with N—[p′]↑→N″
          ... | unknownParty↑ _ = lsp′N‴≡lsp′N
          ... | honestParty↑ _ hp′ = contradiction hp′ $ corrupt⇒¬honest cp′
          ... | corruptParty↑ _ _
              rewrite
                localStatePreservation-broadcastMsgsᶜ
                  {N} {makeBlockᶜ (clock N) (history N) (messages N) (advState N) .proj₁} = lsp′N‴≡lsp′N
      ...   | no p≢p′ = goal N‴—[p′]↑→N*
        where
          ps′Uniq : Unique ps′
          ps′Uniq = headʳ ps′∷ʳp′Uniq

          p′∉ps′ : p′ ∉ ps′
          p′∉ps′ = Unique[xs∷ʳx]⇒x∉xs ps′∷ʳp′Uniq

          lsp′N‴≡lsp′N : N‴ .states ⁉ p′ ≡ N .states ⁉ p′
          lsp′N‴≡lsp′N = localStatePreservation-∉-↑∗ p′∉ps′ N—[ps′]↑→∗N‴

          pHasInN⇔p∈ps′ : p hasStateIn N ⇔ p ∈ ps′
          pHasInN⇔p∈ps′ =
            mk⇔
              (λ pHasInN → ∈-∷ʳ-≢⁻ (pHasInN⇔p∈ps′∷ʳp′ .Equivalence.to pHasInN) p≢p′)
              (λ p∈ps′ → pHasInN⇔p∈ps′∷ʳp′ .Equivalence.from $ L.Mem.∈-++⁺ˡ p∈ps′)

          ih : ∀ {N*} → _ ⊢ N —[ ps′ ]↑→∗ N* → N* .states ⁉ p ≡ N″ .states ⁉ p
          ih = localStatePreservation-∈-↑∗ʳ ps′r ps′Uniq pHasInN⇔p∈ps′ N—[p]↑→N″ ∘ —[]→∗⇒—[]→∗ʳ

          goal : _ ⊢ N‴ —[ p′ ]↑→ N* → N* .states ⁉ p ≡ N″ .states ⁉ p
          goal (unknownParty↑ _) = ih N—[ps′]↑→∗N‴
          goal (honestParty↑ {ls = ls} _ _)
            with makeBlockʰ (N‴ .clock) (txSelection (N‴ .clock) p′) p′ ls
          ... | newMsgs , newLs rewrite localStatePreservation-broadcastMsgsʰ {updateLocalState p′ newLs N‴} {newMsgs}
              with p ≟ p′
          ...   | yes p≡p′ = contradiction p≡p′ p≢p′
          ...   | no _ rewrite set-⁉-¬ (N‴ .states) p′ p newLs (≢-sym p≢p′) = ih N—[ps′]↑→∗N‴
          goal (corruptParty↑ _ _)
            with makeBlockᶜ (clock N‴) (history N‴) (messages N‴) (advState N‴)
          ... | newMds , _ rewrite localStatePreservation-broadcastMsgsᶜ {N‴} {newMds} = ih N—[ps′]↑→∗N‴

  blocksDeliveredInEvolution-↑ : ∀ {N N′ N″ : GlobalState} {p : Party} →
      N₀ ↝⋆ N
    → _ ⊢ N —[ N .execOrder ]↑→∗ N″
    → _ ⊢ N —[ p ]↑→ N′
    → Honest p
    → p ∈ N .execOrder
    → ∀ {p′ : Party} {d : Delay} →
        blocksDeliveredIn p′ d N′ ⊆ˢ blocksDeliveredIn p′ d N″
  blocksDeliveredInEvolution-↑ {N} {N′} {N″} {p} N₀↝⋆N N—[eoN]↑→∗N″ N—[p]↑→N′ hp p∈eoN {p′} {d} =
    blocksDeliveredInEvolution-↑ʳ (reverseView (N .execOrder)) eoN! p∈eoN (—[]→∗⇒—[]→∗ʳ N—[eoN]↑→∗N″)
    where
      ¬cp : ¬ Corrupt p
      ¬cp = honest⇒¬corrupt hp

      eoN! : Unique (N .execOrder)
      eoN! = execOrderUniqueness N₀↝⋆N

      open import Data.List.Reverse

      blocksDeliveredInEvolution-↑ʳ : ∀ {N* ps} →
          Reverse ps
        → Unique ps
        → p ∈ ps
        → _ ⊢ N —[ ps ]↑→∗ʳ N*
        → blocksDeliveredIn p′ d N′ ⊆ˢ blocksDeliveredIn p′ d N*
      blocksDeliveredInEvolution-↑ʳ {N*} (ps* ∶ ps*r ∶ʳ p*) [ps*∷ʳp*]! p∈[ps*∷ʳp*] N—[ps*∷ʳp*]↑→∗ʳN*
        with —[∷ʳ]→∗-split $ —[]→∗ʳ⇒—[]→∗ N—[ps*∷ʳp*]↑→∗ʳN*
      ... | N‴ , N—[ps*]↑→∗N‴ , N‴—[p*]↑→N* = goal
        where
          ps*! : Unique ps*
          ps*! = headʳ [ps*∷ʳp*]!

          p*∉ps* : p* ∉ ps*
          p*∉ps* = Unique[xs∷ʳx]⇒x∉xs [ps*∷ʳp*]!

          lsp*N≡lsp*N‴ : N .states ⁉ p* ≡ N‴ .states ⁉ p*
          lsp*N≡lsp*N‴ = sym $ localStatePreservation-∉-↑∗ p*∉ps* N—[ps*]↑→∗N‴

          ih : p ∈ ps* → blocksDeliveredIn p′ d N′ ⊆ˢ blocksDeliveredIn p′ d N‴
          ih p∈ps* = blocksDeliveredInEvolution-↑ʳ ps*r ps*! p∈ps* (—[]→∗⇒—[]→∗ʳ N—[ps*]↑→∗N‴)

          goal : blocksDeliveredIn p′ d N′ ⊆ˢ blocksDeliveredIn p′ d N*
          goal with ∈-∷ʳ⁻ p∈[ps*∷ʳp*]
          ... | inj₁ p∈ps* = L.SubS.⊆-trans (ih p∈ps*) (blocksDeliveredInEvolution-↑′ N‴—[p*]↑→N*)
          ... | inj₂ p≡p*  = goal-p≡p* N‴—[p*]↑→N*
            where
              N—[p*]↑→N′ : _ ⊢ N —[ p* ]↑→ N′
              N—[p*]↑→N′ rewrite sym p≡p* = N—[p]↑→N′

              goal-p≡p* : _ ⊢ N‴ —[ p* ]↑→ N* → blocksDeliveredIn p′ d N′ ⊆ˢ blocksDeliveredIn p′ d N*
              goal-p≡p* N‴—[p*]↑→N* with N—[p*]↑→N′
              ... | unknownParty↑ _     = blocksDeliveredInEvolution-↑∗ (—[]→∗ʳ⇒—[]→∗ N—[ps*∷ʳp*]↑→∗ʳN*)
              ... | corruptParty↑ _ cp* = contradiction (subst Corrupt (sym p≡p*) cp*) ¬cp
              ... | honestParty↑ {ls = ls} lsp*N hp* with N‴—[p*]↑→N*
              ...   | unknownParty↑ lsp*N*≡◇ = contradiction lsp*N*≡◇ lsp*N*≢◇
                where
                  lsp*N*≢◇ : N* .states ⁉ p* ≢ nothing
                  lsp*N*≢◇ rewrite sym lsp*N≡lsp*N‴ | lsp*N = λ ()
              ...   | corruptParty↑ _ cp* = contradiction (subst Corrupt (sym p≡p*) cp*) ¬cp
              ...   | honestParty↑ {ls = ls′} ls′p*N‴ _ rewrite clockPreservation-↑∗ N—[ps*]↑→∗N‴
                        with Params.winnerᵈ params {p*} {N .clock}
              ...     | ⁇ (no  _) = blocksDeliveredInEvolution-↑∗ N—[ps*]↑→∗N‴
              ...     | ⁇ (yes _) = goal-wp*
                where
                  nb : LocalState → Block
                  nb ls = mkBlock (hash (tip (bestChain (N .clock ∸ 1) (ls .tree)))) (N .clock) (txSelection (N .clock) p*) p*

                  ls′≡ls : ls′ ≡ ls
                  ls′≡ls = sym $ M.just-injective $ trans (sym lsp*N) ls′p*N
                    where
                      ls′p*N : N .states ⁉ p* ≡ just ls′
                      ls′p*N rewrite lsp*N≡lsp*N‴ = ls′p*N‴

                  dlv? : Decidable¹ λ e → DeliveredIn e p′ d
                  dlv? = λ e → ¿ DeliveredIn e ¿² p′ d

                  mkenv : LocalState → Party → Envelope
                  mkenv ls = λ party → ⦅ newBlock (nb ls) , party , 𝟙 ⦆

                  goal-wp* :
                    map (projBlock ∘ msg) (filter dlv? (map (mkenv ls) (N .execOrder) ++ N .messages))
                    ⊆ˢ
                    map (projBlock ∘ msg) (filter dlv? (map (mkenv ls′) (N‴ .execOrder) ++ N‴ .messages))
                  goal-wp*
                    rewrite
                      ls′≡ls
                    | L.filter-++ dlv? (map (mkenv ls) (N .execOrder)) (N .messages)
                    | L.map-++ (projBlock ∘ msg) (filter dlv? (map (mkenv ls) (N .execOrder))) (filter dlv? (N .messages))
                    | L.filter-++ dlv? (map (mkenv ls) (N‴ .execOrder)) (N‴ .messages)
                    | L.map-++ (projBlock ∘ msg) (filter dlv? (map (mkenv ls) (N‴ .execOrder))) (filter dlv? (N‴ .messages))
                      = L.SubS.++⁺
                          (∈-resp-↭ $ map⁺ _ $ filter-↭ _ $ map⁺ _ $ execOrderPreservation-↭-↑∗ N—[ps*]↑→∗N‴)
                          (blocksDeliveredInEvolution-↑∗ N—[ps*]↑→∗N‴)
