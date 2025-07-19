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
open import Protocol.TreeType ⦃ params ⦄
open import Protocol.Message ⦃ params ⦄
open import Protocol.Network ⦃ params ⦄; open Envelope
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Prelude.STS.Properties using (—[]→∗⇒—[]→∗ʳ; —[]→∗ʳ⇒—[]→∗; —[∷ʳ]→∗-split; —[[]]→∗ʳ⇒≡)
open import Prelude.AssocList.Properties.Ext using (set-⁉; set-⁉-¬)
open import Data.List.Membership.Propositional.Properties.Ext using (∈-∷ʳ-≢⁻)
open import Data.List.Relation.Unary.AllPairs.Properties.Ext using (headʳ)
open import Data.List.Relation.Unary.Unique.Propositional.Properties.Ext using (Unique[xs∷ʳx]⇒x∉xs)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∈-resp-↭)
open import Data.List.Relation.Binary.Permutation.Propositional using (↭-sym)
open import Data.Maybe.Properties.Ext using (Is-just⇒to-witness)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using (≢-sym)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Function.Properties.Equivalence using (⇔-isEquivalence)
open import Function.Properties.Equivalence.Ext using (⊤⇎⊥)
open IsEquivalence {ℓ = 0ℓ} ⇔-isEquivalence renaming (trans to ⇔-trans) hiding (refl; sym)

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
--    → N₁ .clock ≡ N₁′ .clock
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
  localStatePreservation-∉-↓∗ = {!!}

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
