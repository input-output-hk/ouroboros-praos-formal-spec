open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Base.Network
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.Network ⦃ params ⦄; open Envelope
open import Protocol.Message ⦃ params ⦄
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Prelude.STS.Properties using (—[]→∗⇒—[]→∗ʳ)
open import Data.List.Membership.Propositional.Properties.Ext using (∉-∷ʳ⁻)
open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_ ; ≡ˢ-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (map⁺)
open import Data.List.Relation.Binary.BagAndSetEquality using (↭⇒∼bag; bag-=⇒)
open import Function.Base using (∣_⟩-_)

messagesAfterTickPreservation : ∀ (N : GlobalState) →
  L.map msg (tick N .messages) ≡ L.map msg (N .messages)
messagesAfterTickPreservation N
  rewrite
    sym $ L.map-∘ {g = msg} {f = decreaseDelay} (N .messages)
    = refl

messagesAfterPermutationPreservation : ∀ {N : GlobalState} {envelopes : List Envelope} →
    N .messages ↭ envelopes
  → L.map msg envelopes ≡ˢ L.map msg (N .messages)
messagesAfterPermutationPreservation π = ≡ˢ-sym $ bag-=⇒ $ ↭⇒∼bag $ map⁺ msg π

opaque

  unfolding honestMsgsDelivery

  immediateMessagesPreservation-∉-↓∗ : ∀ {N N′ : GlobalState} {ps : List Party} {p : Party} →
      p ∉ ps
    → _ ⊢ N —[ ps ]↓→∗ N′
    → immediateMsgs p N′ ≡ immediateMsgs p N
  immediateMessagesPreservation-∉-↓∗ = ∣ flip immediateMessagesPreservation-∉-↓∗ʳ ⟩- —[]→∗⇒—[]→∗ʳ
    where
      immediateMessagesPreservation-∉-↓∗ʳ : ∀ {N N′ : GlobalState} {ps : List Party} {p : Party} →
          _ ⊢ N —[ ps ]↓→∗ʳ N′
        → p ∉ ps
        → immediateMsgs p N′ ≡ immediateMsgs p N
      immediateMessagesPreservation-∉-↓∗ʳ [] _ = refl
      immediateMessagesPreservation-∉-↓∗ʳ {N} {N′} {ps} {p} (_∷ʳ_ {is = ps′} {i = p′} {s′ = N″} {eq = eq}
        N—[ps′]↓→∗ʳN″ N″↝[p′]↓N′) p∉ps = goal N″↝[p′]↓N′
        where
          p∉ps′∷ʳp′ : p ∉ ps′ L.∷ʳ p′
          p∉ps′∷ʳp′ rewrite eq = p∉ps

          ih : p ∉ ps′ → immediateMsgs p N″ ≡ immediateMsgs p N
          ih = immediateMessagesPreservation-∉-↓∗ʳ N—[ps′]↓→∗ʳN″

          [≢𝟘,p′] : List Envelope → List Envelope
          [≢𝟘,p′] = L.filter ¿ ¬_ ∘ flip Immediate p′ ¿¹

          goal* : ∀ es* → p ≢ p′ → L.filter ¿ flip Immediate p ¿¹ ([≢𝟘,p′] es*) ≡ L.filter ¿ flip Immediate p ¿¹ es*
          goal* [] _ = refl
          goal* (e ∷ es) p≢p′
            with e .cd ≟ 𝟘 | e .rcv ≟ p′
          ... | no eϕ≢𝟘    | _
            rewrite L.filter-reject ¿ flip Immediate p ¿¹ {x = e} {xs = [≢𝟘,p′] es} (dec-de-morgan₂ (inj₁ eϕ≢𝟘))
              = goal* es p≢p′
          ... | yes eϕ≡𝟘   | yes eᵣ≡p′
              with e .rcv ≟ p
          ...   | yes eᵣ≡p = contradiction (trans (sym eᵣ≡p) eᵣ≡p′) p≢p′
          ...   | no _     = goal* es p≢p′
          goal* (e ∷ es) p≢p′
              | yes eϕ≡𝟘   | no eᵣ≢p′
              with e .rcv ≟ p
          ...   | yes eᵣ≡p
                    rewrite
                      eϕ≡𝟘
                    | L.filter-accept ¿ flip Immediate p ¿¹ {x = e} {xs = [≢𝟘,p′] es} (eϕ≡𝟘 , eᵣ≡p)
                      = cong (e ∷_) $ goal* es p≢p′
          ...   | no eᵣ≢p
                    rewrite
                      eϕ≡𝟘
                    | L.filter-reject ¿ flip Immediate p ¿¹ {x = e} {xs = [≢𝟘,p′] es} (dec-de-morgan₂ (inj₂ eᵣ≢p))
                      = goal* es p≢p′

          goal : _ ⊢ N″ —[ p′ ]↓→ N′ → immediateMsgs p N′ ≡ immediateMsgs p N
          goal N″↝[p′]↓N′ with ∉-∷ʳ⁻ p∉ps′∷ʳp′
          ... | p≢p′ , p∉ps′ with N″↝[p′]↓N′
          ...   | unknownParty↓ _    = ih p∉ps′
          ...   | honestParty↓  _ _  rewrite sym $ ih p∉ps′ = goal* (N″ .messages) p≢p′
          ...   | corruptParty↓ _ _  with
             processMsgsᶜ
               (fetchNewMsgs p′ N″ .proj₁)
               (fetchNewMsgs p′ N″ .proj₂ .clock)
               (fetchNewMsgs p′ N″ .proj₂ .history)
               (fetchNewMsgs p′ N″ .proj₂ .messages)
               (fetchNewMsgs p′ N″ .proj₂ .advState)
          ... | newMds , _ = goalᶜ newMds
            where
              Nᶜ : List (Message × DelayMap) → GlobalState
              Nᶜ mds = broadcastMsgsᶜ mds (removeImmediateMsgs p′ N″)

              goalᶜ : ∀ (mds* : List (Message × DelayMap)) →
                L.filter ¿ flip Immediate p ¿¹ (Nᶜ mds* .messages)
                ≡
                L.filter ¿ flip Immediate p ¿¹ (N .messages)
              goalᶜ [] rewrite sym $ ih p∉ps′ = goal* (N″ .messages) p≢p′
              goalᶜ ((m , φ) ∷ mds)
                rewrite
                  L.filter-++
                    ¿ flip Immediate p ¿¹
                    (L.map (λ party → ⦅ m , party , φ party .value ⦆) (Nᶜ mds .execOrder))
                    (Nᶜ mds .messages)
                | goalᶜ mds
                  = goalᶜ′ (Nᶜ mds .execOrder)
                where
                  goalᶜ′ : ∀ ps* →
                    L.filter ¿ flip Immediate p ¿¹ (L.map (λ party → ⦅ m , party , φ party .value ⦆) ps*)
                    ++
                    L.filter ¿ flip Immediate p ¿¹ (N .messages)
                    ≡
                    L.filter ¿ flip Immediate p ¿¹ (N .messages)
                  goalᶜ′ [] = refl
                  goalᶜ′ (p* ∷ ps*) with φ p*
                  ... | 𝟙 , _ = goalᶜ′ ps*
                  ... | 𝟚 , _ = goalᶜ′ ps*
