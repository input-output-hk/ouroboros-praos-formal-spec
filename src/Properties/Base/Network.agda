{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled

open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Base.Network
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.Block ⦃ params ⦄
open import Protocol.Network ⦃ params ⦄; open Envelope
open import Protocol.Message ⦃ params ⦄
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Prelude.STS.Properties using (—[]→∗⇒—[]→∗ʳ)
open import Data.List.Relation.Binary.SetEquality using (⊆×⊇⇒≡ˢ)
open import Data.List.Membership.Propositional.Properties.Ext using (∉-∷ʳ⁻; ∉-∷⁻)
open import Data.List.Relation.Unary.Unique.Propositional.Properties using (Unique[x∷xs]⇒x∉xs)
open import Data.List.Relation.Binary.Subset.Propositional.Properties.Ext using (⊆-++-comm)
open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_ ; ≡ˢ-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∈-resp-↭; map⁺)
open import Data.List.Relation.Binary.BagAndSetEquality using (↭⇒∼bag; bag-=⇒)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Ext using (Starʳ)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.Ext using (Star⇒Starʳ; Starʳ⇒Star)
open import Relation.Binary.PropositionalEquality using (≢-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (All-resp-↭)
open import Function.Base using (∣_⟩-_)
open import Data.Fin.Properties.Ext using (pred-≤; pred-injective; >0⇒≢0)

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
                      = cong (e ∷_) $ goal* es p≢p′
          ...   | no eᵣ≢p
                    rewrite
                      eϕ≡𝟘
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

nonImmediateBlocksPreservation : ∀ {p : Party} {N : GlobalState} {d : Delay} →
    d Fi.> (Delay ∋ 𝟘)
  → L.All.All ((Fi._> (Delay ∋ 𝟘)) ∘ cd) (N .messages)
  → blocksDeliveredIn p (Fi.pred d) (record (tick N) { progress = ready }) ≡ blocksDeliveredIn p d N
nonImmediateBlocksPreservation {p} {N} {d} d>𝟘 cds>𝟘 = goal cds>𝟘
  where
    goal : ∀ {es : List Envelope} →
        L.All.All ((Fi._> (Delay ∋ 𝟘)) ∘ cd) es
      → map (projBlock ∘ msg) (L.filter (λ env → ¿ DeliveredIn env ¿² p (Fi.pred d)) (map decreaseDelay es))
        ≡
        map (projBlock ∘ msg) (L.filter (λ env → ¿ DeliveredIn env ¿² p d) es)
    goal {[]} _ = refl
    goal {⦅ m , p′ , φ ⦆ ∷ es} cds>𝟘 with p′ ≟ p | φ ≟ d
    ... | no p′≢p | yes φ≡d
      rewrite
          L.filter-reject (λ env → ¿ DeliveredIn env ¿² p (Fi.pred d)) {⦅ m , p′ , pred φ ⦆} {map decreaseDelay es} (dec-de-morgan₂ (inj₂ p′≢p))
        | dec-yes (pred φ Fi.≟ pred d) (cong pred φ≡d) .proj₂
        | L.filter-reject (λ env → ¿ DeliveredIn env ¿² p d) {⦅ m , p′ , φ ⦆} {es} (dec-de-morgan₂ (inj₂ p′≢p))
        = goal {es} (L.All.tail cds>𝟘)
    ... | no p′≢p | no φ≢d
      rewrite
          L.filter-reject (λ env → ¿ DeliveredIn env ¿² p (Fi.pred d)) {⦅ m , p′ , pred φ ⦆} {map decreaseDelay es} (dec-de-morgan₂ (inj₂ p′≢p))
        | dec-no (pred φ Fi.≟ pred d) (contraposition (pred-injective (>0⇒≢0 $ L.All.head cds>𝟘) (>0⇒≢0 d>𝟘) ) φ≢d)
        | L.filter-reject (λ env → ¿ DeliveredIn env ¿² p d) {⦅ m , p′ , φ ⦆} {es} (dec-de-morgan₂ (inj₂ p′≢p))
        = goal {es} (L.All.tail cds>𝟘)
    ... | yes p′≡p | yes φ≡d
      rewrite
        dec-yes (pred φ Fi.≟ pred d) (cong pred φ≡d) .proj₂
      | L.filter-accept (λ env → ¿ DeliveredIn env ¿² p (Fi.pred d)) {⦅ m , p′ , pred φ ⦆} {map decreaseDelay es} (cong pred φ≡d , p′≡p)
        = cong (projBlock m ∷_) $ goal {es} (L.All.tail cds>𝟘)
    ... | yes p′≡p | no φ≢d
      rewrite
        dec-no (pred φ Fi.≟ pred d) (contraposition (pred-injective (>0⇒≢0 $ L.All.head cds>𝟘) (>0⇒≢0 d>𝟘) ) φ≢d)
      | L.filter-reject (λ env → ¿ DeliveredIn env ¿² p (Fi.pred d)) {⦅ m , p′ , pred φ ⦆} {map decreaseDelay es}
          (dec-de-morgan₂ (inj₁ $ (contraposition (pred-injective (>0⇒≢0 $ L.All.head cds>𝟘) (>0⇒≢0 d>𝟘) ) φ≢d)))
        = goal {es} (L.All.tail cds>𝟘)

no𝟚DelayMessagesAfterTick : ∀ {p : Party} {N : GlobalState} →
    N₀ ↝⋆ N
  → blocksDeliveredIn p 𝟚 (record (tick N) { progress = ready }) ≡ []
no𝟚DelayMessagesAfterTick = {!!}

opaque

  unfolding honestMsgsDelivery corruptMsgsDelivery honestBlockMaking

  messageDelayUpperBound : ∀ {N : GlobalState} →
      N₀ ↝⋆ N
    → L.All.All ((Fi._≤ (Delay ∋ 𝟚)) ∘ cd) (N .messages)
  messageDelayUpperBound = messageDelayUpperBoundʳ ∘ Star⇒Starʳ
    where
      open RTC; open Starʳ
      messageDelayUpperBoundʳ : ∀ {N : GlobalState} →
          N₀ ↝⋆ʳ N
        → L.All.All ((Fi._≤ (Delay ∋ 𝟚)) ∘ cd) (N .messages)
      messageDelayUpperBoundʳ εʳ = []
      messageDelayUpperBoundʳ {N} (_◅ʳ_ {j = N′} N₀↝⋆ʳN′ N′↝N) = goal N′↝N
        where
          ih : L.All.All ((Fi._≤ (Delay ∋ 𝟚)) ∘ cd) (N′ .messages)
          ih = messageDelayUpperBoundʳ N₀↝⋆ʳN′

          goal : N′ ↝ N → L.All.All ((Fi._≤ (Delay ∋ 𝟚)) ∘ cd) (N .messages)
          goal (deliverMsgs {N′ = N″} N′Ready N′—[eoN′]↓→∗N″) = goal* (—[]→∗⇒—[]→∗ʳ N′—[eoN′]↓→∗N″)
            where
              goal* : ∀ {N* ps} →
                  _ ⊢ N′ —[ ps ]↓→∗ʳ N*
                → L.All.All ((Fi._≤ (Delay ∋ 𝟚)) ∘ cd) (N* .messages)
              goal* [] = ih
              goal* {N*} (_∷ʳ_ {is = ps′} {i = p′} {s′ = N‴} {eq = eq} ts⋆ ts) = step ts
                where
                  ih* : L.All.All ((Fi._≤ (Delay ∋ 𝟚)) ∘ cd) (N‴ .messages)
                  ih* = goal* ts⋆

                  step : _ ⊢ N‴ —[ p′ ]↓→ N* → L.All.All ((Fi._≤ (Delay ∋ 𝟚)) ∘ cd) (N* .messages)
                  step (unknownParty↓ _) = ih*
                  step (honestParty↓ _ _) = L.SubS.All-resp-⊇ (L.SubS.filter-⊆ _ _) ih*
                  step (corruptParty↓ _ _) with
                     processMsgsᶜ
                       (fetchNewMsgs p′ N‴ .proj₁)
                       (fetchNewMsgs p′ N‴ .proj₂ .clock)
                       (fetchNewMsgs p′ N‴ .proj₂ .history)
                       (fetchNewMsgs p′ N‴ .proj₂ .messages)
                       (fetchNewMsgs p′ N‴ .proj₂ .advState)
                  ... | newMds , _ = goalᶜ newMds
                    where
                      Nᶜ : List (Message × DelayMap) → GlobalState
                      Nᶜ mds = broadcastMsgsᶜ mds (removeImmediateMsgs p′ N‴)

                      goalᶜ : ∀ (mds* : List (Message × DelayMap)) →
                        L.All.All ((Fi._≤ (Delay ∋ 𝟚)) ∘ cd) (Nᶜ mds* .messages)
                      goalᶜ [] = L.SubS.All-resp-⊇ (L.SubS.filter-⊆ _ _) ih*
                      goalᶜ ((m , φ) ∷ mds) = L.All.++⁺ (goalᶜ-∷ (Nᶜ mds .execOrder)) (goalᶜ mds)
                        where
                          goalᶜ-∷ : ∀ ps* →
                            L.All.All ((Fi._≤ (Delay ∋ 𝟚)) ∘ cd) (L.map (λ party → ⦅ m , party , φ party .value ⦆) ps*)
                          goalᶜ-∷ [] = []
                          goalᶜ-∷ (p* ∷ ps*) with φ p*
                          ... | 𝟙 , _ = Nat.s≤s Nat.z≤n ∷ goalᶜ-∷ ps*
                          ... | 𝟚 , _ = Nat.≤-refl ∷ goalᶜ-∷ ps*
          goal (makeBlock {N′ = N″} N′MsgsDelivered N′—[eoN′]↑→∗N″) = goal* $ —[]→∗⇒—[]→∗ʳ N′—[eoN′]↑→∗N″
            where
              goal* : ∀ {N* ps} →
                  _ ⊢ N′ —[ ps ]↑→∗ʳ N*
                → L.All.All ((Fi._≤ (Delay ∋ 𝟚)) ∘ cd) (N* .messages)
              goal* [] = ih
              goal* {N*} (_∷ʳ_ {is = ps′} {i = p′} {s′ = N‴} {eq = eq} ts⋆ ts) = step ts
                where
                  ih* : L.All.All ((Fi._≤ (Delay ∋ 𝟚)) ∘ cd) (N‴ .messages)
                  ih* = goal* ts⋆

                  step : _ ⊢ N‴ —[ p′ ]↑→ N* → L.All.All ((Fi._≤ (Delay ∋ 𝟚)) ∘ cd) (N* .messages)
                  step (unknownParty↑ _  ) = ih*
                  step (honestParty↑ {ls = ls} _ _) = goalʰ $ mb .proj₁
                    where
                      mb : List Message × LocalState
                      mb = makeBlockʰ (N‴ .clock) (txSelection (N‴ .clock) p′) p′ ls

                      N‴ʰ : List Message → GlobalState
                      N‴ʰ ms = broadcastMsgsʰ ms (updateLocalState p′ (mb .proj₂) N‴)

                      goalʰ : ∀ ms →
                        L.All.All ((Fi._≤ (Delay ∋ 𝟚)) ∘ cd) (N‴ʰ ms .messages)
                      goalʰ [] = ih*
                      goalʰ (m ∷ ms) = L.All.++⁺ (goalʰ-∷ (N‴ʰ ms .execOrder)) (goalʰ ms)
                        where
                          goalʰ-∷ : ∀ ps* → L.All.All ((Fi._≤ (Delay ∋ 𝟚)) ∘ cd) (L.map (λ party → ⦅ m , party , 𝟙 ⦆) ps*)
                          goalʰ-∷ [] = []
                          goalʰ-∷ (p* ∷ ps*) = Nat.s≤s Nat.z≤n ∷ goalʰ-∷ ps*
                  step (corruptParty↑ _ _) = goalᶜ mds
                    where
                      mds : List (Message × DelayMap)
                      mds = makeBlockᶜ (N‴ .clock) (N‴ .history) (N‴ .messages) (N‴ .advState) .proj₁

                      N‴ᶜ : List (Message × DelayMap) → GlobalState
                      N‴ᶜ mds = broadcastMsgsᶜ mds N‴

                      goalᶜ : ∀ mds → L.All.All ((Fi._≤ (Delay ∋ 𝟚)) ∘ cd) (N‴ᶜ mds .messages)
                      goalᶜ [] = ih*
                      goalᶜ ((m , φ) ∷ mds) = L.All.++⁺ (goalᶜ-∷ (N‴ᶜ mds .execOrder)) (goalᶜ mds)
                        where
                          goalᶜ-∷ : ∀ ps* →
                            L.All.All ((Fi._≤ (Delay ∋ 𝟚)) ∘ cd) (L.map (λ party → ⦅ m , party , φ party .value ⦆) ps*)
                          goalᶜ-∷ [] = []
                          goalᶜ-∷ (p* ∷ ps*) with φ p*
                          ... | 𝟙 , _ = Nat.s≤s Nat.z≤n ∷ goalᶜ-∷ ps*
                          ... | 𝟚 , _ = Nat.≤-refl ∷ goalᶜ-∷ ps*
          goal (advanceRound _) = goal* (N′ .messages) ih
            where
              goal* : ∀ ms →
                  L.All.All ((Fi._≤ (Delay ∋ 𝟚)) ∘ cd) ms
                → L.All.All ((Fi._≤ (Delay ∋ 𝟚)) ∘ cd) (L.map decreaseDelay ms)
              goal* [] _ = []
              goal* (m ∷ ms) [≤𝟚][m+ms] =
                Nat.≤-trans (pred-≤ (m .cd)) (Fi.toℕ≤pred[n] (m .cd)) ∷ goal* ms (L.All.tail [≤𝟚][m+ms])
          goal (permuteParties _) = ih
          goal (permuteMsgs msN′↭es) = All-resp-↭ msN′↭es ih

blockDelayUniqueness : ∀ (φ : DelayMap) (m : Message) (p : Party) (ps : List Party) →
    p ∈ ps
  → Unique ps
  → map (projBlock ∘ msg) (filter (λ e′ → ¿ DeliveredIn e′ ¿² p 𝟙) (map (λ party → ⦅ m , party , φ party .value ⦆) ps))
    ++
    map (projBlock ∘ msg) (filter (λ e′ → ¿ DeliveredIn e′ ¿² p 𝟚) (map (λ party → ⦅ m , party , φ party .value ⦆) ps))
    ≡ˢ
    [ projBlock m ]
blockDelayUniqueness _ _ _ [] p∈[] _ = contradiction p∈[] λ ()
blockDelayUniqueness φ m@(newBlock b*) p (p′ ∷ ps) (here p≡p′) [p′+ps]! rewrite p≡p′ with φ p′
... | 𝟙 , _
  rewrite L.filter-accept (λ e′ → ¿ DeliveredIn e′ ¿² p′ 𝟙) {⦅ m , p′ , 𝟙 ⦆} {map (λ p* → ⦅ m , p* , φ p* .value ⦆) ps} (refl , refl) =
    ⊆×⊇⇒≡ˢ ⊆π λ {b} b∈[mᵇ] → here (L.Any.singleton⁻ b∈[mᵇ])
  where
    dlv? : (p* : Party) (d : Delay) → Decidable¹ λ e′ → DeliveredIn e′ p* d
    dlv? p* d e′ = ¿ DeliveredIn e′ ¿² p* d

    mkenv : Party → Envelope
    mkenv p* = ⦅ m , p* , φ p* .value ⦆

    ⊆π : projBlock m
         ∷ (map (λ{ ⦅ m , _ , _ ⦆ → projBlock m }) (filter (dlv? p′ 𝟙) (map mkenv ps))
            ++
            map (λ{ ⦅ m , _ , _ ⦆ → projBlock m }) (filter (dlv? p′ 𝟚) (map mkenv ps)))
         ⊆ˢ
         [ projBlock m ]
    ⊆π {b} (here b≡mᵇ) rewrite b≡mᵇ = here refl
    ⊆π {b} (there b∈𝟙s+𝟚s) = ⊆π* p′∉ps b∈𝟙s+𝟚s
      where
        p′∉ps : p′ ∉ ps
        p′∉ps = Unique[x∷xs]⇒x∉xs [p′+ps]!

        ⊆π* : ∀ {ps*} →
            p′ ∉ ps*
          → b ∈ (map (λ{ ⦅ m , _ , _ ⦆ → projBlock m }) (filter (dlv? p′ 𝟙) (map mkenv ps*))
                 ++
                 map (λ{ ⦅ m , _ , _ ⦆ → projBlock m }) (filter (dlv? p′ 𝟚) (map mkenv ps*)))
          → b ∈ [ projBlock m ]
        ⊆π* {p* ∷ ps*} p′∉p*+ps* b∈𝟙s+𝟚s+p*ₑ with ∉-∷⁻ p′∉p*+ps*
        ... | p′≢p* , p′∉ps*
              rewrite
                L.filter-reject (dlv? p′ 𝟙) {⦅ m , p* , φ p* .value ⦆} {map mkenv ps*} (dec-de-morgan₂ (inj₂ (≢-sym p′≢p*)))
              | L.filter-reject (dlv? p′ 𝟚) {⦅ m , p* , φ p* .value ⦆} {map mkenv ps*} (dec-de-morgan₂ (inj₂ (≢-sym p′≢p*)))
              = ⊆π* {ps*} p′∉ps* b∈𝟙s+𝟚s+p*ₑ

... | 𝟚 , _
  rewrite
    L.filter-accept (λ e′ → ¿ DeliveredIn e′ ¿² p′ 𝟚) {⦅ m , p′ , 𝟚 ⦆} {map (λ p* → ⦅ m , p* , φ p* .value ⦆) ps} (refl , refl) =
      ⊆×⊇⇒≡ˢ
        ⊆π
        λ {b} b∈[mᵇ] →
          subst
            (λ ◆ → b ∈ map (λ{ ⦅ m , _ , _ ⦆ → projBlock m }) (filter (dlv? p′ 𝟙) (map mkenv ps))
                       ++ ◆ ∷ map (λ{ ⦅ m , _ , _ ⦆ → projBlock m }) (filter (dlv? p′ 𝟚) (map mkenv ps)))
            (L.Any.singleton⁻ b∈[mᵇ])
            (L.Mem.∈-insert {v = b} _)
  where
    dlv? : (p* : Party) (d : Delay) → Decidable¹ λ e′ → DeliveredIn e′ p* d
    dlv? p* d e′ = ¿ DeliveredIn e′ ¿² p* d

    mkenv : Party → Envelope
    mkenv p* = ⦅ m , p* , φ p* .value ⦆

    ⊆π : map (λ{ ⦅ m , _ , _ ⦆ → projBlock m }) (filter (dlv? p′ 𝟙) (map mkenv ps))
         ++
         projBlock m ∷ map (λ{ ⦅ m , _ , _ ⦆ → projBlock m }) (filter (dlv? p′ 𝟚) (map mkenv ps))
         ⊆ˢ
         [ projBlock m ]
    ⊆π = L.SubS.⊆-trans (aux _ _ _) ⊆π′
      where
        aux : ∀ (bs bs′ : List Block) (b : Block) → bs ++ b ∷ bs′ ⊆ˢ b ∷ bs ++ bs′
        aux bs bs′ b = let open L.SubS.⊆-Reasoning Block in begin
          bs ++ b ∷ bs′          ≡⟨ L.++-assoc bs _ _ ⟨
          (bs ++ [ b ]) ++ bs′   ⊆⟨ L.SubS.++⁺ˡ bs′ $ ⊆-++-comm bs _ ⟩
          b ∷ bs ++ bs′          ∎

        ⊆π′ : projBlock m
             ∷ (map (λ{ ⦅ m , _ , _ ⦆ → projBlock m }) (filter (dlv? p′ 𝟙) (map mkenv ps))
                ++
                map (λ{ ⦅ m , _ , _ ⦆ → projBlock m }) (filter (dlv? p′ 𝟚) (map mkenv ps)))
             ⊆ˢ
             [ projBlock m ]
        ⊆π′ {b} (here b≡mᵇ) rewrite b≡mᵇ = here refl
        ⊆π′ {b} (there b∈𝟙s+𝟚s) = ⊆π* p′∉ps b∈𝟙s+𝟚s
          where
            p′∉ps : p′ ∉ ps
            p′∉ps = Unique[x∷xs]⇒x∉xs [p′+ps]!

            ⊆π* : ∀ {ps*} →
                p′ ∉ ps*
              → b ∈ (map (λ{ ⦅ m , _ , _ ⦆ → projBlock m }) (filter (dlv? p′ 𝟙) (map mkenv ps*))
                     ++
                     map (λ{ ⦅ m , _ , _ ⦆ → projBlock m }) (filter (dlv? p′ 𝟚) (map mkenv ps*)))
              → b ∈ [ projBlock m ]
            ⊆π* {p* ∷ ps*} p′∉p*+ps* b∈𝟙s+𝟚s+p*ₑ with ∉-∷⁻ p′∉p*+ps*
            ... | p′≢p* , p′∉ps*
                  rewrite
                    L.filter-reject (dlv? p′ 𝟙) {⦅ m , p* , φ p* .value ⦆} {map mkenv ps*} (dec-de-morgan₂ (inj₂ (≢-sym p′≢p*)))
                  | L.filter-reject (dlv? p′ 𝟚) {⦅ m , p* , φ p* .value ⦆} {map mkenv ps*} (dec-de-morgan₂ (inj₂ (≢-sym p′≢p*)))
                  = ⊆π* {ps*} p′∉ps* b∈𝟙s+𝟚s+p*ₑ
blockDelayUniqueness φ m p (p′ ∷ ps) (there p∈ps) [p′+ps]! = goal-p∈ps
  where
    dlv? : (d : Delay) → Decidable¹ λ e′ → DeliveredIn e′ p d
    dlv? d e′ = ¿ DeliveredIn e′ ¿² p d

    mkenv : Party → Envelope
    mkenv p* = ⦅ m , p* , φ p* .value ⦆

    e′ : Envelope
    e′ = ⦅ m , p′ , φ p′ .value ⦆

    p′∉ps : p′ ∉ ps
    p′∉ps = Unique[x∷xs]⇒x∉xs [p′+ps]!

    ps! : Unique ps
    ps! = U.tail [p′+ps]!
      where import Data.List.Relation.Unary.Unique.Propositional as U

    p≢p′ : p ≢ p′
    p≢p′ = λ p≡p′ → contradiction p∈ps (subst (_∉ ps) (sym p≡p′) p′∉ps)

    goal-p∈ps :
      map (projBlock ∘ msg) (filter (dlv? 𝟙) (map mkenv (p′ ∷ ps)))
      ++
      map (projBlock ∘ msg) (filter (dlv? 𝟚) (map mkenv (p′ ∷ ps)))
      ≡ˢ
      [ projBlock m ]
    goal-p∈ps
      rewrite
        L.filter-reject (dlv? 𝟙) {e′} {map mkenv ps} (dec-de-morgan₂ (inj₂ (≢-sym p≢p′)))
      | L.filter-reject (dlv? 𝟚) {e′} {map mkenv ps} (dec-de-morgan₂ (inj₂ (≢-sym p≢p′)))
      = blockDelayUniqueness φ m p ps p∈ps ps!
