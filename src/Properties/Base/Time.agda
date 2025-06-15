{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled

open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Base.Time
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot; Honesty)
open import Protocol.Crypto ⦃ params ⦄ using (Hashable); open Hashable ⦃ ... ⦄
open import Protocol.Block ⦃ params ⦄
open import Protocol.Chain ⦃ params ⦄
open import Protocol.TreeType ⦃ params ⦄
open import Protocol.Message ⦃ params ⦄
open import Protocol.Network ⦃ params ⦄; open Envelope
open import Properties.Base.ForgingFree ⦃ params ⦄ ⦃ assumptions ⦄
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Prelude.STS.Properties using (—[]→∗⇒—[]→∗ʳ; —[]→∗ʳ⇒—[]→∗)
open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_)
open import Data.List.Properties.Ext using (foldr-preservesʳ')
open import Data.List.Relation.Binary.Subset.Propositional.Properties.Ext using (∷⊆⇒∈)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Ext using (Starʳ)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.Ext using (Star⇒Starʳ; Starʳ⇒Star)
open import Relation.Binary.Core using (_Preserves_⟶_)
open import Data.Nat.Properties using (<-trans)
open import Data.Nat.Base using (z<s; s<s)

opaque

  unfolding honestMsgsDelivery honestBlockMaking

  clockPreservation-broadcastMsgʰ : ∀ (msg : Message) (N : GlobalState) →
    broadcastMsgʰ msg N .clock ≡ N .clock
  clockPreservation-broadcastMsgʰ msg N = refl

  clockPreservation-broadcastMsgsʰ : ∀ (msgs : List Message) (N : GlobalState) →
    broadcastMsgsʰ msgs N .clock ≡ N .clock
  clockPreservation-broadcastMsgsʰ msgs N = foldr-preservesʳ'
    {P = λ N′ → N′ .clock ≡ N .clock}
    (λ msg {N′} prf → prf)
    refl
    msgs

  clockPreservation-broadcastMsgᶜ : ∀ (msg : Message) (ϕ : DelayMap) (N : GlobalState) →
    broadcastMsgᶜ msg ϕ N .clock ≡ N .clock
  clockPreservation-broadcastMsgᶜ msg ϕ N = refl

  clockPreservation-broadcastMsgsᶜ : ∀ (mϕs : List (Message × DelayMap)) (N : GlobalState) →
    broadcastMsgsᶜ mϕs N .clock ≡ N .clock
  clockPreservation-broadcastMsgsᶜ mϕs N = foldr-preservesʳ'
    {P = λ N′ → N′ .clock ≡ N .clock}
    (λ (msg , ϕ) {N′} prf → prf)
    refl
    mϕs

  clockPreservation-↓ : ∀ {N N′ : GlobalState} {p : Party} →
    _ ⊢ N —[ p ]↓→ N′ → N′ .clock ≡ N .clock
  clockPreservation-↓ (unknownParty↓ _  ) = refl
  clockPreservation-↓ (honestParty↓  _ _) = refl
  clockPreservation-↓ (corruptParty↓ _ _) = clockPreservation-broadcastMsgsᶜ (proj₁ (processMsgsᶜ _ _ _ _ _)) _

  clockPreservation-↓∗ : ∀ {N N′ : GlobalState} {ps : List Party} →
    _ ⊢ N —[ ps ]↓→∗ N′ → N′ .clock ≡ N .clock
  clockPreservation-↓∗ = fold (λ _ N N′ → N′ .clock ≡ N .clock) (λ ts π → trans π (clockPreservation-↓ ts)) refl

  clockPreservation-↑ : ∀ {N N′ : GlobalState} {p : Party} →
    _ ⊢ N —[ p ]↑→ N′ → N′ .clock ≡ N .clock
  clockPreservation-↑ (unknownParty↑ _) = refl
  clockPreservation-↑ {N} {_} {p} (honestParty↑ _ _)
    with Params.winnerᵈ params {p} {N .clock}
  ... | ⁇ (yes _) = refl
  ... | ⁇ (no _)  = refl
  clockPreservation-↑ (corruptParty↑ _ _) = clockPreservation-broadcastMsgsᶜ (proj₁ (makeBlockᶜ _ _ _ _)) _

  clockPreservation-↑∗ : ∀ {N N′ : GlobalState} {ps : List Party} →
    _ ⊢ N —[ ps ]↑→∗ N′ → N′ .clock ≡ N .clock
  clockPreservation-↑∗ = fold (λ _ N N′ → N′ .clock ≡ N .clock) (λ ts π → trans π (clockPreservation-↑ ts)) refl

  clockMonotonicity : clock Preserves _↝⋆_ ⟶ _≤_
  clockMonotonicity {N} {.N} RTC.ε = Nat.≤-refl
  clockMonotonicity {N} {N′} (RTC._◅_ {j = N″} ts↝ ts↝⋆) = Nat.≤-trans (clockMonotonicity′ ts↝) (clockMonotonicity ts↝⋆)
    where
      clockMonotonicity′ : N ↝ N″ → N .clock ≤ N″ .clock
      clockMonotonicity′ (deliverMsgs    _ ts) = Nat.≤-reflexive $ sym $ clockPreservation-↓∗ ts
      clockMonotonicity′ (makeBlock      _ ts) = Nat.≤-reflexive $ sym $ clockPreservation-↑∗ ts
      clockMonotonicity′ (advanceRound   _   ) = Nat.<⇒≤ $ Nat.n<1+n _
      clockMonotonicity′ (permuteParties _   ) = Nat.≤-refl
      clockMonotonicity′ (permuteMsgs    _   ) = Nat.≤-refl

positiveClock : ∀ {N : GlobalState} → N₀ ↝⋆ N → N .clock > 0
positiveClock = positiveClock′ ∘ Star⇒Starʳ
  where
    open Starʳ
    positiveClock′ : ∀ {N : GlobalState} → N₀ ↝⋆ʳ N → N .clock > 0
    positiveClock′ {.N₀} εʳ = Nat.z<s
    positiveClock′ {N} (ts↝⋆ ◅ʳ ts↝) with ih ← positiveClock′ ts↝⋆ | ts↝
    ... | deliverMsgs    _ ts↓∗ rewrite clockPreservation-↓∗ ts↓∗ = ih
    ... | makeBlock      _ ts↑∗ rewrite clockPreservation-↑∗ ts↑∗ = ih
    ... | advanceRound   _      = <-trans z<s (s<s ih)
    ... | permuteParties _      = ih
    ... | permuteMsgs    _      = ih

rewindToReady : ∀ {N : GlobalState} →
    N₀ ↝⁺ N
  → ∃[ N′ ] N₀ ↝⋆ N′ × N′ ↝⋆ N × N′ .progress ≡ ready × N′ .clock ≡ N .clock ∸ 1
rewindToReady = {!!}

∃ReadyBeforeMsgsDelivered : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → N .progress ≡ msgsDelivered
  → ∃[ N′ ] N₀ ↝⋆ N′ × N′ ↝⋆⟨ 0 ⟩ N × N′ .progress ≡ ready
∃ReadyBeforeMsgsDelivered = {!!}

noPrematureHonestBlocksAtReady : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → ForgingFree N
  → N .progress ≡ ready
  → L.All.All ((_< N .clock) ∘ slot) (honestBlockHistory N)
noPrematureHonestBlocksAtReady = {!!}

noPrematureHonestBlocksAt↓ : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → ForgingFree N
  → N .progress ≡ msgsDelivered
  → L.All.All ((_< N .clock) ∘ slot) (honestBlockHistory N)
noPrematureHonestBlocksAt↓ = {!!}

opaque

  unfolding honestMsgsDelivery corruptMsgsDelivery honestBlockMaking corruptBlockMaking

  noPrematureHonestBlocks : ∀ {N : GlobalState} →
      N₀ ↝⋆ N
    → ForgingFree N
    → L.All.All ((_≤ N .clock) ∘ slot) (honestBlockHistory N)
  noPrematureHonestBlocks = noPrematureHonestBlocksʳ ∘ Star⇒Starʳ
    where
      open RTC; open Starʳ
      noPrematureHonestBlocksʳ : ∀ {N : GlobalState} →
          N₀ ↝⋆ʳ N
        → ForgingFree N
        → L.All.All ((_≤ N .clock) ∘ slot) (honestBlockHistory N)
      noPrematureHonestBlocksʳ εʳ _ = []
      noPrematureHonestBlocksʳ {N} (_◅ʳ_ {j = N′} N₀↝⋆ʳN′ N′↝N) ffN = goal N′↝N
        where
          ffN′ : ForgingFree N′
          ffN′ = ForgingFreePrev (N′↝N ◅ ε) ffN

          ih : L.All.All ((_≤ N′ .clock) ∘ slot) (honestBlockHistory N′)
          ih = noPrematureHonestBlocksʳ N₀↝⋆ʳN′ ffN′

          goal : N′ ↝ N → L.All.All ((_≤ N .clock) ∘ slot) (honestBlockHistory N)
          goal (deliverMsgs {N′ = N″} N′Ready N′—[eoN′]↓→∗N″) =
            subst
              _
              (sym $ clockPreservation-↓∗ N′—[eoN′]↓→∗N″)
              (goal* N″↷↓N $ —[]→∗⇒—[]→∗ʳ N′—[eoN′]↓→∗N″)
            where
              N″↷↓N : N″ ↷↓ N
              N″↷↓N = progress↓ (↷↓-refl {N})

              goal* : ∀ {N″ ps} →
                   N″ ↷↓ N
                 → _ ⊢ N′ —[ ps ]↓→∗ʳ N″
                 → L.All.All ((_≤ N′ .clock) ∘ slot) (honestBlockHistory N″)
              goal* _ [] = ih
              goal* {N″} N″↷↓N (_∷ʳ_ {is = ps} {i = p} {s′ = N‴} N′—[ps]↓→∗ʳN‴ N‴↝[p]↓N″) = step* N‴↝[p]↓N″
                where
                  N‴↷↓N : N‴ ↷↓ N
                  N‴↷↓N = delivery↓ N‴↝[p]↓N″ N″↷↓N

                  ih* : L.All.All ((_≤ N′ .clock) ∘ slot) (honestBlockHistory N‴)
                  ih* = goal* N‴↷↓N N′—[ps]↓→∗ʳN‴

                  step* : _ ⊢ N‴ —[ p ]↓→ N″ → L.All.All ((_≤ N′ .clock) ∘ slot) (honestBlockHistory N″)
                  step* (unknownParty↓ _  ) = ih*
                  step* (honestParty↓  _ _) = ih*
                  step* (corruptParty↓ _ _) = step*′ {mds} sub
                    where
                      mds : List (Message × DelayMap)
                      mds =
                        processMsgsᶜ
                          (L.map msg (immediateMsgs p N‴))
                          (N‴ .clock)
                          (N‴ .history)
                          (removeImmediateMsgs p N‴ .messages)
                          (N‴ .advState)
                          .proj₁

                      sub : L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                      sub = ffN .proj₁ N‴↷↓N

                      step*′ : ∀ {mds} →
                          L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                        → L.All.All
                            ((_≤ N′ .clock) ∘ slot)
                            (honestBlockHistory (broadcastMsgsᶜ mds (removeImmediateMsgs p N‴)))
                      step*′ {[]} _ = ih*
                      step*′ {(m , _) ∷ mds} sub with bᵐ ← projBlock m | ¿ HonestBlock bᵐ ¿
                      ... | yes hbᵐ = bᵐₜ≤N′ₜ ∷ step*′ {mds} sub′
                        where
                          bᵐₜ≤N′ₜ : bᵐ .slot ≤ N′ .clock
                          bᵐₜ≤N′ₜ = L.All.lookup ih* $ ∷⊆⇒∈ sub

                          sub′ : L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                          sub′ = L.SubS.⊆-trans (L.SubS.xs⊆x∷xs _ bᵐ) sub
                      ... | no ¬hbᵐ = step*′ {mds} sub
          goal (makeBlock {N′ = N″} N′MsgsDelivered N′—[eoN′]↑→∗N″) =
            subst
              _
              (sym $ clockPreservation-↑∗ N′—[eoN′]↑→∗N″)
              (goal* N″↷↑N $ —[]→∗⇒—[]→∗ʳ N′—[eoN′]↑→∗N″)
            where
              N″↷↑N : N″ ↷↑ N
              N″↷↑N = progress↑ (↷↑-refl {N})

              goal* : ∀ {N″ ps} →
                   N″ ↷↑ N
                 → _ ⊢ N′ —[ ps ]↑→∗ʳ N″
                 → L.All.All ((_≤ N′ .clock) ∘ slot) (honestBlockHistory N″)
              goal* _ [] = ih
              goal* {N″} N″↷↑N (_∷ʳ_ {is = ps} {i = p} {s′ = N‴} N′—[ps]↑→∗ʳN‴ N‴↝[p]↑N″) = step* N‴↝[p]↑N″
                where
                  N‴↷↑N : N‴ ↷↑ N
                  N‴↷↑N = blockMaking↑ N‴↝[p]↑N″ N″↷↑N

                  ih* : L.All.All ((_≤ N′ .clock) ∘ slot) (honestBlockHistory N‴)
                  ih* = goal* N‴↷↑N N′—[ps]↑→∗ʳN‴

                  step* : _ ⊢ N‴ —[ p ]↑→ N″ → L.All.All ((_≤ N′ .clock) ∘ slot) (honestBlockHistory N″)
                  step* (unknownParty↑ _  ) = ih*
                  step* (honestParty↑ {ls = ls} lsπ hp) with Params.winnerᵈ params {p} {N‴ .clock}
                  ... | ⁇ (no ¬isWinner) = ih*
                  ... | ⁇ (yes isWinner) rewrite lsπ | hp = nbₜ≤N′ₜ ∷ ih*
                    where
                      best : Chain
                      best = bestChain (N‴ .clock  ∸ 1) (ls .tree)

                      nb : Block
                      nb = mkBlock (hash (tip best)) (N‴ .clock) (txSelection (N‴ .clock) p) p

                      nbₜ≤N′ₜ : nb .slot ≤ N′ .clock
                      nbₜ≤N′ₜ rewrite clockPreservation-↑∗ (—[]→∗ʳ⇒—[]→∗ N′—[ps]↑→∗ʳN‴) = Nat.≤-refl
                  step* (corruptParty↑ _ _) = step*′ {mds} sub
                    where
                      mds : List (Message × DelayMap)
                      mds = makeBlockᶜ (N‴ .clock) (N‴ .history) (N‴ .messages) (N‴ .advState) .proj₁

                      sub : L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                      sub = ffN .proj₂ N‴↷↑N

                      step*′ : ∀ {mds} →
                          L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                        → L.All.All ((_≤ N′ .clock) ∘ slot) (honestBlockHistory (broadcastMsgsᶜ mds N‴))
                      step*′ {[]} _ = ih*
                      step*′ {(m , _) ∷ mds} sub with bᵐ ← projBlock m | ¿ HonestBlock bᵐ ¿
                      ... | yes hbᵐ = bᵐₜ≤N′ₜ ∷ step*′ {mds} sub′
                        where
                          bᵐₜ≤N′ₜ : bᵐ .slot ≤ N′ .clock
                          bᵐₜ≤N′ₜ = L.All.lookup ih* $ ∷⊆⇒∈ sub

                          sub′ : L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                          sub′ = L.SubS.⊆-trans (L.SubS.xs⊆x∷xs _ bᵐ) sub
                      ... | no ¬hbᵐ = step*′ {mds} sub
          goal (advanceRound   _) = L.All.map Nat.m≤n⇒m≤1+n ih
          goal (permuteParties _) = ih
          goal (permuteMsgs    _) = ih

honestBlocksBelowSlotPreservation : ∀ {N N′ : GlobalState} →
    N₀ ↝⋆ N
  → N ↝⋆ N′
  → ForgingFree N′
  → filter ((_<? N .clock) ∘ slot) (honestBlockHistory N)
    ≡ˢ
    filter ((_<? N .clock) ∘ slot) (honestBlockHistory N′)
honestBlocksBelowSlotPreservation = {!!}
