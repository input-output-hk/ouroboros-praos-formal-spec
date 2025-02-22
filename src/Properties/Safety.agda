open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot; slot₀; Honesty)
open import Protocol.Params using (Params)
open import Protocol.Block
open import Protocol.Chain using (Chain; genesisBlock; tip; chainFromBlock; _✓; ✓⇒≢[]; ✓⇒gbIsHead; ✓-∷)
open import Protocol.Crypto using (Hashable)
open import Protocol.Message
open import Protocol.Network
open import Protocol.TreeType
open Params ⦃ ... ⦄
open Honesty
open Hashable ⦃ ... ⦄
open Envelope
open import Relation.Binary.PropositionalEquality.Properties

module Properties.Safety
  ⦃ params : Params ⦄
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
  {parties₀ : List Party} ⦃ parties₀Uniqueness : Unique parties₀ ⦄
  ⦃ genesisBlockSlot : genesisBlock .slot ≡ 0 ⦄
  where

open import Function.Bundles
open import Function.Related.Propositional as Related
open import Relation.Binary.PropositionalEquality using (≢-sym)
open import Data.Nat.Base using (z<s; s<s)
open import Data.Nat.Properties using (<-trans)
open import Data.Nat.Properties.Ext using (pred[n]<n)
open import Data.List.Properties.Ext using (filter-∘-comm; filter-∘-×; []≢∷ʳ; Px-findᵇ⁻; ∷≢[]; ≢[]⇒∷)
open import Data.List.Relation.Unary.Unique.Propositional.Properties.Ext using (++⁻; Unique[x∷xs]⇒x∉xs; Unique[xs∷ʳx]⇒x∉xs)
open import Data.List.Relation.Unary.All.Properties.Ext using (cartesianProduct⁻)
open import Data.List.Relation.Binary.Permutation.Propositional using (↭-refl; ↭-trans)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties.Ext using (Unique-resp-↭)
open import Data.List.Relation.Binary.Subset.Propositional.Properties.Ext using (cartesianProduct-⊆-Mono; filterᵇ-mono)
open import Data.List.Membership.Propositional.Properties.Ext using (x∈x∷xs; ∈-∷⁻; ∈-findᵇ⁻; ∈-∷-≢⁻)
open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_; ≡ˢ-refl; ≡ˢ-trans; ≡ˢ⇒⊆×⊇; ⊆×⊇⇒≡ˢ; deduplicate-cong; filter-cong; All-resp-≡ˢ; cartesianProduct-cong)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Ext using (Starʳ)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.Ext using (Star⇒Starʳ; Starʳ⇒Star)
open import Relation.Binary.PropositionalEquality.Properties.Ext using (≡×≢⇒≢; =/=⇔≢; ==⇔≡)
open import Prelude.STS.Ext using (fold)
open import Prelude.STS.Properties.Ext using (—[]→∗⇒—[]→∗ʳ; —[]→∗ʳ⇒—[]→∗)
open import Protocol.BaseTypes using (slot₀)
open import Protocol.Semantics {T} {AdversarialState} {honestyOf} {txSelection} {processMsgsᶜ} {makeBlockᶜ}

open GlobalState
open LocalState

N₀ : GlobalState
N₀ =
  record
    { clock     = slot₀
    ; messages  = []
    ; states    = map (_, it .def) parties₀
    ; history   = []
    ; advState  = adversarialState₀
    ; execOrder = parties₀
    ; progress  = ready
    }

-- the standard library version is strangely for f : A → A → A
foldr-preservesʳ' : ∀ {A B : Set} {P : B → Set} {f : A → B → B} →
  (∀ x {y} → P y → P (f x y)) → ∀ {e} → P e → ∀ xs → P (L.foldr f e xs)
foldr-preservesʳ' pres Pe []       = Pe
foldr-preservesʳ' pres Pe (_ ∷ xs) = pres _ (foldr-preservesʳ' pres Pe xs)

honestLocalTreeInHonestGlobalTree : ∀ {N : GlobalState} {p : Party} {ls : LocalState} →
    N₀ ↝⋆ N
  → isHonest p
  → N .states ⁉ p ≡ just ls
  → allBlocks (ls .tree) ⊆ˢ allBlocks (honestTree N)
honestLocalTreeInHonestGlobalTree = {!!}

honestGlobalTreeInBlockHistory : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → allBlocks (honestTree N) ⊆ˢ genesisBlock ∷ blockHistory N
honestGlobalTreeInBlockHistory = {!!}

private opaque

  unfolding honestMsgsDelivery honestBlockMaking

  localStatePreservation-↑∗ : ∀ {N N′ : GlobalState} {ps : List Party} {p : Party} →
    p ∉ ps → _ ⊢ N —[ ps ]↑→∗ N′ → N′ .states ⁉ p ≡ N .states ⁉ p
  localStatePreservation-↑∗ = {!!}

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

  execOrderPreservation-broadcastMsgᶜ : ∀ (msg : Message) (ϕ : DelayMap) (N : GlobalState) →
    N .execOrder ↭ broadcastMsgᶜ msg ϕ N .execOrder
  execOrderPreservation-broadcastMsgᶜ msg ϕ N = ↭-refl

  execOrderPreservation-broadcastMsgsᶜ : ∀ (mϕs : List (Message × DelayMap)) (N : GlobalState) →
    N .execOrder ↭ broadcastMsgsᶜ mϕs N .execOrder
  execOrderPreservation-broadcastMsgsᶜ mϕs N = foldr-preservesʳ'
    {P = λ N′ → N .execOrder ↭ N′ .execOrder}
    (λ (msg , ϕ) {N′} eoN↭eoN′ → ↭-trans eoN↭eoN′ (execOrderPreservation-broadcastMsgᶜ msg ϕ N′))
    ↭-refl
    mϕs

  execOrderPreservation-↭-↓ : ∀ {N N′ : GlobalState} {p : Party} →
    _ ⊢ N —[ p ]↓→ N′ → N .execOrder ↭ N′ .execOrder
  execOrderPreservation-↭-↓ (unknownParty↓ _  ) = ↭-refl
  execOrderPreservation-↭-↓ (honestParty↓  _ _) = ↭-refl
  execOrderPreservation-↭-↓ (corruptParty↓ _ _) = execOrderPreservation-broadcastMsgsᶜ (proj₁ (processMsgsᶜ _ _ _ _ _)) _

  execOrderPreservation-↭-↑ : ∀ {N N′ : GlobalState} {p : Party} →
    _ ⊢ N —[ p ]↑→ N′ → N .execOrder ↭ N′ .execOrder
  execOrderPreservation-↭-↑ (unknownParty↑ _) = ↭-refl
  execOrderPreservation-↭-↑ {N} {_} {p} (honestParty↑ _ _)
    with Params.winnerᵈ params {p} {N .clock}
  ... | ⁇ (yes _) = ↭-refl
  ... | ⁇ (no _)  = ↭-refl
  execOrderPreservation-↭-↑ (corruptParty↑ _ _) = execOrderPreservation-broadcastMsgsᶜ (proj₁ (makeBlockᶜ _ _ _ _)) _

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

module _ {a ℓ} {A : Set a} {R : Rel A ℓ} where

  open import Data.List.Relation.Unary.AllPairs as AllPairs using (AllPairs; []; _∷_)
  open import Data.List.Relation.Unary.AllPairs.Properties.Ext as AP using (++⁻)

  headʳ : ∀ {x xs} → AllPairs R (xs L.∷ʳ x) → AllPairs R xs
  headʳ {xs = xs} prf = proj₁ (AP.++⁻ prf)

execOrderPreservation-↭-↓∗ : ∀ {N N′ : GlobalState} {ps : List Party} →
  _ ⊢ N —[ ps ]↓→∗ N′ → N .execOrder ↭ N′ .execOrder
execOrderPreservation-↭-↓∗ = fold (const $ _↭_ on execOrder) (λ ts π → ↭-trans (execOrderPreservation-↭-↓ ts) π) ↭-refl

execOrderPreservation-↭-↑∗ : ∀ {N N′ : GlobalState} {ps : List Party} →
  _ ⊢ N —[ ps ]↑→∗ N′ → N .execOrder ↭ N′ .execOrder
execOrderPreservation-↭-↑∗ = fold (const $ _↭_ on execOrder) (λ ts π → ↭-trans (execOrderPreservation-↭-↑ ts) π) ↭-refl

execOrderPreservation-↭-↝ : ∀ {N N′ : GlobalState} → N ↝ N′ → N .execOrder ↭ N′ .execOrder
execOrderPreservation-↭-↝ (deliverMsgs    _ ts∗ ) = execOrderPreservation-↭-↓∗ ts∗
execOrderPreservation-↭-↝ (makeBlock      _ ts∗ ) = execOrderPreservation-↭-↑∗ ts∗
execOrderPreservation-↭-↝ (advanceRound   _     ) = ↭-refl
execOrderPreservation-↭-↝ (permuteParties eoN↭ps) = eoN↭ps
execOrderPreservation-↭-↝ (permuteMsgs    _     ) = ↭-refl

execOrderPreservation-↭ : ∀ {N N′ : GlobalState} → N ↝⋆ N′ → N .execOrder ↭ N′ .execOrder
execOrderPreservation-↭ = RTC.fold (_↭_ on execOrder) (λ N↝N″ eoN″↭eoN′ → ↭-trans (execOrderPreservation-↭-↝ N↝N″) eoN″↭eoN′) ↭-refl

execOrderUniqueness : ∀ {N : GlobalState} → N₀ ↝⋆ N → Unique (N .execOrder)
execOrderUniqueness N₀↝⋆N = Unique-resp-↭ (execOrderPreservation-↭ N₀↝⋆N) parties₀Uniqueness

isSuperSlot : Slot → Type
isSuperSlot sl = length (filter (λ p → ¿ winner p sl × isHonest p ¿) parties₀) ≡ 1

isSuperBlock : Block → Type
isSuperBlock b = isHonest (b .pid) × isSuperSlot (b .slot)

superBlocks : GlobalState → List Block
superBlocks N = L.deduplicate _≟_ $ filter ¿ isSuperBlock ¿¹ (blockHistory N)

superBlocksAltDef : ∀ N → superBlocks N ≡ (L.deduplicate _≟_ $ filter ¿ isSuperSlot ∘ slot ¿¹ (honestBlockHistory N))
superBlocksAltDef N
  rewrite filter-∘-comm ¿ isSuperSlot ∘ slot ¿¹ ¿ isHonest ∘ pid ¿¹ (blockHistory N)
    | sym $ filter-∘-× ¿ isHonest ∘ pid ¿¹ ¿ isSuperSlot ∘ slot ¿¹ (blockHistory N)
    = refl

module _ where

  private variable
    N₁ N₂ : GlobalState

  -- The messages delivery phase sub-step relation.
  data _↷↓_ : GlobalState → GlobalState → Type where

    refine↓ :
      ∙ N₁ ↝⋆ N₂
      ────────────────────────────────────
      N₁ ↷↓ N₂

    progress↓ :
      ∙ record N₁ { progress = msgsDelivered } ↷↓ N₂
      ────────────────────────────────────
      N₁ ↷↓ N₂

    delivery↓ : ∀ {N′ : GlobalState} {p : Party} →
      ∙ _ ⊢ N₁ —[ p ]↓→ N′
      ∙ N′ ↷↓ N₂
      ────────────────────────────────────
      N₁ ↷↓ N₂

  ↷↓-refl : ∀ {N} → N ↷↓ N
  ↷↓-refl = refine↓ ε
    where open Star

  -- The block making phase sub-step relation.
  data _↷↑_ : GlobalState → GlobalState → Type where

    refine↑ :
      ∙ N₁ ↝⋆ N₂
      ────────────────────────────────────
      N₁ ↷↑ N₂

    progress↑ :
      ∙ record N₁ { progress = blockMade } ↷↑ N₂
      ────────────────────────────────────
      N₁ ↷↑ N₂

    blockMaking↑ : ∀ {N′ : GlobalState} {p : Party} →
      ∙ _ ⊢ N₁ —[ p ]↑→ N′
      ∙ N′ ↷↑ N₂
      ────────────────────────────────────
      N₁ ↷↑ N₂

  ↷↑-refl : ∀ {N} → N ↷↑ N
  ↷↑-refl = refine↑ ε
    where open Star

-- The condition `∀ {N₁} → N₁ ↷↓ N₂ → ∀ {p} → ...` forces the forging-free property to hold at each
-- previous "sub-step" within the delivery/minting phase. A sub-step is either starting a
-- new round, changing the progress to `msgsDelivered`/‵blockMade` or executing the messages
-- delivery/block minting for a party `p`.
--
-- Thus, an honest block can be broadcast by a corrupt party _only_ if such block was already in the
-- history at the beginning of the delivery/minting phase.
isForgingFree↓ : GlobalState → Type
isForgingFree↓ N₂ = ∀ {N₁ : GlobalState} → N₁ ↷↓ N₂ → ∀ {p : Party} →
  let
    (msgs , N₁′) = fetchNewMsgs p N₁
    mds = processMsgsᶜ
      msgs
      (N₁′ .clock)
      (N₁′ .history)
      (N₁′ .messages)
      (N₁′ .advState)
      .proj₁
    nbs = map (projBlock ∘ proj₁) mds
  in
    nbs ⊆ʰ blockHistory N₁′

isForgingFree↓Prev : ∀ {N₁ N₂ : GlobalState} → isForgingFree↓ N₂ → N₁ ↝⋆ N₂ → isForgingFree↓ N₁
isForgingFree↓Prev ff↓ ts↝⋆ ts↷↓ = ff↓ (isForgingFree↓Prev′ ts↷↓ ts↝⋆)
  where
    isForgingFree↓Prev′ : ∀ {N₁ N₂ N′ : GlobalState} → N₁ ↷↓ N′ → N′ ↝⋆ N₂ → N₁ ↷↓ N₂
    isForgingFree↓Prev′ (refine↓ x)     ts↝⋆ = refine↓ (x ◅◅ ts↝⋆)
    isForgingFree↓Prev′ (progress↓ x)   ts↝⋆ = progress↓ (isForgingFree↓Prev′ x ts↝⋆)
    isForgingFree↓Prev′ (delivery↓ x y) ts↝⋆ = delivery↓ x (isForgingFree↓Prev′ y ts↝⋆)

isForgingFree↑ : GlobalState → Type
isForgingFree↑ N₂ = ∀ {N₁ : GlobalState} → N₁ ↷↑ N₂ →
  let
    mds = makeBlockᶜ (N₁ .clock) (N₁ .history) (N₁ .messages) (N₁ .advState) .proj₁
    nbs = map (projBlock ∘ proj₁) mds
  in
    nbs ⊆ʰ blockHistory N₁

isForgingFree↑Prev : ∀ {N₁ N₂ : GlobalState} → isForgingFree↑ N₂ → N₁ ↝⋆ N₂ → isForgingFree↑ N₁
isForgingFree↑Prev ff↑ ts↝⋆ ts↷↑ = ff↑ (isForgingFree↑Prev′ ts↷↑ ts↝⋆)
  where
    isForgingFree↑Prev′ : ∀ {N₁ N₂ N′ : GlobalState} → N₁ ↷↑ N′ → N′ ↝⋆ N₂ → N₁ ↷↑ N₂
    isForgingFree↑Prev′ (refine↑ x)        ts↝⋆ = refine↑ (x ◅◅ ts↝⋆)
    isForgingFree↑Prev′ (progress↑ x)      ts↝⋆ = progress↑ (isForgingFree↑Prev′ x ts↝⋆)
    isForgingFree↑Prev′ (blockMaking↑ x y) ts↝⋆ = blockMaking↑ x (isForgingFree↑Prev′ y ts↝⋆)

isForgingFree : GlobalState → Type
isForgingFree N = isForgingFree↓ N × isForgingFree↑ N

isForgingFreePrev : ∀ {N₁ N₂} → N₁ ↝⋆ N₂ → isForgingFree N₂ → isForgingFree N₁
isForgingFreePrev N₁↝⋆N₂ (ffN₂↓ , ffN₂↑) = isForgingFree↓Prev ffN₂↓ N₁↝⋆N₂ , isForgingFree↑Prev ffN₂↑ N₁↝⋆N₂

historyPreservation-broadcastMsgᶜ : ∀ (msg : Message) (ϕ : DelayMap) (N : GlobalState) →
  N .history ⊆ˢ broadcastMsgᶜ msg ϕ N .history
historyPreservation-broadcastMsgᶜ msg ϕ N p = there p

historyPreservation-broadcastMsgsᶜ : ∀ (mϕs : List (Message × DelayMap)) (N : GlobalState) →
  N .history ⊆ˢ broadcastMsgsᶜ mϕs N .history
historyPreservation-broadcastMsgsᶜ mϕs N {x = x} p = foldr-preservesʳ'
  {P = λ N → x ∈ N .history}
  (λ x {N} → historyPreservation-broadcastMsgᶜ (proj₁ x) (proj₂ x) N)
  p
  mϕs

blockHistoryPreservation-broadcastMsgsᶜ : ∀ (mϕs : List (Message × DelayMap)) (N : GlobalState) →
  blockHistory N ⊆ˢ blockHistory (broadcastMsgsᶜ mϕs N)
blockHistoryPreservation-broadcastMsgsᶜ mϕs N = L.SubS.map⁺ _ (historyPreservation-broadcastMsgsᶜ mϕs N)

private opaque

  unfolding honestMsgsDelivery honestBlockMaking

  historyPreservation-↓ : ∀ {p : Party} {N₁ N₂ : GlobalState} →
    _ ⊢ N₁ —[ p ]↓→ N₂ → N₁ .history ⊆ˢ N₂ .history
  historyPreservation-↓ (unknownParty↓ _)   = id
  historyPreservation-↓ (honestParty↓ _ _)  = id
  historyPreservation-↓ (corruptParty↓ _ _) = historyPreservation-broadcastMsgsᶜ (proj₁ (processMsgsᶜ _ _ _ _ _)) _

  historyPreservation-↓∗ : ∀ {N₁ N₂ : GlobalState} {ps : List Party} →
    _ ⊢ N₁ —[ ps ]↓→∗ N₂ → N₁ .history ⊆ˢ N₂ .history
  historyPreservation-↓∗ = fold (const $ _⊆ˢ_ on history) (L.SubS.⊆-trans ∘ historyPreservation-↓) L.SubS.⊆-refl

  historyPreservation-↑ : ∀ {p : Party} {N₁ N₂ : GlobalState} →
    _ ⊢ N₁ —[ p ]↑→ N₂ → N₁ .history ⊆ˢ N₂ .history
  historyPreservation-↑ (unknownParty↑ _) = id
  historyPreservation-↑ {p} {N₁} (honestParty↑ _ _) prf
    with Params.winnerᵈ params {p} {N₁ .clock}
  ... | ⁇ (yes _) = there prf
  ... | ⁇ (no _)  = prf
  historyPreservation-↑ (corruptParty↑ _ _) prf = historyPreservation-broadcastMsgsᶜ (proj₁ (makeBlockᶜ _ _ _ _)) _ prf

  historyPreservation-↑∗ : ∀ {N₁ N₂ : GlobalState} {ps : List Party} →
    _ ⊢ N₁ —[ ps ]↑→∗ N₂ → N₁ .history ⊆ˢ N₂ .history
  historyPreservation-↑∗ = fold (const $ _⊆ˢ_ on history) (L.SubS.⊆-trans ∘ historyPreservation-↑) L.SubS.⊆-refl

  historyPreservation-↝ : ∀ {N₁ N₂ : GlobalState} → N₁ ↝ N₂ → N₁ .history ⊆ˢ N₂ .history
  historyPreservation-↝ (deliverMsgs _ p)  = historyPreservation-↓∗ p
  historyPreservation-↝ (makeBlock _ p)    = historyPreservation-↑∗ p
  historyPreservation-↝ (advanceRound _)   = id
  historyPreservation-↝ (permuteParties _) = id
  historyPreservation-↝ (permuteMsgs _)    = id

  -- TODO: Use RTC.fold
  historyPreservation-↝⋆ : ∀ {N₁ N₂ : GlobalState} → N₁ ↝⋆ N₂ → N₁ .history ⊆ˢ N₂ .history
  historyPreservation-↝⋆ = RTC.fold (_⊆ˢ_ on history) (L.SubS.⊆-trans ∘ historyPreservation-↝) L.SubS.⊆-refl

  blockHistoryPreservation-↓ : ∀ {N₁ N₂ : GlobalState} {p : Party} →
    _ ⊢ N₁ —[ p ]↓→ N₂ → blockHistory N₁ ⊆ˢ blockHistory N₂
  blockHistoryPreservation-↓ = L.SubS.map⁺ _ ∘ historyPreservation-↓

  blockHistoryPreservation-↑ : ∀ {N₁ N₂ : GlobalState} {p : Party} →
    _ ⊢ N₁ —[ p ]↑→ N₂ → blockHistory N₁ ⊆ˢ blockHistory N₂
  blockHistoryPreservation-↑ = L.SubS.map⁺ _ ∘ historyPreservation-↑

  blockHistoryPreservation-↝⋆ : ∀ {N₁ N₂ : GlobalState} → N₁ ↝⋆ N₂ → blockHistory N₁ ⊆ˢ blockHistory N₂
  blockHistoryPreservation-↝⋆ = L.SubS.map⁺ _ ∘ historyPreservation-↝⋆

  blockHistoryPreservation-↑∗ : ∀ {N₁ N₂ : GlobalState} {ps : List Party} →
    _ ⊢ N₁ —[ ps ]↑→∗ N₂ → blockHistory N₁ ⊆ˢ blockHistory N₂
  blockHistoryPreservation-↑∗ = L.SubS.map⁺ _ ∘ historyPreservation-↑∗

  blockHistoryPreservation-↓∗ : ∀ {N₁ N₂ : GlobalState} {ps : List Party} →
    _ ⊢ N₁ —[ ps ]↓→∗ N₂ → blockHistory N₁ ⊆ˢ blockHistory N₂
  blockHistoryPreservation-↓∗ = L.SubS.map⁺ _ ∘ historyPreservation-↓∗

  isCollisionFreePrev-↓ : ∀ {p : Party} {N₁ N₂ : GlobalState} → _ ⊢ N₁ —[ p ]↓→ N₂ → isCollisionFree N₂ → isCollisionFree N₁
  isCollisionFreePrev-↓ {p} {N₁} {N₂} ts cfN₂ = isBlockListCollisionFree-⊆ subs cfN₂
    where
      subs : genesisBlock ∷ blockHistory N₁ ⊆ˢ genesisBlock ∷ blockHistory N₂
      subs = L.SubS.∷⁺ʳ genesisBlock (blockHistoryPreservation-↓ ts)

  isCollisionFreePrev-↑ : ∀ {p : Party} {N₁ N₂ : GlobalState} → _ ⊢ N₁ —[ p ]↑→ N₂ → isCollisionFree N₂ → isCollisionFree N₁
  isCollisionFreePrev-↑ {p} {N₁} {N₂} ts cfN₂ = isBlockListCollisionFree-⊆ subs cfN₂
    where
      subs : genesisBlock ∷ blockHistory N₁ ⊆ˢ genesisBlock ∷ blockHistory N₂
      subs = L.SubS.∷⁺ʳ genesisBlock (blockHistoryPreservation-↑ ts)

  isCollisionFreePrev : ∀ {N₁ N₂ : GlobalState} → N₁ ↝⋆ N₂ → isCollisionFree N₂ → isCollisionFree N₁
  isCollisionFreePrev {N₁} {N₂} N₁↝⋆N₂ cfN₂ = isBlockListCollisionFree-⊆ subs cfN₂
    where
      subs : genesisBlock ∷ blockHistory N₁ ⊆ˢ genesisBlock ∷ blockHistory N₂
      subs = L.SubS.∷⁺ʳ genesisBlock (blockHistoryPreservation-↝⋆ N₁↝⋆N₂)

  honestBlockHistoryPreservation-broadcastMsgsᶜ : ∀ {N : GlobalState} {mds : List (Message × DelayMap)} →
      map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N
    → honestBlockHistory N ≡ˢ honestBlockHistory (broadcastMsgsᶜ mds N)
  honestBlockHistoryPreservation-broadcastMsgsᶜ {_} {[]} _ = ≡ˢ-refl
  honestBlockHistoryPreservation-broadcastMsgsᶜ {N} {(newBlock b , _) ∷ mds} prf
    with ih ← honestBlockHistoryPreservation-broadcastMsgsᶜ {N} {mds} | ¿ isHonestBlock b ¿
  ... | no _   = ih prf
  ... | yes bh = goal
    where
      π₁ : honestBlocks (b ∷ map (projBlock ∘ proj₁) mds) ≡ b ∷ honestBlocks (map (projBlock ∘ proj₁) mds)
      π₁ rewrite bh = refl

      π₂ : b ∷ map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N
      π₂ = L.SubS.⊆-trans (L.SubS.⊆-reflexive π₁) prf

      π₃ : map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N
      π₃ = ∷-⊆ʰ {map (projBlock ∘ proj₁) mds} {blockHistory N} {b} bh π₂

      π₄ : honestBlockHistory N ≡ˢ honestBlockHistory (broadcastMsgsᶜ mds N)
      π₄ = ih π₃

      goal : honestBlockHistory N ≡ˢ b ∷ honestBlockHistory (broadcastMsgsᶜ mds N)
      goal = ⊆×⊇⇒≡ˢ ⊆ˢπ ⊇ˢπ
        where
          ⊆ˢπ : honestBlockHistory N ⊆ˢ b ∷ honestBlockHistory (broadcastMsgsᶜ mds N)
          ⊆ˢπ {b′} b′∈lhs with b ≟ b′
          ... | yes eq rewrite eq = x∈x∷xs _
          ... | no ¬eq = L.SubS.xs⊆x∷xs _ b (to π₄ b′∈lhs)
            where open Function.Bundles.Equivalence

          ⊇ˢπ : b ∷ honestBlockHistory (broadcastMsgsᶜ mds N) ⊆ˢ honestBlockHistory N
          ⊇ˢπ = L.SubS.∈-∷⁺ʳ (prf {b} (x∈x∷xs _)) (≡ˢ⇒⊆×⊇ π₄ .proj₂)

  honestBlockHistoryPreservation-↓∗ : ∀ {N N′ : GlobalState} {ps : List Party} →
      N₀ ↝⋆ N
    → _ ⊢ N —[ ps ]↓→∗ N′
    → isForgingFree (record N′ { progress = msgsDelivered })
    → N .progress ≡ ready
    → honestBlockHistory N ≡ˢ honestBlockHistory N′
  honestBlockHistoryPreservation-↓∗ {N} {N′} {ps} N₀↝⋆N N—[ps]↓→∗N′ ff NReady = honestBlockHistoryPreservationʳ-↓∗ {N} {N′} ps prfN₂ (—[]→∗⇒—[]→∗ʳ N—[ps]↓→∗N′)
    where
      N₂ : GlobalState
      N₂ = record N′ { progress = msgsDelivered }

      prfN₂ : N′ ↷↓ N₂
      prfN₂ = progress↓ (↷↓-refl {N₂})

      honestBlockHistoryPreservationʳ-↓∗ : ∀ {N N′ : GlobalState} (ps : List Party) →
          N′ ↷↓ N₂
        → _ ⊢ N —[ ps ]↓→∗ʳ N′
        → honestBlockHistory N ≡ˢ honestBlockHistory N′
      honestBlockHistoryPreservationʳ-↓∗ {N} {.N} .[] prfN₂ [] = ≡ˢ-refl
      honestBlockHistoryPreservationʳ-↓∗ {N} {N′} _ prfN₂ (_∷ʳ_ {is = ps} {i = p} {s′ = N″} ts⋆ ts) = step ts
        where
          ih : honestBlockHistory N ≡ˢ honestBlockHistory N″
          ih = honestBlockHistoryPreservationʳ-↓∗ _ (delivery↓ ts prfN₂) ts⋆

          step : _ ⊢ N″ —[ p ]↓→ N′ → honestBlockHistory N ≡ˢ honestBlockHistory N′
          step (unknownParty↓ _) = ih
          -- Honest parties do not broadcast any (in particular, honest) blocks in the delivery phase.
          step (honestParty↓ _ _) = ih
          -- Corrupt parties do not broadcast new _honest_ blocks in the delivery phase (by the forging-free property).
          step (corruptParty↓ _ _) = ≡ˢ-trans ih (honestBlockHistoryPreservation-broadcastMsgsᶜ {removeImmediateMsgs p N″} {mds} sub)
            where
              mds : List (Message × DelayMap)
              mds =
                processMsgsᶜ
                  (map msg (immediateMsgs p N″))
                  (N″ .clock)
                  (N″ .history)
                  (removeImmediateMsgs p N″ .messages)
                  (N″ .advState)
                  .proj₁

              sub : map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N″
              sub = ff .proj₁ (delivery↓ ts prfN₂)

-- Proof of `subsetCfbPreservation`
module _ where

  private

    ancestorPreservation : ∀ {bs bs′ : List Block} {b b′ : Block} →
        isBlockListCollisionFree bs′
      → bs ⊆ˢ bs′
      → L.findᵇ ((b .prev ==_) ∘ hash) bs ≡ just b′
      → L.findᵇ ((b .prev ==_) ∘ hash) bs′ ≡ just b′
    ancestorPreservation {bs} {bs′} {b} {b′} cfbs′ bs⊆ˢbs′ eqf = goal cfbs′ b′∈bs′
      where
        b′∈bs′ : b′ ∈ bs′
        b′∈bs′ = bs⊆ˢbs′ $ ∈-findᵇ⁻ eqf

        prevb≡hb′ : b .prev == hash b′ ≡ true
        prevb≡hb′ = Px-findᵇ⁻ {P = ((b .prev ==_) ∘ hash)} {xs = bs} eqf

        prevb≡b″ : ∀ {b″} → b′ ≡ b″ → b .prev == hash b″ ≡ true
        prevb≡b″ b′≡b″ = subst _ b′≡b″ prevb≡hb′

        goal : ∀ {bs′} → isBlockListCollisionFree bs′ → b′ ∈ bs′ → L.findᵇ ((b .prev ==_) ∘ hash) bs′ ≡ just b′
        goal {b″ ∷ bs″} cfbs′ b′∈bs′ with b′ ≟ b″
        ... | yes b′≡b″ rewrite prevb≡b″ b′≡b″ = cong just (sym b′≡b″)
        ... | no b′≢b″ = goal′
          where
            b′∈bs″ : b′ ∈ bs″
            b′∈bs″ = ∈-∷-≢⁻ b′∈bs′ b′≢b″

            hb′≢hb″ : hash b′ ≢ hash b″
            hb′≢hb″ = contraposition (cartesianProduct⁻ cfbs′ (L.Mem.∈-++⁺ʳ [ b″ ] b′∈bs″) (x∈x∷xs bs″)) b′≢b″

            prevb≢hb″ : b .prev == hash b″ ≡ false
            prevb≢hb″ = Equivalence.from =/=⇔≢ $ ≡×≢⇒≢ (Equivalence.to ==⇔≡ prevb≡hb′) hb′≢hb″

            goal′ : L.findᵇ ((b .prev ==_) ∘ hash) (b″ ∷ bs″) ≡ just b′
            goal′ rewrite prevb≢hb″ = goal {bs″} (isBlockListCollisionFree-∷ {bs = bs″} cfbs′) b′∈bs″

  {-# TERMINATING #-}
  -- TODO: Prove termination using `WellFounded` (if needed).
  subsetCfbPreservation : ∀ {bs bs′ : List Block} {b : Block} →
      isBlockListCollisionFree bs′
    → bs ⊆ˢ bs′
    → chainFromBlock b bs ≢ []
    → chainFromBlock b bs ≡ chainFromBlock b bs′
  subsetCfbPreservation {bs} {bs′} {b} cfbs′ bs⊆ˢbs′ cfbbs≢[]
    with b == genesisBlock
  ... | true = refl
  ... | false with b .prev == hash genesisBlock
  ... |   true = refl
  ... |   false with L.findᵇ ((b .prev ==_) ∘ hash) bs in eqf
  ... |     nothing = contradiction refl cfbbs≢[]
  ... |     just b′ with chainFromBlock b′ (L.filterᵇ (not ∘ (_== b′)) bs) in eqcfb
  ... |       [] = contradiction refl cfbbs≢[]
  ... |       b′′ ∷ bs′′
                rewrite
                  ancestorPreservation {b = b} cfbs′ bs⊆ˢbs′ eqf
                | sym $ subsetCfbPreservation
                    {L.filterᵇ (not ∘ (_== b′)) bs}
                    {L.filterᵇ (not ∘ (_== b′)) bs′}
                    {b′}
                    (isBlockListCollisionFree-⊆ (L.SubS.filter-⊆ _ bs′) cfbs′)
                    (filterᵇ-mono bs⊆ˢbs′)
                    (subst (_≢ []) (sym eqcfb) ∷≢[])
                | eqcfb
                  = refl

subsetCfb✓Preservation : ∀ {bs bs′ : List Block} {b : Block} →
    isBlockListCollisionFree bs′
  → bs ⊆ˢ bs′
  → chainFromBlock b bs ✓
  → chainFromBlock b bs′ ✓
subsetCfb✓Preservation {bs} {bs′} {b} cfbs′ bs⊆ˢbs′ cfbbs✓ = subst _✓ cfbbs≡cfbbs′ cfbbs✓
  where
    cfbbs≢[] : chainFromBlock b bs ≢ []
    cfbbs≢[] = subst (_≢ []) (✓⇒gbIsHead cfbbs✓ .proj₂) (≢-sym []≢∷ʳ)

    cfbbs≡cfbbs′ : chainFromBlock b bs ≡ chainFromBlock b bs′
    cfbbs≡cfbbs′ = subsetCfbPreservation cfbs′ bs⊆ˢbs′ cfbbs≢[]

cfbInBlockListIsSubset : ∀ {b : Block} {bs : List Block} {c : Chain} →
  let
    gbs : List Block
    gbs = genesisBlock ∷ bs
  in
    isBlockListCollisionFree gbs
  → (b ∷ c) ✓
  → c ⊆ˢ gbs
  → chainFromBlock b bs ≡ b ∷ c
cfbInBlockListIsSubset = {!!}

private opaque

  unfolding honestBlockMaking corruptBlockMaking

  honestBlockCfb✓ : ∀ {N : GlobalState} {b : Block} →
      N₀ ↝⋆ N
    → isForgingFree N
    → isCollisionFree N
    → b ∈ honestBlockHistory N
    → chainFromBlock b (blockHistory N) ✓
  honestBlockCfb✓ = honestBlockCfb✓ʳ ∘ Star⇒Starʳ
    where
      open RTC; open Starʳ
      honestBlockCfb✓ʳ : ∀ {N : GlobalState} {b : Block} →
          N₀ ↝⋆ʳ N
        → isForgingFree N
        → isCollisionFree N
        → b ∈ honestBlockHistory N
        → chainFromBlock b (blockHistory N) ✓
      honestBlockCfb✓ʳ εʳ ffN cfN b∈hbhN = contradiction b∈hbhN L.Any.¬Any[]
      honestBlockCfb✓ʳ {N} {b} (_◅ʳ_ {j = N′} N₀↝⋆ʳN′ N′↝N) ffN cfN b∈hbhN = goal N′↝N
        where
          N₀↝⋆N′ : N₀ ↝⋆ N′
          N₀↝⋆N′ = Starʳ⇒Star N₀↝⋆ʳN′

          ffN′ : isForgingFree N′
          ffN′ = isForgingFreePrev (N′↝N ◅ ε) ffN

          cfN′ : isCollisionFree N′
          cfN′ = isCollisionFreePrev (N′↝N ◅ ε) cfN

          goal : N′ ↝ N → chainFromBlock b (blockHistory N) ✓
          goal N′↝N
            with N′↝N
          ... | deliverMsgs {N′ = N″} N′Ready N′—[eoN′]↓→∗N″ = deliverMsgsGoal cfN (—[]→∗⇒—[]→∗ʳ N′—[eoN′]↓→∗N″)
            where
              hbhPres : honestBlockHistory N′ ≡ˢ honestBlockHistory N
              hbhPres = honestBlockHistoryPreservation-↓∗ N₀↝⋆N′ N′—[eoN′]↓→∗N″ ffN N′Ready

              b∈hbhN′ : b ∈ honestBlockHistory N′
              b∈hbhN′ = ≡ˢ⇒⊆×⊇ hbhPres .proj₂ b∈hbhN

              ih : chainFromBlock b (blockHistory N′) ✓
              ih = honestBlockCfb✓ʳ N₀↝⋆ʳN′ ffN′ cfN′ b∈hbhN′

              deliverMsgsGoal : ∀ {N″ ps} → isCollisionFree N″ → _ ⊢ N′ —[ ps ]↓→∗ʳ N″ → chainFromBlock b (blockHistory N″) ✓
              deliverMsgsGoal _ [] = ih
              deliverMsgsGoal {N″} cfN″ (_∷ʳ_ {s′ = N‴} N′—[ps]↓→∗ʳN‴ N‴↝[p]↓N″) = subst _✓ cfbhN‴≡cfbhN″ ih′
                where
                  cfN‴ : isCollisionFree N‴
                  cfN‴ = isCollisionFreePrev-↓ N‴↝[p]↓N″ cfN″

                  ih′ : chainFromBlock b (blockHistory N‴) ✓
                  ih′ = deliverMsgsGoal cfN‴ N′—[ps]↓→∗ʳN‴

                  cfbhN″ : isBlockListCollisionFree (blockHistory N″)
                  cfbhN″ = isBlockListCollisionFree-∷ {blockHistory N″} {genesisBlock} cfN″

                  bhN‴⊆bhN″ : blockHistory N‴ ⊆ˢ blockHistory N″
                  bhN‴⊆bhN″ = blockHistoryPreservation-↓ N‴↝[p]↓N″

                  cfbhN‴≢[] : chainFromBlock b (blockHistory N‴) ≢ []
                  cfbhN‴≢[] = subst (_≢ []) (✓⇒gbIsHead ih′ .proj₂) (≢-sym []≢∷ʳ)

                  cfbhN‴≡cfbhN″ : chainFromBlock b (blockHistory N‴) ≡ chainFromBlock b (blockHistory N″)
                  cfbhN‴≡cfbhN″ = subsetCfbPreservation cfbhN″ bhN‴⊆bhN″ cfbhN‴≢[]

          ... | makeBlock {N′ = N″} N′MsgsDelivered N′—[eoN′]↑→∗N″ = makeBlockGoal (N′ .execOrder) N″↷↑N″[bM] cfN b∈hbhN uniqEoN′ (—[]→∗⇒—[]→∗ʳ N′—[eoN′]↑→∗N″)
            where
              ih : b ∈ honestBlockHistory N′ → chainFromBlock b (blockHistory N′) ✓
              ih b∈hbhN′ = honestBlockCfb✓ʳ N₀↝⋆ʳN′ ffN′ cfN′ b∈hbhN′

              N″↷↑N″[bM] : N″ ↷↑ record N″ { progress = blockMade }
              N″↷↑N″[bM] = progress↑ (↷↑-refl)

              uniqEoN′ : Unique (N′ .execOrder)
              uniqEoN′ = execOrderUniqueness N₀↝⋆N′

              makeBlockGoal : ∀ {N″} ps →
                  N″ ↷↑ N
                → isCollisionFree N″
                → b ∈ honestBlockHistory N″
                → Unique ps
                → _ ⊢ N′ —[ ps ]↑→∗ʳ N″
                → chainFromBlock b (blockHistory N″) ✓
              makeBlockGoal {N″} [] prfN cfN″ b∈hbhN″ _ [] = ih b∈hbhN″
              makeBlockGoal {N″} [] prfN cfN″ b∈hbhN″ _ (_∷ʳ_ {eq = eq} _ _) = contradiction eq []≢∷ʳ
              makeBlockGoal {N″} (p ∷ ps) prfN cfN″ b∈hbhN″ p∷psUniq (_∷ʳ_ {is = ps′} {i = p′} {s′ = N‴} {eq = eq} ts⋆ ts) = step ts
                where
                  cfN‴ : isCollisionFree N‴
                  cfN‴ = isCollisionFreePrev-↑ ts cfN″

                  p∉ps : p ∉ ps
                  p∉ps = Unique[x∷xs]⇒x∉xs p∷psUniq

                  psUniq : Unique ps
                  psUniq = U.tail p∷psUniq
                    where import Data.List.Relation.Unary.Unique.Propositional as U

                  ps′∷ʳp′Uniq : Unique (ps′ L.∷ʳ p′)
                  ps′∷ʳp′Uniq = subst Unique eq p∷psUniq

                  ps′Uniq : Unique ps′
                  ps′Uniq = headʳ ps′∷ʳp′Uniq

                  p′∉ps′ : p′ ∉ ps′
                  p′∉ps′ = Unique[xs∷ʳx]⇒x∉xs ps′∷ʳp′Uniq

                  ih′ : b ∈ honestBlockHistory N‴ → chainFromBlock b (blockHistory N‴) ✓
                  ih′ b∈hbhN‴ = makeBlockGoal {N‴} ps′ (blockMaking↑ ts prfN) cfN‴ b∈hbhN‴ ps′Uniq ts⋆

                  step : _ ⊢ N‴ —[ p′ ]↑→ N″ → chainFromBlock b (blockHistory N″) ✓
                  step (unknownParty↑ _) = ih′ b∈hbhN″
                  step (honestParty↑ {ls = ls} lsπ hp′π) with Params.winnerᵈ params {p′} {N‴ .clock}
                  ... | ⁇ (yes isWinner) = step-honestParty↑
                    where
                      best : Chain
                      best = bestChain (N‴ .clock ∸ 1) (ls .tree)

                      nb : Block
                      nb = mkBlock
                        (hash (tip best))
                        (N‴ .clock)
                        (txSelection (N‴ .clock) p′)
                        p′

                      b∈nb∷hbhN‴ : b ∈ nb ∷ honestBlockHistory N‴
                      b∈nb∷hbhN‴ rewrite hp′π = b∈hbhN″

                      bhπ : blockHistory N‴ ⊆ˢ nb ∷ blockHistory N‴
                      bhπ  = L.SubS.xs⊆x∷xs _ _

                      cfπ : isBlockListCollisionFree (nb ∷ blockHistory N‴)
                      cfπ = isBlockListCollisionFree-∷ {nb ∷ blockHistory N‴} {genesisBlock} cfN″

                      step-honestParty↑ : chainFromBlock b (nb ∷ blockHistory N‴) ✓
                      step-honestParty↑ with ∈-∷⁻ b∈nb∷hbhN‴
                      ... | inj₁ b≡nb rewrite b≡nb = subst _✓ (sym cfbIsNb∷Best) nb∷best✓
                        where
                          best✓ : best ✓
                          best✓ = valid (ls .tree) (N‴ .clock ∸ 1)

                          nb∷best✓ : (nb ∷ best) ✓
                          nb∷best✓ with ≢[]⇒∷ (✓⇒≢[] best✓)
                          ... | bestH , bestT , best≡bestH∷bestT
                            rewrite best≡bestH∷bestT =
                              ✓-∷ .Equivalence.to (isWinner , refl , nb>ˢbestH , subst _✓ best≡bestH∷bestT best✓)
                            where
                              nb>ˢbestH : N‴ .clock > bestH .slot -- i.e., nb >ˢ bestH
                              nb>ˢbestH = Nat.≤-<-trans bestHₛ≤N‴ₜ-1 N‴ₜ-1<N‴ₜ
                                where
                                  bestH∈best : bestH ∈ best
                                  bestH∈best rewrite best≡bestH∷bestT = x∈x∷xs bestT {bestH}

                                  bestHₛ≤N‴ₜ-1 : bestH .slot ≤ N‴ .clock ∸ 1
                                  bestHₛ≤N‴ₜ-1 = L.All.lookup (bestChainSlotBounded (ls .tree) (N‴ .clock ∸ 1)) bestH∈best

                                  N‴ₜ-1<N‴ₜ : N‴ .clock ∸ 1 < N‴ .clock
                                  N‴ₜ-1<N‴ₜ = pred[n]<n {N‴ .clock} ⦃ Nat.>-nonZero N‴ₜ>0 ⦄
                                    where
                                      N‴ₜ>0 : N‴ .clock > 0
                                      N‴ₜ>0 rewrite (clockPreservation-↑∗ (—[]→∗ʳ⇒—[]→∗ ts⋆)) = positiveClock N₀↝⋆N′

                          cfbIsNb∷Best : chainFromBlock nb (nb ∷ blockHistory N‴) ≡ nb ∷ best
                          cfbIsNb∷Best = cfbInBlockListIsSubset cfN″ nb∷best✓ bestInHist
                            where
                              -- TODO: Use ⊆-Reasoning
                              bestInHist : best ⊆ˢ genesisBlock ∷ nb ∷ blockHistory N‴
                              bestInHist = begin
                                best
                                  ⊆⟨ selfContained (ls .tree) (N‴ .clock ∸ 1) ⟩
                                filter (λ b → slot b ≤? (N‴ .clock ∸ 1)) (allBlocks (ls .tree))
                                  ⊆⟨ L.SubS.filter-⊆ (λ b → slot b ≤? (N‴ .clock ∸ 1)) (allBlocks (ls .tree)) ⟩
                                allBlocks (ls .tree)
                                  ⊆⟨ honestLocalTreeInHonestGlobalTree N₀↝⋆N′ hp′π ls[p′]inN′ ⟩
                                allBlocks (honestTree N′)
                                  ⊆⟨ honestGlobalTreeInBlockHistory N₀↝⋆N′ ⟩
                                genesisBlock ∷ blockHistory N′
                                  ⊆⟨ L.SubS.∷⁺ʳ _ (blockHistoryPreservation-↑∗ (—[]→∗ʳ⇒—[]→∗ ts⋆)) ⟩
                                genesisBlock ∷ blockHistory N‴
                                  ⊆⟨ L.SubS.xs⊆x∷xs _ _ ⟩
                                nb ∷ genesisBlock ∷ blockHistory N‴
                                  ⊆⟨ L.SubS.⊆-reflexive-↭ (swap _ _ refl) ⟩
                                genesisBlock ∷ nb ∷ blockHistory N‴ ∎
                                where
                                  open L.SubS.⊆-Reasoning Block
                                  open Data.List.Relation.Binary.Permutation.Propositional

                                  ls[p′]inN′ : N′ .states ⁉ p′ ≡ just ls
                                  ls[p′]inN′ rewrite sym $ localStatePreservation-↑∗ p′∉ps′ (—[]→∗ʳ⇒—[]→∗ ts⋆) = lsπ

                      ... | inj₂ b∈hbhN‴ = subsetCfb✓Preservation cfπ bhπ cfb✓π
                        where
                          cfb✓π : chainFromBlock b (blockHistory N‴) ✓
                          cfb✓π = ih′ b∈hbhN‴
                  ... | ⁇ (no _) = ih′ b∈hbhN″
                  step (corruptParty↑ _ _) = step-corruptParty↑
                    where
                      mds : List (Message × DelayMap)
                      mds =
                        makeBlockᶜ
                         (N‴ .clock)
                         (N‴ .history)
                         (N‴ .messages)
                         (N‴ .advState)
                         .proj₁

                      sub : L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                      sub = ffN .proj₂ (blockMaking↑ ts prfN)

                      b∈hbhN‴ : b ∈ honestBlockHistory N‴
                      b∈hbhN‴ = ≡ˢ⇒⊆×⊇ eqhs .proj₂ b∈hbhN″
                        where
                          eqhs : honestBlockHistory N‴ ≡ˢ honestBlockHistory (broadcastMsgsᶜ mds N‴)
                          eqhs = honestBlockHistoryPreservation-broadcastMsgsᶜ {N‴} {mds} sub

                      bhπ : blockHistory N‴ ⊆ˢ blockHistory (broadcastMsgsᶜ mds N‴)
                      bhπ  = blockHistoryPreservation-broadcastMsgsᶜ mds N‴

                      cfπ : isBlockListCollisionFree (blockHistory (broadcastMsgsᶜ mds N‴))
                      cfπ = isBlockListCollisionFree-∷ {blockHistory (broadcastMsgsᶜ mds N‴)} {genesisBlock} cfN″

                      cfb✓π : chainFromBlock b (blockHistory N‴) ✓
                      cfb✓π = ih′ b∈hbhN‴

                      step-corruptParty↑ : chainFromBlock b (blockHistory (broadcastMsgsᶜ mds N‴)) ✓
                      step-corruptParty↑ = subsetCfb✓Preservation cfπ bhπ cfb✓π

          ... | advanceRound   _ = honestBlockCfb✓ʳ N₀↝⋆ʳN′ ffN′ cfN b∈hbhN
          ... | permuteParties _ = honestBlockCfb✓ʳ N₀↝⋆ʳN′ ffN′ cfN b∈hbhN
          ... | permuteMsgs    _ = honestBlockCfb✓ʳ N₀↝⋆ʳN′ ffN′ cfN b∈hbhN

honestCfbPreservation-↓∗ : ∀ {N N′ : GlobalState} {b : Block} →
    N₀ ↝⋆ N
  → _ ⊢ N —[ N .execOrder ]↓→∗ N′
  → isForgingFree N
  → isCollisionFree N′
  → b ∈ honestBlockHistory N
  → N .progress ≡ ready
  → chainFromBlock b (blockHistory N) ≡ chainFromBlock b (blockHistory N′)
honestCfbPreservation-↓∗ {N} {N′} {b} N₀↝⋆N N—[eoN′]↓→∗N′ ffN cfN′ b∈hbhN NReady = subsetCfbPreservation cfbhN′ bhN⊆bhN′ cfbN≢[]
  where
    cfbhN′ : isBlockListCollisionFree (blockHistory N′)
    cfbhN′ = isBlockListCollisionFree-∷ {blockHistory N′} {genesisBlock} cfN′

    bhN⊆bhN′ : blockHistory N ⊆ˢ blockHistory N′
    bhN⊆bhN′ = blockHistoryPreservation-↓∗ N—[eoN′]↓→∗N′

    cfbN≢[] : chainFromBlock b (blockHistory N) ≢ []
    cfbN≢[] = ✓⇒≢[] cfbbN✓
      where
        N↝⋆N′↓ : N ↝⋆ record N′ {progress = msgsDelivered}
        N↝⋆N′↓ = deliverMsgs NReady N—[eoN′]↓→∗N′ ◅ ε
          where open RTC

        cfN : isCollisionFree N
        cfN = isCollisionFreePrev N↝⋆N′↓ cfN′

        cfbbN✓ : chainFromBlock b (blockHistory N) ✓
        cfbbN✓ = honestBlockCfb✓ N₀↝⋆N ffN cfN b∈hbhN

honestPosPreservation-↓∗ : ∀ {N N′ : GlobalState} {b : Block} →
    N₀ ↝⋆ N
  → _ ⊢ N —[ N .execOrder ]↓→∗ N′
  → isForgingFree N
  → isCollisionFree N′
  → b ∈ honestBlockHistory N
  → N .progress ≡ ready
  → blockPos b N ≡ blockPos b N′
honestPosPreservation-↓∗ N₀↝⋆N N—[eoN′]↓→∗N′ ffN cfN′ b∈hbhN NReady = cong length $ honestCfbPreservation-↓∗ N₀↝⋆N N—[eoN′]↓→∗N′ ffN cfN′ b∈hbhN NReady

-- TODO: More involved than needed, simplify using superBlocksAltDef.
superBlocksInHonestBlockHistory :  ∀ {N} → superBlocks N ⊆ˢ honestBlockHistory N
superBlocksInHonestBlockHistory {N} {b} b∈sbsN =
  let
    (b∈hbh , bIsHonest , _) = L.Mem.∈-filter⁻ ¿ isSuperBlock ¿¹ {xs = blockHistory N} (L.Mem.∈-deduplicate⁻ _≟_ (filter ¿ isSuperBlock ¿¹ (blockHistory N)) b∈sbsN)
  in
    L.Mem.∈-filter⁺ ¿ isHonestBlock ¿¹ b∈hbh bIsHonest

superBlocksPreservation-↓∗ : ∀ {N N′ : GlobalState} →
    N₀ ↝⋆ N
  → _ ⊢ N —[ N .execOrder ]↓→∗ N′
  → isForgingFree record N′ { progress = msgsDelivered }
  → N .progress ≡ ready
  → superBlocks N ≡ˢ superBlocks N′
superBlocksPreservation-↓∗ {N} {N′} N₀↝⋆N N—[ps]↓→∗N′ ffN′ NReady {b} = begin
  b ∈ superBlocks N
    ≡⟨ cong (b ∈_) (superBlocksAltDef N) ⟩
  b ∈ (L.deduplicate _≟_ $ filter ¿ isSuperSlot ∘ slot ¿¹ (honestBlockHistory N))
    ∼⟨ deduplicate-cong $ filter-cong $ honestBlockHistoryPreservation-↓∗ N₀↝⋆N  N—[ps]↓→∗N′ ffN′ NReady ⟩
  b ∈ (L.deduplicate _≟_ $ filter ¿ isSuperSlot ∘ slot ¿¹ (honestBlockHistory N′))
    ≡⟨ cong (b ∈_) (sym $ superBlocksAltDef N′) ⟩
  b ∈ superBlocks N′ ∎
  where open Related.EquationalReasoning

-- The following lemma is a central step towards proving the common prefix property.
superBlockPositions : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → isCollisionFree N
  → isForgingFree N
  → L.All.All
      (λ where (sb , b) → blockPos sb N ≢ blockPos b N ⊎ sb ≡ b)
      (L.cartesianProduct (superBlocks N) (honestBlockHistory N))
superBlockPositions = superBlockPositionsʳ ∘ Star⇒Starʳ
  where
    open RTC; open Starʳ
    superBlockPositionsʳ : ∀ {N : GlobalState} →
        N₀ ↝⋆ʳ N
      → isCollisionFree N
      → isForgingFree N
      → L.All.All
          (λ where (sb , b) → blockPos sb N ≢ blockPos b N ⊎ sb ≡ b)
          (L.cartesianProduct (superBlocks N) (honestBlockHistory N))
    superBlockPositionsʳ εʳ cfp ffp = L.All.All.[]
    superBlockPositionsʳ {N} (_◅ʳ_ {j = N′} N₀↝⋆ʳN′ N′↝N) cfp ffp
      with
        ih ← superBlockPositionsʳ N₀↝⋆ʳN′ (isCollisionFreePrev (N′↝N ◅ ε) cfp) (isForgingFreePrev (N′↝N ◅ ε) ffp)
      | N′↝N
    ... | deliverMsgs {N′} {N″} N′Ready N′—[eoN′]↓→∗N″ = goal
      where
        ffN′ : isForgingFree N′
        ffN′ = isForgingFreePrev (N′↝N ◅ ε) ffp

        cfpN′ : isCollisionFree N′
        cfpN′ = isCollisionFreePrev (N′↝N ◅ ε) cfp

        N₀↝⋆N′ : N₀ ↝⋆ N′
        N₀↝⋆N′ = Starʳ⇒Star N₀↝⋆ʳN′

        hbhPres : honestBlockHistory N′ ≡ˢ honestBlockHistory N
        hbhPres = honestBlockHistoryPreservation-↓∗ N₀↝⋆N′ N′—[eoN′]↓→∗N″ ffp N′Ready

        goal :
          L.All.All
            (λ where (sb , b) → blockPos sb N ≢ blockPos b N ⊎ sb ≡ b)
            (L.cartesianProduct (superBlocks N) (honestBlockHistory N))
        goal = L.All.cartesianProduct⁺ (≡.setoid _) (≡.setoid _) _ _ pres′
          where
            open import Relation.Binary.PropositionalEquality.Properties as ≡

            goal′ :
              L.All.All
                (λ where (sb , b) → blockPos sb N′ ≢ blockPos b N′ ⊎ sb ≡ b)
                (L.cartesianProduct (superBlocks N) (honestBlockHistory N))
            goal′ = All-resp-≡ˢ (cartesianProduct-cong sbsPres hbhPres) ih
              where
                sbsPres : superBlocks N′ ≡ˢ superBlocks N
                sbsPres = superBlocksPreservation-↓∗ N₀↝⋆N′ N′—[eoN′]↓→∗N″ ffp N′Ready

            pres : ∀ {sb b} → sb ∈ superBlocks N → b ∈ honestBlockHistory N → blockPos sb N′ ≢ blockPos b N′ ⊎ sb ≡ b
            pres = cartesianProduct⁻ goal′

            blockPosPres : ∀ {b} → b ∈ honestBlockHistory N → blockPos b N′ ≡ blockPos b N
            blockPosPres {b} b∈hbhN = honestPosPreservation-↓∗ N₀↝⋆N′ N′—[eoN′]↓→∗N″ ffN′ cfp b∈hbhN′ N′Ready
              where
                b∈hbhN′ : b ∈ honestBlockHistory N′
                b∈hbhN′ = ≡ˢ⇒⊆×⊇ hbhPres .proj₂ b∈hbhN

            pres′ : ∀ {sb b} → sb ∈ superBlocks N → b ∈ honestBlockHistory N → blockPos sb N ≢ blockPos b N ⊎ sb ≡ b
            pres′ {sb} {b} sb∈sbsN b∈hbhN with pres {sb} {b} sb∈sbsN b∈hbhN
            ... | inj₂ sb≡b = inj₂ sb≡b
            ... | inj₁ possb≢posb with blockPosPres (superBlocksInHonestBlockHistory {N} sb∈sbsN) | blockPosPres b∈hbhN
            ... |  eqsb | eqb = inj₁ (subst₂ _≢_ eqsb eqb possb≢posb)

    ... | makeBlock {N′} {N″} N′MsgsDelivered N′—[eoN′]↑→∗N″ = {!!}
    ... | advanceRound   _                  = ih
    ... | permuteParties _                  = ih
    ... | permuteMsgs    _                  = ih
