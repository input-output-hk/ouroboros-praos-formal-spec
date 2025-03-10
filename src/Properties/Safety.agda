open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot; slot₀; Honesty)
open import Protocol.Params using (Params)
open import Protocol.Block
open import Protocol.Chain using (Chain; genesisBlock; tip; chainFromBlock; _✓; ✓⇒≢[]; ✓⇒gbIsHead; ✓-∷; cfbStartsWithBlock; DecreasingSlots)
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
open import Data.Nat.Properties using (<-trans; 0≢1+n; +-comm)
open import Data.Nat.Properties.Ext using (pred[n]<n; suc-≢-injective)
open import Data.List.Properties.Ext using (filter-∘-comm; filter-∘-×; []≢∷ʳ; Px-findᵇ⁻; ∷≢[]; ≢[]⇒∷; filter-acceptʳ; filter-rejectʳ)
open import Data.List.Relation.Unary.Linked.Properties using (Linked⇒AllPairs)
open import Data.List.Relation.Unary.Unique.Propositional.Properties.Ext using (++⁻; Unique[x∷xs]⇒x∉xs; Unique[xs∷ʳx]⇒x∉xs)
open import Data.List.Relation.Unary.All.Properties.Ext using (cartesianProduct⁻)
open import Data.List.Relation.Unary.AllPairs.Properties.Ext renaming (++⁻ to AP-++⁻)
open import Data.List.Relation.Binary.Permutation.Propositional using (↭-refl; ↭-trans)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties.Ext using (Unique-resp-↭; length-cong; filter-↭)
open import Data.List.Relation.Binary.Subset.Propositional.Properties.Ext using (cartesianProduct-⊆-Mono; filterᵇ-mono; ∷-⊆; ∷-⊆⁺; ∷⊆⇒∈)
open import Data.List.Membership.Propositional.Properties.Ext using (x∈x∷xs; ∈-∷⁻; ∈-findᵇ⁻; ∈-∷-≢⁻)
open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_; ≡ˢ-refl; ≡ˢ-sym; ≡ˢ-trans; ≡ˢ⇒⊆×⊇; ⊆×⊇⇒≡ˢ; deduplicate-cong; filter-cong; All-resp-≡ˢ; Any-resp-≡ˢ; cartesianProduct-cong)
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

honestGlobalTreeInHonestLocalTree : ∀ {N N′ : GlobalState} {p : Party} {ls : LocalState} →
    N₀ ↝⋆ N
  → isHonest p
  → N .progress ≡ ready
  → N′ .progress ≡ msgsDelivered
  → N ↝⋆⟨ 0 ⟩ N′
  → N′ .states ⁉ p ≡ just ls
  → allBlocks (honestTree N) ⊆ˢ allBlocks (ls .tree)
honestGlobalTreeInHonestLocalTree = {!!}

honestGlobalTreeInBlockHistory : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → allBlocks (honestTree N) ⊆ˢ genesisBlock ∷ blockHistory N
honestGlobalTreeInBlockHistory = {!!}

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

∃ReadyBeforeMsgsDelivered : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → N .progress ≡ msgsDelivered
  → ∃[ N′ ] N₀ ↝⋆ N′ × N′ ↝⋆⟨ 0 ⟩ N × N′ .progress ≡ ready
∃ReadyBeforeMsgsDelivered = {!!}

allPartiesHaveLocalState : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → L.All.All (M.Is-just ∘ (N .states ⁉_)) (N .execOrder)
allPartiesHaveLocalState = {!!}

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

∈-superBlocks⁻ : ∀ {N : GlobalState} {b : Block} → b ∈ superBlocks N → b ∈ blockHistory N × isSuperBlock b
∈-superBlocks⁻ = L.Mem.∈-filter⁻ _ ∘ L.Mem.∈-deduplicate⁻ _ _

∈-superBlocks⁺ : ∀ {N : GlobalState} {b : Block} → b ∈ blockHistory N → isSuperBlock b → b ∈ superBlocks N
∈-superBlocks⁺ = L.Mem.∈-deduplicate⁺ _ ∘₂ L.Mem.∈-filter⁺ _

superBlocksAltDef : ∀ N → superBlocks N ≡ (L.deduplicate _≟_ $ filter ¿ isSuperSlot ∘ slot ¿¹ (honestBlockHistory N))
superBlocksAltDef N
  rewrite filter-∘-comm ¿ isSuperSlot ∘ slot ¿¹ ¿ isHonest ∘ pid ¿¹ (blockHistory N)
    | sym $ filter-∘-× ¿ isHonest ∘ pid ¿¹ ¿ isSuperSlot ∘ slot ¿¹ (blockHistory N)
    = refl

superBlocks⊆honestBlockHistory : ∀ (N : GlobalState) → superBlocks N ⊆ˢ honestBlockHistory N
superBlocks⊆honestBlockHistory N rewrite superBlocksAltDef N = begin
  (L.deduplicate _≟_ $ filter ¿ isSuperSlot ∘ slot ¿¹ (honestBlockHistory N))
    ⊆⟨ L.Mem.∈-deduplicate⁻ _≟_ _ ⟩
  filter ¿ isSuperSlot ∘ slot ¿¹ (honestBlockHistory N)
    ⊆⟨ L.SubS.filter-⊆ _ _ ⟩
  honestBlockHistory N ∎
  where open L.SubS.⊆-Reasoning _

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

  honestBlockHistoryPreservation-↝⋆⟨0⟩ : ∀ {N N′ : GlobalState} →
      N₀ ↝⋆ N
    → N .progress ≡ ready
    → N ↝⋆⟨ 0 ⟩ N′
    → isForgingFree N′
    → N′ .progress ≡ msgsDelivered
    → honestBlockHistory N ≡ˢ honestBlockHistory N′
  honestBlockHistoryPreservation-↝⋆⟨0⟩ = {!!}

noPrematureHonestBlocksAtReady : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → isForgingFree N
  → N .progress ≡ ready
  → L.All.All (λ b → b .slot < N .clock) (honestBlockHistory N)
noPrematureHonestBlocksAtReady = {!!}

noPrematureHonestBlocksAt↓ : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → isForgingFree N
  → N .progress ≡ msgsDelivered
  → L.All.All (λ b → b .slot < N .clock) (honestBlockHistory N)
noPrematureHonestBlocksAt↓ = {!!}

noPrematureHonestBlocks : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → isForgingFree N
  → L.All.All (λ b → b .slot ≤ N .clock) (honestBlockHistory N)
noPrematureHonestBlocks = {!!}

honestBlocksBelowSlotPreservation : ∀ {N N′ : GlobalState} →
    N₀ ↝⋆ N
  → N ↝⋆ N′
  → isForgingFree N′
  → filter (λ b → b .slot <? N .clock) (honestBlockHistory N)
    ≡ˢ
    filter (λ b → b .slot <? N .clock) (honestBlockHistory N′)
honestBlocksBelowSlotPreservation = {!!}

honestBlockCfb✓∗ : ∀ {N₁ N₂ N′ : GlobalState} {ps : List Party} →
    N₀ ↝⋆ N₁
  → N₁ ↝⋆ N₂
  → isForgingFree N₂
  → _ ⊢ N₁ —[ ps ]↑→∗ N′
  → N′ ↷↑ N₂
  → Unique ps
  → isCollisionFree N′
  → L.All.All (λ b → chainFromBlock b (blockHistory N′) ✓) (honestBlockHistory N′)
honestBlockCfb✓∗ = {!!}

cfbInHonestTree : ∀ {N : GlobalState} {b : Block} →
    N₀ ↝⋆ N
  → isForgingFree N
  → isCollisionFree N
  → b ∈ honestBlockHistory N
  → chainFromBlock b (blockHistory N) ⊆ˢ allBlocks (honestTree N)
cfbInHonestTree = {!!}

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
honestPosPreservation-↓∗ N₀↝⋆N N—[eoN′]↓→∗N′ ffN cfN′ b∈hbhN NReady = cong ∣_∣ $ honestCfbPreservation-↓∗ N₀↝⋆N N—[eoN′]↓→∗N′ ffN cfN′ b∈hbhN NReady

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

private opaque

  unfolding honestBlockMaking corruptBlockMaking _✓

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
      superBlockPositionsʳ {N} (_◅ʳ_ {j = N′} N₀↝⋆ʳN′ N′↝N) cfN ffN
        with
          ih ← superBlockPositionsʳ N₀↝⋆ʳN′ (isCollisionFreePrev (N′↝N ◅ ε) cfN) (isForgingFreePrev (N′↝N ◅ ε) ffN)
        | N′↝N
      ... | deliverMsgs {N′} {N″} N′Ready N′—[eoN′]↓→∗N″ = goal
        where
          ffN′ : isForgingFree N′
          ffN′ = isForgingFreePrev (N′↝N ◅ ε) ffN

          cfpN′ : isCollisionFree N′
          cfpN′ = isCollisionFreePrev (N′↝N ◅ ε) cfN

          N₀↝⋆N′ : N₀ ↝⋆ N′
          N₀↝⋆N′ = Starʳ⇒Star N₀↝⋆ʳN′

          hbhPres : honestBlockHistory N′ ≡ˢ honestBlockHistory N
          hbhPres = honestBlockHistoryPreservation-↓∗ N₀↝⋆N′ N′—[eoN′]↓→∗N″ ffN N′Ready

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
                  sbsPres = superBlocksPreservation-↓∗ N₀↝⋆N′ N′—[eoN′]↓→∗N″ ffN N′Ready

              pres : ∀ {sb b} → sb ∈ superBlocks N → b ∈ honestBlockHistory N → blockPos sb N′ ≢ blockPos b N′ ⊎ sb ≡ b
              pres = cartesianProduct⁻ goal′

              blockPosPres : ∀ {b} → b ∈ honestBlockHistory N → blockPos b N′ ≡ blockPos b N
              blockPosPres {b} b∈hbhN = honestPosPreservation-↓∗ N₀↝⋆N′ N′—[eoN′]↓→∗N″ ffN′ cfN b∈hbhN′ N′Ready
                where
                  b∈hbhN′ : b ∈ honestBlockHistory N′
                  b∈hbhN′ = ≡ˢ⇒⊆×⊇ hbhPres .proj₂ b∈hbhN

              pres′ : ∀ {sb b} → sb ∈ superBlocks N → b ∈ honestBlockHistory N → blockPos sb N ≢ blockPos b N ⊎ sb ≡ b
              pres′ {sb} {b} sb∈sbsN b∈hbhN with pres {sb} {b} sb∈sbsN b∈hbhN
              ... | inj₂ sb≡b = inj₂ sb≡b
              ... | inj₁ possb≢posb with blockPosPres (superBlocksInHonestBlockHistory {N} sb∈sbsN) | blockPosPres b∈hbhN
              ... |  eqsb | eqb = inj₁ (subst₂ _≢_ eqsb eqb possb≢posb)

      ... | makeBlock {N′} {N″} N′MsgsDelivered N′—[eoN′]↑→∗N″ = goal
        where
          ffN′ : isForgingFree N′
          ffN′ = isForgingFreePrev (N′↝N ◅ ε) ffN

          cfN′ : isCollisionFree N′
          cfN′ = isCollisionFreePrev (N′↝N ◅ ε) cfN

          N₀↝⋆N′ : N₀ ↝⋆ N′
          N₀↝⋆N′ = Starʳ⇒Star N₀↝⋆ʳN′

          N″ₜ≡N′ₜ : N″ .clock ≡ N′ .clock
          N″ₜ≡N′ₜ = clockPreservation-↑∗ N′—[eoN′]↑→∗N″

          goal :
            L.All.All
              (λ where (sb , b) → blockPos sb N ≢ blockPos b N ⊎ sb ≡ b)
              (L.cartesianProduct (superBlocks N) (honestBlockHistory N))
          goal = L.All.cartesianProduct⁺ (≡.setoid _) (≡.setoid _) _ _ pres′
            where
              open import Relation.Binary.PropositionalEquality.Properties as ≡

              N′↝⋆N : N′ ↝⋆ N
              N′↝⋆N = Starʳ⇒Star (εʳ ◅ʳ N′↝N)

              N₀↝⋆N : N₀ ↝⋆ N
              N₀↝⋆N = N₀↝⋆N′ ◅◅ N′↝⋆N

              nphb : ∀ {b} → b ∈ honestBlockHistory N → b .slot ≤ N .clock
              nphb = L.All.lookup (noPrematureHonestBlocks N₀↝⋆N ffN)

              pres′ : ∀ {sb b} → sb ∈ superBlocks N → b ∈ honestBlockHistory N → blockPos sb N ≢ blockPos b N ⊎ sb ≡ b
              pres′ {sb} {b} sb∈sbsN b∈hbhN
                with sb∈hbhN ← superBlocks⊆honestBlockHistory N sb∈sbsN | Nat.m≤n⇒m<n∨m≡n (nphb sb∈hbhN)
              ... | inj₁ sbₜ<Nₜ = goal-sbₜ<Nₜ
                where
                  sb∈fhbhN′ : sb ∈ filter (λ b′ → b′ .slot <? N′ .clock) (honestBlockHistory N′)
                  sb∈fhbhN′ =
                         sb∈hbhN ∶
                    sb ∈ honestBlockHistory N
                      |> λ ◆ → L.Mem.∈-filter⁺ _ ◆ sbₜ<Nₜ ∶
                    sb ∈ filter (λ b′ → b′ .slot <? N .clock) (honestBlockHistory N)
                      |> subst _ (clockPreservation-↑∗ N′—[eoN′]↑→∗N″) ∶
                    sb ∈ filter (λ b′ → b′ .slot <? N′ .clock) (honestBlockHistory N)
                      |> ≡ˢ⇒⊆×⊇ (honestBlocksBelowSlotPreservation N₀↝⋆N′ N′↝⋆N ffN) .proj₂ ∶
                    sb ∈ filter (λ b′ → b′ .slot <? N′ .clock) (honestBlockHistory N′)
                    where open import Function.Reasoning

                  sb∈hbhN′ : sb ∈ honestBlockHistory N′
                  sb∈hbhN′ = L.SubS.filter-⊆ _ _ sb∈fhbhN′

                  sb∈sbsN′ : sb ∈ superBlocks N′
                  sb∈sbsN′ = ∈-superBlocks⁺ {N′} (L.Mem.∈-filter⁻ _ {xs = blockHistory N′} sb∈hbhN′ .proj₁) (∈-superBlocks⁻ {N} sb∈sbsN .proj₂)

                  goal-sbₜ<Nₜ : blockPos sb N ≢ blockPos b N ⊎ sb ≡ b
                  goal-sbₜ<Nₜ with ∃ReadyBeforeMsgsDelivered N₀↝⋆N′ N′MsgsDelivered
                  ... | Nᴿ , N₀↝⋆Nᴿ , Nᴿ↝⋆⟨0⟩N′ , NᴿReady = makeBlockGoal-sbₜ<Nₜ (N′ .execOrder) N″↷↑N″[bM] cfN b∈hbhN uniqEoN′ (—[]→∗⇒—[]→∗ʳ N′—[eoN′]↑→∗N″)
                    where

                      sb∈hbhNᴿ : sb ∈ honestBlockHistory Nᴿ
                      sb∈hbhNᴿ = ≡ˢ⇒⊆×⊇ (honestBlockHistoryPreservation-↝⋆⟨0⟩ N₀↝⋆Nᴿ NᴿReady Nᴿ↝⋆⟨0⟩N′ ffN′ N′MsgsDelivered) .proj₂ sb∈hbhN′

                      Nᴿ↝⋆N′ : Nᴿ ↝⋆ N′
                      Nᴿ↝⋆N′ = Nᴿ↝⋆⟨0⟩N′ .proj₁

                      Nᴿ↝⋆N : Nᴿ ↝⋆ N
                      Nᴿ↝⋆N = Nᴿ↝⋆N′ ◅◅ N′↝⋆N

                      Nᴿₜ≡N′ₜ : Nᴿ .clock ≡ N′ .clock
                      Nᴿₜ≡N′ₜ = Nᴿ↝⋆⟨0⟩N′ .proj₂

                      ffNᴿ : isForgingFree Nᴿ
                      ffNᴿ = isForgingFreePrev Nᴿ↝⋆N′ ffN′

                      cfNᴿ : isCollisionFree Nᴿ
                      cfNᴿ = isCollisionFreePrev Nᴿ↝⋆N′ cfN′

                      cfbhNᴿ≢[] : chainFromBlock sb (blockHistory Nᴿ) ≢ []
                      cfbhNᴿ≢[] = subst (_≢ []) (✓⇒gbIsHead cfbhNᴿ✓ .proj₂) (≢-sym []≢∷ʳ)
                        where
                          cfbhNᴿ✓ : chainFromBlock sb (blockHistory Nᴿ) ✓
                          cfbhNᴿ✓ = L.All.lookup (L.All.tabulate $ λ {b} → honestBlockCfb✓ N₀↝⋆Nᴿ ffNᴿ cfNᴿ) sb∈hbhNᴿ

                      cfbhNᴿ≡cfbhN′ : chainFromBlock sb (blockHistory Nᴿ) ≡ chainFromBlock sb (blockHistory N′)
                      cfbhNᴿ≡cfbhN′ = subsetCfbPreservation cfbhN′ bhNᴿ⊆bhN′ cfbhNᴿ≢[]
                        where
                          cfbhN′ : isBlockListCollisionFree (blockHistory N′)
                          cfbhN′ = isBlockListCollisionFree-∷ {blockHistory N′} {genesisBlock} cfN′

                          bhNᴿ⊆bhN′ : blockHistory Nᴿ ⊆ˢ blockHistory N′
                          bhNᴿ⊆bhN′ = blockHistoryPreservation-↝⋆ Nᴿ↝⋆N′

                      cfbhNᴿ≡cfbhN : chainFromBlock sb (blockHistory Nᴿ) ≡ chainFromBlock sb (blockHistory N)
                      cfbhNᴿ≡cfbhN = subsetCfbPreservation cfbhN bhNᴿ⊆bhN cfbhNᴿ≢[]
                        where
                          cfbhN : isBlockListCollisionFree (blockHistory N)
                          cfbhN = isBlockListCollisionFree-∷ {blockHistory N} {genesisBlock} cfN

                          bhNᴿ⊆bhN : blockHistory Nᴿ ⊆ˢ blockHistory N
                          bhNᴿ⊆bhN = blockHistoryPreservation-↝⋆ Nᴿ↝⋆N

                      ih′ : b ∈ honestBlockHistory N′ → blockPos sb Nᴿ ≢ blockPos b N′ ⊎ sb ≡ b
                      ih′ b∈hbhN′ = subst (λ ◆ → ∣ ◆ ∣ ≢ blockPos b N′ ⊎ sb ≡ b) (sym cfbhNᴿ≡cfbhN′) (cartesianProduct⁻ (superBlockPositionsʳ N₀↝⋆ʳN′ cfN′ ffN′) sb∈sbsN′ b∈hbhN′)

                      N″↷↑N″[bM] : N″ ↷↑ record N″ { progress = blockMade }
                      N″↷↑N″[bM] = progress↑ (↷↑-refl)

                      uniqEoN′ : Unique (N′ .execOrder)
                      uniqEoN′ = execOrderUniqueness N₀↝⋆N′

                      makeBlockGoal-sbₜ<Nₜ : ∀ {N*} ps →
                          N* ↷↑ N
                        → isCollisionFree N*
                        → b ∈ honestBlockHistory N*
                        → Unique ps
                        → _ ⊢ N′ —[ ps ]↑→∗ʳ N*
                        → blockPos sb N ≢ blockPos b N* ⊎ sb ≡ b
                      makeBlockGoal-sbₜ<Nₜ rewrite sym cfbhNᴿ≡cfbhN = makeBlockGoal-sbₜ<Nₜ′
                        where
                          makeBlockGoal-sbₜ<Nₜ′ : ∀ {N*} ps →
                              N* ↷↑ N
                            → isCollisionFree N*
                            → b ∈ honestBlockHistory N*
                            → Unique ps
                            → _ ⊢ N′ —[ ps ]↑→∗ʳ N*
                            → blockPos sb Nᴿ ≢ blockPos b N* ⊎ sb ≡ b
                          makeBlockGoal-sbₜ<Nₜ′ {N*} [] _ _ b∈hbhN* _ [] = ih′ b∈hbhN*
                          makeBlockGoal-sbₜ<Nₜ′ {N*} [] _ _ _ _ (_∷ʳ_ {eq = eq} _ _) = contradiction eq []≢∷ʳ
                          makeBlockGoal-sbₜ<Nₜ′ {N*} (p ∷ ps) prfN cfN* b∈hbhN* p∷psUniq (_∷ʳ_ {is = ps′} {i = p′} {s′ = N‴} {eq = eq} ts⋆ ts) = step ts
                            where
                              cfN‴ : isCollisionFree N‴
                              cfN‴ = isCollisionFreePrev-↑ ts cfN*

                              ps′∷ʳp′Uniq : Unique (ps′ L.∷ʳ p′)
                              ps′∷ʳp′Uniq = subst Unique eq p∷psUniq

                              ps′Uniq : Unique ps′
                              ps′Uniq = headʳ ps′∷ʳp′Uniq

                              p′∉ps′ : p′ ∉ ps′
                              p′∉ps′ = Unique[xs∷ʳx]⇒x∉xs ps′∷ʳp′Uniq

                              ih* : b ∈ honestBlockHistory N‴ → blockPos sb Nᴿ ≢ blockPos b N‴ ⊎ sb ≡ b
                              ih* b∈hbhN‴ = makeBlockGoal-sbₜ<Nₜ′ {N‴} ps′ (blockMaking↑ ts prfN) cfN‴ b∈hbhN‴ ps′Uniq ts⋆

                              step : _ ⊢ N‴ —[ p′ ]↑→ N* → blockPos sb Nᴿ ≢ blockPos b N* ⊎ sb ≡ b
                              step (unknownParty↑ _) = ih* b∈hbhN*
                              step (honestParty↑ {ls = ls} lsπ hp′π) with Params.winnerᵈ params {p′} {N‴ .clock}
                              ... | ⁇ (yes isWinner) rewrite lsπ = step-honestParty↑
                                where
                                  lsN′ : N′ .states ⁉ p′ ≡ just ls
                                  lsN′ rewrite sym $ localStatePreservation-↑∗ p′∉ps′ (—[]→∗ʳ⇒—[]→∗ ts⋆) = lsπ

                                  best : Chain
                                  best = bestChain (N‴ .clock ∸ 1) (ls .tree)

                                  nb : Block
                                  nb = mkBlock
                                    (hash (tip best))
                                    (N‴ .clock)
                                    (txSelection (N‴ .clock) p′)
                                    p′

                                  b∈nb∷hbhN‴ : b ∈ nb ∷ honestBlockHistory N‴
                                  b∈nb∷hbhN‴ rewrite hp′π = b∈hbhN*

                                  bhπ : blockHistory N‴ ⊆ˢ nb ∷ blockHistory N‴
                                  bhπ  = L.SubS.xs⊆x∷xs _ _

                                  cfπ : isBlockListCollisionFree (nb ∷ blockHistory N‴)
                                  cfπ = isBlockListCollisionFree-∷ {nb ∷ blockHistory N‴} {genesisBlock} cfN*

                                  cfb≢[] : b ∈ honestBlockHistory N‴ → chainFromBlock b (blockHistory N‴) ≢ []
                                  cfb≢[] b∈hbhN‴ = subst (_≢ []) (✓⇒gbIsHead cfbhN‴✓ .proj₂) (≢-sym []≢∷ʳ)
                                    where
                                      cfbhN‴✓ : chainFromBlock b (blockHistory N‴) ✓
                                      cfbhN‴✓ = L.All.lookup (honestBlockCfb✓∗ N₀↝⋆N′ N′↝⋆N ffN (—[]→∗ʳ⇒—[]→∗ ts⋆) (blockMaking↑ ts prfN) ps′Uniq cfN‴) b∈hbhN‴

                                  step-honestParty↑ : blockPos sb Nᴿ ≢ ∣ chainFromBlock b (nb ∷ blockHistory N‴) ∣ ⊎ sb ≡ b
                                  step-honestParty↑ with ∈-∷⁻ b∈nb∷hbhN‴ | b ≟ nb
                                  ... | inj₁ b≡nb    | no b≢nb = contradiction b≡nb b≢nb
                                  ... | inj₂ b∈hbhN‴ | no _ rewrite sym $ subsetCfbPreservation cfπ bhπ (cfb≢[] b∈hbhN‴) = ih* b∈hbhN‴
                                  ... | _            | yes b≡nb rewrite b≡nb = subst (λ ◆ → blockPos sb Nᴿ ≢ ∣ ◆ ∣ ⊎ sb ≡ nb) (sym cfb≡nb∷best) possb
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

                                      cfb≡nb∷best : chainFromBlock nb (nb ∷ blockHistory N‴) ≡ nb ∷ best
                                      cfb≡nb∷best = cfbInBlockListIsSubset cfN* nb∷best✓ bestInHist
                                        where
                                          bestInHist : best ⊆ˢ genesisBlock ∷ nb ∷ blockHistory N‴
                                          bestInHist = begin
                                            best
                                              ⊆⟨ selfContained (ls .tree) (N‴ .clock ∸ 1) ⟩
                                            filter (λ b → slot b ≤? (N‴ .clock ∸ 1)) (allBlocks (ls .tree))
                                              ⊆⟨ L.SubS.filter-⊆ (λ b → slot b ≤? (N‴ .clock ∸ 1)) (allBlocks (ls .tree)) ⟩
                                            allBlocks (ls .tree)
                                              ⊆⟨ honestLocalTreeInHonestGlobalTree N₀↝⋆N′ hp′π lsN′ ⟩
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

                                      possb : blockPos sb Nᴿ ≢ ∣ nb ∷ best ∣ ⊎ sb ≡ nb
                                      possb with chainFromBlock sb (blockHistory Nᴿ) in cfbNᴿEq
                                      ... | []     = inj₁ $ (flip contradiction) Nat.0≢1+n
                                      ... | b′ ∷ c = inj₁ $ contraposition Nat.suc-injective ∣c∣≢∣best∣
                                        where
                                          ∣b′∷c∣≤∣best∣ : ∣ b′ ∷ c ∣ ≤ ∣ best ∣
                                          ∣b′∷c∣≤∣best∣ = subst (λ ◆ → ∣ ◆ ∣ ≤ ∣ best ∣) cfbNᴿEq $ optimal (chainFromBlock sb (blockHistory Nᴿ)) (ls .tree) (N‴ .clock ∸ 1) cfbNᴿ✓ cfbNᴿ⊆t
                                            where
                                              cfbNᴿ✓ : chainFromBlock sb (blockHistory Nᴿ) ✓
                                              cfbNᴿ✓ = honestBlockCfb✓ N₀↝⋆Nᴿ ffNᴿ cfNᴿ sb∈hbhNᴿ

                                              cfbNᴿ⊆t : chainFromBlock sb (blockHistory Nᴿ) ⊆ˢ filter (λ b″ → b″ .slot ≤? N‴ .clock ∸ 1) (allBlocks (ls .tree))
                                              cfbNᴿ⊆t {b″} b″∈cfb = L.Mem.∈-filter⁺ _ {xs = allBlocks (ls .tree)} b″∈t b″ₜ≤N‴ₜ-1
                                                where
                                                  b″∈t : b″ ∈ allBlocks (ls .tree)
                                                  b″∈t = L.SubS.⊆-trans π₁ π₂  b″∈cfb
                                                    where
                                                      π₁ : chainFromBlock sb (blockHistory Nᴿ) ⊆ˢ allBlocks (honestTree Nᴿ)
                                                      π₁ = cfbInHonestTree N₀↝⋆Nᴿ ffNᴿ cfNᴿ sb∈hbhNᴿ

                                                      π₂ : allBlocks (honestTree Nᴿ) ⊆ˢ allBlocks (ls .tree)
                                                      π₂ = honestGlobalTreeInHonestLocalTree N₀↝⋆Nᴿ hp′π NᴿReady N′MsgsDelivered Nᴿ↝⋆⟨0⟩N′ lsN′

                                                  b″ₜ≤N‴ₜ-1 : b″ .slot ≤ N‴ .clock ∸ 1
                                                  b″ₜ≤N‴ₜ-1 rewrite clockPreservation-↑∗ (—[]→∗ʳ⇒—[]→∗ ts⋆) = Nat.≤-trans {j = sb .slot} b″ₜ≤sbₜ sbₜ≤N′ₜ-1
                                                    where
                                                      b″ₜ≤sbₜ : b″ .slot ≤ sb .slot
                                                      b″ₜ≤sbₜ with cfbStartsWithBlock {sb} {blockHistory Nᴿ} (subst (_≢ []) (sym cfbNᴿEq) ∷≢[])
                                                      ... | c′ , cfb≡sb∷c′ = case ∈-∷⁻ b″∈b′∷c of λ where
                                                           (inj₁ b″≡b′) → subst (λ ◆ → ◆ .slot ≤ sb .slot) (sym $ trans b″≡b′ b′≡sb) Nat.≤-refl
                                                           (inj₂ b″∈c) → Nat.<⇒≤ (sb>ˢb″ b″∈c)
                                                        where
                                                          b″∈b′∷c : b″ ∈ b′ ∷ c
                                                          b″∈b′∷c rewrite cfbNᴿEq = b″∈cfb

                                                          b′∷c≡sb∷c′ : _≡_ {A = List Block} (b′ ∷ c) (sb ∷ c′)
                                                          b′∷c≡sb∷c′ = trans (sym cfbNᴿEq) cfb≡sb∷c′

                                                          b′≡sb : b′ ≡ sb
                                                          b′≡sb = L.∷-injective b′∷c≡sb∷c′ .proj₁

                                                          [b′∷c]✓ : (b′ ∷ c) ✓
                                                          [b′∷c]✓ = subst _✓ cfbNᴿEq $ honestBlockCfb✓ N₀↝⋆Nᴿ ffNᴿ cfNᴿ sb∈hbhNᴿ

                                                          ds[b′∷c] : DecreasingSlots (b′ ∷ c)
                                                          ds[b′∷c] = [b′∷c]✓ .proj₂ .proj₂

                                                          b′>ˢc : L.All.All (b′ >ˢ_) c
                                                          b′>ˢc = L.All.head $ AP-++⁻ (Linked⇒AllPairs (λ {b b′ b″} → >ˢ-trans {b} {b′} {b″}) ds[b′∷c]) .proj₂ .proj₂
                                                          sb>ˢb″ : b″ ∈ c → sb >ˢ b″
                                                          sb>ˢb″ rewrite sym b′≡sb = L.All.lookup b′>ˢc

                                                      sbₜ≤N′ₜ-1 : sb .slot ≤ N′ .clock ∸ 1
                                                      sbₜ≤N′ₜ-1 = Nat.<⇒≤pred $ L.Mem.∈-filter⁻ (λ b′ → b′ .slot <? N′ .clock) {xs = honestBlockHistory N′} sb∈fhbhN′ .proj₂

                                          ∣c∣≢∣best∣ : ∣ c ∣ ≢ ∣ best ∣
                                          ∣c∣≢∣best∣ p = contradiction (subst (∣ b′ ∷ c ∣ ≤_) (sym p) ∣b′∷c∣≤∣best∣) Nat.1+n≰n

                              ... | ⁇ (no _) = ih* b∈hbhN*
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
                                  b∈hbhN‴ = ≡ˢ⇒⊆×⊇ eqhs .proj₂ b∈hbhN*
                                    where
                                      eqhs : honestBlockHistory N‴ ≡ˢ honestBlockHistory (broadcastMsgsᶜ mds N‴)
                                      eqhs = honestBlockHistoryPreservation-broadcastMsgsᶜ {N‴} {mds} sub

                                  bhπ : blockHistory N‴ ⊆ˢ blockHistory (broadcastMsgsᶜ mds N‴)
                                  bhπ  = blockHistoryPreservation-broadcastMsgsᶜ mds N‴

                                  cfπ : isBlockListCollisionFree (blockHistory (broadcastMsgsᶜ mds N‴))
                                  cfπ = isBlockListCollisionFree-∷ {blockHistory (broadcastMsgsᶜ mds N‴)} {genesisBlock} cfN*

                                  cfb≢[] : chainFromBlock b (blockHistory N‴) ≢ []
                                  cfb≢[] = subst (_≢ []) (✓⇒gbIsHead cfbhN‴✓ .proj₂) (≢-sym []≢∷ʳ)
                                    where
                                      cfbhN‴✓ : chainFromBlock b (blockHistory N‴) ✓
                                      cfbhN‴✓ = L.All.lookup (honestBlockCfb✓∗ N₀↝⋆N′ N′↝⋆N ffN (—[]→∗ʳ⇒—[]→∗ ts⋆) (blockMaking↑ ts prfN) ps′Uniq cfN‴) b∈hbhN‴

                                  step-corruptParty↑ : blockPos sb Nᴿ ≢ blockPos b (broadcastMsgsᶜ mds N‴) ⊎ sb ≡ b
                                  step-corruptParty↑ rewrite sym $ subsetCfbPreservation cfπ bhπ cfb≢[] = ih* b∈hbhN‴

              ... | inj₂ sbₜ≡Nₜ = goal-sbₜ≡Nₜ
                where
                  N″↷↑N″[bM] : N″ ↷↑ record N″ { progress = blockMade }
                  N″↷↑N″[bM] = progress↑ (↷↑-refl)

                  uniqEoN′ : Unique (N′ .execOrder)
                  uniqEoN′ = execOrderUniqueness N₀↝⋆N′

                  sbIsHonest : isHonest (sb .pid)
                  sbIsHonest = ∈-superBlocks⁻ {N} sb∈sbsN .proj₂ .proj₁

                  sbHasSuperSlot : isSuperSlot (sb .slot)
                  sbHasSuperSlot = ∈-superBlocks⁻ {N} sb∈sbsN .proj₂ .proj₂

                  goal-sbₜ≡Nₜ : blockPos sb N ≢ blockPos b N ⊎ sb ≡ b
                  goal-sbₜ≡Nₜ = makeBlockGoal-sbₜ≡Nₜ (N′ .execOrder) (allPartiesHaveLocalState N₀↝⋆N′) eoSb N″↷↑N″[bM] cfN (L.SubS.filter-⊆ _ _ sb∈hbhN) b∈hbhN uniqEoN′ (—[]→∗⇒—[]→∗ʳ N′—[eoN′]↑→∗N″)
                    where
                      eoSb : length (filter (λ p → ¿ winner p (sb .slot) × isHonest p ¿) (N′ .execOrder)) ≡ 1
                      eoSb = trans (sym $ length-cong (filter-↭ _ (execOrderPreservation-↭ N₀↝⋆N′))) sbHasSuperSlot

                      makeBlockGoal-sbₜ≡Nₜ : ∀ {N*} ps →
                          L.All.All (M.Is-just ∘ (N′ .states ⁉_)) ps
                        → length (filter (λ p → ¿ winner p (sb .slot) × isHonest p ¿) ps) ≡ 1
                        → N* ↷↑ N
                        → isCollisionFree N*
                        → sb ∈ blockHistory N*
                        → b ∈ honestBlockHistory N*
                        → Unique ps
                        → _ ⊢ N′ —[ ps ]↑→∗ʳ N*
                        → blockPos sb N* ≢ blockPos b N* ⊎ sb ≡ b
                      makeBlockGoal-sbₜ≡Nₜ {N*} [] _ p∷psSb _ _ _ _ _ = contradiction p∷psSb 0≢1+n
                      makeBlockGoal-sbₜ≡Nₜ {N*} (p ∷ ps) p∷psLss p∷psSb prfN cfN* sb∈bhN* b∈hbhN* p∷psUniq (_∷ʳ_ {is = ps′} {i = p′} {s′ = N‴} {eq = eq} ts⋆ ts) = step ts
                        where
                          cfN‴ : isCollisionFree N‴
                          cfN‴ = isCollisionFreePrev-↑ ts cfN*

                          ps′∷ʳp′Uniq : Unique (ps′ L.∷ʳ p′)
                          ps′∷ʳp′Uniq = subst Unique eq p∷psUniq

                          ps′Uniq : Unique ps′
                          ps′Uniq = headʳ ps′∷ʳp′Uniq

                          p′∉ps′ : p′ ∉ ps′
                          p′∉ps′ = Unique[xs∷ʳx]⇒x∉xs ps′∷ʳp′Uniq

                          ps′∷ʳp′Sb : length (filter (λ p → ¿ winner p (sb .slot) × isHonest p ¿) (ps′ L.∷ʳ p′)) ≡ 1
                          ps′∷ʳp′Sb = subst (λ ◆ → length (filter (λ p → ¿ winner p (sb .slot) × isHonest p ¿) ◆) ≡ 1) eq p∷psSb

                          ps′∷ʳp′Lss : L.All.All (M.Is-just ∘ (N′ .states ⁉_)) (ps′ L.∷ʳ p′)
                          ps′∷ʳp′Lss = subst (L.All.All (M.Is-just ∘ (N′ .states ⁉_))) eq p∷psLss

                          ps′Lss : L.All.All (M.Is-just ∘ (N′ .states ⁉_)) ps′
                          ps′Lss = L.All.∷ʳ⁻ ps′∷ʳp′Lss .proj₁

                          N‴ₜ≡N′ₜ : N‴ .clock ≡ N′ .clock
                          N‴ₜ≡N′ₜ = clockPreservation-↑∗ (—[]→∗ʳ⇒—[]→∗ ts⋆)

                          sbₜ≡N‴ₜ : sb .slot ≡ N‴ .clock
                          sbₜ≡N‴ₜ rewrite sbₜ≡Nₜ | N″ₜ≡N′ₜ | sym N‴ₜ≡N′ₜ = refl

                          sbₜ≡N′ₜ : sb .slot ≡ N′ .clock
                          sbₜ≡N′ₜ rewrite sbₜ≡N‴ₜ | N‴ₜ≡N′ₜ = refl

                          ih* :
                              length (filter (λ p → ¿ winner p (sb .slot) × isHonest p ¿) ps′) ≡ 1
                            → sb ∈ blockHistory N‴
                            → b ∈ honestBlockHistory N‴
                            → blockPos sb N‴ ≢ blockPos b N‴ ⊎ sb ≡ b
                          ih* ps′Sb sb∈bhN‴ b∈bhbN‴ = makeBlockGoal-sbₜ≡Nₜ {N‴} ps′ ps′Lss ps′Sb (blockMaking↑ ts prfN) cfN‴ sb∈bhN‴ b∈bhbN‴ ps′Uniq ts⋆

                          step : _ ⊢ N‴ —[ p′ ]↑→ N* → blockPos sb N* ≢ blockPos b N* ⊎ sb ≡ b
                          step (unknownParty↑ ls≡◇) = contradiction ls≡◇ (subst (_≢ nothing) lsN′≡lsN* ls≢◇)
                            where
                              ls≢◇ : N′ .states ⁉ p′ ≢ nothing
                              ls≢◇ ls≡◇ = contradiction (subst M.Is-just ls≡◇ (L.All.∷ʳ⁻ ps′∷ʳp′Lss .proj₂)) λ()
                              lsN′≡lsN* : N′ .states ⁉ p′ ≡ N* .states ⁉ p′
                              lsN′≡lsN* = sym $ localStatePreservation-↑∗ p′∉ps′ (—[]→∗ʳ⇒—[]→∗ ts⋆)
                          step (honestParty↑ {ls = ls} lsπ hp′π) with Params.winnerᵈ params {p′} {N‴ .clock}
                          ... | ⁇ (no ¬isWinner) = ih* ps′Sb sb∈bhN* b∈hbhN*
                            where
                              ¬honestWinner : ¬ (winner p′ (sb .slot) × isHonest p′)
                              ¬honestWinner rewrite sbₜ≡N‴ₜ = dec-de-morgan₂ (inj₁ ¬isWinner)

                              ps′Sb : length (filter (λ p → ¿ winner p (sb .slot) × isHonest p ¿) ps′) ≡ 1
                              ps′Sb rewrite sym $ filter-rejectʳ (λ p → ¿ winner p (sb .slot) × isHonest p ¿) {xs = ps′} ¬honestWinner = ps′∷ʳp′Sb
                          ... | ⁇ (yes isWinner) = step-honestWinner↑
                            where
                              honestWinner : winner p′ (N′ .clock) × isHonest p′
                              honestWinner rewrite N‴ₜ≡N′ₜ = isWinner , hp′π

                              ps′Sb : length (filter (λ p → ¿ winner p (N′ .clock) × isHonest p ¿) ps′) ≡ 0
                              ps′Sb = Nat.suc-injective ps′Sb′
                                where
                                  ps′Sb′ : suc (length (filter (λ p → ¿ winner p (N′ .clock) × isHonest p ¿) ps′)) ≡ 1
                                  ps′Sb′ = begin
                                    suc (length (filter (λ p → ¿ winner p (N′ .clock) × isHonest p ¿) ps′))
                                      ≡⟨ +-comm _ 1 ⟨
                                    length (filter (λ p → ¿ winner p (N′ .clock) × isHonest p ¿) ps′) + 1
                                      ≡⟨ L.length-++ (filter (λ p → ¿ winner p (N′ .clock) × isHonest p ¿) ps′) {[ p′ ]} ⟨
                                    length (filter (λ p → ¿ winner p (N′ .clock) × isHonest p ¿) ps′ L.∷ʳ p′)
                                      ≡⟨ cong length $ filter-acceptʳ (λ p → ¿ winner p (N′ .clock) × isHonest p ¿) {xs = ps′} honestWinner ⟨
                                    length (filter (λ p → ¿ winner p (N′ .clock) × isHonest p ¿) (ps′ L.∷ʳ p′))
                                      ≡⟨ subst _ sbₜ≡N′ₜ ps′∷ʳp′Sb ⟩
                                    1 ∎
                                    where open ≡-Reasoning

                              lsN′ : N′ .states ⁉ p′ ≡ just ls
                              lsN′ rewrite sym $ localStatePreservation-↑∗ p′∉ps′ (—[]→∗ʳ⇒—[]→∗ ts⋆) = lsπ

                              best : Chain
                              best = bestChain (N‴ .clock ∸ 1) (ls .tree)

                              nb : Block
                              nb = mkBlock
                                (hash (tip best))
                                (N‴ .clock)
                                (txSelection (N‴ .clock) p′)
                                p′

                              sb∈nb∷bhN‴ : sb ∈ nb ∷ blockHistory N‴
                              sb∈nb∷bhN‴ rewrite hp′π = sb∈bhN*

                              b∈nb∷hbhN‴ : b ∈ nb ∷ honestBlockHistory N‴
                              b∈nb∷hbhN‴ rewrite hp′π = b∈hbhN*

                              hbhN′≡hbhN‴ : honestBlockHistory N′ ≡ˢ honestBlockHistory N‴
                              hbhN′≡hbhN‴ = hbhN′≡hbhN‴† ps′ ps′Lss ps′Uniq (blockMaking↑ ts prfN) ps′Sb ts⋆
                                where
                                  hbhN′≡hbhN‴† : ∀ {N**} ps′ →
                                      L.All.All (M.Is-just ∘ (N′ .states ⁉_)) ps′
                                    → Unique ps′
                                    → N** ↷↑ N
                                    → length (filter (λ p → ¿ winner p (N′ .clock) × isHonest p ¿) ps′) ≡ 0
                                    → _ ⊢ N′ —[ ps′ ]↑→∗ʳ N**
                                    → honestBlockHistory N′ ≡ˢ honestBlockHistory N**
                                  hbhN′≡hbhN‴† {N**} _ _ _ _ _ [] = ≡ˢ-refl
                                  hbhN′≡hbhN‴† {N**} _ p∷psLss p∷psUniq prfN** p∷psSb (_∷ʳ_ {is = ps″} {i = p″} {s′ = N⁗} {eq = eq} ts⋆′ ts′) = step† ts′
                                    where
                                      ps″∷ʳp″Uniq : Unique (ps″ L.∷ʳ p″)
                                      ps″∷ʳp″Uniq = subst Unique eq p∷psUniq

                                      ps″Uniq : Unique ps″
                                      ps″Uniq = headʳ ps″∷ʳp″Uniq

                                      p″∉ps″ : p″ ∉ ps″
                                      p″∉ps″ = Unique[xs∷ʳx]⇒x∉xs ps″∷ʳp″Uniq

                                      ps″∷ʳp″Lss : L.All.All (M.Is-just ∘ (N′ .states ⁉_)) (ps″ L.∷ʳ p″)
                                      ps″∷ʳp″Lss = subst (L.All.All (M.Is-just ∘ (N′ .states ⁉_))) eq p∷psLss

                                      ps″Lss : L.All.All (M.Is-just ∘ (N′ .states ⁉_)) ps″
                                      ps″Lss = L.All.∷ʳ⁻ ps″∷ʳp″Lss .proj₁

                                      ps″∷ʳp″Sb : length (filter (λ p → ¿ winner p (N′ .clock) × isHonest p ¿) (ps″ L.∷ʳ p″)) ≡ 0
                                      ps″∷ʳp″Sb = subst (λ ◆ → length (filter (λ p → ¿ winner p (N′ .clock) × isHonest p ¿) ◆) ≡ 0) eq p∷psSb

                                      N⁗ₜ≡N′ₜ : N⁗ .clock ≡ N′ .clock
                                      N⁗ₜ≡N′ₜ = clockPreservation-↑∗ (—[]→∗ʳ⇒—[]→∗ ts⋆′)

                                      ih** :
                                          length (filter (λ p → ¿ winner p (N′ .clock) × isHonest p ¿) ps″) ≡ 0
                                        → honestBlockHistory N′ ≡ˢ honestBlockHistory N⁗
                                      ih** ps″Sb = hbhN′≡hbhN‴† ps″ ps″Lss ps″Uniq (blockMaking↑ ts′ prfN**) ps″Sb ts⋆′

                                      step† : _ ⊢ N⁗ —[ p″ ]↑→ N** → honestBlockHistory N′ ≡ˢ honestBlockHistory N**
                                      step† (unknownParty↑ ls≡◇) = contradiction ls≡◇ (subst (_≢ nothing) lsN′≡lsN** ls≢◇)
                                        where
                                          ls≢◇ : N′ .states ⁉ p″ ≢ nothing
                                          ls≢◇ ls≡◇ = contradiction (subst M.Is-just ls≡◇ (L.All.∷ʳ⁻ ps″∷ʳp″Lss .proj₂)) λ()

                                          lsN′≡lsN** : N′ .states ⁉ p″ ≡ N** .states ⁉ p″
                                          lsN′≡lsN** = sym $ localStatePreservation-↑∗ p″∉ps″ (—[]→∗ʳ⇒—[]→∗ ts⋆′)
                                      step† (honestParty↑ {ls = ls} lsπ hp″π) with Params.winnerᵈ params {p″} {N⁗ .clock}
                                      ... | ⁇ (no ¬isWinner) = ih** ps″Sb
                                        where
                                          ¬p″HonestWinner : ¬ (winner p″ (N′ .clock) × isHonest p″)
                                          ¬p″HonestWinner rewrite N⁗ₜ≡N′ₜ = dec-de-morgan₂ (inj₁ ¬isWinner)

                                          ps″Sb : length (filter (λ p → ¿ winner p (N′ .clock) × isHonest p ¿) ps″) ≡ 0
                                          ps″Sb rewrite sym $ filter-rejectʳ (λ p → ¿ winner p (N′ .clock) × isHonest p ¿) {xs = ps″} ¬p″HonestWinner = ps″∷ʳp″Sb
                                      ... | ⁇ (yes isWinner) = contradiction ps″∷ʳp″Sb (Nat.n>0⇒n≢0 ps″∷ʳp″Sb>0)
                                        where
                                          p″HonestWinner : winner p″ (N′ .clock) × isHonest p″
                                          p″HonestWinner rewrite N⁗ₜ≡N′ₜ = isWinner , hp″π

                                          ps″∷ʳp″Sb>0 : length (filter (λ p → ¿ winner p (N′ .clock) × isHonest p ¿) (ps″ L.∷ʳ p″)) > 0
                                          ps″∷ʳp″Sb>0 = begin-strict
                                            0 <⟨ Nat.0<1+n {_} ⟩
                                            suc (length (filter (λ p → ¿ winner p (N′ .clock) × isHonest p ¿) ps″))
                                              ≡⟨ +-comm _ 1 ⟨
                                            length (filter (λ p → ¿ winner p (N′ .clock) × isHonest p ¿) ps″) + 1
                                              ≡⟨ L.length-++ (filter (λ p → ¿ winner p (N′ .clock) × isHonest p ¿) ps″) {[ p″ ]} ⟨
                                            length (filter (λ p → ¿ winner p (N′ .clock) × isHonest p ¿) ps″ L.∷ʳ p″)
                                              ≡⟨ cong length $ filter-acceptʳ (λ p → ¿ winner p (N′ .clock) × isHonest p ¿) {xs = ps″} p″HonestWinner ⟨
                                            length (filter (λ p → ¿ winner p (N′ .clock) × isHonest p ¿) (ps″ L.∷ʳ p″)) ∎
                                            where
                                              import Data.Nat.Properties as ℕₚ
                                              open ℕₚ.≤-Reasoning

                                      step† (corruptParty↑ _ cp″π) = ≡ˢ-trans (ih** ps″Sb) eqhs
                                        where
                                          mds : List (Message × DelayMap)
                                          mds =
                                            makeBlockᶜ
                                             (N⁗ .clock)
                                             (N⁗ .history)
                                             (N⁗ .messages)
                                             (N⁗ .advState)
                                             .proj₁

                                          sub : L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N⁗
                                          sub = ffN .proj₂ (blockMaking↑ ts′ prfN**)

                                          ¬p″HonestWinner : ¬ (winner p″ (N′ .clock) × isHonest p″)
                                          ¬p″HonestWinner = dec-de-morgan₂ (inj₂ (corrupt⇒¬honest cp″π))

                                          ps″Sb : length (filter (λ p → ¿ winner p (N′ .clock) × isHonest p ¿) ps″) ≡ 0
                                          ps″Sb rewrite sym $ filter-rejectʳ (λ p → ¿ winner p (N′ .clock) × isHonest p ¿) {xs = ps″} ¬p″HonestWinner = ps″∷ʳp″Sb

                                          eqhs : honestBlockHistory N⁗ ≡ˢ honestBlockHistory (broadcastMsgsᶜ mds N⁗)
                                          eqhs = honestBlockHistoryPreservation-broadcastMsgsᶜ {N⁗} {mds} sub

                              step-honestWinner↑ : ∣ chainFromBlock sb (nb ∷ blockHistory N‴) ∣ ≢ ∣ chainFromBlock b (nb ∷ blockHistory N‴) ∣ ⊎ sb ≡ b
                              step-honestWinner↑ with ∈-∷⁻ sb∈nb∷bhN‴
                              ... | inj₂ sb∈bhN‴ = contradiction sbₜ≡N′ₜ (Nat.<⇒≢ sbₜ<N′ₜ)
                                where
                                  sb∈hbhN‴ : sb ∈ honestBlockHistory N‴
                                  sb∈hbhN‴ = L.Mem.∈-filter⁺ ¿ isHonestBlock ¿¹ sb∈bhN‴ sbIsHonest

                                  sbₜ<N′ₜ : sb .slot < N′ .clock
                                  sbₜ<N′ₜ = L.All.lookup (All-resp-≡ˢ hbhN′≡hbhN‴ (noPrematureHonestBlocksAt↓ N₀↝⋆N′ ffN′ N′MsgsDelivered)) sb∈hbhN‴
                              ... | inj₁ sb≡nb with ∈-∷⁻ b∈nb∷hbhN‴
                              ... |   inj₁ b≡nb = inj₂ (trans sb≡nb (sym b≡nb))
                              ... |   inj₂ b∈hbhN‴ rewrite sb≡nb = subst (λ ◆ → ∣ ◆ ∣ ≢ ∣ chainFromBlock b (nb ∷ blockHistory N‴) ∣ ⊎ nb ≡ b) (sym cfb≡nb∷best) step-honestWinner↑′
                                where
                                  step-honestWinner↑′ : ∣ nb ∷ best ∣ ≢ ∣ chainFromBlock b (nb ∷ blockHistory N‴) ∣ ⊎ nb ≡ b
                                  step-honestWinner↑′ with ∃ReadyBeforeMsgsDelivered N₀↝⋆N′ N′MsgsDelivered
                                  ... | Nᴿ , N₀↝⋆Nᴿ , Nᴿ↝⋆⟨0⟩N′ , NᴿReady = step-honestWinner↑″
                                    where
                                      b∈hbhN′ : b ∈ honestBlockHistory N′
                                      b∈hbhN′ = Any-resp-≡ˢ (≡ˢ-sym hbhN′≡hbhN‴) b∈hbhN‴

                                      b∈hbhNᴿ : b ∈ honestBlockHistory Nᴿ
                                      b∈hbhNᴿ = ≡ˢ⇒⊆×⊇ (honestBlockHistoryPreservation-↝⋆⟨0⟩ N₀↝⋆Nᴿ NᴿReady Nᴿ↝⋆⟨0⟩N′ ffN′ N′MsgsDelivered) .proj₂ b∈hbhN′

                                      Nᴿ↝⋆N′ : Nᴿ ↝⋆ N′
                                      Nᴿ↝⋆N′ = Nᴿ↝⋆⟨0⟩N′ .proj₁

                                      ffNᴿ : isForgingFree Nᴿ
                                      ffNᴿ = isForgingFreePrev Nᴿ↝⋆N′ ffN′

                                      cfNᴿ : isCollisionFree Nᴿ
                                      cfNᴿ = isCollisionFreePrev Nᴿ↝⋆N′ cfN′

                                      bhNᴿ⊆nb∷bhN‴ : blockHistory Nᴿ ⊆ˢ nb ∷ blockHistory N‴
                                      bhNᴿ⊆nb∷bhN‴ = L.SubS.⊆-trans (blockHistoryPreservation-↝⋆ Nᴿ↝⋆N′) (L.SubS.⊆-trans (blockHistoryPreservation-↑∗ (—[]→∗ʳ⇒—[]→∗ ts⋆)) (L.SubS.xs⊆x∷xs _ _))

                                      cfπ : isBlockListCollisionFree (nb ∷ blockHistory N‴)
                                      cfπ = isBlockListCollisionFree-∷ {nb ∷ blockHistory N‴} {genesisBlock} cfN*

                                      cfbhNᴿ≢[] : chainFromBlock b (blockHistory Nᴿ) ≢ []
                                      cfbhNᴿ≢[] = ✓⇒≢[] cfbhNᴿ✓
                                        where
                                          cfbhNᴿ✓ : chainFromBlock b (blockHistory Nᴿ) ✓
                                          cfbhNᴿ✓ = L.All.lookup (L.All.tabulate $ λ {b} → honestBlockCfb✓ N₀↝⋆Nᴿ ffNᴿ cfNᴿ) b∈hbhNᴿ                                       

                                      cfbNᴿ≡cfb[nb∷N‴] : chainFromBlock b (blockHistory Nᴿ) ≡ chainFromBlock b (nb ∷ blockHistory N‴)
                                      cfbNᴿ≡cfb[nb∷N‴] = subsetCfbPreservation cfπ bhNᴿ⊆nb∷bhN‴ cfbhNᴿ≢[]

                                      step-honestWinner↑″ : ∣ nb ∷ best ∣ ≢ ∣ chainFromBlock b (nb ∷ blockHistory N‴) ∣ ⊎ nb ≡ b
                                      step-honestWinner↑″ rewrite sym cfbNᴿ≡cfb[nb∷N‴] with chainFromBlock b (blockHistory Nᴿ) in cfbNᴿEq
                                      ... | []     = inj₁ $ (flip contradiction) (≢-sym Nat.0≢1+n)
                                      ... | b′ ∷ c = inj₁ $ contraposition Nat.suc-injective (≢-sym ∣c∣≢∣best∣)
                                        where
                                          ∣b′∷c∣≤∣best∣ : ∣ b′ ∷ c ∣ ≤ ∣ best ∣
                                          ∣b′∷c∣≤∣best∣ = subst (λ ◆ → ∣ ◆ ∣ ≤ ∣ best ∣) cfbNᴿEq $ optimal (chainFromBlock b (blockHistory Nᴿ)) (ls .tree) (N‴ .clock ∸ 1) cfbNᴿ✓ cfbNᴿ⊆t
                                            where
                                              cfbNᴿ✓ : chainFromBlock b (blockHistory Nᴿ) ✓
                                              cfbNᴿ✓ = honestBlockCfb✓ N₀↝⋆Nᴿ ffNᴿ cfNᴿ b∈hbhNᴿ

                                              cfbNᴿ⊆t : chainFromBlock b (blockHistory Nᴿ) ⊆ˢ filter (λ b″ → b″ .slot ≤? N‴ .clock ∸ 1) (allBlocks (ls .tree))
                                              cfbNᴿ⊆t {b″} b″∈cfb = L.Mem.∈-filter⁺ _ {xs = allBlocks (ls .tree)} b″∈t b″ₜ≤N‴ₜ-1
                                                where
                                                  b″∈t : b″ ∈ allBlocks (ls .tree)
                                                  b″∈t = L.SubS.⊆-trans π₁ π₂ b″∈cfb
                                                    where
                                                      π₁ : chainFromBlock b (blockHistory Nᴿ) ⊆ˢ allBlocks (honestTree Nᴿ)
                                                      π₁ = cfbInHonestTree N₀↝⋆Nᴿ ffNᴿ cfNᴿ b∈hbhNᴿ

                                                      π₂ : allBlocks (honestTree Nᴿ) ⊆ˢ allBlocks (ls .tree)
                                                      π₂ = honestGlobalTreeInHonestLocalTree N₀↝⋆Nᴿ hp′π NᴿReady N′MsgsDelivered Nᴿ↝⋆⟨0⟩N′ lsN′

                                                  b″ₜ≤N‴ₜ-1 : b″ .slot ≤ N‴ .clock ∸ 1
                                                  b″ₜ≤N‴ₜ-1 rewrite clockPreservation-↑∗ (—[]→∗ʳ⇒—[]→∗ ts⋆) = Nat.≤-trans {j = b .slot} b″ₜ≤bₜ bₜ≤N′ₜ-1
                                                    where
                                                      b″ₜ≤bₜ : b″ .slot ≤ b .slot
                                                      b″ₜ≤bₜ with cfbStartsWithBlock {b} {blockHistory Nᴿ} (subst (_≢ []) (sym cfbNᴿEq) ∷≢[])
                                                      ... | c′ , cfb≡b∷c′ = case ∈-∷⁻ b″∈b′∷c of λ where
                                                           (inj₁ b″≡b′) → subst (λ ◆ → ◆ .slot ≤ b .slot) (sym $ trans b″≡b′ b′≡b) Nat.≤-refl
                                                           (inj₂ b″∈c) → Nat.<⇒≤ (b>ˢb″ b″∈c)
                                                        where
                                                          b″∈b′∷c : b″ ∈ b′ ∷ c
                                                          b″∈b′∷c rewrite cfbNᴿEq = b″∈cfb

                                                          b′∷c≡b∷c′ : _≡_ {A = List Block} (b′ ∷ c) (b ∷ c′)
                                                          b′∷c≡b∷c′ = trans (sym cfbNᴿEq) cfb≡b∷c′

                                                          b′≡b : b′ ≡ b
                                                          b′≡b = L.∷-injective b′∷c≡b∷c′ .proj₁

                                                          [b′∷c]✓ : (b′ ∷ c) ✓
                                                          [b′∷c]✓ = subst _✓ cfbNᴿEq $ honestBlockCfb✓ N₀↝⋆Nᴿ ffNᴿ cfNᴿ b∈hbhNᴿ

                                                          ds[b′∷c] : DecreasingSlots (b′ ∷ c)
                                                          ds[b′∷c] = [b′∷c]✓ .proj₂ .proj₂

                                                          b′>ˢc : L.All.All (b′ >ˢ_) c
                                                          b′>ˢc = L.All.head $ AP-++⁻ (Linked⇒AllPairs (λ {b b′ b″} → >ˢ-trans {b} {b′} {b″}) ds[b′∷c]) .proj₂ .proj₂

                                                          b>ˢb″ : b″ ∈ c → b >ˢ b″
                                                          b>ˢb″ rewrite sym b′≡b = L.All.lookup b′>ˢc

                                                      bₜ≤N′ₜ-1 : b .slot ≤ N′ .clock ∸ 1
                                                      bₜ≤N′ₜ-1 rewrite sym (Nᴿ↝⋆⟨0⟩N′ .proj₂) = Nat.<⇒≤pred bₜ<Nᴿₜ
                                                        where
                                                          bₜ<Nᴿₜ : b .slot < Nᴿ .clock
                                                          bₜ<Nᴿₜ = L.All.lookup (noPrematureHonestBlocksAtReady N₀↝⋆Nᴿ ffNᴿ NᴿReady) b∈hbhNᴿ

                                          ∣c∣≢∣best∣ : ∣ c ∣ ≢ ∣ best ∣
                                          ∣c∣≢∣best∣ p = contradiction (subst (∣ b′ ∷ c ∣ ≤_) (sym p) ∣b′∷c∣≤∣best∣) Nat.1+n≰n

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

                                  cfb≡nb∷best : chainFromBlock nb (nb ∷ blockHistory N‴) ≡ nb ∷ best
                                  cfb≡nb∷best = cfbInBlockListIsSubset cfN* nb∷best✓ bestInHist
                                    where
                                      bestInHist : best ⊆ˢ genesisBlock ∷ nb ∷ blockHistory N‴
                                      bestInHist = begin
                                        best
                                          ⊆⟨ selfContained (ls .tree) (N‴ .clock ∸ 1) ⟩
                                        filter (λ b → slot b ≤? (N‴ .clock ∸ 1)) (allBlocks (ls .tree))
                                          ⊆⟨ L.SubS.filter-⊆ (λ b → slot b ≤? (N‴ .clock ∸ 1)) (allBlocks (ls .tree)) ⟩
                                        allBlocks (ls .tree)
                                          ⊆⟨ honestLocalTreeInHonestGlobalTree N₀↝⋆N′ hp′π lsN′ ⟩
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

                          step (corruptParty↑ _ cp′π) = step-corruptParty↑
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

                              hbhᶜN‴≡hbhN‴ : honestBlockHistory (broadcastMsgsᶜ mds N‴) ≡ˢ honestBlockHistory N‴
                              hbhᶜN‴≡hbhN‴ = hbhᶜN‴≡hbhN‴† {mds} sub
                                where
                                  hbhᶜN‴≡hbhN‴† : ∀ {mds} →
                                      L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                                    → honestBlockHistory (broadcastMsgsᶜ mds N‴) ≡ˢ honestBlockHistory N‴
                                  hbhᶜN‴≡hbhN‴† {[]} _ = ≡ˢ-refl
                                  hbhᶜN‴≡hbhN‴† {(m , _) ∷ mds} sub with ¿ isHonestBlock (projBlock m) ¿
                                  ... | yes hbm = ⊆×⊇⇒≡ˢ ⊆π ⊇π
                                    where
                                      ⊆π : projBlock m ∷ honestBlockHistory (broadcastMsgsᶜ mds N‴) ⊆ˢ honestBlockHistory N‴
                                      ⊆π {b} b∈∷ with ∈-∷⁻ b∈∷
                                      ... | inj₁ b≡bₘ rewrite b≡bₘ = ∷⊆⇒∈ sub
                                      ... | inj₂ b∈hbhᶜN‴ = ≡ˢ⇒⊆×⊇ (hbhᶜN‴≡hbhN‴† {mds} (∷-⊆ sub)) .proj₁ b∈hbhᶜN‴

                                      ⊇π : honestBlockHistory N‴ ⊆ˢ projBlock m ∷ honestBlockHistory (broadcastMsgsᶜ mds N‴)
                                      ⊇π = ∷-⊆⁺ (≡ˢ⇒⊆×⊇ (hbhᶜN‴≡hbhN‴† {mds} (∷-⊆ sub)) .proj₂)
                                  ... | no _ = hbhᶜN‴≡hbhN‴† {mds} sub

                              ¬p′HonestWinner : ¬ (winner p′ (sb .slot) × isHonest p′)
                              ¬p′HonestWinner = dec-de-morgan₂ (inj₂ (corrupt⇒¬honest cp′π))

                              ps′Sb : length (filter (λ p → ¿ winner p (sb .slot) × isHonest p ¿) ps′) ≡ 1
                              ps′Sb rewrite sym $ filter-rejectʳ (λ p → ¿ winner p (sb .slot) × isHonest p ¿) {xs = ps′} ¬p′HonestWinner = ps′∷ʳp′Sb

                              sb∈hbhN* : sb ∈ honestBlockHistory (broadcastMsgsᶜ mds N‴)
                              sb∈hbhN* = L.Mem.∈-filter⁺ ¿ isHonestBlock ¿¹ sb∈bhN* sbIsHonest

                              sb∈hbhN‴ : sb ∈ honestBlockHistory N‴
                              sb∈hbhN‴ = ≡ˢ⇒⊆×⊇ hbhᶜN‴≡hbhN‴ .proj₁ sb∈hbhN*

                              sb∈bhN‴ : sb ∈ blockHistory N‴
                              sb∈bhN‴ = L.Mem.∈-filter⁻ _ {xs = blockHistory N‴} sb∈hbhN‴ .proj₁

                              b∈hbhN‴ : b ∈ honestBlockHistory N‴
                              b∈hbhN‴ = ≡ˢ⇒⊆×⊇ hbhᶜN‴≡hbhN‴ .proj₁ b∈hbhN*

                              bhπ : blockHistory N‴ ⊆ˢ blockHistory (broadcastMsgsᶜ mds N‴)
                              bhπ  = blockHistoryPreservation-broadcastMsgsᶜ mds N‴

                              cfπ : isBlockListCollisionFree (blockHistory (broadcastMsgsᶜ mds N‴))
                              cfπ = isBlockListCollisionFree-∷ {blockHistory (broadcastMsgsᶜ mds N‴)} {genesisBlock} cfN*

                              cfbhN‴≢[] : ∀ {b′} → b′ ∈ honestBlockHistory N‴ → chainFromBlock b′ (blockHistory N‴) ≢ []
                              cfbhN‴≢[] {b′} b′∈hbhN‴ = ✓⇒≢[] cfbhN‴✓
                                where
                                  cfbhN‴✓ : chainFromBlock b′ (blockHistory N‴) ✓
                                  cfbhN‴✓ = L.All.lookup (honestBlockCfb✓∗ N₀↝⋆N′ N′↝⋆N ffN (—[]→∗ʳ⇒—[]→∗ ts⋆) (blockMaking↑ ts prfN) ps′Uniq cfN‴) b′∈hbhN‴

                              step-corruptParty↑ : blockPos sb (broadcastMsgsᶜ mds N‴) ≢ blockPos b (broadcastMsgsᶜ mds N‴) ⊎ sb ≡ b
                              step-corruptParty↑
                                rewrite
                                    sym $ subsetCfbPreservation cfπ bhπ (cfbhN‴≢[] sb∈hbhN‴)
                                  | sym $ subsetCfbPreservation cfπ bhπ (cfbhN‴≢[] b∈hbhN‴)
                                  = ih* ps′Sb sb∈bhN‴ b∈hbhN‴

      ... | advanceRound   _                  = ih
      ... | permuteParties _                  = ih
      ... | permuteMsgs    _                  = ih
