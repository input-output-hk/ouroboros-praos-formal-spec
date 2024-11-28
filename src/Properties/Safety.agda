{-# OPTIONS --allow-unsolved-metas #-} -- FIXME: Remove later

open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot; slot₀; Honesty)
open import Protocol.Params using (Params)
open import Protocol.Block
open import Protocol.Chain using (genesisBlock)
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
  ⦃ ps : Params ⦄
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
  {parties₀ : List Party}
  where

open import Protocol.Semantics {T} {AdversarialState} {honestyOf} {txSelection} {processMsgsᶜ} {makeBlockᶜ}
open GlobalState

N₀ : GlobalState
N₀ =
  record
    { clock     = slot₀
    ; messages  = []
    ; states    = L.foldr (λ p states → set p (it .def) states) [] parties₀
    ; history   = []
    ; advState  = adversarialState₀
    ; execOrder = parties₀
    ; progress  = ready
    }

isSuperSlot : Slot → Type
isSuperSlot sl = length (filter (λ p → ¿ winner p sl × isHonest p ¿) parties₀) ≡ 1

isSuperBlock : Block → Type
isSuperBlock b = isHonest (b .pid) × isSuperSlot (b .slot)

superBlocks : GlobalState → List Block
superBlocks N = L.deduplicate _≟_ $ filter ¿ isSuperBlock ¿¹ (blockHistory N)

private variable
  N₁ N₂ : GlobalState

data MsgsDeliverySteps : GlobalState → GlobalState → Type₁ where

  refineStepR :
    ∙ N₁ ↝⋆ N₂
    ────────────────────────────────────
    MsgsDeliverySteps N₁ N₂

  progressR :
    ∙ MsgsDeliverySteps (record N₁ { progress = msgsDelivered }) N₂
    ────────────────────────────────────
    MsgsDeliverySteps N₁ N₂

  deliveryStep : ∀ {p} →
    ∙ MsgsDeliverySteps (executeMsgsDelivery p N₁) N₂
    ────────────────────────────────────
    MsgsDeliverySteps N₁ N₂

data BlockMakingSteps : GlobalState → GlobalState → Type₁ where

  refineStepB :
    ∙ N₁ ↝⋆ N₂
    ────────────────────────────────────
    BlockMakingSteps N₁ N₂

  progressB :
    ∙ BlockMakingSteps (record N₁ { progress = blockMade }) N₂
    ────────────────────────────────────
    BlockMakingSteps N₁ N₂

  blockMakingStep : ∀ {p} →
    ∙ BlockMakingSteps (executeBlockMaking p N₁) N₂
    ────────────────────────────────────
    BlockMakingSteps N₁ N₂

isForgingFreeD : GlobalState → Type₁
isForgingFreeD N₂ = ∀ {N₁} → MsgsDeliverySteps N₁ N₂ → ∀ {p} →
  let
    (msgs , N₁′) = fetchNewMsgs p N₁
    mds = processMsgsᶜ
      msgs
      (N₁′ .clock)
      (N₁′ .history)
      (N₁′ .messages)
      (N₁′ .advState)
      .proj₁
    nbs = map (λ where (newBlock b , _) → b) mds
  in
    nbs ⊆ʰ blockHistory N₁′

isForgingFreeB : GlobalState → Type₁
isForgingFreeB N₂ = ∀ {N₁} → BlockMakingSteps N₁ N₂ →
  let
    mds = makeBlockᶜ (N₁ .clock) (N₁ .history) (N₁ .messages) (N₁ .advState) .proj₁
    nbs = map (λ where (newBlock b , _) → b) mds
  in
    nbs ⊆ʰ blockHistory N₁

isForgingFree : GlobalState → Type₁
isForgingFree N = isForgingFreeD N × isForgingFreeB N

-- Main lemma for proving the Common Prefix property

-- TODO: Use Yves' RTC property in branch "proofs" in the Peras repo.

open import Relation.Binary.Definitions using (Reflexive; RightTrans)
open import Relation.Binary using (_⇒_; _⇔_)
open Star

T⇒Star[T] : ∀ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} → T ⇒ Star T
T⇒Star[T] = _◅ ε

-- TODO: Perhaps move to stdlib.
Star⇒≡⊎∃ : ∀ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} {i k} → Star T i k → i ≡ k ⊎ (∃[ j ] Star T i j × T j k)
Star⇒≡⊎∃ ε = inj₁ refl
Star⇒≡⊎∃ {i = i} (iTj ◅ jT⋆k) with Star⇒≡⊎∃ jT⋆k
... | inj₁ j≡k                 = inj₂ (i , ε , subst _ j≡k iTj)
... | inj₂ (k′ , jT⋆k′ , k′Tk) = inj₂ (k′ , iTj ◅ jT⋆k′ , k′Tk)

{-
≡⊎∃⇒Star : ∀ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} {i k} → i ≡ k ⊎ (∃[ j ] Star T i j × T j k) → Star T i k
≡⊎∃⇒Star (inj₁ i≡k) = subst _ i≡k ε
≡⊎∃⇒Star (inj₂ (j , iT⋆j , jTk)) = {!!}
-}

data Starᵈ {ℓ ℓ′} {I : Set ℓ} (T : Rel I ℓ′) : Rel I (ℓ ⊔ₗ ℓ′) where
  ⟨_⟩ᵈ : T ⇒ Starᵈ T
  εᵈ   : Reflexive  (Starᵈ T)
  _◅ᵈ_ : Transitive (Starᵈ T)

Star⇒Starᵈ : ∀ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} → Star T ⇒ Starᵈ T
Star⇒Starᵈ ε            = εᵈ
Star⇒Starᵈ (iTj ◅ jT⋆k) = ⟨ iTj ⟩ᵈ ◅ᵈ Star⇒Starᵈ jT⋆k

Starᵈ⇒Star : ∀ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} → Starᵈ T ⇒ Star T
Starᵈ⇒Star ⟨ iTj ⟩ᵈ       = iTj ◅ ε
Starᵈ⇒Star εᵈ             = ε
Starᵈ⇒Star (iT⋆j ◅ᵈ jT⋆k) = Starᵈ⇒Star iT⋆j ◅◅ Starᵈ⇒Star jT⋆k

Starᵈ⇔Star : ∀ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} → Starᵈ T ⇔ Star T
Starᵈ⇔Star = Starᵈ⇒Star , Star⇒Starᵈ

data Starʳ {ℓ ℓ′} {I : Set ℓ} (T : Rel I ℓ′) : Rel I (ℓ ⊔ₗ ℓ′) where
  εʳ   : Reflexive  (Starʳ T)
  _◅ʳ_ : RightTrans (Starʳ T) T

infixr 5 _◅◅ʳ_

_◅◅ʳ_ : ∀ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} → Transitive (Starʳ T)
xs ◅◅ʳ εʳ        = xs
xs ◅◅ʳ (ys ◅ʳ y) = (xs ◅◅ʳ ys) ◅ʳ y

Starʳ⇒Starᵈ : ∀ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} → Starʳ T ⇒ Starᵈ T
Starʳ⇒Starᵈ εʳ            = εᵈ
Starʳ⇒Starᵈ (iT⋆j ◅ʳ jTk) = Starʳ⇒Starᵈ iT⋆j ◅ᵈ ⟨ jTk ⟩ᵈ

Starᵈ⇒Starʳ : ∀ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} → Starᵈ T ⇒ Starʳ T
Starᵈ⇒Starʳ ⟨ iTk ⟩ᵈ       = εʳ ◅ʳ iTk
Starᵈ⇒Starʳ εᵈ             = εʳ
Starᵈ⇒Starʳ (iT⋆j ◅ᵈ jT⋆k) = Starᵈ⇒Starʳ iT⋆j ◅◅ʳ Starᵈ⇒Starʳ jT⋆k

Starᵈ⇔Starʳ : ∀ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} → Starᵈ T ⇔ Starʳ T
Starᵈ⇔Starʳ = Starᵈ⇒Starʳ , Starʳ⇒Starᵈ

open import Function.Base using (λ-; _$-)

{-
--test2 : ∀ {a b} {A : Set a} {R : A → A → Set b} → ({x y : A} → R x y) → ((x y : A) → R x y)
--test2 = λ- {!!}
--test2 f = λ- (λ- f)

test3 : ∀ {a b c} {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
      (f : ∀ {x} (y : B x) → C y) (g : (x : A) → B x) (x : A) → f (g x) ≡ (f ∘ g) x
test3 f g x = refl

test3' : ∀ {a b} {A : Set a} {R : A → A → Set b} → (f : {x y : A} → R x y) → λ- (λ- f) ≡ (λ- ∘ λ-) f
test3' = {!!}

--test3' : {!!}
--test3' f = test3 λ- λ- f
-}

test1 : ∀ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} → ∀ x y → Star T x y → Starᵈ T x y
test1 = λ- (λ- (proj₂ Starᵈ⇔Star))

test2 : ∀ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} → ∀ x y → Starᵈ T x y → Starʳ T x y
test2 = λ- (λ- (proj₁ Starᵈ⇔Starʳ))


infixr 9 _∘⇒_
--_∘⇒_ : ∀ {ℓ ℓ′} {A : Type ℓ′} {R S T : Rel A ℓ} → R ⇒ S → S ⇒ T → R ⇒ T
--_∘⇒_ : ∀ {ℓ ℓ′ ℓ″ ℓ'''} {A : Type ℓ} {R : Rel A ℓ′} {S : Rel A ℓ″} {T : Rel A ℓ'''} → R ⇒ S → S ⇒ T → R ⇒ T
--_∘⇒_ : ∀ {ℓ ℓ′} {A : Type ℓ} {R : Rel A ℓ′} {S : Rel A ℓ′} {T : Rel A ℓ′} → R ⇒ S → S ⇒ T → R ⇒ T
_∘⇒_ : ∀ {ℓ ℓ′  ℓ″ ℓ‴} {A : Type ℓ} {R : Rel A ℓ′} {S : Rel A ℓ″} {T : Rel A ℓ‴} → R ⇒ S → S ⇒ T → R ⇒ T
(p1 ∘⇒ p2) {x} {y} = p2 {x} {y} ∘ p1 {x} {y}

Star⇒Starʳ : ∀ {ℓ ℓ′} {I : Type ℓ} {T : Rel I ℓ′} → Star T ⇒ Starʳ T
Star⇒Starʳ {x = x} {y = y} = proj₁ Starᵈ⇔Starʳ {x} {y} ∘ proj₂ Starᵈ⇔Star {x} {y}

Starʳ⇒Star : ∀ {ℓ ℓ′} {I : Type ℓ} {T : Rel I ℓ′} → Starʳ T ⇒ Star T
Starʳ⇒Star {x = x} {y = y} = proj₁ Starᵈ⇔Star {x} {y} ∘ proj₂ Starᵈ⇔Starʳ {x} {y}
--Starʳ⇒Star {x = x} {y = y} = (proj₂ Starᵈ⇔Starʳ {x} {y} ∘⇒ proj₁ Starᵈ⇔Star) {x} {y}

Star⇔Starʳ : ∀ {ℓ ℓ′} {I : Set ℓ} {T : Rel I ℓ′} → Star T ⇔ Starʳ T
Star⇔Starʳ = Star⇒Starʳ , Starʳ⇒Star


infix 2 _↝⋆ʳ_
_↝⋆ʳ_ = Starʳ _↝_



module LA = L.All

-- the standard library version is strangely for f : A → A → A
foldr-preservesʳ' : ∀{A B : Set}{P : B → Set} {f : A → B → B} →
  (∀ x {y} → P y → P (f x y)) → ∀ {e} → P e → ∀ xs → P (L.foldr f e xs)
foldr-preservesʳ' pres Pe []       = Pe
foldr-preservesʳ' pres Pe (_ ∷ xs) = pres _ (foldr-preservesʳ' pres Pe xs)

blockHistoryPreservation-broadcastMsgᶜ : (msg : Message)(ϕ : DelayMap)(N : GlobalState) →
  blockHistory N ⊆ˢ blockHistory (broadcastMsgᶜ msg ϕ N)
blockHistoryPreservation-broadcastMsgᶜ msg ϕ N p = there p

blockHistoryPreservation-broadcastMsgsᶜ : (mϕs : List (Message × DelayMap))
  (N : GlobalState) →
  blockHistory N ⊆ˢ blockHistory (broadcastMsgsᶜ mϕs N)
blockHistoryPreservation-broadcastMsgsᶜ mϕs N {x = x} p = foldr-preservesʳ'
  {P = λ N → x ∈ blockHistory N}
  (λ x {N} → blockHistoryPreservation-broadcastMsgᶜ (proj₁ x) (proj₂ x) N)
  p
  mϕs

blockHistoryPreservation-executeMsgsDelivery : (p : Party)(N : GlobalState) →
  blockHistory N ⊆ˢ blockHistory (executeMsgsDelivery p N)
blockHistoryPreservation-executeMsgsDelivery p N q with states N ⁉ p
... | nothing = q
... | just l with honestyOf p
... | honest  = q
... | corrupt =  blockHistoryPreservation-broadcastMsgsᶜ
  (proj₁ (processMsgsᶜ _ _ _ _ _))
  _
  q 

blockHistoryPreservation-deliverMsgs : (N : GlobalState) →
  blockHistory N ⊆ˢ blockHistory (L.foldr executeMsgsDelivery N (N .execOrder))
blockHistoryPreservation-deliverMsgs N p = foldr-preservesʳ'
  {P = λ N → _ ∈ blockHistory N}
  (λ x {N} → blockHistoryPreservation-executeMsgsDelivery x N)
  p
  (N .execOrder)


blockHistoryPreservation-executeBlockMaking : (p : Party)(N : GlobalState) →
  blockHistory N ⊆ˢ blockHistory (executeBlockMaking p N)
blockHistoryPreservation-executeBlockMaking p N q with states N ⁉ p
... | nothing = q
... | just l with honestyOf p
... | corrupt = blockHistoryPreservation-broadcastMsgsᶜ
  (proj₁ (makeBlockᶜ _ _ _ _))
  _
  q
... | honest with Params.winnerᵈ ps {p} {N .clock}
... | ⁇ (yes p) = there q
... | ⁇ (no p) = q

blockHistoryPreservation-makeBlock : (N : GlobalState) →
  blockHistory N ⊆ˢ blockHistory (L.foldr executeBlockMaking N (N .execOrder))
blockHistoryPreservation-makeBlock N p = foldr-preservesʳ'
  {P = λ N → _ ∈ blockHistory N}
  (λ x {N} → blockHistoryPreservation-executeBlockMaking x N)
  p
  (N .execOrder)

blockHistoryPreservation : ∀ {N₁ N₂} → N₁ ↝ N₂ → blockHistory N₁ ⊆ˢ blockHistory N₂
blockHistoryPreservation {N₁ = N} (deliverMsgs p) q =
  blockHistoryPreservation-deliverMsgs N q
blockHistoryPreservation {N₁ = N} (makeBlock p) q =
  blockHistoryPreservation-makeBlock N q
blockHistoryPreservation (advanceRound p)   q = q
blockHistoryPreservation (permuteParties p) q = q
blockHistoryPreservation (permuteMsgs p)    q = q

blockHistoryPreservation⋆ : ∀ {N₁ N₂} → N₁ ↝⋆ N₂ → blockHistory N₁ ⊆ˢ blockHistory N₂
blockHistoryPreservation⋆ ε q = q
blockHistoryPreservation⋆ (p ◅ ps) q = blockHistoryPreservation⋆ ps (blockHistoryPreservation p q)

-- TODO: Check if already in stdlib, otherwise maybe add.
cartesianProduct-⊆ˢ-Mono : ∀ {A : Set} {xs ys : List A} → xs ⊆ˢ ys → L.cartesianProduct xs xs ⊆ˢ L.cartesianProduct ys ys
cartesianProduct-⊆ˢ-Mono {xs = xs} {ys = ys} xs⊆ˢys {x₁ , x₂} [x₁,x₂]∈xs×xs = L.Mem.∈-cartesianProduct⁺ (proj₁ prf) (proj₂ prf)
  where
    prf : x₁ ∈ ys × x₂ ∈ ys
    prf = let (x₁∈xs , x₂∈xs) = L.Mem.∈-cartesianProduct⁻ xs xs [x₁,x₂]∈xs×xs in xs⊆ˢys x₁∈xs , xs⊆ˢys x₂∈xs

isCollisionFreePrev : ∀ {N₁ N₂} → N₁ ↝⋆ N₂ → isCollisionFree N₂ → isCollisionFree N₁
isCollisionFreePrev N₁↝⋆N₂ cfN₂ =  LA.anti-mono (cartesianProduct-⊆ˢ-Mono (L.SubS.∷⁺ʳ genesisBlock (blockHistoryPreservation⋆ N₁↝⋆N₂))) cfN₂ 

isForgingFreeDPrev : ∀ {N₁ N₂} → N₁ ↝⋆ N₂ → isForgingFreeD N₂ → isForgingFreeD N₁
isForgingFreeDPrev = {!!}

isForgingFreeBPrev : ∀ {N₁ N₂} → N₁ ↝⋆ N₂ → isForgingFreeB N₂ → isForgingFreeB N₁
isForgingFreeBPrev = {!!}

isForgingFreePrev : ∀ {N₁ N₂} → N₁ ↝⋆ N₂ → isForgingFree N₂ → isForgingFree N₁
isForgingFreePrev N₁↝⋆N₂ (ffDN₂ , ffBN₂) = isForgingFreeDPrev N₁↝⋆N₂ ffDN₂ , isForgingFreeBPrev N₁↝⋆N₂ ffBN₂

historyMsgsDeliveryPreservation : ∀ {N p} → N .history ⊆ˢ executeMsgsDelivery p N .history
historyMsgsDeliveryPreservation = {!!}

historyMsgsDeliveryPreservation⋆ : ∀ {N ps} → N .history ⊆ˢ L.foldr executeMsgsDelivery N ps .history
historyMsgsDeliveryPreservation⋆ {N} {[]}     = L.SubS.⊆-refl
historyMsgsDeliveryPreservation⋆ {N} {p ∷ ps} = L.SubS.⊆-trans (historyMsgsDeliveryPreservation⋆ {N} {ps}) (historyMsgsDeliveryPreservation {L.foldr executeMsgsDelivery N ps} {p})

honestBlockHistoryMsgsDeliveryPreservation : ∀ {N} →
    N₀ ↝⋆ N
  → isForgingFree (record (L.foldr executeMsgsDelivery N (N .execOrder)) { progress = msgsDelivered })
  → N .progress ≡ ready
  → honestBlockHistory N ≡ honestBlockHistory (L.foldr executeMsgsDelivery N (N .execOrder))
honestBlockHistoryMsgsDeliveryPreservation = {!!}

honestPosMsgsDeliveryPreservation : ∀ {N b} →
    N₀ ↝⋆ N
  → isForgingFree N
  → isCollisionFree (L.foldr executeMsgsDelivery N (N .execOrder))
  → b ∈ honestBlockHistory N
  → N .progress ≡ ready
  → blockPos b N ≡ blockPos b (L.foldr executeMsgsDelivery N (N .execOrder))
honestPosMsgsDeliveryPreservation = {!!}

superBlockPositions : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → isCollisionFree N
  → isForgingFree N
  → LA.All
      (λ where (sb , b) → blockPos sb N ≢ blockPos b N ⊎ sb ≡ b)
      (L.cartesianProduct (superBlocks N) (honestBlockHistory N))
{-      
superBlockPositions N₀↝⋆N cfp ffp with Star⇒≡⊎∃ N₀↝⋆N
... | inj₁ N₀≡N rewrite sym N₀≡N = LA.All.[]
... | inj₂ (N′ , N₀↝⋆N′ , N′↝N) with superBlockPositions N₀↝⋆N′ {!!} {!!}
... |   x = {!!}
{- with N′↝N
... |   deliverMsgs progress≡ready = {!!}
... |   makeBlock x = {!!}
... |   advanceRound x = {!!}
... |   permuteParties x = {!!}
... |   permuteMsgs x = {!!}
-}
-}
superBlockPositions = superBlockPositionsʳ ∘ Star⇒Starʳ
  where
    superBlockPositionsʳ : ∀ {N : GlobalState} →
        N₀ ↝⋆ʳ N
      → isCollisionFree N
      → isForgingFree N
      → LA.All
          (λ where (sb , b) → blockPos sb N ≢ blockPos b N ⊎ sb ≡ b)
          (L.cartesianProduct (superBlocks N) (honestBlockHistory N))
    superBlockPositionsʳ εʳ cfp ffp = LA.All.[]
    superBlockPositionsʳ (N₀↝⋆ʳN′ ◅ʳ N′↝N) cfp ffp with N′↝N | superBlockPositionsʳ N₀↝⋆ʳN′ (isCollisionFreePrev (N′↝N ◅ ε) cfp)  (isForgingFreePrev (N′↝N ◅ ε) ffp)
    ... | deliverMsgs    N′Ready         | ih = {!!}
    ... | makeBlock      N′MsgsDelivered | ih = {!!}
    ... | advanceRound   _ | ih = ih
    ... | permuteParties _ | ih = ih
    ... | permuteMsgs    _ | ih = ih
