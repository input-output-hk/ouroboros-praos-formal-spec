{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled

open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Base.SuperBlocks
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
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.ForgingFree ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.CollisionFree ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.LocalState ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.BlockHistory ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.Time ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.ExecutionOrder ⦃ params ⦄ ⦃ assumptions ⦄
open import Prelude.STS
open import Prelude.STS.Properties using (—[]→∗⇒—[]→∗ʳ; —[]→∗ʳ⇒—[]→∗; —[∷ʳ]→∗-split; —[[]]→∗ʳ⇒≡)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Function.Properties.Equivalence using (⇔-isEquivalence)
open import Function.Properties.Equivalence.Ext using (≡⇒⇔)
open import Function.Related.Propositional as Related
open import Relation.Unary using (_≐′_; Empty) renaming (_⊆′_ to _⋐′_; _⊇′_ to _⋑′_; _⊆_ to _⋐_)
open import Relation.Unary.Properties using (≐′⇒≐)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Ext using (Starʳ)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.Ext using (Star⇒Starʳ; Starʳ⇒Star)
open import Data.Maybe.Properties.Ext using (Is-just⇒to-witness)
open import Data.List.Properties using (filter-≐; filter-reject; filter-accept; length-++)
open import Data.List.Membership.Propositional.Properties.Ext using (∈-∷⁻; x∈x∷xs)
open import Data.List.Ext using (ι; undup; count)
open import Data.List.Properties.Ext using (filter-∘-comm; filter-∘-×; ∈-ι⁺; filter-deduplicate-comm; filter-Empty; count-accept-∷ʳ; count-reject-∷ʳ; count-accept-∷; count-reject-∷; count-Empty; count-none; ≢[]⇒∷)
open import Data.List.Properties.Undup using (count-undup)
open import Data.List.Relation.Unary.AllPairs.Properties.Ext using (headʳ)
open import Data.List.Relation.Unary.Unique.Propositional.Properties.Ext using (Unique[xs∷ʳx]⇒x∉xs; Unique-≡ˢ-#≡)
open import Data.List.Relation.Unary.Unique.DecPropositional.Properties (_≟_ {A = Block}) using (deduplicate-!)
open import Data.List.Relation.Binary.Subset.Propositional.Properties.Ext using (∷⊆⇒∈)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (↭-length)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties.Ext using (filter-↭)
open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_; ≡ˢ⇒⊆×⊇; filter-cong; deduplicate-id; deduplicate-cong)

HonestWinnerAt : Slot → Party → Type _
HonestWinnerAt sl p = winner p sl × Honest p

HonestWinnerAt? : Decidable² HonestWinnerAt
HonestWinnerAt? = ¿ HonestWinnerAt ¿²

SuperSlot : Pred Slot 0ℓ
SuperSlot sl = length (filter (HonestWinnerAt? sl) parties₀) ≡ 1

SuperBlock : Pred Block 0ℓ
SuperBlock b = Honest (b .pid) × SuperSlot (b .slot)

superBlocks : GlobalState → List Block
superBlocks N = L.deduplicate _≟_ $ filter ¿ SuperBlock ¿¹ (blockHistory N)

∈-superBlocks⁻ : ∀ {N : GlobalState} {b : Block} → b ∈ superBlocks N → b ∈ blockHistory N × SuperBlock b
∈-superBlocks⁻ = L.Mem.∈-filter⁻ _ ∘ L.Mem.∈-deduplicate⁻ _ _

∈-superBlocks⁺ : ∀ {N : GlobalState} {b : Block} → b ∈ blockHistory N → SuperBlock b → b ∈ superBlocks N
∈-superBlocks⁺ = L.Mem.∈-deduplicate⁺ _ ∘₂ L.Mem.∈-filter⁺ _

superBlocksAltDef : ∀ N → superBlocks N ≡ (L.deduplicate _≟_ $ filter ¿ SuperSlot ∘ slot ¿¹ (honestBlockHistory N))
superBlocksAltDef N
  rewrite filter-∘-comm ¿ SuperSlot ∘ slot ¿¹ ¿ Honest ∘ pid ¿¹ (blockHistory N)
    | sym $ filter-∘-× ¿ Honest ∘ pid ¿¹ ¿ SuperSlot ∘ slot ¿¹ (blockHistory N)
    = refl

{--------
-- NOTE: In Coq this is defined as:
-- length (filter (λ p → ¿ winner p sl × Corrupt p ¿) $ L.allFin numParties) > 1
-- Is it actually the same?
CorruptSlot : Pred Slot 0ℓ
CorruptSlot sl = length (filter (λ p → ¿ winner p sl × Corrupt p ¿) parties₀) > 1
--------}

-- Corrupt slots: Slots where there are at least one corrupt winner.

CorruptSlotIn : REL (List Party) Slot 0ℓ
CorruptSlotIn ps sl = L.Any.Any (λ p → winner p sl × Corrupt p) ps

CorruptSlot : Pred Slot 0ℓ
CorruptSlot sl = CorruptSlotIn (L.allFin numParties) sl

CorruptSlotW : Pred Slot 0ℓ
CorruptSlotW sl = CorruptSlotIn parties₀ sl

-- The list of slots in the range [sl₁, sl₂)
slotsInRange : Slot → Slot → List Slot
slotsInRange sl₁ sl₂ = ι sl₁ (sl₂ ∸ sl₁)
--map (_+ sl₁) $ L.upTo (sl₂ ∸ sl₁)

superSlotsInRange : Slot → Slot → List Slot
superSlotsInRange = filter ¿ SuperSlot ¿¹ ∘₂ slotsInRange

superBlocksInRange : GlobalState → Slot → Slot → List Block
superBlocksInRange N sl₁ sl₂ = filter (λ b → ¿ sl₁ ≤ b .slot × b .slot < sl₂ ¿) (superBlocks N)

corruptSlotsInRange : Slot → Slot → List Slot
corruptSlotsInRange = filter ¿ CorruptSlot ¿¹ ∘₂ slotsInRange

slotsInRange-≤-+ : ∀ {P : Pred Slot 0ℓ} (P? : Decidable¹ P) (sl₁ sl₂ sl₃ : Slot) →
  length (filter P? (slotsInRange sl₁ sl₂)) ≤ length (filter P? (slotsInRange sl₁ (sl₂ + sl₃)))
slotsInRange-≤-+ = {!!}

slotsInRange-++ : ∀ {P : Pred Slot 0ℓ} (P? : Decidable¹ P) {sl₁ sl₂ sl₃ : Slot} →
  sl₁ ≤ sl₂ → sl₂ ≤ sl₃ → filter P? (slotsInRange sl₁ sl₃) ≡ filter P? (slotsInRange sl₁ sl₂) ++ filter P? (slotsInRange sl₂ sl₃)
slotsInRange-++ = {!!}

slotsInRange-∈ : ∀ {sl₁ sl₂ sl : Slot} → sl₁ ≤ sl → sl < sl₂ → sl ∈ slotsInRange sl₁ sl₂
slotsInRange-∈ {sl₁} {sl₂} {sl} sl₁≤sl sl<sl₂ = ∈-ι⁺ sl₁≤sl $
  begin-strict
    sl                ≡⟨ Nat.m∸n+n≡m sl₁≤sl ⟨
    (sl ∸ sl₁) + sl₁  ≡⟨ Nat.+-comm _ sl₁ ⟩
    sl₁ + (sl ∸ sl₁)  <⟨ Nat.+-monoʳ-< sl₁ $ Nat.∸-monoˡ-< sl<sl₂ sl₁≤sl ⟩
    sl₁ + (sl₂ ∸ sl₁) ∎
  where open Nat.≤-Reasoning

emptySlotsInRange : ∀ {sl₁ sl₂ : Slot} →
    sl₁ ≥ sl₂
  → slotsInRange sl₁ sl₂ ≡ []
emptySlotsInRange sl₁≥sl₂ rewrite Nat.m≤n⇒m∸n≡0 sl₁≥sl₂ = refl

blocksInRangeSplit : ∀ (bs : List Block) {sl₁ sl₂ sl : Slot} →
    sl₁ ≤ sl
  → sl ≤ sl₂
  → filter (λ b → ¿ sl₁ ≤ b .slot × b .slot < sl₂ ¿) bs
    ↭
    filter (λ b → ¿ sl₁ ≤ b .slot × b .slot < sl ¿) bs
    ++
    filter (λ b → ¿ sl ≤ b .slot × b .slot < sl₂ ¿) bs
blocksInRangeSplit = {!!}

superBlocksPreservation-↓∗ : ∀ {N N′ : GlobalState} →
    N₀ ↝⋆ N
  → _ ⊢ N —[ N .execOrder ]↓→∗ N′
  → ForgingFree record N′ { progress = msgsDelivered }
  → N .progress ≡ ready
  → superBlocks N ≡ˢ superBlocks N′
superBlocksPreservation-↓∗ {N} {N′} N₀↝⋆N N—[ps]↓→∗N′ ffN′ NReady {b} = begin
  b ∈ superBlocks N
    ≡⟨ cong (b ∈_) (superBlocksAltDef N) ⟩
  b ∈ (L.deduplicate _≟_ $ filter ¿ SuperSlot ∘ slot ¿¹ (honestBlockHistory N))
    ∼⟨ deduplicate-cong $ filter-cong $ honestBlockHistoryPreservation-↓∗ N₀↝⋆N  N—[ps]↓→∗N′ ffN′ NReady ⟩
  b ∈ (L.deduplicate _≟_ $ filter ¿ SuperSlot ∘ slot ¿¹ (honestBlockHistory N′))
    ≡⟨ cong (b ∈_) (sym $ superBlocksAltDef N′) ⟩
  b ∈ superBlocks N′ ∎
  where open Related.EquationalReasoning

superBlocks⊆honestBlockHistory : ∀ (N : GlobalState) → superBlocks N ⊆ˢ honestBlockHistory N
superBlocks⊆honestBlockHistory N rewrite superBlocksAltDef N = begin
  (L.deduplicate _≟_ $ filter ¿ SuperSlot ∘ slot ¿¹ (honestBlockHistory N)) ⊆⟨ L.Mem.∈-deduplicate⁻ _≟_ _ ⟩
  filter ¿ SuperSlot ∘ slot ¿¹ (honestBlockHistory N)                       ⊆⟨ L.SubS.filter-⊆ _ _ ⟩
  honestBlockHistory N ∎
  where open L.SubS.⊆-Reasoning _

opaque

  unfolding honestBlockMaking corruptBlockMaking count

  open IsEquivalence {ℓ = 0ℓ} ⇔-isEquivalence renaming (refl to ⇔-refl; sym to ⇔-sym; trans to ⇔-trans)

  superBlockOneness :  ∀ {N : GlobalState} →
      N₀ ↝⋆ N
    → ForgingFree N
    → N .progress ≡ blockMade
    → (length (superBlocksInRange N (N .clock) (1 + N .clock)) ≡ 1) ⇔ SuperSlot (N .clock)
  superBlockOneness = superBlockOnenessʳ ∘ Star⇒Starʳ
    where
      open RTC; open Starʳ

      superBlockOnenessʳ :  ∀ {N : GlobalState} →
          N₀ ↝⋆ʳ N
        → ForgingFree N
        → N .progress ≡ blockMade
        → (length (superBlocksInRange N (N .clock) (1 + N .clock)) ≡ 1) ⇔ SuperSlot (N .clock)
      superBlockOnenessʳ {N} (_◅ʳ_ {j = N′} N₀↝⋆ʳN′ N′↝N) ffN NBlockMade = goal N′↝N
        where
          N₀↝⋆N′ : N₀ ↝⋆ N′
          N₀↝⋆N′ = Starʳ⇒Star N₀↝⋆ʳN′

          ffN′ : ForgingFree N′
          ffN′ = ForgingFreePrev (N′↝N ◅ ε) ffN

          ih :
              N′ .progress ≡ blockMade
            →
              (length (superBlocksInRange N′ (N′ .clock) (1 + N′ .clock)) ≡ 1)
              ⇔
              SuperSlot (N′ .clock)
          ih = superBlockOnenessʳ N₀↝⋆ʳN′ ffN′

          goal :
              N′ ↝ N
            →
              (length (superBlocksInRange N (N .clock) (1 + N .clock)) ≡ 1)
              ⇔
              SuperSlot (N .clock)
          goal (makeBlock {N′ = N″} N′MsgsDelivered N′—[eoN′]↑→∗N″) = subst₂ _⇔_ (sym onesb≡onehw) (sym ss≡onehw) makeBlockGoal
            where
              ss≡onehw :
                SuperSlot (N .clock)
                ≡
                (length (filter (HonestWinnerAt? (N′ .clock)) (N′ .execOrder)) ≡ 1)
              ss≡onehw rewrite
                   clockPreservation-↑∗ N′—[eoN′]↑→∗N″
                 | ↭-length $ filter-↭ (HonestWinnerAt? (N′ .clock)) (execOrderPreservation-↭ N₀↝⋆N′)
                 = refl

              sb≐onehw :
                (λ b → (N′ .clock ≤ b .slot × b .slot < 1 + N′ .clock) × SuperBlock b)
                ≐′
                (λ b → b .slot ≡ N′ .clock × Honest (b .pid) × length (filter (HonestWinnerAt? (N′ .clock)) (N′ .execOrder)) ≡ 1)
              sb≐onehw = ⊆π , ⊇π
                where
                  bₜ≡N′ₜ : ∀ {b} → N′ .clock ≤ b .slot × b .slot < 1 + N′ .clock → b .slot ≡ N′ .clock
                  bₜ≡N′ₜ (N′ₜ≤bₜ , bₜ<1+N′ₜ) = sym $ Nat.≤-antisym N′ₜ≤bₜ (Nat.≤-pred bₜ<1+N′ₜ)

                  ⊆π :
                    (λ b → (N′ .clock ≤ b .slot × b .slot < 1 + N′ .clock) × SuperBlock b)
                    ⋐′
                    (λ b → b .slot ≡ N′ .clock × Honest (b .pid) × length (filter (HonestWinnerAt? (N′ .clock)) (N′ .execOrder)) ≡ 1)
                  ⊆π b ((N′ₜ≤bₜ , bₜ<1+N′ₜ) , sbb)
                    rewrite bₜ≡N′ₜ {b} (N′ₜ≤bₜ , bₜ<1+N′ₜ) =
                        refl
                      , sbb .proj₁
                      , ≡⇒⇔ ss≡onehw .Equivalence.to (subst _ (sym $ clockPreservation-↑∗ N′—[eoN′]↑→∗N″) (sbb .proj₂))

                  ⊇π :
                    (λ b → (N′ .clock ≤ b .slot × b .slot < 1 + N′ .clock) × SuperBlock b)
                    ⋑′
                    (λ b → b .slot ≡ N′ .clock × Honest (b .pid) × length (filter (HonestWinnerAt? (N′ .clock)) (N′ .execOrder)) ≡ 1)
                  ⊇π b (N′ₜ≤bₜ , bₜ<1+N′ₜ , sbb)
                    rewrite N′ₜ≤bₜ =
                        (Nat.≤-refl , Nat.≤-refl)
                      , bₜ<1+N′ₜ
                      , (subst _ (clockPreservation-↑∗ N′—[eoN′]↑→∗N″) $ ≡⇒⇔ ss≡onehw .Equivalence.from sbb)

              onesb≡onehw :
                (length (superBlocksInRange N (N .clock) (1 + N .clock)) ≡ 1)
                ≡
                (length (
                  filter (λ b → ¿
                      b .slot ≡ N′ .clock
                    × HonestBlock b
                    × length (filter (HonestWinnerAt? (N′ .clock)) (N′ .execOrder)) ≡ 1 ¿)
                    (L.deduplicate _≟_ (blockHistory N))) ≡ 1)
              onesb≡onehw
                rewrite
                  clockPreservation-↑∗ N′—[eoN′]↑→∗N″
                | sym $ filter-deduplicate-comm {P? = ¿ SuperBlock ¿¹} (blockHistory N)
                | sym $ filter-∘-× (λ b → ¿ N′ .clock ≤ b .slot × b .slot < 1 + N′ .clock ¿) ¿ SuperBlock ¿¹ (L.deduplicate _≟_ (blockHistory N))
                | filter-≐ (λ b → ¿ N′ .clock ≤ b .slot × b .slot < 1 + N′ .clock ¿ ×-dec ¿ SuperBlock ¿¹ b) _ (≐′⇒≐ sb≐onehw) (L.deduplicate _≟_ (blockHistory N))
                = refl

              N″↷↑N″[bM] : N″ ↷↑ record N″ { progress = blockMade }
              N″↷↑N″[bM] = progress↑ (↷↑-refl)

              N′Uniq : Unique (N′ .execOrder)
              N′Uniq = execOrderUniqueness N₀↝⋆N′

              N′AllLs : L.All.All (_hasStateIn N′) (N′ .execOrder)
              N′AllLs = allPartiesHaveLocalState N₀↝⋆N′

              makeBlockGoal :
                count
                  (λ b → ¿
                      b .slot ≡ N′ .clock
                    × HonestBlock b
                    × count (HonestWinnerAt? (N′ .clock)) (N′ .execOrder) ≡ 1 ¿)
                  (L.deduplicate _≟_ (blockHistory N)) ≡ 1
                ⇔
                count (HonestWinnerAt? (N′ .clock)) (N′ .execOrder) ≡ 1
              makeBlockGoal =
                  makeBlockGoal* (reverseView (N′ .execOrder)) N″↷↑N″[bM] N′Uniq N′AllLs (—[]→∗⇒—[]→∗ʳ N′—[eoN′]↑→∗N″)
                where
                  open import Data.List.Reverse

                  makeBlockGoal* : ∀ {N* ps} →
                      Reverse ps
                    → N* ↷↑ N
                    → Unique ps
                    → L.All.All (_hasStateIn N′) ps
                    → _ ⊢ N′ —[ ps ]↑→∗ʳ N*
                    →
                      count
                        (λ b → ¿
                            b .slot ≡ N′ .clock
                          × HonestBlock b
                          × count (HonestWinnerAt? (N′ .clock)) ps ≡ 1 ¿)
                        (L.deduplicate _≟_ (blockHistory N*)) ≡ 1
                      ⇔
                      count (HonestWinnerAt? (N′ .clock)) ps ≡ 1
                  makeBlockGoal* {N* = N*} [] _ _ _ _ = goal-[]
                    where
                      P : Pred Block 0ℓ
                      P = λ b → slot b ≡ clock N′ × HonestBlock b × length {A = Block} [] ≡ 1

                      EmptyP : Empty P
                      EmptyP _ (_ , _ , 0≡1) = contradiction 0≡1 λ ()

                      goal-[] :
                        count ¿ P ¿¹ (L.deduplicate _≟_ (blockHistory N*)) ≡ 1
                        ⇔
                        length {A = Block} [] ≡ 1
                      goal-[] rewrite filter-Empty ¿ P ¿¹ EmptyP (L.deduplicate _≟_ (blockHistory N*)) = ⇔-refl
                  makeBlockGoal* {N* = N*} (ps′ ∶ ps′r ∶ʳ p′) N*↷↑N ps′∷ʳp′Uniq ps′∷ʳp′AllLs ts*
                    with —[∷ʳ]→∗-split (—[]→∗ʳ⇒—[]→∗ ts*)
                  ... | N‴ , ts⁺′ , ts = goal-∷ʳ ts
                    where
                      ts⁺ : _ ⊢ N′ —[ ps′ ]↑→∗ʳ N‴
                      ts⁺ = —[]→∗⇒—[]→∗ʳ ts⁺′

                      ps′Uniq : Unique ps′
                      ps′Uniq = headʳ ps′∷ʳp′Uniq

                      p′∉ps′ : p′ ∉ ps′
                      p′∉ps′ = Unique[xs∷ʳx]⇒x∉xs ps′∷ʳp′Uniq

                      ps′AllLs : L.All.All (_hasStateIn N′) ps′
                      ps′AllLs = L.All.∷ʳ⁻ ps′∷ʳp′AllLs .proj₁

                      p′HasLs : p′ hasStateIn N′
                      p′HasLs = L.All.∷ʳ⁻ ps′∷ʳp′AllLs .proj₂

                      P : Pred Block 0ℓ
                      P = λ b →
                              b .slot ≡ N′ .clock
                            × HonestBlock b
                            × count (HonestWinnerAt? (N′ .clock)) ps′ ≡ 1

                      ih* :
                        count ¿ P ¿¹ (L.deduplicate _≟_ (blockHistory N‴)) ≡ 1
                        ⇔
                        count (HonestWinnerAt? (N′ .clock)) ps′ ≡ 1
                      ih* = makeBlockGoal* {N* = N‴} ps′r (blockMaking↑ ts N*↷↑N) ps′Uniq ps′AllLs ts⁺

                      goal-∷ʳ : _ ⊢ N‴ —[ p′ ]↑→ N* →
                        count
                          (λ b → ¿
                               b .slot ≡ N′ .clock
                             × HonestBlock b
                             × count (HonestWinnerAt? (N′ .clock)) (ps′ L.∷ʳ p′) ≡ 1 ¿)
                        (L.deduplicate _≟_ (blockHistory N*)) ≡ 1
                        ⇔
                        count (HonestWinnerAt? (N′ .clock)) (ps′ L.∷ʳ p′) ≡ 1
                      goal-∷ʳ ts
                        with HonestWinnerAt? (N′ .clock) p′
                      ... | yes hwp′@(wp′ , hp′)
                        rewrite
                          count-accept-∷ʳ (HonestWinnerAt? (N′ .clock)) {xs = ps′} hwp′
                          = goal-∷ʳ-hwp′ ts
                        where
                          p′HasLsInN* : p′ hasStateIn N*
                          p′HasLsInN* = hasState⇔-↑∗ ts⁺′ ts .Equivalence.to p′HasLs

                          ls′ : LocalState
                          ls′ = M.to-witness p′HasLsInN*

                          ls′π : N* .states ⁉ p′ ≡ just ls′
                          ls′π = Is-just⇒to-witness p′HasLsInN*

                          wp′N‴ : winner p′ (N‴ .clock)
                          wp′N‴ = subst (winner p′) (sym $ clockPreservation-↑∗ ts⁺′) wp′

                          goal-∷ʳ-hwp′ : _ ⊢ N‴ —[ p′ ]↑→ N* →
                            count
                              (λ b → ¿
                                   b .slot ≡ N′ .clock
                                 × HonestBlock b
                                 × 1 + count (HonestWinnerAt? (N′ .clock)) ps′ ≡ 1 ¿)
                            (L.deduplicate _≟_ (blockHistory N*)) ≡ 1
                            ⇔
                            1 + count (HonestWinnerAt? (N′ .clock)) ps′ ≡ 1
                          goal-∷ʳ-hwp′ ts with count (HonestWinnerAt? (N′ .clock)) ps′ in cnthw≡
                          ... | suc n = goal-∷ʳ-hwp′-sn
                            where
                              P′ : Pred Block 0ℓ
                              P′ = λ b → b .slot ≡ N′ .clock × Honest (b .pid) × 1 + suc n ≡ 1

                              EmptyP′ : Empty P′
                              EmptyP′ _ (_ , _ , ssn≡1) = contradiction ssn≡1 λ ()

                              goal-∷ʳ-hwp′-sn :
                                count ¿ P′ ¿¹ (L.deduplicate _≟_ (blockHistory N*)) ≡ 1
                                ⇔
                                1 + suc n ≡ 1
                              goal-∷ʳ-hwp′-sn
                                rewrite
                                  count-Empty ¿ P′ ¿¹ EmptyP′ (L.deduplicate _≟_ (blockHistory N*))
                                = mk⇔ (λ ()) λ ()
                          ... | 0 with ts
                          ... |   unknownParty↑ ls′≡◇ = contradiction ls′≡◇ ls′≢◇
                            where
                              ls′≢◇ : N* .states ⁉ p′ ≢ nothing
                              ls′≢◇ rewrite ls′π = flip contradiction λ ()
                          ... |   honestParty↑ {ls = ls} lsπ hp′π
                                rewrite
                                  sym $ count-undup ¿ (λ b → b .slot ≡ N′ .clock × HonestBlock b × 1 ≡ 1) ¿¹ (blockHistory N*)
                                | dec-yes ¿ winner p′ (N‴ .clock) ¿ wp′N‴ .proj₂
                                | clockPreservation-↑∗ ts⁺′
                                = goal-∷ʳ-hwp′-0-h
                            where
                              P′ : Pred Block 0ℓ
                              P′ = λ b → b .slot ≡ N′ .clock × HonestBlock b × 1 ≡ 1

                              cnt≡0 : count ¿ P′ ¿¹ (undup (blockHistory N‴)) ≡ 0
                              cnt≡0 = cnt≡0* (reverseView ps′) ¬hwps′ (blockMaking↑ ts N*↷↑N) ts⁺
                                where
                                  ¬hwps′ : L.All.All (¬_ ∘  HonestWinnerAt (N′ .clock)) ps′
                                  ¬hwps′ = count-none (HonestWinnerAt? (N′ .clock)) cnthw≡

                                  cnt≡0* : ∀ {N⁺ ps⁺} →
                                      Reverse ps⁺
                                    → L.All.All (¬_ ∘  HonestWinnerAt (N′ .clock)) ps⁺
                                    → N⁺ ↷↑ N
                                    → _ ⊢ N′ —[ ps⁺ ]↑→∗ʳ N⁺
                                    → count ¿ P′ ¿¹ (undup (blockHistory N⁺)) ≡ 0
                                  cnt≡0* {N⁺} [] _ _ ts⁺ = cnt≡0*-[]* {bs† = blockHistory N⁺} nphb
                                    where
                                      nphb : L.All.All ((_< N′ .clock) ∘ slot) (L.filter ¿ HonestBlock ¿¹ (blockHistory N⁺))
                                      nphb rewrite sym $ —[[]]→∗ʳ⇒≡ ts⁺ = noPrematureHonestBlocksAt↓ N₀↝⋆N′ ffN′ N′MsgsDelivered

                                      cnt≡0*-[]* : ∀ {bs†} →
                                          L.All.All ((_< N′ .clock) ∘ slot) (L.filter ¿ HonestBlock ¿¹ bs†)
                                        → count ¿ P′ ¿¹ (undup bs†) ≡ 0
                                      cnt≡0*-[]* {[]} _ = refl
                                      cnt≡0*-[]* {b† ∷ bs†} π with ¿ HonestBlock b† ¿
                                      ... | yes hb† with ¿ b† ∈ bs† ¿
                                      ... |   yes b†∈bs† = cnt≡0*-[]* {bs†} (L.All.tail π)
                                      ... |   no  b†∉bs† with b† .slot ≟ N′ .clock
                                      ... |     yes b†ₜ≡N′ₜ = contradiction (subst (_< N′ .clock) b†ₜ≡N′ₜ b†ₜ<N′ₜ) (Nat.<-irrefl refl)
                                        where
                                          b†ₜ<N′ₜ : b† .slot < N′ .clock
                                          b†ₜ<N′ₜ rewrite hb† = L.All.head π
                                      ... |     no  b†ₜ≢N′ₜ
                                                  rewrite
                                                    count-reject-∷ ¿ P′ ¿¹ {x = b†} {xs = undup bs†}
                                                      (flip contradiction b†ₜ≢N′ₜ ∘ proj₁)
                                                  = cnt≡0*-[]* {bs†} (L.All.tail π)
                                      cnt≡0*-[]* {b† ∷ bs†} π
                                          | no ¬hb† with ¿ b† ∈ bs† ¿
                                      ... |   yes b†∈bs† = cnt≡0*-[]* {bs†} π
                                      ... |   no  b†∉bs†
                                                rewrite
                                                 count-reject-∷ ¿ P′ ¿¹ {x = b†} {xs = undup bs†}
                                                   (flip contradiction ¬hb† ∘ proj₁ ∘ proj₂)
                                                = cnt≡0*-[]* {bs†} π
                                  cnt≡0* {N⁺} (ps⁺ ∶ rps⁺ ∶ʳ p⁺) ¬hw[ps⁺+p⁺] N⁺↷↑N ts⁺
                                    with —[∷ʳ]→∗-split (—[]→∗ʳ⇒—[]→∗ ts⁺)
                                  ... | N† , ts†′ , ts = cnt≡0*-∷ʳ ts
                                    where
                                      ts† : _ ⊢ N′ —[ ps⁺ ]↑→∗ʳ N†
                                      ts† = —[]→∗⇒—[]→∗ʳ ts†′

                                      ¬hwps⁺ : L.All.All (¬_ ∘ HonestWinnerAt (N′ .clock)) ps⁺
                                      ¬hwps⁺ = L.All.∷ʳ⁻ ¬hw[ps⁺+p⁺] .proj₁

                                      ¬hwp⁺ : ¬ HonestWinnerAt (N′ .clock) p⁺
                                      ¬hwp⁺ = L.All.∷ʳ⁻ ¬hw[ps⁺+p⁺] .proj₂

                                      ih⁺ : count ¿ P′ ¿¹ (undup (blockHistory N†)) ≡ 0
                                      ih⁺ = cnt≡0* {N†} rps⁺ ¬hwps⁺ (blockMaking↑ ts N⁺↷↑N) ts†

                                      cnt≡0*-∷ʳ :
                                           _ ⊢ N† —[ p⁺ ]↑→ N⁺
                                        → count ¿ P′ ¿¹ (undup (blockHistory N⁺)) ≡ 0
                                      cnt≡0*-∷ʳ (unknownParty↑ _) = ih⁺
                                      cnt≡0*-∷ʳ (honestParty↑ {ls = ls} lsπ hp⁺π) = cnt≡0*-∷ʳ-h
                                        where
                                          eqMakeBlockʰ :
                                            makeBlockʰ (N† .clock) (txSelection (N† .clock) p⁺) p⁺ ls
                                            ≡
                                            makeBlockʰ (N′ .clock) (txSelection (N′ .clock) p⁺) p⁺ ls
                                          eqMakeBlockʰ rewrite sym $ clockPreservation-↑∗ ts†′ = refl

                                          ¬wp⁺ : ¬ winner p⁺ (N′ .clock)
                                          ¬wp⁺ rewrite clockPreservation-↑ ts = ¬[p×q]×q⇒¬p ¬hwp⁺ hp⁺π

                                          cnt≡0*-∷ʳ-h : count ¿ P′ ¿¹ (undup (blockHistory (honestBlockMaking p⁺ ls N†))) ≡ 0
                                          cnt≡0*-∷ʳ-h rewrite eqMakeBlockʰ | dec-no (winnerᵈ .dec) ¬wp⁺ = ih⁺
                                      cnt≡0*-∷ʳ (corruptParty↑ _ _) = cnt≡0*-∷ʳ-c
                                        where
                                          mds : List (Message × DelayMap)
                                          mds = makeBlockᶜ (N′ .clock) (N† .history) (N† .messages) (N† .advState) .proj₁

                                          eqMakeBlockᶜ :
                                            makeBlockᶜ (N† .clock) (N† .history) (N† .messages) (N† .advState) .proj₁
                                            ≡
                                            mds
                                          eqMakeBlockᶜ rewrite sym $ clockPreservation-↑∗ ts†′ = refl

                                          sub : L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N†
                                          sub rewrite sym eqMakeBlockᶜ = ffN .proj₂ (blockMaking↑ ts N⁺↷↑N)

                                          cnt≡0*-∷ʳ-c : count ¿ P′ ¿¹ (undup (blockHistory (corruptBlockMaking p⁺ N†))) ≡ 0
                                          cnt≡0*-∷ʳ-c
                                            rewrite
                                              eqMakeBlockᶜ
                                            | sym $ count-undup ¿ P′ ¿¹ (blockHistory (broadcastMsgsᶜ mds N†))
                                            | sym $ count-undup ¿ P′ ¿¹ (blockHistory N†)
                                            = cnt≡0*-∷ʳ-c-* {mds} sub
                                            where
                                              cnt≡0*-∷ʳ-c-* : ∀ {mds} →
                                                L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N†
                                                →
                                                count ¿ P′ ¿¹ (undup (blockHistory (broadcastMsgsᶜ mds N†))) ≡ 0
                                              cnt≡0*-∷ʳ-c-* {[]} _ = ih⁺
                                              cnt≡0*-∷ʳ-c-* {(m , _) ∷ mds} sub
                                                with bᵐ ← projBlock m
                                                  | ¿ HonestBlock bᵐ ¿ | ¿ bᵐ ∈ blockHistory (broadcastMsgsᶜ mds N†) ¿
                                              ... | yes hbᵐ  | yes bᵐ∈bhN†ᶜ = cnt≡0*-∷ʳ-c-* {mds} sub′
                                                where
                                                   sub′ : L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N†
                                                   sub′ = L.SubS.⊆-trans (L.SubS.xs⊆x∷xs _ bᵐ) sub
                                              ... | yes hbᵐ  | no  bᵐ∉bhN†ᶜ = contradiction bᵐ∈bhN†ᶜ bᵐ∉bhN†ᶜ
                                                where
                                                  bᵐ∈bhN† : bᵐ ∈ blockHistory N†
                                                  bᵐ∈bhN† = L.SubS.filter-⊆ ¿ HonestBlock ¿¹ (blockHistory N†) $ ∷⊆⇒∈ sub

                                                  bᵐ∈bhN†ᶜ : bᵐ ∈ blockHistory (broadcastMsgsᶜ mds N†)
                                                  bᵐ∈bhN†ᶜ = blockHistoryPreservation-broadcastMsgsᶜ mds N† bᵐ∈bhN†
                                              ... | no _     | yes bᵐ∈bhN†ᶜ = cnt≡0*-∷ʳ-c-* {mds} sub
                                              ... | no ¬hbᵐ  | no  bᵐ∉bhN†ᶜ
                                                rewrite
                                                  count-reject-∷ ¿ P′ ¿¹ {x = bᵐ} {xs = undup (blockHistory (broadcastMsgsᶜ mds N†))}
                                                    λ where (_ , hbᵐ , _) → contradiction hbᵐ ¬hbᵐ
                                                = cnt≡0*-∷ʳ-c-* {mds} sub

                              best : Chain
                              best = bestChain (N′ .clock  ∸ 1) (ls .tree)

                              nb : Block
                              nb = mkBlock (hash (tip best)) (N′ .clock) (txSelection (N′ .clock) p′) p′

                              goal-∷ʳ-hwp′-0-h :
                                count ¿ P′ ¿¹ (undup (nb ∷ blockHistory N‴)) ≡ 1
                                ⇔
                                1 ≡ 1
                              goal-∷ʳ-hwp′-0-h with ¿ nb ∈ blockHistory N‴ ¿
                              ... | yes nb∈bhN‴ = goal-∷ʳ-hwp′-0-h-* cnt≡0 nb∈bhN‴
                                where
                                  goal-∷ʳ-hwp′-0-h-* : ∀ {bs*} →
                                      count ¿ P′ ¿¹ (undup bs*) ≡ 0
                                    → nb ∈ bs*
                                    → count ¿ P′ ¿¹ (undup bs*) ≡ 1
                                      ⇔
                                      1 ≡ 1
                                  goal-∷ʳ-hwp′-0-h-* {[]} cnt≡0 nb∈[] = contradiction nb∈[] λ ()
                                  goal-∷ʳ-hwp′-0-h-* {b* ∷ bs*} cnt≡0 nb∈b*∷bs* with ∈-∷⁻ nb∈b*∷bs*
                                  ... | inj₂ nb∈bs* with ¿ b* ∈ bs* ¿
                                  ... |   yes b*∈bs* = goal-∷ʳ-hwp′-0-h-* {bs*} cnt≡0 nb∈bs*
                                  ... |   no  b*∉bs* with ¿ P′ b* ¿
                                  ... |     yes P′b*
                                              rewrite
                                                count-accept-∷ ¿ P′ ¿¹ {x = b*} {xs = undup bs*} P′b*
                                              = contradiction cnt≡0 λ ()
                                  ... |     no ¬P′b* with ¬-distrib-×-dec ¬P′b*
                                  ... |       inj₁ b*ₜ≢N′ₜ
                                                rewrite count-reject-∷ ¿ P′ ¿¹ {x = b*} {xs = undup bs*}
                                                  (flip contradiction b*ₜ≢N′ₜ ∘ proj₁)
                                                = goal-∷ʳ-hwp′-0-h-* {bs*} cnt≡0 nb∈bs*
                                  ... |       inj₂ ¬hb*
                                                rewrite count-reject-∷ ¿ P′ ¿¹ {x = b*} {xs = undup bs*}
                                                  (flip contradiction ¬hb* ∘ proj₂)
                                                = goal-∷ʳ-hwp′-0-h-* {bs*} cnt≡0 nb∈bs*
                                  goal-∷ʳ-hwp′-0-h-* {b* ∷ bs*} cnt≡0 nb∈b*∷bs*
                                      | inj₁ nb≡b* rewrite sym nb≡b* with ¿ nb ∈ bs* ¿
                                  ... |   yes nb∈bs* = goal-∷ʳ-hwp′-0-h-* {bs*} cnt≡0 nb∈bs*
                                  ... |   no  nb∉bs* = contradiction cnt≡0 λ ()
                              ... | no nb∉bhN‴
                                rewrite
                                  dec-no ¿ nb ∈ blockHistory N‴ ¿ nb∉bhN‴
                                | count-accept-∷ ¿ P′ ¿¹ {x = nb} {xs = undup (blockHistory N‴)} (refl , hp′ , refl)
                                | cnt≡0
                                = ⇔-refl
                          ... |   corruptParty↑ _ cp′π = contradiction hp′ $ corrupt⇒¬honest cp′π
                      ... | no ¬hwp′ rewrite count-reject-∷ʳ (HonestWinnerAt? (N′ .clock)) {xs = ps′} ¬hwp′
                          with ts
                      ... |   unknownParty↑ _ = ih*
                      ... |   honestParty↑ {ls = ls} lsπ hp′π = ⇔-trans goal-∷ʳ-h¬wp′ ih*
                        where
                          eqMakeBlockʰ :
                            makeBlockʰ (N‴ .clock) (txSelection (N‴ .clock) p′) p′ ls
                            ≡
                            makeBlockʰ (N′ .clock) (txSelection (N′ .clock) p′) p′ ls
                          eqMakeBlockʰ rewrite sym $ clockPreservation-↑∗ ts⁺′ = refl

                          ¬wp′ : ¬ winner p′ (N′ .clock)
                          ¬wp′ rewrite clockPreservation-↑ ts = ¬[p×q]×q⇒¬p ¬hwp′ hp′π

                          goal-∷ʳ-h¬wp′ :
                            count ¿ P ¿¹ (L.deduplicate _≟_ (blockHistory (honestBlockMaking p′ ls N‴))) ≡ 1
                            ⇔
                            count ¿ P ¿¹ (L.deduplicate _≟_ (blockHistory N‴)) ≡ 1
                          goal-∷ʳ-h¬wp′ rewrite eqMakeBlockʰ | dec-no (winnerᵈ .dec) ¬wp′ = ⇔-refl
                      ... |   corruptParty↑ _ _ = ⇔-trans goal-∷ʳ-c¬wp′ ih*
                        where
                          mds : List (Message × DelayMap)
                          mds = makeBlockᶜ (N′ .clock) (N‴ .history) (N‴ .messages) (N‴ .advState) .proj₁

                          eqMakeBlockᶜ :
                            makeBlockᶜ (N‴ .clock) (N‴ .history) (N‴ .messages) (N‴ .advState) .proj₁
                            ≡
                            mds
                          eqMakeBlockᶜ rewrite sym $ clockPreservation-↑∗ ts⁺′ = refl

                          sub : L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                          sub rewrite sym eqMakeBlockᶜ = ffN .proj₂ (blockMaking↑ ts N*↷↑N)

                          goal-∷ʳ-c¬wp′ :
                            count ¿ P ¿¹ (L.deduplicate _≟_ (blockHistory (corruptBlockMaking p′ N‴))) ≡ 1
                            ⇔
                            count ¿ P ¿¹ (L.deduplicate _≟_ (blockHistory N‴)) ≡ 1
                          goal-∷ʳ-c¬wp′
                            rewrite
                              eqMakeBlockᶜ
                            | sym $ count-undup ¿ P ¿¹ (blockHistory (broadcastMsgsᶜ mds N‴))
                            | sym $ count-undup ¿ P ¿¹ (blockHistory N‴)
                            = goal-∷ʳ-c¬wp′-* {mds} sub
                            where
                              goal-∷ʳ-c¬wp′-* : ∀ {mds} →
                                L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                                →
                                count ¿ P ¿¹ (undup (blockHistory (broadcastMsgsᶜ mds N‴))) ≡ 1
                                ⇔
                                count ¿ P ¿¹ (undup (blockHistory N‴)) ≡ 1
                              goal-∷ʳ-c¬wp′-* {[]} _ = ⇔-refl
                              goal-∷ʳ-c¬wp′-* {(m , _) ∷ mds} sub
                                with bᵐ ← projBlock m
                                  | ¿ HonestBlock bᵐ ¿ | ¿ bᵐ ∈ blockHistory (broadcastMsgsᶜ mds N‴) ¿
                              ... | yes hbᵐ  | yes bᵐ∈bhN‴ᶜ = goal-∷ʳ-c¬wp′-* {mds} sub′
                                where
                                   sub′ : L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                                   sub′ = L.SubS.⊆-trans (L.SubS.xs⊆x∷xs _ bᵐ) sub
                              ... | yes hbᵐ  | no  bᵐ∉bhN‴ᶜ = contradiction bᵐ∈bhN‴ᶜ bᵐ∉bhN‴ᶜ
                                where
                                  bᵐ∈bhN‴ : bᵐ ∈ blockHistory N‴
                                  bᵐ∈bhN‴ = L.SubS.filter-⊆ ¿ HonestBlock ¿¹ (blockHistory N‴) $ ∷⊆⇒∈ sub

                                  bᵐ∈bhN‴ᶜ : bᵐ ∈ blockHistory (broadcastMsgsᶜ mds N‴)
                                  bᵐ∈bhN‴ᶜ = blockHistoryPreservation-broadcastMsgsᶜ mds N‴ bᵐ∈bhN‴
                              ... | no _     | yes bᵐ∈bhN‴ᶜ = goal-∷ʳ-c¬wp′-* {mds} sub
                              ... | no ¬hbᵐ  | no  bᵐ∉bhN‴ᶜ
                                rewrite
                                  count-reject-∷ ¿ P ¿¹ {x = bᵐ} {xs = undup (blockHistory (broadcastMsgsᶜ mds N‴))}
                                    λ where (_ , hbᵐ , _) → contradiction hbᵐ ¬hbᵐ
                                  = goal-∷ʳ-c¬wp′-* {mds} sub
          goal (permuteParties _) = ih NBlockMade
          goal (permuteMsgs    _) = ih NBlockMade

superSlots≡superBlocks : ∀ {N : GlobalState} {sl₁ sl₂ : Slot} →
    N₀ ↝⋆ N
  → ForgingFree N
  → 0 < sl₁
  → sl₂ ≤ N .clock
  → length (superSlotsInRange sl₁ sl₂) ≡ length (superBlocksInRange N sl₁ sl₂)
superSlots≡superBlocks = superSlots≡superBlocksʳ ∘ Star⇒Starʳ
    where
      open RTC; open Starʳ

      superSlots≡superBlocksʳ :  ∀ {N : GlobalState} {sl₁ sl₂ : Slot} →
          N₀ ↝⋆ʳ N
        → ForgingFree N
        → 0 < sl₁
        → sl₂ ≤ N .clock
        → length (superSlotsInRange sl₁ sl₂) ≡ length (superBlocksInRange N sl₁ sl₂)
      superSlots≡superBlocksʳ {N} {sl₁} {sl₂} εʳ ffN 0<sl₁ sl₂≤1
        with sl₁
      ... | 0 = contradiction 0<sl₁ (Nat.<-irrefl refl)
      ... | suc sl₁′
          with sl₂
      ...   | 0 = refl
      ...   | suc sl₂′ rewrite Nat.n≤0⇒n≡0 $ Nat.≤-pred sl₂≤1 | Nat.0∸n≡0 sl₁′ = refl
      superSlots≡superBlocksʳ {N} {sl₁} {sl₂} (_◅ʳ_ {j = N′} N₀↝⋆ʳN′ N′↝N) ffN 0<sl₁ sl₂≤Nₜ = goal N′↝N
        where
          N₀↝⋆N′ : N₀ ↝⋆ N′
          N₀↝⋆N′ = Starʳ⇒Star N₀↝⋆ʳN′

          ffN′ : ForgingFree N′
          ffN′ = ForgingFreePrev (N′↝N ◅ ε) ffN

          ih : sl₂ ≤ N′ .clock → length (superSlotsInRange sl₁ sl₂) ≡ length (superBlocksInRange N′ sl₁ sl₂)
          ih = superSlots≡superBlocksʳ {N′} {sl₁} {sl₂} N₀↝⋆ʳN′ ffN′ 0<sl₁

          P : Pred Block 0ℓ
          P = λ b → sl₁ ≤ b .slot × b .slot < sl₂

          goal : N′ ↝ N → length (superSlotsInRange sl₁ sl₂) ≡ length (superBlocksInRange N sl₁ sl₂)
          goal (deliverMsgs {N′ = N″} N′Ready N′—[eoN′]↓→∗N″) = let open ≡-Reasoning in begin
            length (superSlotsInRange sl₁ sl₂)
              ≡⟨ ih sl₂≤N′ₜ ⟩
            length (superBlocksInRange N′ sl₁ sl₂)
              ≡⟨ cong length $ filter-deduplicate-comm {P? = ¿ P ¿¹} (filter ¿ SuperBlock ¿¹ (blockHistory N′)) ⟩
            length (L.deduplicate  _≟_ (filter ¿ P ¿¹ (filter ¿ SuperBlock ¿¹ (blockHistory N′))))
              ≡⟨ Unique-≡ˢ-#≡
                   (deduplicate-! $ filter ¿ P ¿¹ (filter ¿ SuperBlock ¿¹ (blockHistory N′))) eq .Equivalence.to
                   (deduplicate-! $ filter ¿ P ¿¹ (filter ¿ SuperBlock ¿¹ (blockHistory N))) ⟩
            length (L.deduplicate  _≟_ (filter ¿ P ¿¹ (filter ¿ SuperBlock ¿¹ (blockHistory N))))
              ≡⟨ cong length $ sym $ filter-deduplicate-comm {P? = ¿ P ¿¹} (filter ¿ SuperBlock ¿¹ (blockHistory N)) ⟩
            length (superBlocksInRange N sl₁ sl₂)
            ∎
            where
              sl₂≤N′ₜ : sl₂ ≤ N′ .clock
              sl₂≤N′ₜ rewrite clockPreservation-↓∗ N′—[eoN′]↓→∗N″ = sl₂≤Nₜ

              eq :
                L.deduplicate _≟_ (filter ¿ P ¿¹ (filter ¿ SuperBlock ¿¹ (blockHistory N′)))
                ≡ˢ
                L.deduplicate _≟_ (filter ¿ P ¿¹ (filter ¿ SuperBlock ¿¹ (blockHistory N)))
              eq {b} = begin
                b ∈ L.deduplicate _≟_ (filter ¿ P ¿¹ (filter ¿ SuperBlock ¿¹ (blockHistory N′)))
                  ≡⟨ cong (b ∈_) $ filter-deduplicate-comm {P? = ¿ P ¿¹} (filter ¿ SuperBlock ¿¹ (blockHistory N′)) ⟨
                b ∈ filter ¿ P ¿¹ (superBlocks N′)
                ∼⟨ filter-cong $ superBlocksPreservation-↓∗ N₀↝⋆N′ N′—[eoN′]↓→∗N″ ffN N′Ready ⟩
                b ∈ filter ¿ P ¿¹ (superBlocks N)
                  ≡⟨ cong (b ∈_) $ filter-deduplicate-comm {P? = ¿ P ¿¹} (filter ¿ SuperBlock ¿¹ (blockHistory N)) ⟩
                b ∈ L.deduplicate _≟_ (filter ¿ P ¿¹ (filter ¿ SuperBlock ¿¹ (blockHistory N)))
                ∎
                where open Related.EquationalReasoning

          goal (makeBlock {N′ = N″} N′MsgsDelivered N′—[eoN′]↑→∗N″) = let open ≡-Reasoning in begin
            length (superSlotsInRange sl₁ sl₂)
              ≡⟨ ih sl₂≤N′ₜ ⟩
            length (superBlocksInRange N′ sl₁ sl₂)
              ≡⟨ cong length $ filter-deduplicate-comm {P? = ¿ P ¿¹} (filter ¿ SuperBlock ¿¹ (blockHistory N′)) ⟩
            length (L.deduplicate  _≟_ (filter ¿ P ¿¹ (filter ¿ SuperBlock ¿¹ (blockHistory N′))))
              ≡⟨ Unique-≡ˢ-#≡
                   (deduplicate-! $ filter ¿ P ¿¹ (filter ¿ SuperBlock ¿¹ (blockHistory N′))) eq .Equivalence.to
                   (deduplicate-! $ filter ¿ P ¿¹ (filter ¿ SuperBlock ¿¹ (blockHistory N))) ⟩
            length (L.deduplicate  _≟_ (filter ¿ P ¿¹ (filter ¿ SuperBlock ¿¹ (blockHistory N))))
              ≡⟨ cong length $ sym $ filter-deduplicate-comm {P? = ¿ P ¿¹} (filter ¿ SuperBlock ¿¹ (blockHistory N)) ⟩
            length (superBlocksInRange N sl₁ sl₂) ∎
            where
              sl₂≤N′ₜ : sl₂ ≤ N′ .clock
              sl₂≤N′ₜ rewrite clockPreservation-↑∗ N′—[eoN′]↑→∗N″ = sl₂≤Nₜ

              N′↝⋆N : N′ ↝⋆ N
              N′↝⋆N = Starʳ⇒Star (εʳ ◅ʳ N′↝N)

              eq :
                L.deduplicate _≟_ (filter ¿ P ¿¹ (filter ¿ SuperBlock ¿¹ (blockHistory N′)))
                ≡ˢ
                L.deduplicate _≟_ (filter ¿ P ¿¹ (filter ¿ SuperBlock ¿¹ (blockHistory N)))
              eq {b} = begin
                b ∈ L.deduplicate _≟_ (filter ¿ P ¿¹ (filter ¿ SuperBlock ¿¹ (blockHistory N′)))
                  ∼⟨ deduplicate-id _ ⟩
                b ∈ filter ¿ P ¿¹ (filter ¿ SuperBlock ¿¹ (blockHistory N′))
                  ≡⟨ cong ((b ∈_) ∘ filter ¿ P ¿¹) $ filter-∘-× ¿ HonestBlock ¿¹ ¿ SuperSlot ∘ slot ¿¹ (blockHistory N′) ⟩
                b ∈ filter ¿ P ¿¹ (filter ¿ HonestBlock ¿¹ (filter ¿ SuperSlot ∘ slot ¿¹ (blockHistory N′)))
                  ≡⟨ cong ((b ∈_) ∘ filter ¿ P ¿¹) $ filter-∘-comm ¿ HonestBlock ¿¹ ¿ SuperSlot ∘ slot ¿¹ (blockHistory N′) ⟩
                b ∈ filter ¿ P ¿¹ (filter ¿ SuperSlot ∘ slot ¿¹ (honestBlockHistory N′))
                  ≡⟨ cong (b ∈_) $ filter-∘-comm ¿ P ¿¹ ¿ SuperSlot ∘ slot ¿¹ (honestBlockHistory N′) ⟩
                b ∈ filter ¿ SuperSlot ∘ slot ¿¹ (filter ¿ P ¿¹ (honestBlockHistory N′))
                  ∼⟨ filter-cong f<PN′⇔f<PN ⟩
                b ∈ filter ¿ SuperSlot ∘ slot ¿¹ (filter ¿ P ¿¹ (honestBlockHistory N))
                  ≡⟨ cong (b ∈_) $ filter-∘-comm ¿ P ¿¹ ¿ SuperSlot ∘ slot ¿¹ (honestBlockHistory N) ⟨
                b ∈ filter ¿ P ¿¹ (filter ¿ SuperSlot ∘ slot ¿¹ (honestBlockHistory N))
                  ≡⟨ cong ((b ∈_) ∘ filter ¿ P ¿¹) $ filter-∘-comm ¿ HonestBlock ¿¹ ¿ SuperSlot ∘ slot ¿¹ (blockHistory N) ⟨
                b ∈ filter ¿ P ¿¹ (filter ¿ HonestBlock ¿¹ (filter ¿ SuperSlot ∘ slot ¿¹ (blockHistory N)))
                  ≡⟨ cong ((b ∈_) ∘ filter ¿ P ¿¹) $ filter-∘-× ¿ HonestBlock ¿¹ ¿ SuperSlot ∘ slot ¿¹ (blockHistory N) ⟨
                b ∈ filter ¿ P ¿¹ (filter ¿ SuperBlock ¿¹ (blockHistory N))
                  ∼⟨ SK-sym $ deduplicate-id _ ⟩
                b ∈ L.deduplicate _≟_ (filter ¿ P ¿¹ (filter ¿ SuperBlock ¿¹ (blockHistory N)))
                ∎
                where
                  open Related.EquationalReasoning

                  P⋐<N′ₜ : P ⋐ ((_< N′ .clock) ∘ slot)
                  P⋐<N′ₜ {b} (sl₁≤bₜ , bₜ<sl₂) = Nat.<-≤-trans bₜ<sl₂ sl₂≤N′ₜ

                  f<PN′⇔f<PN : ∀ {b} →
                    b ∈ filter ¿ P ¿¹ (honestBlockHistory N′)
                    ⇔
                    b ∈ filter ¿ P ¿¹ (honestBlockHistory N)
                  f<PN′⇔f<PN {b} with ¿ P b ¿
                  ... | yes Pb = mk⇔ to from
                    where
                      f<N′ₜN′≡ˢf<N′ₜN :
                        filter ((_<? N′ .clock) ∘ slot) (honestBlockHistory N′)
                        ≡ˢ
                        filter ((_<? N′ .clock) ∘ slot) (honestBlockHistory N)
                      f<N′ₜN′≡ˢf<N′ₜN = honestBlocksBelowSlotPreservation N₀↝⋆N′ N′↝⋆N ffN

                      to :
                        b ∈ filter ¿ P ¿¹ (honestBlockHistory N′)
                        →
                        b ∈ filter ¿ P ¿¹ (honestBlockHistory N)
                      to b∈fPN′ with L.Mem.∈-filter⁻ ¿ P ¿¹ {xs = honestBlockHistory N′} b∈fPN′
                      ... | b∈hbhN′ , _ with L.Mem.∈-filter⁻ ((_<? N′ .clock) ∘ slot) {xs = honestBlockHistory N} b∈f<N′ₜN
                        where
                          b∈f<N′ₜN′ : b ∈ filter ((_<? N′ .clock) ∘ slot) (honestBlockHistory N′)
                          b∈f<N′ₜN′ = L.Mem.∈-filter⁺ ((_<? N′ .clock) ∘ slot) b∈hbhN′ (P⋐<N′ₜ {b} Pb)

                          b∈f<N′ₜN : b ∈ filter ((_<? N′ .clock) ∘ slot) (honestBlockHistory N)
                          b∈f<N′ₜN = ≡ˢ⇒⊆×⊇ f<N′ₜN′≡ˢf<N′ₜN .proj₁ b∈f<N′ₜN′
                      ...   | b∈hbhN , _ = L.Mem.∈-filter⁺ ¿ P ¿¹ b∈hbhN Pb

                      from :
                        b ∈ filter ¿ P ¿¹ (honestBlockHistory N)
                        →
                        b ∈ filter ¿ P ¿¹ (honestBlockHistory N′)
                      from b∈fPN with L.Mem.∈-filter⁻ ¿ P ¿¹ {xs = honestBlockHistory N} b∈fPN
                      ... | b∈hbhN , _ with L.Mem.∈-filter⁻ ((_<? N′ .clock) ∘ slot) {xs = honestBlockHistory N′} b∈f<N′ₜN′
                        where
                          b∈f<N′ₜN : b ∈ filter ((_<? N′ .clock) ∘ slot) (honestBlockHistory N)
                          b∈f<N′ₜN = L.Mem.∈-filter⁺ ((_<? N′ .clock) ∘ slot) b∈hbhN (P⋐<N′ₜ {b} Pb)

                          b∈f<N′ₜN′ : b ∈ filter ((_<? N′ .clock) ∘ slot) (honestBlockHistory N′)
                          b∈f<N′ₜN′ = ≡ˢ⇒⊆×⊇ f<N′ₜN′≡ˢf<N′ₜN .proj₂ b∈f<N′ₜN
                      ...   | b∈hbhN′ , _ = L.Mem.∈-filter⁺ ¿ P ¿¹ b∈hbhN′ Pb
                  ... | no ¬Pb = mk⇔ to from
                    where
                      to :
                        b ∈ filter ¿ P ¿¹ (honestBlockHistory N′)
                        →
                        b ∈ filter ¿ P ¿¹ (honestBlockHistory N)
                      to b∈fPN′ with L.Mem.∈-filter⁻ ¿ P ¿¹ {xs = honestBlockHistory N′} b∈fPN′
                      ... | _ , Pb = contradiction Pb ¬Pb

                      from :
                        b ∈ filter ¿ P ¿¹ (honestBlockHistory N)
                        →
                        b ∈ filter ¿ P ¿¹ (honestBlockHistory N′)
                      from b∈fPN with L.Mem.∈-filter⁻ ¿ P ¿¹ {xs = honestBlockHistory N} b∈fPN
                      ... | _ , Pb = contradiction Pb ¬Pb

          goal (advanceRound N′BlockMade) with Nat.m≤n⇒m<n∨m≡n sl₂≤Nₜ
          ... | inj₁ sl₂<Nₜ = ih $ Nat.≤-pred sl₂<Nₜ
          ... | inj₂ sl₂≡Nₜ rewrite sl₂≡Nₜ = goal-sl₂≡Nₜ
            where
              goal-sl₂≡Nₜ : length (superSlotsInRange sl₁ (1 + N′ .clock)) ≡ length (superBlocksInRange N sl₁ (1 + N′ .clock))
              goal-sl₂≡Nₜ with sl₁ ≤? N′ .clock
              ... | no sl₁≰N′ₜ rewrite emptySlotsInRange (Nat.≰⇒> sl₁≰N′ₜ) = subst ((0 ≡_) ∘ length) []≡sb[sl₁,1+N′ₜ] refl
                where
                  []≡sb[sl₁,1+N′ₜ] : [] ≡ superBlocksInRange N sl₁ (1 + N′ .clock)
                  []≡sb[sl₁,1+N′ₜ] = []≡sb[sl₁,1+N′ₜ]* (superBlocks N)
                    where
                      P′? : Decidable¹ (λ b → sl₁ ≤ b .slot × b .slot < 1 + N′ .clock)
                      P′? b = ¿ sl₁ ≤ b .slot × b .slot < 1 + N′ .clock ¿

                      []≡sb[sl₁,1+N′ₜ]* : ∀ bs → [] ≡ filter P′? bs
                      []≡sb[sl₁,1+N′ₜ]* [] = refl
                      []≡sb[sl₁,1+N′ₜ]* (b ∷ bs) with P′? b
                      ... | yes P′b@(sl₁≤bₜ , bₜ<1+N′ₜ) = contradiction sl₁≤N′ₜ sl₁≰N′ₜ
                        where
                          bₜ≤N′ₜ : b .slot ≤ N′ .clock
                          bₜ≤N′ₜ = Nat.≤-pred bₜ<1+N′ₜ

                          sl₁≤N′ₜ : sl₁ ≤ N′ .clock
                          sl₁≤N′ₜ = Nat.≤-trans sl₁≤bₜ bₜ≤N′ₜ
                      ... | no ¬P′b rewrite filter-reject P′? {b} {bs} ¬P′b = []≡sb[sl₁,1+N′ₜ]* bs
              ... | yes sl₁≤N′ₜ = let open ≡-Reasoning in begin
                length (superSlotsInRange sl₁ (1 + N′ .clock))
                  ≡⟨ cong length $ slotsInRange-++ ¿ SuperSlot ¿¹ sl₁≤N′ₜ (Nat.n≤1+n (N′ .clock)) ⟩
                length (superSlotsInRange sl₁ (N′ .clock) ++ superSlotsInRange (N′ .clock) (1 + N′ .clock))
                  ≡⟨ length-++ (superSlotsInRange sl₁ (N′ .clock)) ⟩
                length (superSlotsInRange sl₁ (N′ .clock)) + length (superSlotsInRange (N′ .clock) (1 + N′ .clock))
                  ≡⟨ cong (_+ _) $ superSlots≡superBlocksʳ {N′} {sl₁} {N′ .clock} N₀↝⋆ʳN′ ffN′ 0<sl₁ Nat.≤-refl ⟩
                length (superBlocksInRange N sl₁ (N′ .clock)) + length (superSlotsInRange (N′ .clock) (1 + N′ .clock))
                  ≡⟨ cong (length (superBlocksInRange N sl₁ (N′ .clock)) +_) |ss|≡|sb|[N′ₜ,1+N′ₜ] ⟩
                length (superBlocksInRange N sl₁ (N′ .clock)) + length (superBlocksInRange N (N′ .clock) (1 + N′ .clock))
                  ≡⟨ length-++ (superBlocksInRange N sl₁ (N′ .clock)) ⟨
                length (superBlocksInRange N sl₁ (N′ .clock) ++ superBlocksInRange N (N′ .clock) (1 + N′ .clock))
                  ≡⟨ ↭-length sb[N′ₜ,1+N′ₜ]-split ⟨
                length (superBlocksInRange N sl₁ (1 + N′ .clock))
                  ∎
                where
                  sb[N′ₜ,1+N′ₜ]-split :
                    superBlocksInRange N sl₁ (1 + N′ .clock)
                    ↭
                    superBlocksInRange N sl₁ (N′ .clock) ++ superBlocksInRange N (N′ .clock) (1 + N′ .clock)
                  sb[N′ₜ,1+N′ₜ]-split = blocksInRangeSplit (superBlocks N) sl₁≤N′ₜ (Nat.n≤1+n (N′ .clock))

                  ι≡[N′ₜ] : ι (N′ .clock) (suc (N′ .clock) ∸ N′ .clock) ≡ [ N′ .clock ]
                  ι≡[N′ₜ] rewrite Nat.m+n∸n≡m 1 (N′ .clock) = refl

                  |ss|≡|sb|[N′ₜ,1+N′ₜ] :
                    length (superSlotsInRange (N′ .clock) (1 + N′ .clock))
                    ≡
                    length (superBlocksInRange N (N′ .clock) (1 + N′ .clock))
                  |ss|≡|sb|[N′ₜ,1+N′ₜ] rewrite ι≡[N′ₜ] = |ss|≡|sb|[N′ₜ,1+N′ₜ]′
                    where
                      |ss|≡|sb|[N′ₜ,1+N′ₜ]′ :
                        length (filter ¿ SuperSlot ¿¹ [ N′ .clock ])
                        ≡
                        length (superBlocksInRange N (N′ .clock) (1 + N′ .clock))
                      |ss|≡|sb|[N′ₜ,1+N′ₜ]′ with ¿ SuperSlot (N′ .clock) ¿
                      ... | yes ssN′ₜ
                              rewrite
                                filter-accept ¿ SuperSlot ¿¹ {xs = []} ssN′ₜ
                              = sym $ superBlockOneness N₀↝⋆N′ ffN′ N′BlockMade .Equivalence.from ssN′ₜ
                      ... | no ¬ssN′ₜ rewrite filter-reject ¿ SuperSlot ¿¹ {xs = []} ¬ssN′ₜ
                        with superBlocksInRange N (N′ .clock) (1 + N′ .clock) ≟ []
                      ...   | yes sbs≡[] rewrite sbs≡[] = refl
                      ...   | no sbs≢[] = contradiction ssN′ₜ ¬ssN′ₜ
                        where
                          ssN′ₜ : SuperSlot (N′ .clock)
                          ssN′ₜ
                            with ≢[]⇒∷ sbs≢[]
                          ... | sb , sbs′ , sbs≡sb∷sbs′
                              with
                                L.Mem.∈-filter⁻
                                  (λ b → ¿ N′ .clock ≤ b .slot × b .slot < 1 + N′ .clock ¿)
                                  {xs = superBlocks N}
                                  (subst (sb ∈_) (sym sbs≡sb∷sbs′) (x∈x∷xs _))
                          ... | sb∈sbsN , N′ₜ≤sbₜ , sbₜ<1+N′ₜ = subst SuperSlot sbₜ≡N′ₜ sssbₜ
                            where
                              sbₜ≡N′ₜ : sb. slot ≡ N′ .clock
                              sbₜ≡N′ₜ = sym $ Nat.≤-antisym N′ₜ≤sbₜ (Nat.≤-pred sbₜ<1+N′ₜ)

                              sssbₜ : SuperSlot (sb .slot)
                              sssbₜ = ∈-superBlocks⁻ {N} sb∈sbsN .proj₂ .proj₂

          goal (permuteParties _) = ih sl₂≤Nₜ
          goal (permuteMsgs    _) = ih sl₂≤Nₜ
