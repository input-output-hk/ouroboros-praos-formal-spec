{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled

open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Safety.ChainFromBlock
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Properties.Base.Time ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.LocalState ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.ExecutionOrder ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.Trees ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.ForgingFree ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.CollisionFree ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.BlockHistory ⦃ params ⦄ ⦃ assumptions ⦄
open import Prelude.AssocList.Properties.Ext using (set-⁉; set-⁉-¬)
open import Protocol.Prelude
open import Protocol.BaseTypes
open import Protocol.Crypto ⦃ params ⦄ using (Hashable); open Hashable ⦃ ... ⦄
open import Protocol.Block ⦃ params ⦄
open import Protocol.Chain ⦃ params ⦄
open import Protocol.Message ⦃ params ⦄
open import Protocol.Network ⦃ params ⦄; open Envelope
open import Protocol.TreeType ⦃ params ⦄
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Prelude.STS.Properties using (—[]→∗⇒—[]→∗ʳ; —[]→∗ʳ⇒—[]→∗)
open import Data.Nat.Properties.Ext using (pred[n]<n {- ; suc-≢-injective -})
open import Data.Maybe.Properties.Ext using (≡just⇒Is-just)
open import Data.List.Ext using (ι)
open import Data.List.Membership.Propositional.Properties.Ext using (∈-findᵇ⁻; ∈-∷-≢⁻; x∈x∷xs; ∈-∷⁻ {- ; ; ;  -})
open import Data.List.Properties.Ext using (Px-findᵇ⁻; ∷≢[]; []≢∷ʳ; ≢[]⇒∷ {- filter-∘-comm; filter-∘-×; ; ; ; ; filter-acceptʳ; filter-rejectʳ; foldr-preservesʳ' -})
open import Data.List.Relation.Binary.Subset.Propositional.Properties.Ext using (filterᵇ-mono {- cartesianProduct-⊆-Mono; ; ∷-⊆; ∷-⊆⁺; ∷⊆⇒∈ -})
open import Data.List.Relation.Unary.All.Properties.Ext using (cartesianProduct⁻)
open import Data.List.Relation.Unary.AllPairs.Properties.Ext using (headʳ)
open import Data.List.Relation.Unary.Unique.Propositional.Properties.Ext using ({- ++⁻; -} Unique[xs∷ʳx]⇒x∉xs)
open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_; ≡ˢ⇒⊆×⊇ {- ; ≡ˢ-refl; ≡ˢ-sym; ≡ˢ-trans; ; ⊆×⊇⇒≡ˢ; deduplicate-cong; filter-cong; All-resp-≡ˢ; Any-resp-≡ˢ; cartesianProduct-cong -})
open import Relation.Binary.PropositionalEquality.Properties.Ext using (=/=⇔≢; ≡×≢⇒≢; ==⇔≡)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Ext using (Starʳ)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.Ext using (Star⇒Starʳ; Starʳ⇒Star)
open import Data.List.Relation.Unary.Unique.Propositional.Properties using (Unique[x∷xs]⇒x∉xs)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (Any-resp-↭)
open import Function.Bundles
open import Relation.Binary.PropositionalEquality using (≢-sym)
open import Class.DecEq.WithK using (≟-refl)

cfb[gb]≡[gb] : ∀ {bs : List Block} → chainFromBlock genesisBlock bs ≡ [ genesisBlock ]
cfb[gb]≡[gb] rewrite ≟-refl genesisBlock = refl

honestBlockCfb✓-↑∗ : ∀ {N₁ N₂ N′ : GlobalState} {ps : List Party} →
    N₀ ↝⋆ N₁
  → N₁ ↝⋆ N₂
  → ForgingFree N₂
  → _ ⊢ N₁ —[ ps ]↑→∗ N′
  → N′ ↷↑ N₂
  → Unique ps
  → CollisionFree N′
  → L.All.All (λ b → chainFromBlock b (blockHistory N′) ✓) (honestBlockHistory N′)
honestBlockCfb✓-↑∗ = {!!}

cfbInBlockListIsSubset′ : ∀ {b : Block} {bs : List Block} {c : Chain} →
    BlockListCollisionFree bs
  → (b ∷ c) ✓
  → c ⊆ˢ bs
  → chainFromBlock b bs ≡ b ∷ c
cfbInBlockListIsSubset′ = {!!}

cfbInBlockListIsSubset : ∀ {b : Block} {bs : List Block} {c : Chain} →
  let
    gbs : List Block
    gbs = genesisBlock ∷ bs
  in
    BlockListCollisionFree gbs
  → (b ∷ c) ✓
  → c ⊆ˢ gbs
  → chainFromBlock b bs ≡ b ∷ c
cfbInBlockListIsSubset = {!!}

{- Traversing a chain `c` from the tip to the genesis block and calculating
   the length of the "chain from block" of each block `b` is equal to a countdown
   from the length of `c` until 1.
   Example: Let `c` be bᴬ ← bᴰ ← bᴮ ← gb. Then:
     chainFromBlock bᴬ bs ≡ bᴬ ← bᴰ ← bᴮ ← gb ⇒ ∣ chainFromBlock bᴬ bs ∣ ≡ 4
     chainFromBlock bᴰ bs ≡      bᴰ ← bᴮ ← gb ⇒ ∣ chainFromBlock bᴰ bs ∣ ≡ 3
     chainFromBlock bᴰ bs ≡           bᴮ ← gb ⇒ ∣ chainFromBlock bᴮ bs ∣ ≡ 2
     chainFromBlock bᴰ bs ≡                gb ⇒ ∣ chainFromBlock gb bs ∣ ≡ 1
-}
cfbLenghtsIsCountdown : ∀ {bs : List Block} {c : Chain} →
    BlockListCollisionFree bs
  → c ✓
  → c ⊆ˢ genesisBlock ∷ bs
  → L.map (λ b → ∣ chainFromBlock b bs ∣) c ≡ L.reverse (ι 1 ∣ c ∣) -- L.map suc (L.downFrom ∣ c ∣)
cfbLenghtsIsCountdown = {!!}

module _ where

  private

    ancestorPreservation : ∀ {bs bs′ : List Block} {b b′ : Block} →
        BlockListCollisionFree bs′
      → bs ⊆ˢ bs′
      → L.findᵇ ((b .prev ==_) ∘ hash) bs ≡ just b′
      → L.findᵇ ((b .prev ==_) ∘ hash) bs′ ≡ just b′
    ancestorPreservation {bs} {bs′} {b} {b′} cfbs′ bs⊆ˢbs′ eqf = goal cfbs′ b′∈bs′
      where
        b′∈bs′ : b′ ∈ bs′
        b′∈bs′ = bs⊆ˢbs′ $ ∈-findᵇ⁻ eqf

        prevb≡hb′ : (b .prev == hash b′) ≡ true
        prevb≡hb′ = Px-findᵇ⁻ {P = ((b .prev ==_) ∘ hash)} {xs = bs} eqf

        prevb≡b″ : ∀ {b″} → b′ ≡ b″ → (b .prev == hash b″) ≡ true
        prevb≡b″ b′≡b″ = subst _ b′≡b″ prevb≡hb′

        goal : ∀ {bs′} → BlockListCollisionFree bs′ → b′ ∈ bs′ → L.findᵇ ((b .prev ==_) ∘ hash) bs′ ≡ just b′
        goal {b″ ∷ bs″} cfbs′ b′∈bs′ with b′ ≟ b″
        ... | yes b′≡b″ rewrite prevb≡b″ b′≡b″ = cong just (sym b′≡b″)
        ... | no b′≢b″ = goal′
          where
            b′∈bs″ : b′ ∈ bs″
            b′∈bs″ = ∈-∷-≢⁻ b′∈bs′ b′≢b″

            hb′≢hb″ : hash b′ ≢ hash b″
            hb′≢hb″ = contraposition (cartesianProduct⁻ cfbs′ (L.Mem.∈-++⁺ʳ [ b″ ] b′∈bs″) (x∈x∷xs bs″)) b′≢b″

            prevb≢hb″ : (b .prev == hash b″) ≡ false
            prevb≢hb″ = Equivalence.from =/=⇔≢ $ ≡×≢⇒≢ (Equivalence.to ==⇔≡ prevb≡hb′) hb′≢hb″

            goal′ : L.findᵇ ((b .prev ==_) ∘ hash) (b″ ∷ bs″) ≡ just b′
            goal′ rewrite prevb≢hb″ = goal {bs″} (BlockListCollisionFree-∷ {bs = bs″} cfbs′) b′∈bs″

  {-# TERMINATING #-}
  -- TODO: Prove termination using `WellFounded` (if needed).
  subsetCfbPreservation : ∀ {bs bs′ : List Block} {b : Block} →
      BlockListCollisionFree bs′
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
                    (BlockListCollisionFree-⊆ (L.SubS.filter-⊆ _ bs′) cfbs′)
                    (filterᵇ-mono bs⊆ˢbs′)
                    (subst (_≢ []) (sym eqcfb) ∷≢[])
                | eqcfb
                  = refl

subsetCfb✓Preservation : ∀ {bs bs′ : List Block} {b : Block} →
    BlockListCollisionFree bs′
  → bs ⊆ˢ bs′
  → chainFromBlock b bs ✓
  → chainFromBlock b bs′ ✓
subsetCfb✓Preservation {bs} {bs′} {b} cfbs′ bs⊆ˢbs′ cfbbs✓ = subst _✓ cfbbs≡cfbbs′ cfbbs✓
  where
    cfbbs≢[] : chainFromBlock b bs ≢ []
    cfbbs≢[] = subst (_≢ []) (✓⇒gbIsHead cfbbs✓ .proj₂) (≢-sym []≢∷ʳ)

    cfbbs≡cfbbs′ : chainFromBlock b bs ≡ chainFromBlock b bs′
    cfbbs≡cfbbs′ = subsetCfbPreservation cfbs′ bs⊆ˢbs′ cfbbs≢[]

opaque

  unfolding honestBlockMaking corruptBlockMaking

  chainFromNewBlock : ∀ {ls p ps N N′} →
    let
      best = bestChain (N′ .clock ∸ 1) (ls .tree)
      nb = mkBlock (hash (tip best)) (N′ .clock) (txSelection (N′ .clock) p) p
    in
      N₀ ↝⋆ N
    → _ ⊢ N —[ ps ]↑→∗ʳ N′
    → winner p (clock N′)
    → p ∉ ps
    → N′ .states ⁉ p ≡ just ls
    → Honest p
    → BlockListCollisionFree (genesisBlock ∷ nb ∷ blockHistory N′)
    → chainFromBlock nb (nb ∷ blockHistory N′) ≡ nb ∷ best
      ×
      (nb ∷ best) ✓
  chainFromNewBlock {ls} {p} {ps} {N} {N′} N₀↝⋆N ts⋆ isWinner p∉ps lsπ hpπ cf[gb+nb+bhN′] rewrite dec-yes (Params.winnerᵈ params {p} {N′ .clock} .dec) isWinner .proj₂ = cfbInBlockListIsSubset cf[gb+nb+bhN′] nb∷best✓ bestInHist , nb∷best✓
    where
      best : Chain
      best = bestChain (N′ .clock ∸ 1) (ls .tree)

      nb : Block
      nb = mkBlock (hash (tip best)) (N′ .clock) (txSelection (N′ .clock) p) p

      best✓ : best ✓
      best✓ = valid (ls .tree) (N′ .clock ∸ 1)

      nb∷best✓ : (nb ∷ best) ✓
      nb∷best✓ with ≢[]⇒∷ (✓⇒≢[] best✓)
      ... | bestH , bestT , best≡bestH∷bestT
        rewrite best≡bestH∷bestT =
          ✓-∷ .Equivalence.to (isWinner , refl , nb>ˢbestH , subst _✓ best≡bestH∷bestT best✓)
        where
          nb>ˢbestH : N′ .clock > bestH .slot -- i.e., nb >ˢ bestH
          nb>ˢbestH = Nat.≤-<-trans bestHₛ≤N′ₜ-1 N′ₜ-1<N′ₜ
            where
              bestH∈best : bestH ∈ best
              bestH∈best rewrite best≡bestH∷bestT = x∈x∷xs bestT {bestH}

              bestHₛ≤N′ₜ-1 : bestH .slot ≤ N′ .clock ∸ 1
              bestHₛ≤N′ₜ-1 = L.All.lookup (bestChainSlotBounded (ls .tree) (N′ .clock ∸ 1)) bestH∈best

              N′ₜ-1<N′ₜ : N′ .clock ∸ 1 < N′ .clock
              N′ₜ-1<N′ₜ = pred[n]<n {N′ .clock} ⦃ Nat.>-nonZero N′ₜ>0 ⦄
                where
                  N′ₜ>0 : N′ .clock > 0
                  N′ₜ>0 rewrite (clockPreservation-↑∗ (—[]→∗ʳ⇒—[]→∗ ts⋆)) = positiveClock N₀↝⋆N

      bestInHist : best ⊆ˢ genesisBlock ∷ nb ∷ blockHistory N′
      bestInHist = begin
        best
          ⊆⟨ selfContained (ls .tree) (N′ .clock ∸ 1) ⟩
        filter (λ b → slot b ≤? (N′ .clock ∸ 1)) (allBlocks (ls .tree))
          ⊆⟨ L.SubS.filter-⊆ (λ b → slot b ≤? (N′ .clock ∸ 1)) (allBlocks (ls .tree)) ⟩
        allBlocks (ls .tree)
          ⊆⟨ honestLocalTreeInHonestGlobalTree N₀↝⋆N hpπ ls[p]inN ⟩
        allBlocks (honestTree N)
          ⊆⟨ honestGlobalTreeInBlockHistory N₀↝⋆N ⟩
        genesisBlock ∷ blockHistory N
          ⊆⟨ L.SubS.∷⁺ʳ _ (blockHistoryPreservation-↑∗ (—[]→∗ʳ⇒—[]→∗ ts⋆)) ⟩
        genesisBlock ∷ blockHistory N′
          ⊆⟨ L.SubS.xs⊆x∷xs _ _ ⟩
        nb ∷ genesisBlock ∷ blockHistory N′
          ⊆⟨ L.SubS.⊆-reflexive-↭ (swap _ _ refl) ⟩
        genesisBlock ∷ nb ∷ blockHistory N′ ∎
        where
          open L.SubS.⊆-Reasoning Block
          open import Data.List.Relation.Binary.Permutation.Propositional

          ls[p]inN : N .states ⁉ p ≡ just ls
          ls[p]inN rewrite sym $ localStatePreservation-∉-↑∗ p∉ps (—[]→∗ʳ⇒—[]→∗ ts⋆) = lsπ

  honestBlockCfb✓ : ∀ {N : GlobalState} {b : Block} →
      N₀ ↝⋆ N
    → ForgingFree N
    → CollisionFree N
    → b ∈ honestBlockHistory N
    → chainFromBlock b (blockHistory N) ✓
  honestBlockCfb✓ = honestBlockCfb✓ʳ ∘ Star⇒Starʳ
    where
      open RTC; open Starʳ
      honestBlockCfb✓ʳ : ∀ {N : GlobalState} {b : Block} →
          N₀ ↝⋆ʳ N
        → ForgingFree N
        → CollisionFree N
        → b ∈ honestBlockHistory N
        → chainFromBlock b (blockHistory N) ✓
      honestBlockCfb✓ʳ εʳ ffN cfN b∈hbhN = contradiction b∈hbhN L.Any.¬Any[]
      honestBlockCfb✓ʳ {N} {b} (_◅ʳ_ {j = N′} N₀↝⋆ʳN′ N′↝N) ffN cfN b∈hbhN = goal N′↝N
        where
          N₀↝⋆N′ : N₀ ↝⋆ N′
          N₀↝⋆N′ = Starʳ⇒Star N₀↝⋆ʳN′

          ffN′ : ForgingFree N′
          ffN′ = ForgingFreePrev (N′↝N ◅ ε) ffN

          cfN′ : CollisionFree N′
          cfN′ = CollisionFreePrev (N′↝N ◅ ε) cfN

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

              deliverMsgsGoal : ∀ {N″ ps} → CollisionFree N″ → _ ⊢ N′ —[ ps ]↓→∗ʳ N″ → chainFromBlock b (blockHistory N″) ✓
              deliverMsgsGoal _ [] = ih
              deliverMsgsGoal {N″} cfN″ (_∷ʳ_ {s′ = N‴} N′—[ps]↓→∗ʳN‴ N‴↝[p]↓N″) = subst _✓ cfbhN‴≡cfbhN″ ih′
                where
                  cfN‴ : CollisionFree N‴
                  cfN‴ = CollisionFreePrev-↓ N‴↝[p]↓N″ cfN″

                  ih′ : chainFromBlock b (blockHistory N‴) ✓
                  ih′ = deliverMsgsGoal cfN‴ N′—[ps]↓→∗ʳN‴

                  cfbhN″ : BlockListCollisionFree (blockHistory N″)
                  cfbhN″ = BlockListCollisionFree-∷ {blockHistory N″} {genesisBlock} cfN″

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
                → CollisionFree N″
                → b ∈ honestBlockHistory N″
                → Unique ps
                → _ ⊢ N′ —[ ps ]↑→∗ʳ N″
                → chainFromBlock b (blockHistory N″) ✓
              makeBlockGoal {N″} [] prfN cfN″ b∈hbhN″ _ [] = ih b∈hbhN″
              makeBlockGoal {N″} [] prfN cfN″ b∈hbhN″ _ (_∷ʳ_ {eq = eq} _ _) = contradiction eq []≢∷ʳ
              makeBlockGoal {N″} (p ∷ ps) prfN cfN″ b∈hbhN″ p∷psUniq (_∷ʳ_ {is = ps′} {i = p′} {s′ = N‴} {eq = eq} ts⋆ ts) = step ts
                where
                  cfN‴ : CollisionFree N‴
                  cfN‴ = CollisionFreePrev-↑ ts cfN″

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

                      cfπ : BlockListCollisionFree (nb ∷ blockHistory N‴)
                      cfπ = BlockListCollisionFree-∷ {nb ∷ blockHistory N‴} {genesisBlock} cfN″

                      step-honestParty↑ : chainFromBlock b (nb ∷ blockHistory N‴) ✓
                      step-honestParty↑ with ∈-∷⁻ b∈nb∷hbhN‴
                      ... | inj₂ b∈hbhN‴ = subsetCfb✓Preservation cfπ bhπ cfb✓π
                        where
                          cfb✓π : chainFromBlock b (blockHistory N‴) ✓
                          cfb✓π = ih′ b∈hbhN‴
                      ... | inj₁ b≡nb rewrite b≡nb with chainFromNewBlock N₀↝⋆N′ ts⋆ isWinner p′∉ps′ lsπ hp′π cfN″
                      ... |   cfbIsNb∷Best , nb∷best✓ = subst _✓ (sym cfbIsNb∷Best) nb∷best✓
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

                      cfπ : BlockListCollisionFree (blockHistory (broadcastMsgsᶜ mds N‴))
                      cfπ = BlockListCollisionFree-∷ {blockHistory (broadcastMsgsᶜ mds N‴)} {genesisBlock} cfN″

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
  → ForgingFree N
  → CollisionFree N′
  → b ∈ honestBlockHistory N
  → N .progress ≡ ready
  → chainFromBlock b (blockHistory N) ≡ chainFromBlock b (blockHistory N′)
honestCfbPreservation-↓∗ {N} {N′} {b} N₀↝⋆N N—[eoN′]↓→∗N′ ffN cfN′ b∈hbhN NReady = subsetCfbPreservation cfbhN′ bhN⊆bhN′ cfbN≢[]
  where
    cfbhN′ : BlockListCollisionFree (blockHistory N′)
    cfbhN′ = BlockListCollisionFree-∷ {blockHistory N′} {genesisBlock} cfN′

    bhN⊆bhN′ : blockHistory N ⊆ˢ blockHistory N′
    bhN⊆bhN′ = blockHistoryPreservation-↓∗ N—[eoN′]↓→∗N′

    cfbN≢[] : chainFromBlock b (blockHistory N) ≢ []
    cfbN≢[] = ✓⇒≢[] cfbbN✓
      where
        N↝⋆N′↓ : N ↝⋆ record N′ {progress = msgsDelivered}
        N↝⋆N′↓ = deliverMsgs NReady N—[eoN′]↓→∗N′ ◅ ε
          where open RTC

        cfN : CollisionFree N
        cfN = CollisionFreePrev N↝⋆N′↓ cfN′

        cfbbN✓ : chainFromBlock b (blockHistory N) ✓
        cfbbN✓ = honestBlockCfb✓ N₀↝⋆N ffN cfN b∈hbhN

cfbHbhPres :  ∀ {N N′ : GlobalState} {b : Block} →
    N₀ ↝⋆ N′
  → N′ ↝ N
  → ForgingFree N
  → CollisionFree N
  → b ∈ honestBlockHistory N
  → honestBlockHistory N′ ≡ˢ honestBlockHistory N
  → chainFromBlock b (blockHistory N′) ≡ chainFromBlock b (blockHistory N)
cfbHbhPres {N} {N′} {b} N₀↝⋆N′ N′↝N ffN cfN b∈hbhN hbhPres = subsetCfbPreservation cfbhN bhN′⊆bhN cfbhN′≢[]
  where
    open RTC; open Starʳ

    ffN′ : ForgingFree N′
    ffN′ = ForgingFreePrev (N′↝N ◅ ε) ffN

    cfN′ : CollisionFree N′
    cfN′ = CollisionFreePrev (N′↝N ◅ ε) cfN

    cfbhN′≢[] : chainFromBlock b (blockHistory N′) ≢ []
    cfbhN′≢[] = ✓⇒≢[] $ honestBlockCfb✓ N₀↝⋆N′ ffN′ cfN′ b∈hbhN′
      where
        b∈hbhN′ : b ∈ honestBlockHistory N′
        b∈hbhN′ = ≡ˢ⇒⊆×⊇ hbhPres .proj₂ b∈hbhN

    bhN′⊆bhN : blockHistory N′ ⊆ˢ blockHistory N
    bhN′⊆bhN = blockHistoryPreservation-↝⋆ (N′↝N ◅ ε)

    cfbhN : BlockListCollisionFree (blockHistory N)
    cfbhN = BlockListCollisionFree-∷ {blockHistory N} {genesisBlock} cfN

opaque

  unfolding honestBlockMaking corruptBlockMaking

  cfbInHonestTree : ∀ {N : GlobalState} →
      N₀ ↝⋆ N
    → ForgingFree N
    → CollisionFree N
    → L.All.All (λ b → chainFromBlock b (blockHistory N) ⊆ˢ allBlocks (honestTree N)) (honestBlockHistory N)
  cfbInHonestTree = cfbInHonestTreeʳ ∘ Star⇒Starʳ
      where
        open RTC; open Starʳ

        cfbInHonestTreeʳ : ∀ {N : GlobalState} →
            N₀ ↝⋆ʳ N
          → ForgingFree N
          → CollisionFree N
          → L.All.All (λ b → chainFromBlock b (blockHistory N) ⊆ˢ allBlocks (honestTree N)) (honestBlockHistory N)
        cfbInHonestTreeʳ εʳ ffN cfN = L.All.All.[]
        cfbInHonestTreeʳ {N} N₀↝⋆ʳN@(_◅ʳ_ {j = N′} N₀↝⋆ʳN′ N′↝N) ffN cfN
          with
            ih ← cfbInHonestTreeʳ N₀↝⋆ʳN′ (ForgingFreePrev (N′↝N ◅ ε) ffN) (CollisionFreePrev (N′↝N ◅ ε) cfN)
          | N′↝N
        ... | deliverMsgs {N′} {N″} N′Ready N′—[eoN′]↓→∗N″ = L.All.tabulate goal
          where
            N′↝⋆N : N′ ↝⋆ N
            N′↝⋆N = N′↝N ◅ ε

            ffN′ : ForgingFree N′
            ffN′ = ForgingFreePrev N′↝⋆N ffN

            cfN′ : CollisionFree N′
            cfN′ = CollisionFreePrev N′↝⋆N cfN

            N₀↝⋆N′ : N₀ ↝⋆ N′
            N₀↝⋆N′ = Starʳ⇒Star N₀↝⋆ʳN′

            hbhPres : honestBlockHistory N′ ≡ˢ honestBlockHistory N
            hbhPres = honestBlockHistoryPreservation-↓∗ N₀↝⋆N′ N′—[eoN′]↓→∗N″ ffN N′Ready

            goal : ∀ {b} → b ∈ honestBlockHistory N → chainFromBlock b (blockHistory N) ⊆ˢ allBlocks (honestTree N)
            goal {b} b∈hbhN = begin
              chainFromBlock b (blockHistory N)  ≡⟨ cfbHbhPres N₀↝⋆N′ N′↝N ffN cfN b∈hbhN hbhPres ⟨
              chainFromBlock b (blockHistory N′) ⊆⟨ L.All.lookup ih b∈hbhN′ ⟩
              allBlocks (honestTree N′)          ⊆⟨ honestGlobalTreeBlocksMonotonicity N₀↝⋆N′ N′↝N ⟩
              allBlocks (honestTree N)           ∎
              where
                open L.SubS.⊆-Reasoning Block

                b∈hbhN′ : b ∈ honestBlockHistory N′
                b∈hbhN′ = ≡ˢ⇒⊆×⊇ hbhPres .proj₂ b∈hbhN

        ... | makeBlock {N′} {N″} N′MsgsDelivered N′—[eoN′]↑→∗N″ = L.All.tabulate goal
          where
            N₀↝⋆N : N₀ ↝⋆ N
            N₀↝⋆N = Starʳ⇒Star N₀↝⋆ʳN

            N′↝⋆N : N′ ↝⋆ N
            N′↝⋆N = N′↝N ◅ ε

            N₀↝⋆N′ : N₀ ↝⋆ N′
            N₀↝⋆N′ = Starʳ⇒Star N₀↝⋆ʳN′

            ffN′ : ForgingFree N′
            ffN′ = ForgingFreePrev (N′↝N ◅ ε) ffN

            N″↷↑N″[bM] : N″ ↷↑ record N″ { progress = blockMade }
            N″↷↑N″[bM] = progress↑ ↷↑-refl

            ih′ : ∀ {b} → b ∈ honestBlockHistory N′ → chainFromBlock b (blockHistory N′) ⊆ˢ allBlocks (honestTree N′)
            ih′ = L.All.lookup ih

            uniqEoN′ : Unique (N′ .execOrder)
            uniqEoN′ = execOrderUniqueness N₀↝⋆N′

            goal : ∀ {b} → b ∈ honestBlockHistory N → chainFromBlock b (blockHistory N) ⊆ˢ allBlocks (honestTree N)
            goal {b} b∈hbhN = goal* (N′ .execOrder) N″↷↑N″[bM] cfN b∈hbhN uniqEoN′ (—[]→∗⇒—[]→∗ʳ N′—[eoN′]↑→∗N″)
              where
                goal* : ∀ {N*} ps →
                    N* ↷↑ N
                  → CollisionFree N*
                  → b ∈ honestBlockHistory N*
                  → Unique ps
                  → _ ⊢ N′ —[ ps ]↑→∗ʳ N*
                  → chainFromBlock b (blockHistory N*) ⊆ˢ allBlocks (honestTree N*)
                goal* {N*} [] _ _ b∈hbhN* _ [] = ih′ b∈hbhN*
                goal* {N*} [] _ _ _ _ (_∷ʳ_ {eq = eq} _ _) = contradiction eq []≢∷ʳ
                goal* {N*} (p ∷ ps) prfN cfN* b∈hbhN* p∷psUniq (_∷ʳ_ {is = ps′} {i = p′} {s′ = N‴} {eq = eq} ts⋆ ts) = step ts
                  where
                    cfN‴ : CollisionFree N‴
                    cfN‴ = CollisionFreePrev-↑ ts cfN*

                    ps′∷ʳp′Uniq : Unique (ps′ L.∷ʳ p′)
                    ps′∷ʳp′Uniq = subst Unique eq p∷psUniq

                    p′∉ps′ : p′ ∉ ps′
                    p′∉ps′ = Unique[xs∷ʳx]⇒x∉xs ps′∷ʳp′Uniq

                    ps′Uniq : Unique ps′
                    ps′Uniq = headʳ ps′∷ʳp′Uniq

                    ih* : b ∈ honestBlockHistory N‴ → chainFromBlock b (blockHistory N‴) ⊆ˢ allBlocks (honestTree N‴)
                    ih* b∈hbhN‴ = goal* {N‴} ps′ (blockMaking↑ ts prfN) cfN‴ b∈hbhN‴ ps′Uniq ts⋆

                    step : _ ⊢ N‴ —[ p′ ]↑→ N* → chainFromBlock b (blockHistory N*) ⊆ˢ allBlocks (honestTree N*)
                    step (unknownParty↑ _) = ih* b∈hbhN*
                    step (honestParty↑ {ls = ls} lsπ hp′π) with Params.winnerᵈ params {p′} {N‴ .clock}
                    ... | ⁇ (yes isWinner) rewrite lsπ = step′
                      where
                        lsN′ : N′ .states ⁉ p′ ≡ just ls
                        lsN′ rewrite sym $ localStatePreservation-∉-↑∗ p′∉ps′ (—[]→∗ʳ⇒—[]→∗ ts⋆) = lsπ

                        best : Chain
                        best = bestChain (N‴ .clock ∸ 1) (ls .tree)

                        nb : Block
                        nb = mkBlock (hash (tip best)) (N‴ .clock) (txSelection (N‴ .clock) p′) p′

                        b∈nb+hbhN‴ : b ∈ nb ∷ honestBlockHistory N‴
                        b∈nb+hbhN‴ rewrite hp′π = b∈hbhN*

                        N‴⁺ : GlobalState
                        N‴⁺ = updateLocalState p′ (addBlock ls nb) N‴

                        tnb : Tree
                        tnb = extendTree (ls .tree) nb

                        blocksN‴⁺≡p′ : blocks N‴⁺ p′ ≡ allBlocks tnb
                        blocksN‴⁺≡p′ rewrite set-⁉ (N‴ .states) p′ (addBlock ls nb) = refl

                        blocksN‴⁺≢p′ : ∀ {p°} → p° ≢ p′ → blocks N‴ p° ≡ blocks N‴⁺ p°
                        blocksN‴⁺≢p′ {p°} p°≢p′ rewrite lsπ | set-⁉-¬ (N‴ .states) p′ p° (addBlock ls nb) (≢-sym p°≢p′) = refl

                        step′ : chainFromBlock b (nb ∷ blockHistory N‴) ⊆ˢ allBlocks (honestTree N‴⁺)
                        step′
                          with ∈-∷⁻ b∈nb+hbhN‴ | b ≟ nb
                        ... | inj₁ b≡nb            | no b≢nb  = contradiction b≡nb b≢nb
                        ... | inj₂ b∈hbhN‴         | no _     =
                          let open L.SubS.⊆-Reasoning Block in begin
                            chainFromBlock b (nb ∷ blockHistory N‴)  ≡⟨ cfbbhN‴≡cfb[nb+bhN‴] ⟨
                            chainFromBlock b (blockHistory N‴)       ⊆⟨ ih* b∈hbhN‴ ⟩
                            allBlocks (honestTree N‴)                ⊆⟨ step″ {N‴ .execOrder} ⟩
                            allBlocks (honestTree N‴⁺)               ∎
                          where
                            cfbbhN‴≡cfb[nb+bhN‴] : chainFromBlock b (blockHistory N‴) ≡ chainFromBlock b (nb ∷ blockHistory N‴)
                            cfbbhN‴≡cfb[nb+bhN‴] = subsetCfbPreservation blcf[nb+bhN‴] bhN‴⊆nb+bhN‴ cfbhN‴≢[]
                              where
                                bhN‴⊆nb+bhN‴ : blockHistory N‴ ⊆ˢ nb ∷ blockHistory N‴
                                bhN‴⊆nb+bhN‴  = L.SubS.xs⊆x∷xs _ _

                                blcf[nb+bhN‴] : BlockListCollisionFree (nb ∷ blockHistory N‴)
                                blcf[nb+bhN‴] = BlockListCollisionFree-∷ {nb ∷ blockHistory N‴} {genesisBlock} cfN*

                                cfbhN‴≢[] : chainFromBlock b (blockHistory N‴) ≢ []
                                cfbhN‴≢[] = ✓⇒≢[] cfbhN‴✓
                                  where
                                    cfbhN‴✓ : chainFromBlock b (blockHistory N‴) ✓
                                    cfbhN‴✓ = L.All.lookup
                                      (honestBlockCfb✓-↑∗
                                        N₀↝⋆N′ N′↝⋆N ffN (—[]→∗ʳ⇒—[]→∗ ts⋆) (blockMaking↑ ts prfN) ps′Uniq cfN‴)
                                      b∈hbhN‴

                            open import Function.Reasoning

                            step″ : ∀ {ps°} →
                              allBlocks (honestTree record N‴ {execOrder = ps°})
                              ⊆ˢ
                              allBlocks (honestTree record N‴⁺ {execOrder = ps°})
                            step″ {[]} = L.SubS.⊆-refl
                            step″ {p° ∷ ps°} with honestyOf p° in hp°
                            ... | corrupt = step″ {ps°}
                            ... | honest rewrite hp° with p° ≟ p′
                            ... |  yes p°≡p′
                              rewrite
                                p°≡p′
                              | localStatePreservation-∉-↑∗ p′∉ps′ (—[]→∗ʳ⇒—[]→∗ ts⋆)
                              | lsN′
                              | blocksN‴⁺≡p′ =
                              let open L.SubS.⊆-Reasoning Block in begin
                                allBlocks (buildTree (allBlocks (ls .tree)
                                ++
                                (L.concatMap (blocks N‴) $ L.filter ¿ Honest ¿¹ ps°)))
                                  ⊆⟨ ≡ˢ⇒⊆×⊇ (allBlocksBuildTree-++ (allBlocks (ls .tree)) _) .proj₁ ⟩
                                allBlocks (buildTree (allBlocks (ls .tree)))
                                ++
                                allBlocks (buildTree (L.concatMap (blocks N‴) $ L.filter ¿ Honest ¿¹ ps°))
                                  ⊆⟨ L.SubS.++⁺ bks[tls]⊆bks[tnb] (step″ {ps°}) ⟩
                                allBlocks (buildTree (allBlocks tnb))
                                ++
                                allBlocks (buildTree (L.concatMap (blocks N‴⁺) $ L.filter ¿ Honest ¿¹ ps°))
                                  ≡⟨ cong (λ ◆ →
                                       allBlocks (buildTree ◆)
                                       ++
                                       allBlocks (buildTree (L.concatMap (blocks N‴⁺) $ L.filter ¿ Honest ¿¹ ps°)))
                                       (sym blocksN‴⁺≡p′) ⟩
                                allBlocks (buildTree (blocks N‴⁺ p′))
                                ++
                                allBlocks (buildTree (L.concatMap (blocks N‴⁺) $ L.filter ¿ Honest ¿¹ ps°))
                                  ⊆⟨ ≡ˢ⇒⊆×⊇ (allBlocksBuildTree-++ (blocks N‴⁺ p′) _) .proj₂ ⟩
                                allBlocks (buildTree (blocks N‴⁺ p′ ++ (L.concatMap (blocks N‴⁺) $ L.filter ¿ Honest ¿¹ ps°)))
                                ∎
                                where
                                  bks[tls]⊆bks[tnb] :
                                    allBlocks (buildTree (allBlocks (tree ls)))
                                    ⊆ˢ
                                    allBlocks (buildTree (allBlocks tnb))
                                  bks[tls]⊆bks[tnb] = let open L.SubS.⊆-Reasoning Block in begin
                                    allBlocks (buildTree (allBlocks (tree ls))) ⊆⟨ ≡ˢ⇒⊆×⊇ (buildTreeUsesAllBlocks _) .proj₁ ⟩
                                    genesisBlock ∷ allBlocks (ls .tree)         ⊆⟨ L.SubS.∷⁺ʳ _ $
                                      begin
                                        allBlocks (ls .tree)                    ⊆⟨ L.SubS.xs⊆xs++ys _ _ ⟩
                                        allBlocks (ls .tree) ++ [ nb ]          ⊆⟨ ≡ˢ⇒⊆×⊇ (extendable _ _) .proj₂ ⟩
                                        allBlocks tnb                           ∎
                                                                                 ⟩
                                    genesisBlock ∷ allBlocks tnb                ⊆⟨ ≡ˢ⇒⊆×⊇ (buildTreeUsesAllBlocks _) .proj₂ ⟩
                                    allBlocks (buildTree (allBlocks tnb))       ∎
                            ... |  no p°≢p′ = let open L.SubS.⊆-Reasoning Block in begin
                                allBlocks (buildTree (blocks N‴ p° ++ (L.concatMap (blocks N‴) $ L.filter ¿ Honest ¿¹ ps°)))
                                  ⊆⟨ ≡ˢ⇒⊆×⊇ (allBlocksBuildTree-++ (blocks N‴ p°) _) .proj₁ ⟩
                                allBlocks (buildTree (blocks N‴ p°))
                                ++
                                allBlocks (buildTree (L.concatMap (blocks N‴) $ L.filter ¿ Honest ¿¹ ps°))
                                  ⊆⟨ L.SubS.++⁺
                                      (L.SubS.⊆-reflexive $ cong (allBlocks ∘ buildTree) $ blocksN‴⁺≢p′ p°≢p′)
                                      (step″ {ps°})
                                   ⟩
                                allBlocks (buildTree (blocks N‴⁺ p°))
                                ++
                                allBlocks (buildTree (L.concatMap (blocks N‴⁺) $ L.filter ¿ Honest ¿¹ ps°))
                                  ⊆⟨ ≡ˢ⇒⊆×⊇ (allBlocksBuildTree-++ (blocks N‴⁺ p°) _) .proj₂ ⟩
                                allBlocks (buildTree (blocks N‴⁺ p° ++ (L.concatMap (blocks N‴⁺) $ L.filter ¿ Honest ¿¹ ps°)))
                                ∎
                        ... | _                    | yes b≡nb rewrite b≡nb
                               with chainFromNewBlock N₀↝⋆N′ ts⋆ isWinner p′∉ps′ lsπ hp′π cfN*
                        ... |    cfb≡nb∷best , _ rewrite cfb≡nb∷best = step″ p′∈eoN‴
                          where
                            p′∈eoN‴ : p′ ∈ N‴ .execOrder
                            p′∈eoN‴ = Any-resp-↭
                              (execOrderPreservation-↭-↑∗ (—[]→∗ʳ⇒—[]→∗ ts⋆))
                              (hasState⇒∈execOrder N₀↝⋆N′ (≡just⇒Is-just lsN′))

                            step″ : ∀ {ps°} → p′ ∈ ps° → nb ∷ best ⊆ˢ allBlocks (honestTree record N‴⁺ {execOrder = ps°})
                            step″ {p° ∷ ps°} p′∈p°∷ps° with ∈-∷⁻ p′∈p°∷ps°
                            ... | inj₁ p′≡p° rewrite sym p′≡p° | hp′π = let open L.SubS.⊆-Reasoning Block in begin
                              nb ∷ best
                                ⊆⟨ ( λ {b°} b°∈nb+best →
                                   b°∈bks[tnb] b°∈nb+best ∶
                                b° ∈ allBlocks tnb
                                  |> inj₁ ∶
                                b° ∈ allBlocks tnb ⊎ b° ∈ (L.concatMap (blocks N‴⁺) $ L.filter ¿ Honest ¿¹ ps°)
                                  |> L.Mem.++-∈⇔ {xs = allBlocks tnb} .Equivalence.from ∶
                                b° ∈ allBlocks tnb ++ (L.concatMap (blocks N‴⁺) $ L.filter ¿ Honest ¿¹ ps°)
                                  |> inj₂ ∶
                                b° ∈ [ genesisBlock ]
                                ⊎
                                b° ∈ allBlocks tnb ++ (L.concatMap (blocks N‴⁺) $ L.filter ¿ Honest ¿¹ ps°)
                                  |> L.Mem.++-∈⇔ {xs = [ genesisBlock ]} .Equivalence.from ∶
                                b° ∈ genesisBlock ∷ (allBlocks tnb ++ (L.concatMap (blocks N‴⁺) $ L.filter ¿ Honest ¿¹ ps°)) )
                                 ⟩
                              genesisBlock ∷ (allBlocks tnb ++ (L.concatMap (blocks N‴⁺) $ L.filter ¿ Honest ¿¹ ps°))
                                ≡⟨ cong
                                    (λ ◆ → genesisBlock ∷ (◆ ++ (L.concatMap (blocks N‴⁺) $ L.filter ¿ Honest ¿¹ ps°)))
                                    (sym blocksN‴⁺≡p′)
                                 ⟩
                              genesisBlock ∷ (blocks N‴⁺ p′ ++ (L.concatMap (blocks N‴⁺) $ L.filter ¿ Honest ¿¹ ps°))
                                ⊆⟨ ≡ˢ⇒⊆×⊇ (buildTreeUsesAllBlocks _) .proj₂ ⟩
                              allBlocks (buildTree (blocks N‴⁺ p′ ++ (L.concatMap (blocks N‴⁺) $ L.filter ¿ Honest ¿¹ ps°)))
                              ∎
                              where
                                open import Function.Reasoning

                                b°∈bks[tnb] : ∀ {b°} → b° ∈ nb ∷ best → b° ∈ allBlocks tnb
                                b°∈bks[tnb] {b°} b°∈nb+best =
                                    (case ∈-∷⁻ b°∈nb+best of λ where
                                      (inj₁ b°≡nb)   → inj₂ $ subst (_∈ [ nb ]) (sym b°≡nb) (here refl)
                                      (inj₂ b°∈best) → inj₁ $
                                          b°∈best ∶
                                        b° ∈ best
                                          |> selfContained (ls .tree) (N‴ .clock ∸ 1) ∶
                                        b° ∈ filter ((_≤? N‴ .clock ∸ 1) ∘ slot) (allBlocks (ls .tree))
                                          |> L.SubS.filter-⊆ _ _ ∶
                                        b° ∈ allBlocks (ls .tree))
                                    ∶
                                  b° ∈ allBlocks (ls .tree) ⊎ b° ∈ [ nb ]
                                    |> L.Mem.++-∈⇔ .Equivalence.from ∶
                                  b° ∈ allBlocks (ls .tree) ++ [ nb ]
                                    |> ≡ˢ⇒⊆×⊇ (extendable _ _) .proj₂ ∶
                                  b° ∈ allBlocks tnb
                            ... | inj₂ p′∈ps° = let open L.SubS.⊆-Reasoning Block in begin
                              nb ∷ best
                                ⊆⟨ step″ {ps°} p′∈ps° ⟩
                              allBlocks (honestTree record N‴⁺ {execOrder = ps°})
                                ⊆⟨ bks[ps°]⊆bks[p°+ps°] ⟩
                              allBlocks (honestTree record N‴⁺ {execOrder = p° ∷ ps°})
                              ∎
                              where
                                open import Function.Reasoning

                                bks[ps°]⊆bks[p°+ps°] :
                                  allBlocks (honestTree record N‴⁺ {execOrder = ps°})
                                  ⊆ˢ
                                  allBlocks (honestTree record N‴⁺ {execOrder = p° ∷ ps°})
                                bks[ps°]⊆bks[p°+ps°] with honestyOf p°
                                ... | corrupt = L.SubS.⊆-refl
                                ... | honest = let open L.SubS.⊆-Reasoning Block in begin
                                  allBlocks (honestTree record N‴⁺ {execOrder = ps°})
                                    ⊆⟨ ≡ˢ⇒⊆×⊇ (buildTreeUsesAllBlocks _) .proj₁ ⟩
                                  genesisBlock ∷ (L.concatMap (blocks N‴⁺) $ L.filter ¿ Honest ¿¹ ps°)
                                    ⊆⟨ ( λ {b⁺} b⁺∈gb+bks[ps°] →
                                         b⁺∈gb+bks[ps°] ∶
                                       b⁺ ∈ genesisBlock ∷ (L.concatMap (blocks N‴⁺) $ L.filter ¿ Honest ¿¹ ps°)
                                         |> ≡ˢ⇒⊆×⊇ (buildTreeUsesAllBlocks _) .proj₂ ∶
                                       b⁺ ∈ allBlocks (honestTree record N‴⁺ {execOrder = ps°})
                                         |> inj₂ ∶
                                       b⁺ ∈ allBlocks (buildTree (blocks N‴⁺ p°))
                                       ⊎
                                       b⁺ ∈ allBlocks (honestTree record N‴⁺ {execOrder = ps°})
                                         |> L.Mem.++-∈⇔ {xs = allBlocks (buildTree (blocks N‴⁺ p°))} .Equivalence.from ∶
                                       b⁺ ∈ allBlocks (buildTree (blocks N‴⁺ p°))
                                            ++
                                            allBlocks (honestTree record N‴⁺ {execOrder = ps°})
                                       )
                                     ⟩
                                  allBlocks (buildTree (blocks N‴⁺ p°))
                                  ++
                                  allBlocks (honestTree record N‴⁺ {execOrder = ps°})
                                    ⊆⟨ ≡ˢ⇒⊆×⊇ (allBlocksBuildTree-++ (blocks N‴⁺ p°) _) .proj₂ ⟩
                                  allBlocks (buildTree (blocks N‴⁺ p° ++ _))
                                  ∎
                    ... | ⁇ (no ¬isWinner) = let open L.SubS.⊆-Reasoning Block in begin
                      chainFromBlock b (blockHistory N‴)                 ⊆⟨ ih* b∈hbhN* ⟩
                      allBlocks (honestTree N‴)                          ⊆⟨ step″ {N‴ .execOrder} ⟩
                      allBlocks (honestTree N‴⁺)                         ∎
                      where
                        N‴⁺ : GlobalState
                        N‴⁺ = updateLocalState p′ ls N‴

                        step″ : ∀ {ps°} →
                          allBlocks (honestTree record N‴ {execOrder = ps°})
                          ⊆ˢ
                          allBlocks (honestTree record N‴⁺ {execOrder = ps°})
                        step″ {[]} = L.SubS.⊆-refl
                        step″ {p° ∷ ps°} with honestyOf p° in hp°
                        ... | corrupt rewrite eq = step″ {ps°}
                        ... | honest rewrite hp° = let open L.SubS.⊆-Reasoning Block in begin
                          allBlocks (buildTree (blocks N‴ p° ++ (L.concatMap (blocks N‴) $ L.filter ¿ Honest ¿¹ ps°)))
                            ⊆⟨ ≡ˢ⇒⊆×⊇ (allBlocksBuildTree-++ (blocks N‴ p°) _) .proj₁ ⟩
                          allBlocks (buildTree (blocks N‴ p°))
                          ++
                          allBlocks (honestTree record N‴ {execOrder = ps°})
                            ≡⟨ cong (λ ◆ →
                              allBlocks (buildTree ◆)
                              ++
                              allBlocks (honestTree record N‴ {execOrder = ps°})) (sym eqBlocks)
                             ⟩
                          allBlocks (buildTree (blocks N‴⁺ p°))
                          ++
                          allBlocks (honestTree record N‴ {execOrder = ps°})
                            ⊆⟨ L.SubS.++⁺ʳ _ (step″ {ps°}) ⟩
                          allBlocks (buildTree (blocks N‴⁺ p°))
                          ++
                          allBlocks (honestTree record N‴⁺ {execOrder = ps°})
                            ⊆⟨ ≡ˢ⇒⊆×⊇ (allBlocksBuildTree-++ (blocks N‴⁺ p°) _) .proj₂ ⟩
                          allBlocks (buildTree (blocks N‴⁺ p° ++ _))
                          ∎
                          where
                            eqBlocks : blocks N‴⁺ p° ≡ blocks N‴ p°
                            eqBlocks with p° ≟ p′
                            ... | yes eq rewrite eq | lsπ | set-⁉   (N‴ .states) p′    ls             = refl
                            ... | no neq rewrite      lsπ | set-⁉-¬ (N‴ .states) p′ p° ls (≢-sym neq) = refl

                    step (corruptParty↑ _ _) = step′
                      where
                        mds : List (Message × DelayMap)
                        mds = makeBlockᶜ (N‴ .clock) (N‴ .history) (N‴ .messages) (N‴ .advState).proj₁

                        sub : L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                        sub = ffN .proj₂ (blockMaking↑ ts prfN)

                        hbhPres : honestBlockHistory N‴ ≡ˢ honestBlockHistory (broadcastMsgsᶜ mds N‴)
                        hbhPres = honestBlockHistoryPreservation-broadcastMsgsᶜ {N‴} {mds} sub

                        b∈hbhN‴ : b ∈ honestBlockHistory N‴
                        b∈hbhN‴ = ≡ˢ⇒⊆×⊇ hbhPres .proj₂ b∈hbhN*

                        step′ :
                          chainFromBlock b (blockHistory (broadcastMsgsᶜ mds N‴))
                          ⊆ˢ
                          allBlocks (honestTree (broadcastMsgsᶜ mds N‴))
                        step′ = begin
                          chainFromBlock b (blockHistory (broadcastMsgsᶜ mds N‴)) ≡⟨ cfbhN‴≡cfbhBcN‴ ⟨
                          chainFromBlock b (blockHistory N‴)                      ⊆⟨ ih* b∈hbhN‴ ⟩
                          allBlocks (honestTree N‴)                               ⊆⟨ step″ ⟩
                          allBlocks (honestTree (broadcastMsgsᶜ mds N‴))          ∎
                          where
                            open L.SubS.⊆-Reasoning Block

                            cfbhN‴≡cfbhBcN‴ :
                              chainFromBlock b (blockHistory N‴)
                              ≡
                              chainFromBlock b (blockHistory (broadcastMsgsᶜ mds N‴))
                            cfbhN‴≡cfbhBcN‴ = subsetCfbPreservation blcfbhBcN‴ bhN‴⊆bhBcN‴ cfbhN‴≢[]
                              where
                                blcfbhBcN‴ : BlockListCollisionFree (blockHistory (broadcastMsgsᶜ mds N‴))
                                blcfbhBcN‴ = BlockListCollisionFree-∷ {blockHistory (broadcastMsgsᶜ mds N‴)} {genesisBlock} cfN*

                                bhN‴⊆bhBcN‴ : blockHistory N‴ ⊆ˢ blockHistory (broadcastMsgsᶜ mds N‴)
                                bhN‴⊆bhBcN‴ = blockHistoryPreservation-broadcastMsgsᶜ mds N‴

                                cfbhN‴≢[] : chainFromBlock b (blockHistory N‴) ≢ []
                                cfbhN‴≢[] = ✓⇒≢[] cfbhN‴✓
                                  where
                                    cfbhN‴✓ : chainFromBlock b (blockHistory N‴) ✓
                                    cfbhN‴✓ = L.All.lookup
                                      (honestBlockCfb✓-↑∗
                                        N₀↝⋆N′ N′↝⋆N ffN (—[]→∗ʳ⇒—[]→∗ ts⋆) (blockMaking↑ ts prfN) ps′Uniq cfN‴)
                                      b∈hbhN‴

                            step″ : allBlocks (honestTree N‴) ⊆ˢ allBlocks (honestTree (broadcastMsgsᶜ mds N‴))
                            step″
                              rewrite
                                localStatePreservation-broadcastMsgsᶜ {N‴} {mds}
                              | sym $ execOrderPreservation-≡-broadcastMsgsᶜ mds N‴
                              = L.SubS.⊆-refl

        ... | advanceRound   _            = ih
        ... | permuteMsgs    _            = ih
        ... | permuteParties {N′} {ps} _  = L.All.map [cfb⊆htN′]⋐[htN′⊆htN′ps] ih
          where
            open import Relation.Unary renaming (_⊆_ to _⋐_)

            [cfb⊆htN′]⋐[htN′⊆htN′ps] :
              (λ b → chainFromBlock b (blockHistory N′) ⊆ˢ allBlocks (honestTree N′))
              ⋐
              (λ b → chainFromBlock b (blockHistory N′) ⊆ˢ allBlocks (honestTree record N′ {execOrder = ps}))
            [cfb⊆htN′]⋐[htN′⊆htN′ps] {b} cfb⊆htN′ = L.SubS.⊆-trans cfb⊆htN′ htN′⊆htN′ps
              where
                htN′⊆htN′ps : allBlocks (honestTree N′) ⊆ˢ allBlocks (honestTree record N′ {execOrder = ps})
                htN′⊆htN′ps = ≡ˢ⇒⊆×⊇ (honestGlobalTreeBlocksPreservation (N′↝N ◅ ε) refl refl refl) .proj₁
