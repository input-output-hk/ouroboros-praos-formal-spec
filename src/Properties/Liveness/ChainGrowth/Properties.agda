{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled

open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Liveness.ChainGrowth.Properties
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot; Honesty)
open import Protocol.Crypto ⦃ params ⦄ using (Hashable); open Hashable ⦃ ... ⦄
open import Protocol.Block ⦃ params ⦄
open import Protocol.Chain ⦃ params ⦄
open import Protocol.Tree ⦃ params ⦄
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Protocol.Tree.Properties ⦃ params ⦄ ⦃ assumptions ⦄
open import Protocol.Chain.Properties ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.SuperBlocks ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.Time ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.Trees ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.LocalState ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.ExecutionOrder ⦃ params ⦄ ⦃ assumptions ⦄
open import Prelude.AssocList.Properties.Ext using (set-⁉)
open import Data.List.Ext using (ι)
open import Data.List.Properties.Ext using (∈-ι⁺; ι-++; ∈-ι⁻; length0⇒[]; head-++)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties.Ext using (filter-↭)
open import Data.Nat.Properties.Ext using (suc≗+1; ∸-suc; n>0⇒pred[n]<n; 0<n∸m⇒m<n)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Ext using (Starʳ)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.Ext using (Star⇒Starʳ; Starʳ⇒Star)
open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_; ≡ˢ⇒⊇; ≡ˢ⇒⊆; filter-cong)
open import Data.List.Relation.Binary.Permutation.Propositional using (↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∈-resp-↭; map⁺)
open import Function.Bundles using (Equivalence; Inverse)
open import Function.Related.Propositional as Related
open import Data.List.Relation.Binary.BagAndSetEquality using (∷-cong; concat-cong; map-cong; bag-=⇒; ↭⇒∼bag)

firstLuckySlotIsLucky : ∀ {N N′ : GlobalState} {sl : Slot} →
    head (luckySlotsInRange (N .clock) (N′ .clock)) ≡ just sl
  → LuckySlot sl
firstLuckySlotIsLucky = {!!}

firstLuckySlotBetweenStates : ∀ {N N′ : GlobalState} {sl : Slot} →
    head (luckySlotsInRange (N .clock) (N′ .clock)) ≡ just sl
  → N .clock ≤ sl × sl < N′ .clock
firstLuckySlotBetweenStates {N} {N′} {sl} hd[ls[N:N′]]≡sl =
  case ∈-ι⁻ sl∈[N:N′] of λ where
    (Nₜ≤sl , sl<Nₜ+N′ₜ∸Nₜ) → Nₜ≤sl , subst (sl <_) (Nat.m+[n∸m]≡n $ Nat.<⇒≤ Nₜ<N′ₜ) sl<Nₜ+N′ₜ∸Nₜ
  where
    sl∈[N:N′] : sl ∈ ι (N .clock) (N′ .clock ∸ N .clock)
    sl∈[N:N′] = sl∈ss* hd[ls[N:N′]]≡sl
      where
        sl∈ss* : ∀ {ss*} → head (filter ¿ LuckySlot ¿¹ ss*) ≡ just sl → sl ∈ ss*
        sl∈ss* {sl′ ∷ ss*} p with ¿ LuckySlot sl′ ¿
        ... | yes lsl′ rewrite M.just-injective p = here refl
        ... | no ¬lsl′ = L.Mem.∈-++⁺ʳ _ $ sl∈ss* {ss*} p

    Nₜ<N′ₜ : N .clock < N′ .clock
    Nₜ<N′ₜ = 0<n∸m⇒m<n (|ι|>0 (N′ .clock ∸ N .clock) hd[ls[N:N′]]≡sl)
      where
        |ι|>0 : ∀ sl′ → head (filter ¿ LuckySlot ¿¹ $ ι (N .clock) sl′) ≡ just sl → 0 < sl′
        |ι|>0 0         = λ ()
        |ι|>0 (suc _) _ = Nat.s≤s Nat.z≤n

∃FirstLuckySlotBetweenStates : ∀ {N N′ : GlobalState} →
    N₀ ↝⋆ N
  → N ↝⋆ N′
  → 1 ≤ length (luckySlotsInRange (N .clock) (N′ .clock))
  → ∃[ sl ] head (luckySlotsInRange (N .clock) (N′ .clock)) ≡ just sl
∃FirstLuckySlotBetweenStates {N} {N′} N₀↝⋆N N↝⋆N′ 1≤|ls[N:N′]| = ∃FirstLuckySlotBetweenStatesʳ (Star⇒Starʳ N↝⋆N′) 1≤|ls[N:N′]|
  where
    open RTC; open Starʳ
    ∃FirstLuckySlotBetweenStatesʳ : ∀ {N′ : GlobalState} →
        N ↝⋆ʳ N′
      → 1 ≤ length (luckySlotsInRange (N .clock) (N′ .clock))
      → ∃[ sl ] head (luckySlotsInRange (N .clock) (N′ .clock)) ≡ just sl
    ∃FirstLuckySlotBetweenStatesʳ εʳ 1≤|ls[N:N]| = contradiction |ls[N:N]|=0 (Nat.n>0⇒n≢0 1≤|ls[N:N]|)
      where
        |ls[N:N]|=0 : length (luckySlotsInRange (N .clock) (N .clock)) ≡ 0
        |ls[N:N]|=0 rewrite Nat.n∸n≡0 (N .clock) = refl
    ∃FirstLuckySlotBetweenStatesʳ {N′} (_◅ʳ_ {j = N″} N↝⋆ʳN″ N″↝N′) 1≤|ls[N:N′]| = goal N″↝N′ 1≤|ls[N:N′]|
      where
        ih :
            1 ≤ length (luckySlotsInRange (N .clock) (N″ .clock))
          → ∃[ sl ] head (luckySlotsInRange (N .clock) (N″ .clock)) ≡ just sl
        ih = ∃FirstLuckySlotBetweenStatesʳ N↝⋆ʳN″

        N″ₜ-Nₜ-eq : suc (N″ .clock) ∸ (N .clock) ≡ (N″ .clock ∸ N .clock) + 1
        N″ₜ-Nₜ-eq rewrite Nat.+-comm (N″ .clock ∸ N .clock) 1 = ∸-suc (clockMonotonicity (Starʳ⇒Star N↝⋆ʳN″))

        goal : ∀ {N′} →
            N″ ↝ N′
          → 1 ≤ length (luckySlotsInRange (N .clock) (N′ .clock))
          → ∃[ sl ] head (luckySlotsInRange (N .clock) (N′ .clock)) ≡ just sl
        goal (deliverMsgs {N′ = N°} _ N″—[eoN″]↓→∗N°) 1≤|ls[N:N°]| rewrite clockPreservation-↓∗ N″—[eoN″]↓→∗N° = ih 1≤|ls[N:N°]|
        goal (makeBlock   {N′ = N°} _ N″—[eoN″]↑→∗N°) 1≤|ls[N:N°]| rewrite clockPreservation-↑∗ N″—[eoN″]↑→∗N° = ih 1≤|ls[N:N°]|
        goal (advanceRound   _) 1≤|ls[N:N″+1]|
          rewrite
            N″ₜ-Nₜ-eq
          | ι-++ (N .clock) (N″ .clock ∸ N .clock) 1
          | L.filter-++ ¿ LuckySlot ¿¹ (ι (N .clock) (N″ .clock ∸ N .clock)) [ N .clock + (N″ .clock ∸ N .clock) ]
          | Nat.m+[n∸m]≡n $ clockMonotonicity (Starʳ⇒Star N↝⋆ʳN″)
          | L.length-++ (luckySlotsInRange (N .clock) (N″ .clock)) {ys = filter ¿ LuckySlot ¿¹ [ N″ .clock ]}
          = goal′
          where
            goal′ : ∃[ sl ] head (luckySlotsInRange (N .clock) (N″ .clock) ++ filter ¿ LuckySlot ¿¹ [ N″ .clock ]) ≡ just sl
            goal′ with length (luckySlotsInRange (N .clock) (N″ .clock)) in eq
            ... | |ls[N:N″]|@(suc _) = case ih 1≤|ls[N:N″]| of λ where
              (sl* , π) → sl* , head-++ π
                where
                  1≤|ls[N:N″]| : 1 ≤ length (luckySlotsInRange (N .clock) (N″ .clock))
                  1≤|ls[N:N″]| rewrite eq = Nat.s≤s Nat.z≤n
            ... | 0 with ¿ LuckySlot (N″ .clock) ¿
            ...   | no ¬lN″ₜ = contradiction 1≤|ls[N:N″+1]| λ ()
            ...   | yes lN″ₜ
                      rewrite
                        L.filter-accept ¿ LuckySlot ¿¹ {N″ .clock} {[]} lN″ₜ
                      | length0⇒[] {xs = luckySlotsInRange (N .clock) (N″ .clock)} eq
                      = N″ .clock , refl
        goal (permuteParties _) 1≤|ls[N:N′]| = ih 1≤|ls[N:N′]|
        goal (permuteMsgs    _) 1≤|ls[N:N′]| = ih 1≤|ls[N:N′]|

execOrderPreservesHonestChainLength : ∀ {N : GlobalState} {ps : List Party} (sl : Slot) →
    N .execOrder ↭ ps
  → length (bestChain sl (honestTree record N { execOrder = ps })) ≡ length (bestChain sl (honestTree N))
execOrderPreservesHonestChainLength {N} {ps} sl eoN↭ps = Nat.≤-antisym |bc′|≤|bc| |bc|≤|bc′|
  where
    N′ : GlobalState
    N′ = record N { execOrder = ps }

    bc bc′ : Chain
    bc  = bestChain sl (honestTree N)
    bc′ = bestChain sl (honestTree N′)

    eq : filter ((_≤? sl) ∘ slot) (allBlocks (honestTree N′))
         ≡ˢ
         filter ((_≤? sl) ∘ slot) (allBlocks (honestTree N))
    eq = filter-cong eq′
      where
         eq′ : allBlocks (honestTree N′) ≡ˢ allBlocks (honestTree N)
         eq′ {b} = let open Related.EquationalReasoning in begin
           b ∈ allBlocks (honestTree N′)                                       ∼⟨ buildTreeUsesAllBlocks _ ⟩
           b ∈ genesisBlock ∷ (L.concatMap (blocks N′) (honestParties N′))
             ∼⟨ ∷-cong refl (λ {b} → begin
                 b ∈ L.concatMap (blocks N′) (honestParties N′)
                   ∼⟨ concat-cong (λ {b} → begin
                      b ∈ (L.map (blocks N′) (honestParties N′))
                        ∼⟨ bag-=⇒ $ ↭⇒∼bag $ map⁺ _ $ filter-↭ _ (↭-sym eoN↭ps) ⟩
                      b ∈ (L.map (blocks N) (honestParties N))
                    ∎
                    ) ⟩
               b ∈ (L.concatMap (blocks N) (honestParties N))
                 ∎
              ) ⟩
           b ∈ genesisBlock ∷ (L.concatMap (blocks N) (honestParties N))       ∼⟨ SK-sym $ buildTreeUsesAllBlocks _ ⟩
           b ∈ allBlocks (honestTree N)                                        ∎

    |bc|≤|bc′| : length bc ≤ length bc′
    |bc|≤|bc′| = optimal bc (honestTree N′) sl (valid (honestTree N) sl) $
                   L.SubS.⊆-trans (selfContained (honestTree N) sl) (≡ˢ⇒⊇ eq)

    |bc′|≤|bc| : length bc′ ≤ length bc
    |bc′|≤|bc| = optimal bc′ (honestTree N) sl (valid (honestTree N′) sl) $
                   L.SubS.⊆-trans (selfContained (honestTree N′) sl) (≡ˢ⇒⊆ eq)

opaque

  unfolding honestBlockMaking

  bestChainGrowth : ∀ {N N′ : GlobalState} {p : Party} {ls ls′ : LocalState} →
      N₀ ↝⋆ N
    → winner p (N .clock)
    → Honest p
    → N .states ⁉ p ≡ just ls
    → _ ⊢ N —[ p ]↑→ N′
    → N′ .states ⁉ p ≡ just ls′
    → length (bestChain (N .clock ∸ 1) (ls .tree)) < length (bestChain (N .clock) (ls′ .tree))
  bestChainGrowth {N = N} {p = p} _ _ _ lspN (unknownParty↑ ls≡◇) _ = contradiction ls≡◇ ls′≢◇
    where
      ls′≢◇ : N .states ⁉ p ≢ nothing
      ls′≢◇ rewrite lspN = flip contradiction λ ()
  bestChainGrowth {N} {N′} {p} {ls} {ls′} N₀↝⋆N wp hp lspN (honestParty↑ {ls = lsₕ} lsₕpN _) lspN′
    rewrite dec-yes ¿ winner p (N .clock) ¿ wp .proj₂ = goal
    where
      bcₕ : Chain
      bcₕ = bestChain (N .clock ∸ 1) (lsₕ .tree)

      nbₕ : Block
      nbₕ = mkBlock (hash (tip bcₕ)) (N .clock) (txSelection (N .clock) p) p

      lsₕ≡ls : lsₕ ≡ ls
      lsₕ≡ls = M.just-injective $ trans (sym lsₕpN) lspN

      goal : length (bestChain (N .clock ∸ 1) (ls .tree)) < length (bestChain (N .clock) (ls′ .tree))
      goal rewrite set-⁉ (N .states) p (addBlock lsₕ nbₕ) | sym $ M.just-injective lspN′ | lsₕ≡ls = |bc|<|bcext|
        where
          bc : Chain
          bc = bestChain (N .clock ∸ 1) (ls .tree)

          nb : Block
          nb = mkBlock (hash (tip bc)) (N .clock) (txSelection (N .clock) p) p

          |bc|<|bcext| : length bc < length (bestChain (N .clock) (extendTree (ls .tree) nb))
          |bc|<|bcext| = Nat.<-≤-trans {j = length (nb ∷ bc)} Nat.≤-refl |nb+bc|≤|bcext|
            where
              |nb+bc|≤|bcext| : length (nb ∷ bc) ≤ length (bestChain (N .clock) (extendTree (ls .tree) nb))
              |nb+bc|≤|bcext| = optimal (nb ∷ bc) (extendTree (ls .tree) nb) (N .clock) [nb+bc]✓ nb+bc⊆[≤Nₜ][bks[ext]]
                where
                  bc✓ : bc ✓
                  bc✓ = valid (ls .tree) (N .clock ∸ 1)

                  bc⊆[≤Nₜ-1][bks] : bc ⊆ˢ filter ((_≤? N .clock ∸ 1) ∘ slot) (allBlocks (ls .tree))
                  bc⊆[≤Nₜ-1][bks] = selfContained (ls .tree) (N .clock ∸ 1)

                  Nₜ-1<Nₜ : N .clock ∸ 1 < N .clock
                  Nₜ-1<Nₜ = n>0⇒pred[n]<n (positiveClock N₀↝⋆N)

                  [nb+bc]✓ : (nb ∷ bc) ✓
                  [nb+bc]✓ with bc in eq
                  ... | [] = contradiction refl (✓⇒≢[] []✓)
                    where
                      []✓ : [] ✓
                      []✓ rewrite sym eq = bc✓
                  ... | b′ ∷ bc′ = ✓-∷ .Equivalence.to (wp , refl , nb>ˢb′ , subst _✓ eq bc✓)
                    where
                      nb>ˢb′ : nb >ˢ b′
                      nb>ˢb′ =
                        Nat.≤-<-trans
                          ((L.Mem.∈-filter⁻ _ {xs = allBlocks (ls .tree)} $ bc⊆[≤Nₜ-1][bks] b′∈bc) .proj₂)
                          Nₜ-1<Nₜ
                        where
                          b′∈bc : b′ ∈ bc
                          b′∈bc = subst (b′ ∈_) (sym eq) (here refl)

                  nb+bc⊆[≤Nₜ][bks[ext]] : nb ∷ bc ⊆ˢ filter ((_≤? N .clock) ∘ slot) (allBlocks (extendTree (ls .tree) nb))
                  nb+bc⊆[≤Nₜ][bks[ext]] {b} (here b≡nb) rewrite b≡nb = L.Mem.∈-filter⁺ _ nb∈bks[ext] Nat.≤-refl
                    where
                      nb∈bks[ext] : nb ∈ allBlocks (extendTree (ls .tree) nb)
                      nb∈bks[ext] = (≡ˢ⇒⊇ $ extendable (ls .tree) nb) (L.Mem.∈-++⁺ʳ _ (here refl))
                  nb+bc⊆[≤Nₜ][bks[ext]] {b} (there b∈bc) = L.Mem.∈-filter⁺ _ b∈bks[ext] bₜ≤Nₜ
                    where
                      bₜ≤Nₜ : b .slot ≤ N .clock
                      bₜ≤Nₜ = Nat.<⇒≤ $ Nat.≤-<-trans
                                (L.All.lookup (bestChainSlotBounded (ls .tree) (N .clock ∸ 1)) b∈bc)
                                Nₜ-1<Nₜ

                      b∈bks[ext] : b ∈ allBlocks (extendTree (ls .tree) nb)
                      b∈bks[ext] = let open L.SubS.⊆-Reasoning Block in (begin
                        bc                                                        ⊆⟨ bc⊆[≤Nₜ-1][bks] ⟩
                        filter ((_≤? N .clock ∸ 1) ∘ slot) (allBlocks (ls .tree)) ⊆⟨ L.SubS.filter-⊆ _ _ ⟩
                        allBlocks (ls .tree)                                      ⊆⟨ L.SubS.xs⊆xs++ys _ _ ⟩
                        allBlocks (ls .tree) ++ [ nb ]                            ⊆⟨ ≡ˢ⇒⊇ $ extendable _ _ ⟩
                        allBlocks (extendTree (ls .tree) nb)                      ∎) b∈bc
  bestChainGrowth _ _ hp _ (corruptParty↑ _ cp) _ = contradiction hp (corrupt⇒¬honest cp)

honestTreeChainGrowthInSameState : ∀ {N N′ : GlobalState} →
    N₀ ↝⋆ N
  → N ↝⋆⟨ 0 ⟩ N′
  → N .progress ≡ ready
  → N′ .progress ≡ blockMade
  → LuckySlot (N .clock)
  → length (bestChain (N .clock ∸ 1) (honestTree N)) < length (bestChain (N′ .clock) (honestTree N′))
honestTreeChainGrowthInSameState {N} {N′} N₀↝⋆N (N↝⋆N′ , Nₜ≡N′ₜ) NReady N′BlockMade lNₜ =
  honestTreeChainGrowthInSameStateʳ (Star⇒Starʳ N↝⋆N′) Nₜ≡N′ₜ NReady N′BlockMade lNₜ
  where
    open RTC; open Starʳ
    honestTreeChainGrowthInSameStateʳ :  ∀ {N′ : GlobalState} →
        N ↝⋆ʳ N′
      → N .clock ≡ N′ .clock
      → N .progress ≡ ready
      → N′ .progress ≡ blockMade
      → LuckySlot (N .clock)
      → length (bestChain (N .clock ∸ 1) (honestTree N)) < length (bestChain (N′ .clock) (honestTree N′))
    honestTreeChainGrowthInSameStateʳ εʳ _ NReady NBlockMade _ = contradiction (trans (sym NReady) NBlockMade) λ ()
    honestTreeChainGrowthInSameStateʳ {N′} (_◅ʳ_ {j = N″} N↝⋆ʳN″ N″↝N′) Nₜ≡N′ₜ NReady N′BlockMade lNₜ = goal Nₜ≡N′ₜ NReady N′BlockMade N″↝N′
      where
        ih :
            N .clock ≡ N″ .clock
          → N″ .progress ≡ blockMade
          → length (bestChain (N .clock ∸ 1) (honestTree N)) < length (bestChain (N″ .clock) (honestTree N″))
        ih Nₜ≡N″ₜ N″BlockMade = honestTreeChainGrowthInSameStateʳ {N″} N↝⋆ʳN″ Nₜ≡N″ₜ NReady N″BlockMade lNₜ

        goal :
            N .clock ≡ N′ .clock
          → N .progress ≡ ready
          → N′ .progress ≡ blockMade
          → N″ ↝ N′
          → length (bestChain (N .clock ∸ 1) (honestTree N)) < length (bestChain (N′ .clock) (honestTree N′))
        goal _ _ _ (permuteParties {parties = ps} eoN″↭ps) rewrite execOrderPreservesHonestChainLength {N″} (N″ .clock) eoN″↭ps = ih Nₜ≡N′ₜ N′BlockMade
        goal _ _ _ (permuteMsgs _) = ih Nₜ≡N′ₜ N′BlockMade
        goal _ _ _ (makeBlock {N′ = N‴} N″MsgsDelivered N″—[eoN″]↑→∗N‴) rewrite clockPreservation-↑∗ N″—[eoN″]↑→∗N‴ = goal-makeBlock
          where
            N₀↝⋆N″ : N₀ ↝⋆ N″
            N₀↝⋆N″ = N₀↝⋆N ◅◅ (Starʳ⇒Star N↝⋆ʳN″)

            goal-makeBlock : length (bestChain (N .clock ∸ 1) (honestTree N)) < length (bestChain (N″ .clock) (honestTree N‴))
            goal-makeBlock
              with L.Mem.Any↔ .Inverse.from lNₜ
            ... | p , p∈parties₀ , isWinner , hp
              with hasStateInAltDef {N″} .Equivalence.from $ hasState⇔∈parties₀ N₀↝⋆N″ .Equivalence.from p∈parties₀
            ... | ls , lspN″ = Nat.≤-<-trans |bchtN|≤|bcN| |bcN|<|bcN‴|
              where
                |bchtN|≤|bcN| : length (bestChain (N .clock ∸ 1) (honestTree N)) ≤ length (bestChain (N .clock ∸ 1) (ls .tree))
                |bchtN|≤|bcN| =
                  allBlocks⊆⇒|bestChain|≤
                    (N .clock ∸ 1)
                    (honestGlobalTreeInHonestLocalTree N₀↝⋆N hp NReady N″MsgsDelivered (Starʳ⇒Star N↝⋆ʳN″ , Nₜ≡N′ₜ) lspN″)

                |bcN|<|bcN‴| : length (bestChain (N .clock ∸ 1) (ls .tree)) < length (bestChain (N″ .clock) (honestTree N‴))
                |bcN|<|bcN‴|
                  with hasStateInAltDef {N‴} .Equivalence.from $
                         hasState⇔-↑∗ N″—[eoN″]↑→∗N‴ .Equivalence.to (hasStateInAltDef {N″} .Equivalence.to (ls , lspN″))
                ... | ls′ , lspN‴ = Nat.<-≤-trans |bcN|<|bcls′| |bcls′≤bcN‴|
                  where
                    Nᵖ = GlobalState ∋ honestBlockMaking p ls N″

                    N″↝[p]↑Nᵖ : N″ ↝[ p ]↑ Nᵖ
                    N″↝[p]↑Nᵖ = honestParty↑ lspN″ hp

                    lspNᵖ : Nᵖ .states ⁉ p ≡ just ls′
                    lspNᵖ = trans (sym $ localStatePreservation-∈-↑∗ N₀↝⋆N″ N″—[eoN″]↑→∗N‴ N″↝[p]↑Nᵖ) lspN‴

                    |bcN|<|bcls′| : length (bestChain (N .clock ∸ 1) (ls .tree)) < length (bestChain (N″ .clock) (ls′ .tree))
                    |bcN|<|bcls′| =
                      subst
                        (λ ◆ → length (bestChain (◆ ∸ 1) (ls .tree)) < length (bestChain (N″ .clock) (ls′ .tree)))
                        (sym Nₜ≡N′ₜ) $
                        bestChainGrowth N₀↝⋆N″ isWinnerN″ hp lspN″ N″↝[p]↑Nᵖ lspNᵖ
                      where
                        isWinnerN″ : winner p (N″ .clock)
                        isWinnerN″ = subst (winner p) Nₜ≡N′ₜ isWinner

                    |bcls′≤bcN‴| : length (bestChain (N″ .clock) (ls′ .tree)) ≤ length (bestChain (N″ .clock) (honestTree N‴))
                    |bcls′≤bcN‴| = allBlocks⊆⇒|bestChain|≤ (N″ .clock) $ λ {b} b∈bt[ls′] →
                        b∈bt[ls′] ∶
                      b ∈ allBlocks (ls′ .tree)
                        |> bt[ls′]⊆bksN‴ ∶
                      b ∈ L.concatMap (blocks N‴) (honestParties N‴)
                        |> L.SubS.xs⊆x∷xs _ _ ∶
                      b ∈ genesisBlock ∷ L.concatMap (blocks N‴) (honestParties N‴)
                        |> ≡ˢ⇒⊇ (buildTreeUsesAllBlocks _) ∶
                      b ∈ allBlocks (honestTree N‴)
                        where
                          open import Function.Reasoning

                          bt[ls′]⊆bksN‴ : allBlocks (ls′ .tree) ⊆ˢ L.concatMap (blocks N‴) (honestParties N‴)
                          bt[ls′]⊆bksN‴ {b} b∈bt[ls′] =
                            L.Mem.∈-concat⁺′
                              b∈bt[ls′]
                              (L.Mem.∈-map∘filter⁺ (blocks N‴) ¿ Honest ¿¹  (p , p∈eoN″ , bt[ls′]≡bkN‴p , hp))
                            where
                              bt[ls′]≡bkN‴p : allBlocks (ls′ .tree) ≡ blocks N‴ p
                              bt[ls′]≡bkN‴p rewrite lspN‴ = refl

                              p∈eoN″ : p ∈ N‴ .execOrder
                              p∈eoN″ = ∈-resp-↭ (execOrderPreservation-↭-↑∗ N″—[eoN″]↑→∗N‴) (∈-resp-↭ (execOrderPreservation-↭ N₀↝⋆N″) p∈parties₀)

            N‴ₜ≡N″ₜ  : N‴ .clock ≡ N″ .clock
            N‴ₜ≡N″ₜ = clockPreservation-↑∗ N″—[eoN″]↑→∗N‴

honestTreeChainGrowthInNextState : ∀ {N N′ : GlobalState} →
    N₀ ↝⋆ N
  → N ↝⋆⟨ 1 ⟩ N′
  → N .progress ≡ ready
  → N′ .progress ≡ ready
  → LuckySlot (N .clock)
  → length (honestTreeChain N) < length (honestTreeChain N′)
honestTreeChainGrowthInNextState {N} {N′} N₀↝⋆N (N↝⋆N′ , Nₜ+1≡N′ₜ) NReady N′Ready lNₜ =
  honestTreeChainGrowthInNextStateʳ (Star⇒Starʳ N↝⋆N′) Nₜ+1≡N′ₜ N′Ready lNₜ
  where
    open RTC; open Starʳ
    honestTreeChainGrowthInNextStateʳ :  ∀ {N′ : GlobalState} →
        N ↝⋆ʳ N′
      → suc (N .clock) ≡ N′ .clock
      → N′ .progress ≡ ready
      → LuckySlot (N .clock)
      → length (honestTreeChain N) < length (honestTreeChain N′)
    honestTreeChainGrowthInNextStateʳ εʳ Nₜ+1≡Nₜ _ _ = contradiction Nₜ+1≡Nₜ λ ()
    honestTreeChainGrowthInNextStateʳ {N′} (_◅ʳ_ {j = N″} N↝⋆ʳN″ N″↝N′) Nₜ+1≡N′ₜ N′Ready lNₜ = goal N′Ready N″↝N′
      where
        ih : suc (N .clock) ≡ N″ .clock → N″ .progress ≡ ready → length (honestTreeChain N) < length (honestTreeChain N″)
        ih Nₜ+1≡N″ₜ N″Ready = honestTreeChainGrowthInNextStateʳ {N″} N↝⋆ʳN″ Nₜ+1≡N″ₜ N″Ready lNₜ

        goal : N′ .progress ≡ ready → N″ ↝ N′ → length (honestTreeChain N) < length (honestTreeChain N′)
        goal _ (permuteParties {parties = ps} eoN″↭ps) rewrite execOrderPreservesHonestChainLength {N″} (N′ .clock ∸ 1) eoN″↭ps = ih Nₜ+1≡N′ₜ N′Ready
        goal _ (advanceRound N″BlockMade) = honestTreeChainGrowthInSameState N₀↝⋆N (Starʳ⇒Star N↝⋆ʳN″ , Nₜ≡N″ₜ) NReady N″BlockMade lNₜ
          where
            Nₜ≡N″ₜ : N .clock ≡ N″ .clock
            Nₜ≡N″ₜ = Nat.suc-injective Nₜ+1≡N′ₜ

            lN″ₜ : LuckySlot (N″ .clock)
            lN″ₜ = subst LuckySlot Nₜ≡N″ₜ lNₜ
        goal _ (permuteMsgs _) = ih Nₜ+1≡N′ₜ N′Ready

∃LessLuckySlotsBetweenStates : ∀ {N N′ : GlobalState} {w : ℕ} →
    N₀ ↝⋆ N
  → N ↝⋆ N′
  → N .progress ≡ ready
  → w + 1 ≤ length (luckySlotsInRange (N .clock) (N′ .clock))
  → ∃[ N″ ]
      N″ .progress ≡ ready
    × N₀ ↝⋆ N″
    × N″ ↝⋆ N′
    × length (honestTreeChain N) + 1 ≤ length (honestTreeChain N″)
    × w ≤ length (luckySlotsInRange (N″ .clock) (N′ .clock))
∃LessLuckySlotsBetweenStates {N} {N′} {w} N₀↝⋆N N↝⋆N′ NReady w+1≤|ls[N:N′]|
  with ∃FirstLuckySlotBetweenStates N₀↝⋆N N↝⋆N′ $ Nat.≤-trans (Nat.m≤n+m _ _) w+1≤|ls[N:N′]|
... | sl , hd[ls[N:N′]]≡sl
  with firstLuckySlotBetweenStates {N} {N′} hd[ls[N:N′]]≡sl
... | Nₜ≤sl , sl<N′ₜ
  with ∃ReadyBetweenSlots NReady N↝⋆N′ (Nₜ≤sl , Nat.<⇒≤ sl<N′ₜ)
... | Nˡ , NˡReady , Nˡₜ≡sl , N↝⋆Nˡ , Nˡ↝⋆N′
  with ∃ReadyBetweenSlots NˡReady Nˡ↝⋆N′ (subst (_≤ suc sl) (sym Nˡₜ≡sl) (Nat.n≤1+n _) , sl<N′ₜ)
... | N″ , N″Ready , N″ₜ≡sl+1 , Nˡ↝⋆N″ , N″↝⋆N′ =
  N″ , N″Ready , N₀↝⋆N ◅◅ N↝⋆Nˡ ◅◅ Nˡ↝⋆N″ , N″↝⋆N′ , |htcN|+1≤|htcN″| , w≤|ls[N″:N′]|
  where
    |htcN|+1≤|htcN″| : length (honestTreeChain N) + 1 ≤ length (honestTreeChain N″)
    |htcN|+1≤|htcN″| rewrite Nat.+-comm (length (honestTreeChain N)) 1 =
      Nat.≤-<-trans |htcN|≤|htcNˡ| |htcNˡ|<|htcN″|
      where
        |htcN|≤|htcNˡ| : length (honestTreeChain N) ≤ length (honestTreeChain Nˡ)
        |htcN|≤|htcNˡ| = honestTreeChainLengthMonotonicity N₀↝⋆N N↝⋆Nˡ

        |htcNˡ|<|htcN″| : length (honestTreeChain Nˡ) < length (honestTreeChain N″)
        |htcNˡ|<|htcN″| =
          honestTreeChainGrowthInNextState
            (N₀↝⋆N ◅◅ N↝⋆Nˡ)
            (Nˡ↝⋆N″ , (sym $ subst ((N″ .clock ≡_) ∘ suc) (sym Nˡₜ≡sl) N″ₜ≡sl+1))
            NˡReady N″Ready (subst LuckySlot (sym Nˡₜ≡sl) $ firstLuckySlotIsLucky {N} {N′} hd[ls[N:N′]]≡sl)

    w≤|ls[N″:N′]| : w ≤ length (luckySlotsInRange (N″ .clock) (N′ .clock))
    w≤|ls[N″:N′]| = Nat.+-cancelʳ-≤ 1 _ _ |w|+1≤|ls[N″:N′]|+1
      where
        Nₜ≤N″ₜ : N .clock ≤ N″ .clock
        Nₜ≤N″ₜ = clockMonotonicity $ N↝⋆Nˡ ◅◅ Nˡ↝⋆N″

        N″≤N′ₜ : N″ .clock ≤ N′ .clock
        N″≤N′ₜ = clockMonotonicity N″↝⋆N′

        ls[N:N′] ls[N:N″] ls[N″:N′] : List Slot
        ls[N:N′]  = luckySlotsInRange (N .clock)  (N′ .clock)
        ls[N:N″]  = luckySlotsInRange (N .clock)  (N″ .clock)
        ls[N″:N′] = luckySlotsInRange (N″ .clock) (N′ .clock)

        slIsLucky : LuckySlot sl
        slIsLucky = firstLuckySlotIsLucky {N} {N′} hd[ls[N:N′]]≡sl

        ls[N:N″]-def : ls[N:N″] ≡ luckySlotsInRange (N .clock) sl ++ [ sl ]
        ls[N:N″]-def
          rewrite
            N″ₜ≡sl+1
          | trans (∸-suc Nₜ≤sl) (Nat.+-comm 1 _)
          | ι-++ (N .clock) (sl ∸ N .clock) 1
          | L.filter-++ ¿ LuckySlot ¿¹ (ι (N .clock) (sl ∸ N .clock)) [ N .clock + (sl ∸ N .clock) ]
          | Nat.m+[n∸m]≡n Nₜ≤sl
          | L.filter-accept ¿ LuckySlot ¿¹ {sl} {[]} slIsLucky
          = refl

        |ls[N:N″]|≡1 : length ls[N:N″] ≡ 1
        |ls[N:N″]|≡1
          rewrite
            ls[N:N″]-def
          | L.length-++ (luckySlotsInRange (N .clock) sl) {ys = [ sl ]}
          | sym $ suc≗+1 (length (luckySlotsInRange (N .clock) sl))
          = cong suc |ls[N:sl]|≡0
          where
            hd-++≡sl : head (ls[N:N″] ++ ls[N″:N′]) ≡ just sl
            hd-++≡sl =
              subst
                ((_≡ just sl) ∘ head)
                (slotsInRange-filter-++ ¿ LuckySlot ¿¹ Nₜ≤N″ₜ N″≤N′ₜ)
                hd[ls[N:N′]]≡sl

            hd[ls[N:N″]]≡sl : head ls[N:N″] ≡ just sl
            hd[ls[N:N″]]≡sl = hd[ls[ss*]]≡sl sl∈ss[N:N″] hd-++≡sl
              where
                sl∈ss[N:N″] : sl ∈ slotsInRange (N .clock) (N″ .clock)
                sl∈ss[N:N″] =
                  ∈-ι⁺ Nₜ≤sl (subst (sl <_) (sym $ Nat.m+[n∸m]≡n Nₜ≤N″ₜ) (Nat.≤-reflexive $ sym N″ₜ≡sl+1))

                hd[ls[ss*]]≡sl : ∀ {ss*} →
                    sl ∈ ss*
                  → head (filter ¿ LuckySlot ¿¹ ss* ++ ls[N″:N′]) ≡ just sl
                  → head (filter ¿ LuckySlot ¿¹ ss*) ≡ just sl
                hd[ls[ss*]]≡sl {s* ∷ ss*} (here sl≡s*) _
                  rewrite
                    sym $ sl≡s*
                  | L.filter-accept ¿ LuckySlot ¿¹ {sl} {ss*} slIsLucky
                  = refl
                hd[ls[ss*]]≡sl {s* ∷ ss*} (there sl∈ss*) π with ¿ LuckySlot s* ¿
                ... | no ¬ls*
                  rewrite L.filter-reject ¿ LuckySlot ¿¹ {s*} {ss*} ¬ls* = hd[ls[ss*]]≡sl {ss*} sl∈ss* π
                ... | yes ls*
                  rewrite L.filter-accept ¿ LuckySlot ¿¹ {s*} {ss*} ls* = π

            |ls[N:sl]|≡0 : length (luckySlotsInRange (N .clock) sl) ≡ 0
            |ls[N:sl]|≡0 = |ss*|≡0 [<sl][ls[N:sl]] hd[ls[N:sl]+sl]≡sl
              where
                [<sl][ls[N:sl]] : L.All.All (_< sl) (luckySlotsInRange (N .clock) sl)
                [<sl][ls[N:sl]] = L.All.tabulate $ λ {sl′} sl′∈ls[N:sl] →
                  subst
                    (sl′ <_)
                    (Nat.m+[n∸m]≡n Nₜ≤sl)
                    (∈-ι⁻ {N .clock} {sl ∸ N .clock} (L.Mem.∈-filter⁻ _ sl′∈ls[N:sl] .proj₁) .proj₂)

                hd[ls[N:sl]+sl]≡sl : head (luckySlotsInRange (N .clock) sl ++ [ sl ]) ≡ just sl
                hd[ls[N:sl]+sl]≡sl rewrite sym ls[N:N″]-def = hd[ls[N:N″]]≡sl

                |ss*|≡0 : ∀ {ss*} →
                    L.All.All (_< sl) ss*
                  → head (ss* ++ [ sl ]) ≡ just sl
                  → length ss* ≡ 0
                |ss*|≡0 {[]} _ _ = refl
                |ss*|≡0 {s* ∷ ss*} [<sl][s*+ss*] js*≡jssl =
                  contradiction (M.just-injective js*≡jssl) (Nat.<⇒≢ $ L.All.head [<sl][s*+ss*])

        |w|+1≤|ls[N″:N′]|+1 : w + 1 ≤ length ls[N″:N′] + 1
        |w|+1≤|ls[N″:N′]|+1 = begin
          w + 1                              ≤⟨ w+1≤|ls[N:N′]| ⟩
          length ls[N:N′]                    ≡⟨ cong length $ slotsInRange-filter-++ ¿ LuckySlot ¿¹ Nₜ≤N″ₜ N″≤N′ₜ ⟩
          length (ls[N:N″] ++ ls[N″:N′])     ≡⟨ L.length-++ ls[N:N″] ⟩
          length ls[N:N″] + length ls[N″:N′] ≡⟨ cong (_+ length ls[N″:N′]) |ls[N:N″]|≡1 ⟩
          1 + length ls[N″:N′]               ≡⟨ Nat.+-comm 1 _ ⟩
          length ls[N″:N′] + 1               ∎
          where open Nat.≤-Reasoning

honestTreeChainGrowth : ∀ {N N′ : GlobalState} →
    N₀ ↝⋆ N
  → N ↝⋆ N′
  → N .progress ≡ ready
  → ∀ {w : ℕ} →
      w ≤ length (luckySlotsInRange (N .clock) (N′ .clock))
    → length (honestTreeChain N) + w ≤ length (honestTreeChain N′)
honestTreeChainGrowth {N} N₀↝⋆N N↝⋆N′ _ {0} _
  rewrite Nat.+-identityʳ (length (honestTreeChain N)) = honestTreeChainLengthMonotonicity N₀↝⋆N N↝⋆N′
honestTreeChainGrowth {N} {N′} N₀↝⋆N N↝⋆N′ NReady {suc w} w+1≤|ls[Nₜ:N′ₜ]|
  with ∃LessLuckySlotsBetweenStates
         N₀↝⋆N
         N↝⋆N′
         NReady
         $ subst (_≤ length (luckySlotsInRange (N .clock) (N′ .clock))) (suc≗+1 w) w+1≤|ls[Nₜ:N′ₜ]|
... | N″ , N″Ready , N₀↝⋆N″ , N″↝⋆N′ , |htc[N]|+1≤|htc[N″]| , w≤|ls[N″ₜ:N′ₜ]| =
  Nat.≤-trans |htc[N]|+[w+1]≤w+|htc[N″]| w+|htc[N″]|≤|htc[N′]|
  where
    |htc[N]|+[w+1]≤w+|htc[N″]| : length (honestTreeChain N) + suc w ≤ w + length (honestTreeChain N″)
    |htc[N]|+[w+1]≤w+|htc[N″]|
      rewrite
        sym $ Nat.+-assoc (length (honestTreeChain N)) 1 w
      | Nat.+-comm w (length (honestTreeChain N″))
      = Nat.+-monoˡ-≤ w |htc[N]|+1≤|htc[N″]|

    w+|htc[N″]|≤|htc[N′]| : w + length (honestTreeChain N″) ≤ length (honestTreeChain N′)
    w+|htc[N″]|≤|htc[N′]| rewrite Nat.+-comm w (length (honestTreeChain N″)) =
      honestTreeChainGrowth N₀↝⋆N″ N″↝⋆N′ N″Ready w≤|ls[N″ₜ:N′ₜ]|
