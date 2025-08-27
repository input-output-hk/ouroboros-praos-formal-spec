open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Safety.BlockPositions
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.BaseTypes
open import Protocol.Crypto ⦃ params ⦄ using (Hashable); open Hashable ⦃ ... ⦄
open import Protocol.Block ⦃ params ⦄
open import Protocol.Chain ⦃ params ⦄
open import Protocol.Message ⦃ params ⦄
open import Protocol.Network ⦃ params ⦄; open Envelope
open import Protocol.TreeType ⦃ params ⦄
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Protocol.Chain.Properties ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Safety.ChainFromBlock ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.SuperBlocks ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.LocalState ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.Trees ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.ForgingFree ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.CollisionFree ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.BlockHistory ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.ExecutionOrder ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.Time ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Liveness.ChainGrowth ⦃ params ⦄ ⦃ assumptions ⦄ using (honestGlobalTreeInHonestLocalTree)
open import Data.Nat.Properties.Ext using (pred[n]<n; suc-≢-injective)
open import Data.Sum.Algebra.Ext using (¬A⊎B⇒A→B)
open import Data.List.Properties.Ext using ([]≢∷ʳ; ≢[]⇒∷; ∷≢[]; length0⇒[]; filter-acceptʳ; filter-rejectʳ)
open import Data.List.Membership.Propositional.Properties.Ext using (x∈x∷xs; ∈-∷⁻)
open import Data.List.Relation.Unary.All.Properties.Ext using (cartesianProduct⁻)
open import Data.List.Relation.Unary.AllPairs.Properties.Ext using (headʳ)
open import Data.List.Relation.Unary.Unique.DecPropositional.Properties using (deduplicate-!)
open import Data.List.Relation.Unary.Unique.Propositional.Properties.Ext using (Unique[xs∷ʳx]⇒x∉xs; map⁺-∈)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties.Ext using ({- Unique-resp-↭; -} filter-↭)
open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_; ≡ˢ-refl; ≡ˢ-sym; ≡ˢ-trans; ≡ˢ⇒⊆×⊇; ⊆×⊇⇒≡ˢ; deduplicate-cong; filter-cong; cartesianProduct-cong; All-resp-≡ˢ; Any-resp-≡ˢ)
open import Data.List.Relation.Binary.Subset.Propositional.Properties.Ext using (cartesianProduct-⊆-Mono; deduplicate-⊆; ∷-⊆; ∷⊆⇒∈;  ∷-⊆⁺)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Ext using (Starʳ)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.Ext using (Star⇒Starʳ; Starʳ⇒Star)
open import Prelude.STS.Properties using (—[]→∗⇒—[]→∗ʳ; —[]→∗ʳ⇒—[]→∗)
open import Relation.Binary.PropositionalEquality using (≢-sym)
open import Data.List.Relation.Unary.Unique.Propositional.Properties using (Unique[x∷xs]⇒x∉xs)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (↭-length)
open import Data.List.Relation.Binary.Permutation.Propositional using (↭-refl; ↭-trans)
open import Function.Related.Propositional as Related
open import Function.Bundles

✓-impossibility : ∀ {w : Level} {Whatever : Set w} {c : Chain} {b b′ : Block} → [ b ] ✓ → (b ∷ b′ ∷ c) ✓ → Whatever
✓-impossibility {c = c} {b = b} {b′ = b′} [b]✓ [b+b′+c]✓ = contradiction ([gb+c]✓⇔c≡[] .Equivalence.to [gb+b′+c]✓) λ ()
  where
    b≡gb : b ≡ genesisBlock
    b≡gb = [b]✓⇔b≡gb .Equivalence.to [b]✓

    [gb+b′+c]✓ : (genesisBlock ∷ b′ ∷ c) ✓
    [gb+b′+c]✓ rewrite sym b≡gb = [b+b′+c]✓

≡tips⇒≡chains : ∀ {N : GlobalState} {c₁ c₂ : Chain} {b : Block} →
    N₀ ↝⋆ N
  → CollisionFree N
  → (b ∷ c₁) ✓
  → (b ∷ c₂) ✓
  → c₁ ⊆ˢ genesisBlock ∷ blockHistory N
  → c₂ ⊆ˢ genesisBlock ∷ blockHistory N
  → c₁ ≡ c₂
≡tips⇒≡chains {_} {[]}        {[]}        _     _   _       _       _         _         = refl
≡tips⇒≡chains {_} {[]}        {_ ∷ _}     _     _   [b+c₁]✓ [b+c₂]✓ _         _         = ✓-impossibility [b+c₁]✓ [b+c₂]✓
≡tips⇒≡chains {_} {_ ∷ _}     {[]}        _     _   [b+c₁]✓ [b+c₂]✓ _         _         = ✓-impossibility [b+c₂]✓ [b+c₁]✓
≡tips⇒≡chains {N} {b₁′ ∷ c₁′} {b₂′ ∷ c₂′} N₀↝⋆N cfN [b+c₁]✓ [b+c₂]✓ c₁⊆gb+bhN c₂⊆gb+bhN
  with
    ✓-∷ .Equivalence.from [b+c₁]✓ | ✓-∷ .Equivalence.from [b+c₂]✓
... | _ , b⟵b₁′ , _ , [b₁′+c₁′]✓  | _ , b⟵b₂′ , _ , [b₂′+c₂′]✓
  = subst₂ ((_≡ b₂′ ∷ c₂′) ∘₂ _∷_) (sym b₁′≡b₂′) (sym c₁′≡c₂′) refl
  where
    b₁′≡b₂′ : b₁′ ≡ b₂′
    b₁′≡b₂′ = L.All.lookup cfN (L.Mem.∈-cartesianProduct⁺ (∷⊆⇒∈ c₁⊆gb+bhN) (∷⊆⇒∈ c₂⊆gb+bhN)) (trans (sym b⟵b₁′) b⟵b₂′)

    c₁′≡c₂′ : c₁′ ≡ c₂′
    c₁′≡c₂′ = ≡tips⇒≡chains N₀↝⋆N cfN [b₁′+c₁′]✓ [b₁′+c₂′]✓ (∷-⊆ c₁⊆gb+bhN) (∷-⊆ c₂⊆gb+bhN)
      where
        [b₁′+c₂′]✓ : (b₁′ ∷ c₂′) ✓
        [b₁′+c₂′]✓ rewrite b₁′≡b₂′ = [b₂′+c₂′]✓

opaque

  unfolding honestBlockMaking corruptBlockMaking

  olderNonGBBlocksHaveSmallerPositions : ∀ {N : GlobalState} {b : Block} →
      N₀ ↝⋆ N
    → ForgingFree N
    → CollisionFree N
    → b ∈ honestBlockHistory N
    → L.All.All
        (λ b′ → blockPos b′ N < blockPos b N)
        (filter ¿ b >ˢ_ ¿¹ (honestBlockHistory N))
  olderNonGBBlocksHaveSmallerPositions = olderNonGBBlocksHaveSmallerPositionsʳ ∘ Star⇒Starʳ
    where
      open RTC; open Starʳ
      olderNonGBBlocksHaveSmallerPositionsʳ : ∀ {N : GlobalState} {b : Block} →
          N₀ ↝⋆ʳ N
        → ForgingFree N
        → CollisionFree N
        → b ∈ honestBlockHistory N
        → L.All.All
            (λ b′ → blockPos b′ N < blockPos b N)
            (filter ¿ b >ˢ_ ¿¹ (honestBlockHistory N))
      olderNonGBBlocksHaveSmallerPositionsʳ {N} {b} N₀↝⋆ʳN@(_◅ʳ_ {j = N′} N₀↝⋆ʳN′ N′↝N) ffN cfN b∈hbhN = goal N′↝N
        where
          N₀↝⋆N′ : N₀ ↝⋆ N′
          N₀↝⋆N′ = Starʳ⇒Star N₀↝⋆ʳN′

          ffN′ : ForgingFree N′
          ffN′ = ForgingFreePrev (N′↝N ◅ ε) ffN

          cfN′ : CollisionFree N′
          cfN′ = CollisionFreePrev (N′↝N ◅ ε) cfN

          N′↝⋆N : N′ ↝⋆ N
          N′↝⋆N = Starʳ⇒Star (εʳ ◅ʳ N′↝N)

          ih :
              b ∈ honestBlockHistory N′
            → L.All.All (λ b′ → blockPos b′ N′ < blockPos b N′) (filter ¿ b >ˢ_ ¿¹ (honestBlockHistory N′))
          ih b∈hbhN′ = olderNonGBBlocksHaveSmallerPositionsʳ N₀↝⋆ʳN′ ffN′ cfN′ b∈hbhN′

          goal :
              N′ ↝ N
            → L.All.All (λ b′ → blockPos b′ N < blockPos b N) (filter ¿ b >ˢ_ ¿¹ (honestBlockHistory N))
          goal N′↝N
            with N′↝N
          ... | deliverMsgs {N′ = N″} N′Ready N′—[eoN′]↓→∗N″ = L.All.tabulate deliveryMsgsGoal
            where
              hbhPres : honestBlockHistory N′ ≡ˢ honestBlockHistory N
              hbhPres = honestBlockHistoryPreservation-↓∗ N₀↝⋆N′ N′—[eoN′]↓→∗N″ ffN N′Ready

              b∈hbhN′ : b ∈ honestBlockHistory N′
              b∈hbhN′ = ≡ˢ⇒⊆×⊇ hbhPres .proj₂ b∈hbhN

              cfbhN′≡cfbhN : ∀ {b°} →
                  b° ∈ honestBlockHistory N
                → chainFromBlock b° (blockHistory N′) ≡ chainFromBlock b° (blockHistory N)
              cfbhN′≡cfbhN b°∈hbhN = cfbHbhPres N₀↝⋆N′ N′↝N ffN cfN b°∈hbhN hbhPres

              deliveryMsgsGoal : ∀ {b′} → b′ ∈ filter ¿ b >ˢ_ ¿¹ (honestBlockHistory N) → blockPos b′ N < blockPos b N
              deliveryMsgsGoal {b′} b′∈[b>ˢ]hbhN with L.Mem.∈-filter⁻ ¿ b >ˢ_ ¿¹ {xs = honestBlockHistory N} b′∈[b>ˢ]hbhN
              ... | b′∈hbhN , b>ˢb′ = subst₂ (_<_ on ∣_∣) (cfbhN′≡cfbhN b′∈hbhN) (cfbhN′≡cfbhN b∈hbhN) ih′
                where
                  b′∈[b>ˢ]hbhN′ : b′ ∈ filter ¿ b >ˢ_ ¿¹ (honestBlockHistory N′)
                  b′∈[b>ˢ]hbhN′ = ≡ˢ⇒⊆×⊇ (filter-cong hbhPres) .proj₂ b′∈[b>ˢ]hbhN

                  ih′ : blockPos b′ N′ < blockPos b N′
                  ih′ = L.All.lookup (ih b∈hbhN′) b′∈[b>ˢ]hbhN′

          ... | makeBlock {N′} {N″} N′MsgsDelivered N′—[eoN′]↑→∗N″ = L.All.tabulate makeBlockGoal
            where
              b°∈hbhN′ : ∀ {b°} → b° ∈ honestBlockHistory N → b° .slot < N .clock → b° ∈ honestBlockHistory N′
              b°∈hbhN′ {b°} b°∈hbhN b°ₜ<Nₜ = L.SubS.filter-⊆ _ _ $
                  b°∈hbhN ∶
                b° ∈ honestBlockHistory N
                  |> flip (L.Mem.∈-filter⁺ _) b°ₜ<Nₜ ∶
                b° ∈ filter ((_<? N .clock) ∘ slot) (honestBlockHistory N)
                  |> subst _ (clockPreservation-↑∗ N′—[eoN′]↑→∗N″) ∶
                b° ∈ filter ((_<? N′ .clock) ∘ slot) (honestBlockHistory N)
                  |> ≡ˢ⇒⊆×⊇ (honestBlocksBelowSlotPreservation N₀↝⋆N′ N′↝⋆N ffN) .proj₂ ∶
                b° ∈ filter ((_<? N′ .clock) ∘ slot) (honestBlockHistory N′)
                where open import Function.Reasoning

              bcfbhN : BlockListCollisionFree (blockHistory N)
              bcfbhN = BlockListCollisionFree-∷ {blockHistory N} {genesisBlock} cfN

              bhN′⊆bhN : blockHistory N′ ⊆ˢ blockHistory N
              bhN′⊆bhN = blockHistoryPreservation-↝⋆ N′↝⋆N

              bHonest : HonestBlock b
              bHonest = L.Mem.∈-filter⁻ ¿ HonestBlock ¿¹ {xs = blockHistory N} b∈hbhN .proj₂

              nphb : ∀ {b°} → b° ∈ honestBlockHistory N → b° .slot ≤ N .clock
              nphb = L.All.lookup $ noPrematureHonestBlocks (Starʳ⇒Star N₀↝⋆ʳN) ffN

              makeBlockGoal : ∀ {b′} → b′ ∈ filter ¿ b >ˢ_ ¿¹ (honestBlockHistory N) → blockPos b′ N < blockPos b N
              makeBlockGoal {b′} b′∈[b>ˢ]hbhN
                with Nat.m≤n⇒m<n∨m≡n (nphb b∈hbhN) | L.Mem.∈-filter⁻ _ {xs = honestBlockHistory N} b′∈[b>ˢ]hbhN
              ... | inj₂ bₜ≡Nₜ | b′∈hbhN , b>ˢb′ = makeBlockGoal-bₜ≡Nₜ (N′ .execOrder) N″↷↑N″[bM] cfN b∈hbhN uniqEoN′ (—[]→∗⇒—[]→∗ʳ N′—[eoN′]↑→∗N″)
                where
                  b′ₜ<Nₜ : b′ .slot < N .clock
                  b′ₜ<Nₜ rewrite sym bₜ≡Nₜ = b>ˢb′

                  b′∈hbhN′ : b′ ∈ honestBlockHistory N′
                  b′∈hbhN′ = b°∈hbhN′ b′∈hbhN b′ₜ<Nₜ

                  ih′ : b ∈ honestBlockHistory N′ → blockPos b′ N′ < blockPos b N′
                  ih′ b∈hbhN′ = L.All.lookup (ih b∈hbhN′) $ L.Mem.∈-filter⁺ _  b′∈hbhN′ b>ˢb′

                  N″↷↑N″[bM] : N″ ↷↑ record N″ { progress = blockMade }
                  N″↷↑N″[bM] = progress↑ ↷↑-refl

                  uniqEoN′ : Unique (N′ .execOrder)
                  uniqEoN′ = execOrderUniqueness N₀↝⋆N′

                  makeBlockGoal-bₜ≡Nₜ : ∀ {N*} ps →
                      N* ↷↑ N
                    → CollisionFree N*
                    → b ∈ honestBlockHistory N*
                    → Unique ps
                    → _ ⊢ N′ —[ ps ]↑→∗ʳ N*
                    → blockPos b′ N* < blockPos b N*
                  makeBlockGoal-bₜ≡Nₜ {N*} [] _ _ b∈hbhN* _ [] = ih′ b∈hbhN*
                  makeBlockGoal-bₜ≡Nₜ {N*} [] _ _ _ _ (_∷ʳ_ {eq = eq} _ _) = contradiction eq []≢∷ʳ
                  makeBlockGoal-bₜ≡Nₜ {N*} (p ∷ ps) prfN cfN* b∈hbhN* p∷psUniq (_∷ʳ_ {is = ps′} {i = p′} {s′ = N‴} {eq = eq} ts⋆ ts) = step ts
                    where
                      cfN‴ : CollisionFree N‴
                      cfN‴ = CollisionFreePrev-↑ ts cfN*

                      ps′∷ʳp′Uniq : Unique (ps′ L.∷ʳ p′)
                      ps′∷ʳp′Uniq = subst Unique eq p∷psUniq

                      ps′Uniq : Unique ps′
                      ps′Uniq = headʳ ps′∷ʳp′Uniq

                      p′∉ps′ : p′ ∉ ps′
                      p′∉ps′ = Unique[xs∷ʳx]⇒x∉xs ps′∷ʳp′Uniq

                      ih* : b ∈ honestBlockHistory N‴ → blockPos b′ N‴ < blockPos b N‴
                      ih* b∈hbhN‴ = makeBlockGoal-bₜ≡Nₜ {N‴} ps′ (blockMaking↑ ts prfN) cfN‴ b∈hbhN‴ ps′Uniq ts⋆

                      bhN′⊆bhN‴ : blockHistory N′ ⊆ˢ blockHistory N‴
                      bhN′⊆bhN‴ = blockHistoryPreservation-↑∗ (—[]→∗ʳ⇒—[]→∗ ts⋆)

                      b′∈hbhN‴ : b′ ∈ honestBlockHistory N‴
                      b′∈hbhN‴ with L.Mem.∈-filter⁻ _ b′∈hbhN′
                      ... | b′∈bhN′ , b′Honest = L.Mem.∈-filter⁺ _  (bhN′⊆bhN‴ b′∈bhN′) b′Honest

                      cfbhN‴≢[] : ∀ {b°} → b° ∈ honestBlockHistory N‴ → chainFromBlock b° (blockHistory N‴) ≢ []
                      cfbhN‴≢[] {b°} b°∈hbhN‴ = ✓⇒≢[] cfbhN‴✓
                        where
                          cfbhN‴✓ : chainFromBlock b° (blockHistory N‴) ✓
                          cfbhN‴✓ = L.All.lookup (honestBlockCfb✓-↑∗ N₀↝⋆N′ N′↝⋆N ffN (—[]→∗ʳ⇒—[]→∗ ts⋆) (blockMaking↑ ts prfN) ps′Uniq cfN‴) b°∈hbhN‴

                      step : _ ⊢ N‴ —[ p′ ]↑→ N* → blockPos b′ N* < blockPos b N*
                      step (unknownParty↑ _) = ih* b∈hbhN*
                      step (honestParty↑ {ls = ls} lsπ hp′π) with Params.winnerᵈ params {p′} {N‴ .clock}
                      ... | ⁇ (yes isWinner) rewrite lsπ = step-honestParty↑
                        where
                          lsN′ : N′ .states ⁉ p′ ≡ just ls
                          lsN′ rewrite sym $ localStatePreservation-∉-↑∗ p′∉ps′ (—[]→∗ʳ⇒—[]→∗ ts⋆) = lsπ

                          best : Chain
                          best = bestChain (N‴ .clock ∸ 1) (ls .tree)

                          nb : Block
                          nb = mkBlock (hash (tip best)) (N‴ .clock) (txSelection (N‴ .clock) p′) p′

                          b∈nb+hbhN‴ : b ∈ nb ∷ honestBlockHistory N‴
                          b∈nb+hbhN‴ rewrite hp′π = b∈hbhN*

                          bhN‴⊆nb+bhN‴ : blockHistory N‴ ⊆ˢ nb ∷ blockHistory N‴
                          bhN‴⊆nb+bhN‴  = L.SubS.xs⊆x∷xs _ _

                          blcf[nb+bhN‴] : BlockListCollisionFree (nb ∷ blockHistory N‴)
                          blcf[nb+bhN‴] = BlockListCollisionFree-∷ {nb ∷ blockHistory N‴} {genesisBlock} cfN*

                          step-honestParty↑ :
                            ∣ chainFromBlock b′ (nb ∷ blockHistory N‴) ∣
                            <
                            ∣ chainFromBlock b  (nb ∷ blockHistory N‴) ∣
                          step-honestParty↑
                            with ∈-∷⁻ b∈nb+hbhN‴ | b ≟ nb
                          ... | inj₁ b≡nb        | no b≢nb = contradiction b≡nb b≢nb
                          ... | inj₂ b∈hbhN‴     | no _  = subst₂ (_<_ on ∣_∣) (cfbhN‴≡cfb[nb+bhN‴] b′∈hbhN‴) (cfbhN‴≡cfb[nb+bhN‴] b∈hbhN‴) (ih* b∈hbhN‴)
                            where
                              cfbhN‴≡cfb[nb+bhN‴] : ∀ {b°} →
                                  b° ∈ honestBlockHistory N‴
                                → chainFromBlock b° (blockHistory N‴) ≡ chainFromBlock b° (nb ∷ blockHistory N‴)
                              cfbhN‴≡cfb[nb+bhN‴] = subsetCfbPreservation blcf[nb+bhN‴] bhN‴⊆nb+bhN‴ ∘ cfbhN‴≢[]

                          ... | _                | yes b≡nb with chainFromNewBlock N₀↝⋆N′ ts⋆ isWinner p′∉ps′ lsπ hp′π cfN*
                          ... |   cfb≡nb∷best , _ with ∃ReadyBeforeMsgsDelivered N₀↝⋆N′ N′MsgsDelivered
                          ... |     Nᴿ , N₀↝⋆Nᴿ , Nᴿ↝⋆⟨0⟩N′ , NᴿReady rewrite b≡nb | cfb≡nb∷best = ∣cfb[nb+bhN‴]∣<1+∣best∣
                            where
                              b′∈hbhNᴿ : b′ ∈ honestBlockHistory Nᴿ
                              b′∈hbhNᴿ = ≡ˢ⇒⊆×⊇ (honestBlockHistoryPreservation-↝⋆⟨0⟩ N₀↝⋆Nᴿ NᴿReady Nᴿ↝⋆⟨0⟩N′ ffN′ N′MsgsDelivered) .proj₂ b′∈hbhN′

                              Nᴿ↝⋆N′ : Nᴿ ↝⋆ N′
                              Nᴿ↝⋆N′ = Nᴿ↝⋆⟨0⟩N′ .proj₁

                              bhNᴿ⊆bhN‴ : blockHistory Nᴿ ⊆ˢ blockHistory N‴
                              bhNᴿ⊆bhN‴ = blockHistoryPreservation-↑∗ (—[]→∗ʳ⇒—[]→∗ ts⋆) ∘ blockHistoryPreservation-↝⋆ Nᴿ↝⋆N′

                              Nᴿₜ≡N′ₜ : Nᴿ .clock ≡ N′ .clock
                              Nᴿₜ≡N′ₜ = Nᴿ↝⋆⟨0⟩N′ .proj₂

                              ffNᴿ : ForgingFree Nᴿ
                              ffNᴿ = ForgingFreePrev Nᴿ↝⋆N′ ffN′

                              cfNᴿ : CollisionFree Nᴿ
                              cfNᴿ = CollisionFreePrev Nᴿ↝⋆N′ cfN′

                              cfbhNᴿ✓ : chainFromBlock b′ (blockHistory Nᴿ) ✓
                              cfbhNᴿ✓ = honestBlockCfb✓ N₀↝⋆Nᴿ ffNᴿ cfNᴿ b′∈hbhNᴿ

                              cfbhNᴿ≢[] : chainFromBlock b′ (blockHistory Nᴿ) ≢ []
                              cfbhNᴿ≢[] = ✓⇒≢[] cfbhNᴿ✓

                              cfbhNᴿ≡cfb[nb+bhN‴] : chainFromBlock b′ (blockHistory Nᴿ) ≡ chainFromBlock b′ (nb ∷ blockHistory N‴)
                              cfbhNᴿ≡cfb[nb+bhN‴] = subsetCfbPreservation blcf[nb+bhN‴] (∷-⊆⁺ bhNᴿ⊆bhN‴) cfbhNᴿ≢[]

                              ∣cfb[nb+bhN‴]∣<1+∣best∣ : ∣ chainFromBlock b′ (nb ∷ blockHistory N‴) ∣ < 1 + ∣ best ∣
                              ∣cfb[nb+bhN‴]∣<1+∣best∣ = let open Nat.≤-Reasoning in begin-strict
                                ∣ chainFromBlock b′ (nb ∷ blockHistory N‴) ∣ ≡⟨ cong ∣_∣ cfbhNᴿ≡cfb[nb+bhN‴] ⟨
                                ∣ chainFromBlock b′ (blockHistory Nᴿ) ∣      ≤⟨ ∣cfbNᴿ∣≤∣best∣ ⟩
                                ∣ best ∣                                     <⟨ Nat.n<1+n _ ⟩
                                1 + ∣ best ∣ ∎
                                where
                                  cfbNᴿ⊆t :
                                    chainFromBlock b′ (blockHistory Nᴿ)
                                    ⊆ˢ
                                    filter ((_≤? N‴ .clock ∸ 1) ∘ slot) (allBlocks (ls .tree))
                                  cfbNᴿ⊆t {b″} b″∈cfb = L.Mem.∈-filter⁺ _ {xs = allBlocks (ls .tree)} b″∈t b″ₜ≤N‴ₜ-1
                                    where
                                       open L.SubS.⊆-Reasoning Block

                                       b″∈t : b″ ∈ allBlocks (ls .tree)
                                       b″∈t =
                                         b″                                  ∈⟨ b″∈cfb ⟩
                                         chainFromBlock b′ (blockHistory Nᴿ) ⊆⟨ L.All.lookup (cfbInHonestTree N₀↝⋆Nᴿ ffNᴿ cfNᴿ) b′∈hbhNᴿ ⟩
                                         allBlocks (honestTree Nᴿ)           ⊆⟨ honestGlobalTreeInHonestLocalTree N₀↝⋆Nᴿ hp′π NᴿReady N′MsgsDelivered Nᴿ↝⋆⟨0⟩N′ lsN′ ⟩
                                         allBlocks (ls .tree) ∎

                                       b″ₜ≤N‴ₜ-1 : b″ .slot ≤ N‴ .clock ∸ 1
                                       b″ₜ≤N‴ₜ-1 rewrite clockPreservation-↑∗ (—[]→∗ʳ⇒—[]→∗ ts⋆) = Nat.<⇒≤pred b″ₜ<N′ₜ
                                         where
                                           b″ₜ<N′ₜ : b″ .slot < N′ .clock
                                           b″ₜ<N′ₜ with cfbStartsWithBlock {b′} {blockHistory Nᴿ} cfbhNᴿ≢[]
                                           ... | c′ , cfb≡b′∷c′ with ∈-∷⁻ $ subst (b″ ∈_) cfb≡b′∷c′ b″∈cfb
                                           ... |   inj₁ b″≡b′ rewrite b″≡b′ = b>ˢb′
                                           ... |   inj₂ b″∈c′ = Nat.<-trans b′>ˢb″ b>ˢb′
                                             where
                                               [b′∷c′]✓ : (b′ ∷ c′) ✓
                                               [b′∷c′]✓ rewrite sym cfb≡b′∷c′ = cfbhNᴿ✓

                                               b′>ˢb″ : b′ >ˢ b″
                                               b′>ˢb″ = DecreasingSlots-∈ (✓⇒ds [b′∷c′]✓) (here refl) b″∈c′

                                  ∣cfbNᴿ∣≤∣best∣ : ∣ chainFromBlock b′ (blockHistory Nᴿ) ∣ ≤ ∣ best ∣
                                  ∣cfbNᴿ∣≤∣best∣ = optimal (chainFromBlock b′ (blockHistory Nᴿ)) (ls .tree) (N‴ .clock ∸ 1) cfbhNᴿ✓ cfbNᴿ⊆t
                      ... | ⁇ (no _) = ih* b∈hbhN*

                      step (corruptParty↑ _ _) = subst₂ (_<_ on ∣_∣) (cfbhN′≡cfbhN b′∈hbhN‴) (cfbhN′≡cfbhN b∈hbhN‴) (ih* b∈hbhN‴)
                        where
                          mds : List (Message × DelayMap)
                          mds = makeBlockᶜ (N‴ .clock) (N‴ .history) (N‴ .messages) (N‴ .advState).proj₁

                          sub : L.map (projBlock ∘ proj₁) mds ⊆ʰ blockHistory N‴
                          sub = ffN .proj₂ (blockMaking↑ ts prfN)

                          hbhPres : honestBlockHistory N‴ ≡ˢ honestBlockHistory (broadcastMsgsᶜ mds N‴)
                          hbhPres = honestBlockHistoryPreservation-broadcastMsgsᶜ {N‴} {mds} sub

                          b∈hbhN‴ : b ∈ honestBlockHistory N‴
                          b∈hbhN‴ = ≡ˢ⇒⊆×⊇ hbhPres .proj₂ b∈hbhN*

                          bhN‴⊆bhBc : blockHistory N‴ ⊆ˢ blockHistory (broadcastMsgsᶜ mds N‴)
                          bhN‴⊆bhBc = blockHistoryPreservation-broadcastMsgsᶜ mds N‴

                          blcfbhBc : BlockListCollisionFree (blockHistory (broadcastMsgsᶜ mds N‴))
                          blcfbhBc = BlockListCollisionFree-∷ {blockHistory (broadcastMsgsᶜ mds N‴)} {genesisBlock} cfN*

                          cfbhN′≡cfbhN : ∀ {b°} →
                              b° ∈ honestBlockHistory N‴
                            → chainFromBlock b° (blockHistory N‴) ≡ chainFromBlock b° (blockHistory (broadcastMsgsᶜ mds N‴))
                          cfbhN′≡cfbhN = subsetCfbPreservation blcfbhBc bhN‴⊆bhBc ∘ cfbhN‴≢[]

              ... | inj₁ bₜ<Nₜ | _ with L.Mem.∈-filter⁻ _ {xs = honestBlockHistory N} b′∈[b>ˢ]hbhN
              ... |    b′∈hbhN , b>ˢb′ = subst₂ (_<_ on ∣_∣) (cfbhN′≡cfbhN b′∈hbhN′ b′ₜ<Nₜ) (cfbhN′≡cfbhN b∈hbhN′ bₜ<Nₜ) ih′
                where
                  b′ₜ<Nₜ : b′ .slot < N .clock
                  b′ₜ<Nₜ = Nat.<-trans b>ˢb′ bₜ<Nₜ

                  b∈hbhN′ : b ∈ honestBlockHistory N′
                  b∈hbhN′ = b°∈hbhN′ b∈hbhN bₜ<Nₜ

                  b′∈hbhN′ : b′ ∈ honestBlockHistory N′
                  b′∈hbhN′ = b°∈hbhN′ b′∈hbhN b′ₜ<Nₜ

                  cfbhN′≡cfbhN : ∀ {b°} →
                      b° ∈ honestBlockHistory N′
                    → b° .slot < N .clock
                    → chainFromBlock b° (blockHistory N′) ≡ chainFromBlock b° (blockHistory N)
                  cfbhN′≡cfbhN {b°} b°∈hbhN′ b°ₜ<Nₜ = subsetCfbPreservation bcfbhN bhN′⊆bhN cfbhN′≢[]
                    where
                      cfbhN′≢[] : chainFromBlock b° (blockHistory N′) ≢ []
                      cfbhN′≢[] = ✓⇒≢[] cfbhN′✓
                        where
                          cfbhN′✓ : chainFromBlock b° (blockHistory N′) ✓
                          cfbhN′✓ = L.All.lookup (L.All.tabulate $ λ {b} → honestBlockCfb✓ N₀↝⋆N′ ffN′ cfN′) b°∈hbhN′

                  ih′ : blockPos b′ N′ < blockPos b N′
                  ih′ = L.All.lookup (ih b∈hbhN′) $ L.Mem.∈-filter⁺ _ b′∈hbhN′ b>ˢb′

          ... | advanceRound   _                  = ih b∈hbhN
          ... | permuteParties _                  = ih b∈hbhN
          ... | permuteMsgs    _                  = ih b∈hbhN

  olderBlocksHaveSmallerPositions : ∀ {N : GlobalState} {b : Block} →
      N₀ ↝⋆ N
    → ForgingFree N
    → CollisionFree N
    → b ∈ genesisBlock ∷ honestBlockHistory N
    → L.All.All
        (λ b′ → blockPos b′ N < blockPos b N)
        (filter ¿ b >ˢ_ ¿¹ (genesisBlock ∷ honestBlockHistory N))
  olderBlocksHaveSmallerPositions {N} {b} N₀↝⋆N ffN cfN b∈gb+hbhN
    with ∈-∷⁻ b∈gb+hbhN
  ... | inj₁ b≡gb rewrite b≡gb = L.All.tabulate goal-b≡gb
    where
      goal-b≡gb : ∀ {b′} → b′ ∈ filter ¿ genesisBlock >ˢ_ ¿¹ (genesisBlock ∷ honestBlockHistory N) → blockPos b′ N < blockPos genesisBlock N
      goal-b≡gb {b′} b′∈[gbₜ>ˢ]gb+hbhN = contradiction b′∈[0>t]gb+hbhN b′∉[0>t]gb+hbhN
        where
          ∄t<0 : filter ¿ (0 >_) ∘ slot ¿¹ (genesisBlock ∷ honestBlockHistory N) ≡ []
          ∄t<0 = L.filter-none _ {xs = genesisBlock ∷ honestBlockHistory N} (L.All.tabulate $ λ {b″} b″∈gb+hbhN → λ ())

          b′∉[0>t]gb+hbhN : b′ ∉ filter ¿ (0 >_) ∘ slot ¿¹ (genesisBlock ∷ honestBlockHistory N)
          b′∉[0>t]gb+hbhN rewrite ∄t<0 = λ ()

          b′∈[0>t]gb+hbhN : b′ ∈ filter ¿ (0 >_) ∘ slot ¿¹ (genesisBlock ∷ honestBlockHistory N)
          b′∈[0>t]gb+hbhN = subst (λ ◆ → b′ ∈ filter ¿ (◆ >_) ∘ slot ¿¹ (genesisBlock ∷ honestBlockHistory N)) genesisBlockSlot b′∈[gbₜ>ˢ]gb+hbhN

  ... | inj₂ b∈hbhN = L.All.tabulate goal-b∈hbhN
    where
      goal-b∈hbhN : ∀ {b′} → b′ ∈ filter ¿ b >ˢ_ ¿¹ (genesisBlock ∷ honestBlockHistory N) → blockPos b′ N < blockPos b N
      goal-b∈hbhN {b′} b′∈[b>ˢ]gb+hbhN with L.Mem.∈-filter⁻ ¿ b >ˢ_ ¿¹ b′∈[b>ˢ]gb+hbhN
      ... | b′∈gb+hbhN , b>ˢb′ with ∈-∷⁻ b′∈gb+hbhN
      ... |   inj₂ b′∈hbhN = L.All.lookup (olderNonGBBlocksHaveSmallerPositions N₀↝⋆N ffN cfN b∈hbhN) b′∈[b>ˢ]hbhN
        where
          b′∈[b>ˢ]hbhN : b′ ∈ filter ¿ b >ˢ_ ¿¹ (honestBlockHistory N)
          b′∈[b>ˢ]hbhN = L.Mem.∈-filter⁺ ¿ b >ˢ_ ¿¹ b′∈hbhN b>ˢb′
      ... |   inj₁ b′≡gb rewrite b′≡gb | cfb[gb]≡[gb] {blockHistory N} = honestBlockPosition>GBPosition (Star⇒Starʳ N₀↝⋆N) ffN cfN b∈hbhN
        where
          bₜ>0 : b .slot > 0
          bₜ>0 = subst (b .slot >_) genesisBlockSlot b>ˢb′

          open RTC; open Starʳ

          honestBlockPosition>GBPosition : ∀ {N : GlobalState} {b : Block} →
              N₀ ↝⋆ʳ N
            → ForgingFree N
            → CollisionFree N
            → b ∈ honestBlockHistory N
            → 1 < blockPos b N
          honestBlockPosition>GBPosition {N} {b} (_◅ʳ_ {j = N′} N₀↝⋆ʳN′ N′↝N) ffN cfN b∈hbhN = goal N′↝N
            where
              N₀↝⋆N′ : N₀ ↝⋆ N′
              N₀↝⋆N′ = Starʳ⇒Star N₀↝⋆ʳN′

              ffN′ : ForgingFree N′
              ffN′ = ForgingFreePrev (N′↝N ◅ ε) ffN

              cfN′ : CollisionFree N′
              cfN′ = CollisionFreePrev (N′↝N ◅ ε) cfN

              N′↝⋆N : N′ ↝⋆ N
              N′↝⋆N = Starʳ⇒Star (εʳ ◅ʳ N′↝N)

              ih : b ∈ honestBlockHistory N′ → 1 < blockPos b N′
              ih b∈hbhN′ = honestBlockPosition>GBPosition N₀↝⋆ʳN′ ffN′ cfN′ b∈hbhN′

              goal : N′ ↝ N → 1 < blockPos b N
              goal N′↝N
                with N′↝N
              ... | deliverMsgs {N′ = N″} N′Ready N′—[eoN′]↓→∗N″ = subst ((1 <_) ∘ ∣_∣) cfbhN′≡cfbhN (ih b∈hbhN′)
                where
                  hbhPres : honestBlockHistory N′ ≡ˢ honestBlockHistory N
                  hbhPres = honestBlockHistoryPreservation-↓∗ N₀↝⋆N′ N′—[eoN′]↓→∗N″ ffN N′Ready

                  b∈hbhN′ : b ∈ honestBlockHistory N′
                  b∈hbhN′ = ≡ˢ⇒⊆×⊇ hbhPres .proj₂ b∈hbhN

                  cfbhN′≡cfbhN : chainFromBlock b (blockHistory N′) ≡ chainFromBlock b (blockHistory N)
                  cfbhN′≡cfbhN = cfbHbhPres {N} {N′} {b} N₀↝⋆N′ N′↝N ffN cfN b∈hbhN hbhPres

              ... | makeBlock {N′} {N″} N′MsgsDelivered N′—[eoN′]↑→∗N″ = makeBlockGoal (N′ .execOrder) N″↷↑N″[bM] cfN b∈hbhN uniqEoN′ (—[]→∗⇒—[]→∗ʳ N′—[eoN′]↑→∗N″)
                where
                  N″↷↑N″[bM] : N″ ↷↑ record N″ { progress = blockMade }
                  N″↷↑N″[bM] = progress↑ ↷↑-refl

                  uniqEoN′ : Unique (N′ .execOrder)
                  uniqEoN′ = execOrderUniqueness N₀↝⋆N′

                  makeBlockGoal : ∀ {N″} ps →
                      N″ ↷↑ N
                    → CollisionFree N″
                    → b ∈ honestBlockHistory N″
                    → Unique ps
                    → _ ⊢ N′ —[ ps ]↑→∗ʳ N″
                    → 1 < blockPos b N″
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

                      ih′ : b ∈ honestBlockHistory N‴ → 1 < blockPos b N‴
                      ih′ b∈hbhN‴ = makeBlockGoal {N‴} ps′ (blockMaking↑ ts prfN) cfN‴ b∈hbhN‴ ps′Uniq ts⋆

                      step : _ ⊢ N‴ —[ p′ ]↑→ N″ → 1 < blockPos b N″
                      step (unknownParty↑ _) = ih′ b∈hbhN″
                      step (honestParty↑ {ls = ls} lsπ hp′π) with Params.winnerᵈ params {p′} {N‴ .clock}
                      ... | ⁇ (yes isWinner) rewrite lsπ = step-honestParty↑
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

                          cfb≢[] : b ∈ honestBlockHistory N‴ → chainFromBlock b (blockHistory N‴) ≢ []
                          cfb≢[] b∈hbhN‴ = ✓⇒≢[] cfbhN‴✓
                            where
                              cfbhN‴✓ : chainFromBlock b (blockHistory N‴) ✓
                              cfbhN‴✓ = L.All.lookup (honestBlockCfb✓-↑∗ N₀↝⋆N′ N′↝⋆N ffN (—[]→∗ʳ⇒—[]→∗ ts⋆) (blockMaking↑ ts prfN) ps′Uniq cfN‴) b∈hbhN‴

                          step-honestParty↑ : 1 < ∣ chainFromBlock b (nb ∷ blockHistory N‴) ∣
                          step-honestParty↑  with ∈-∷⁻ b∈nb∷hbhN‴
                          ... | inj₂ b∈hbhN‴ = subst ((1 <_) ∘ ∣_∣) cfbhN‴≡cfbhnb+N‴ (ih′ b∈hbhN‴)
                            where
                              cfbhN‴≡cfbhnb+N‴ : chainFromBlock b (blockHistory N‴) ≡ chainFromBlock b (nb ∷ blockHistory N‴)
                              cfbhN‴≡cfbhnb+N‴ = subsetCfbPreservation cfπ bhπ (cfb≢[] b∈hbhN‴)
                          ... | inj₁ b≡nb rewrite b≡nb with chainFromNewBlock N₀↝⋆N′ ts⋆ isWinner p′∉ps′ lsπ hp′π cfN″
                          ... |   cfbIsNb∷Best , _ = subst ((1 <_) ∘ ∣_∣) (sym cfbIsNb∷Best) 1<∣nb+best∣
                            where
                              1<∣nb+best∣ : 1 < suc ∣ best ∣
                              1<∣nb+best∣ rewrite clockPreservation-↑∗ (—[]→∗ʳ⇒—[]→∗ ts⋆) = Nat.+-monoʳ-< 1 0<∣bcN′∣
                                where
                                  0<∣bcN′∣ : 0 < ∣ bestChain (N′ .clock ∸ 1) (ls .tree) ∣
                                  0<∣bcN′∣ = Nat.n≢0⇒n>0 $ contraposition length0⇒[] $ ✓⇒≢[] $ valid (ls .tree) (N′ .clock ∸ 1)
                      ... | ⁇ (no _) = ih′ b∈hbhN″
                      step (corruptParty↑ _ _) = subst ((1 <_) ∘ ∣_∣) cfbhBcN‴≡cfbhN‴ (ih′ b∈hbhN‴)
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

                          cfb≢[] : chainFromBlock b (blockHistory N‴) ≢ []
                          cfb≢[] = ✓⇒≢[] cfbhN‴✓
                            where
                              cfbhN‴✓ : chainFromBlock b (blockHistory N‴) ✓
                              cfbhN‴✓ = L.All.lookup (honestBlockCfb✓-↑∗ N₀↝⋆N′ N′↝⋆N ffN (—[]→∗ʳ⇒—[]→∗ ts⋆) (blockMaking↑ ts prfN) ps′Uniq cfN‴) b∈hbhN‴

                          cfbhBcN‴≡cfbhN‴ : chainFromBlock b (blockHistory N‴) ≡ chainFromBlock b (blockHistory (broadcastMsgsᶜ mds N‴))
                          cfbhBcN‴≡cfbhN‴ = subsetCfbPreservation cfπ bhπ cfb≢[]
              ... | advanceRound   _                  = ih b∈hbhN
              ... | permuteParties _                  = ih b∈hbhN
              ... | permuteMsgs    _                  = ih b∈hbhN

honestPosPreservation-↓∗ : ∀ {N N′ : GlobalState} {b : Block} →
    N₀ ↝⋆ N
  → _ ⊢ N —[ N .execOrder ]↓→∗ N′
  → ForgingFree N
  → CollisionFree N′
  → b ∈ honestBlockHistory N
  → N .progress ≡ ready
  → blockPos b N ≡ blockPos b N′
honestPosPreservation-↓∗ N₀↝⋆N N—[eoN′]↓→∗N′ ffN cfN′ b∈hbhN NReady = cong ∣_∣ $ honestCfbPreservation-↓∗ N₀↝⋆N N—[eoN′]↓→∗N′ ffN cfN′ b∈hbhN NReady

opaque

  unfolding honestBlockMaking corruptBlockMaking _✓

  -- The following lemma is a central step towards proving the common prefix property.
  superBlockPositions : ∀ {N : GlobalState} →
      N₀ ↝⋆ N
    → CollisionFree N
    → ForgingFree N
-- TODO: Bug reported in https://github.com/agda/agda/issues/7856 and fixed in Agda 2.8.0.
--    → L.All.All
--        (λ where (sb , b) → blockPos sb N ≢ blockPos b N ⊎ sb ≡ b)
--        (L.cartesianProduct (superBlocks N) (honestBlockHistory N))
    → L.All.All
        (λ p → blockPos (p .proj₁) N ≢ blockPos (p .proj₂) N ⊎ p .proj₁ ≡ p .proj₂)
        (L.cartesianProduct (superBlocks N) (honestBlockHistory N))
  superBlockPositions = superBlockPositionsʳ ∘ Star⇒Starʳ
    where
      open RTC; open Starʳ
      superBlockPositionsʳ : ∀ {N : GlobalState} →
          N₀ ↝⋆ʳ N
        → CollisionFree N
        → ForgingFree N
        → L.All.All
            (λ where (sb , b) → blockPos sb N ≢ blockPos b N ⊎ sb ≡ b)
            (L.cartesianProduct (superBlocks N) (honestBlockHistory N))
      superBlockPositionsʳ εʳ cfp ffp = L.All.All.[]
      superBlockPositionsʳ {N} (_◅ʳ_ {j = N′} N₀↝⋆ʳN′ N′↝N) cfN ffN
        with
          ih ← superBlockPositionsʳ N₀↝⋆ʳN′ (CollisionFreePrev (N′↝N ◅ ε) cfN) (ForgingFreePrev (N′↝N ◅ ε) ffN)
        | N′↝N
      ... | deliverMsgs {N′} {N″} N′Ready N′—[eoN′]↓→∗N″ = goal
        where
          ffN′ : ForgingFree N′
          ffN′ = ForgingFreePrev (N′↝N ◅ ε) ffN

          cfpN′ : CollisionFree N′
          cfpN′ = CollisionFreePrev (N′↝N ◅ ε) cfN

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
              ... | inj₁ possb≢posb with blockPosPres (superBlocks⊆honestBlockHistory N sb∈sbsN) | blockPosPres b∈hbhN
              ... |  eqsb | eqb = inj₁ (subst₂ _≢_ eqsb eqb possb≢posb)

      ... | makeBlock {N′} {N″} N′MsgsDelivered N′—[eoN′]↑→∗N″ = goal
        where
          ffN′ : ForgingFree N′
          ffN′ = ForgingFreePrev (N′↝N ◅ ε) ffN

          cfN′ : CollisionFree N′
          cfN′ = CollisionFreePrev (N′↝N ◅ ε) cfN

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
                  sb∈fhbhN′ : sb ∈ filter ((_<? N′ .clock) ∘ slot) (honestBlockHistory N′)
                  sb∈fhbhN′ =
                         sb∈hbhN ∶
                    sb ∈ honestBlockHistory N
                      |> flip (L.Mem.∈-filter⁺ _) sbₜ<Nₜ ∶
                    sb ∈ filter ((_<? N .clock) ∘ slot) (honestBlockHistory N)
                      |> subst _ (clockPreservation-↑∗ N′—[eoN′]↑→∗N″) ∶
                    sb ∈ filter ((_<? N′ .clock) ∘ slot) (honestBlockHistory N)
                      |> ≡ˢ⇒⊆×⊇ (honestBlocksBelowSlotPreservation N₀↝⋆N′ N′↝⋆N ffN) .proj₂ ∶
                    sb ∈ filter ((_<? N′ .clock) ∘ slot) (honestBlockHistory N′)
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

                      ffNᴿ : ForgingFree Nᴿ
                      ffNᴿ = ForgingFreePrev Nᴿ↝⋆N′ ffN′

                      cfNᴿ : CollisionFree Nᴿ
                      cfNᴿ = CollisionFreePrev Nᴿ↝⋆N′ cfN′

                      cfbhNᴿ≢[] : chainFromBlock sb (blockHistory Nᴿ) ≢ []
                      cfbhNᴿ≢[] = ✓⇒≢[] cfbhNᴿ✓
                        where
                          cfbhNᴿ✓ : chainFromBlock sb (blockHistory Nᴿ) ✓
                          cfbhNᴿ✓ = L.All.lookup (L.All.tabulate $ λ {b} → honestBlockCfb✓ N₀↝⋆Nᴿ ffNᴿ cfNᴿ) sb∈hbhNᴿ

                      cfbhNᴿ≡cfbhN′ : chainFromBlock sb (blockHistory Nᴿ) ≡ chainFromBlock sb (blockHistory N′)
                      cfbhNᴿ≡cfbhN′ = subsetCfbPreservation cfbhN′ bhNᴿ⊆bhN′ cfbhNᴿ≢[]
                        where
                          cfbhN′ : BlockListCollisionFree (blockHistory N′)
                          cfbhN′ = BlockListCollisionFree-∷ {blockHistory N′} {genesisBlock} cfN′

                          bhNᴿ⊆bhN′ : blockHistory Nᴿ ⊆ˢ blockHistory N′
                          bhNᴿ⊆bhN′ = blockHistoryPreservation-↝⋆ Nᴿ↝⋆N′

                      cfbhNᴿ≡cfbhN : chainFromBlock sb (blockHistory Nᴿ) ≡ chainFromBlock sb (blockHistory N)
                      cfbhNᴿ≡cfbhN = subsetCfbPreservation cfbhN bhNᴿ⊆bhN cfbhNᴿ≢[]
                        where
                          cfbhN : BlockListCollisionFree (blockHistory N)
                          cfbhN = BlockListCollisionFree-∷ {blockHistory N} {genesisBlock} cfN

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
                        → CollisionFree N*
                        → b ∈ honestBlockHistory N*
                        → Unique ps
                        → _ ⊢ N′ —[ ps ]↑→∗ʳ N*
                        → blockPos sb N ≢ blockPos b N* ⊎ sb ≡ b
                      makeBlockGoal-sbₜ<Nₜ rewrite sym cfbhNᴿ≡cfbhN = makeBlockGoal-sbₜ<Nₜ′
                        where
                          makeBlockGoal-sbₜ<Nₜ′ : ∀ {N*} ps →
                              N* ↷↑ N
                            → CollisionFree N*
                            → b ∈ honestBlockHistory N*
                            → Unique ps
                            → _ ⊢ N′ —[ ps ]↑→∗ʳ N*
                            → blockPos sb Nᴿ ≢ blockPos b N* ⊎ sb ≡ b
                          makeBlockGoal-sbₜ<Nₜ′ {N*} [] _ _ b∈hbhN* _ [] = ih′ b∈hbhN*
                          makeBlockGoal-sbₜ<Nₜ′ {N*} [] _ _ _ _ (_∷ʳ_ {eq = eq} _ _) = contradiction eq []≢∷ʳ
                          makeBlockGoal-sbₜ<Nₜ′ {N*} (p ∷ ps) prfN cfN* b∈hbhN* p∷psUniq (_∷ʳ_ {is = ps′} {i = p′} {s′ = N‴} {eq = eq} ts⋆ ts) = step ts
                            where
                              cfN‴ : CollisionFree N‴
                              cfN‴ = CollisionFreePrev-↑ ts cfN*

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
                                  lsN′ rewrite sym $ localStatePreservation-∉-↑∗ p′∉ps′ (—[]→∗ʳ⇒—[]→∗ ts⋆) = lsπ

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

                                  cfπ : BlockListCollisionFree (nb ∷ blockHistory N‴)
                                  cfπ = BlockListCollisionFree-∷ {nb ∷ blockHistory N‴} {genesisBlock} cfN*

                                  cfb≢[] : b ∈ honestBlockHistory N‴ → chainFromBlock b (blockHistory N‴) ≢ []
                                  cfb≢[] b∈hbhN‴ = ✓⇒≢[] cfbhN‴✓
                                    where
                                      cfbhN‴✓ : chainFromBlock b (blockHistory N‴) ✓
                                      cfbhN‴✓ = L.All.lookup (honestBlockCfb✓-↑∗ N₀↝⋆N′ N′↝⋆N ffN (—[]→∗ʳ⇒—[]→∗ ts⋆) (blockMaking↑ ts prfN) ps′Uniq cfN‴) b∈hbhN‴

                                  step-honestParty↑ : blockPos sb Nᴿ ≢ ∣ chainFromBlock b (nb ∷ blockHistory N‴) ∣ ⊎ sb ≡ b
                                  step-honestParty↑ with ∈-∷⁻ b∈nb∷hbhN‴ | b ≟ nb
                                  ... | inj₁ b≡nb    | no b≢nb = contradiction b≡nb b≢nb
                                  ... | inj₂ b∈hbhN‴ | no _ rewrite sym $ subsetCfbPreservation cfπ bhπ (cfb≢[] b∈hbhN‴) = ih* b∈hbhN‴
                                  ... | _            | yes b≡nb rewrite b≡nb
                                    with chainFromNewBlock N₀↝⋆N′ ts⋆ isWinner p′∉ps′ lsπ hp′π cfN*
                                  ... |   cfbIsNb∷Best , _ = subst (λ ◆ → blockPos sb Nᴿ ≢ ∣ ◆ ∣ ⊎ sb ≡ nb) (sym cfbIsNb∷Best) possb
                                    where
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
                                                      π₁ = L.All.lookup (cfbInHonestTree N₀↝⋆Nᴿ ffNᴿ cfNᴿ) sb∈hbhNᴿ

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
                                                          b′>ˢc = ∷-DecreasingSlots ds[b′∷c] .proj₂

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

                                  cfπ : BlockListCollisionFree (blockHistory (broadcastMsgsᶜ mds N‴))
                                  cfπ = BlockListCollisionFree-∷ {blockHistory (broadcastMsgsᶜ mds N‴)} {genesisBlock} cfN*

                                  cfb≢[] : chainFromBlock b (blockHistory N‴) ≢ []
                                  cfb≢[] = ✓⇒≢[] cfbhN‴✓
                                    where
                                      cfbhN‴✓ : chainFromBlock b (blockHistory N‴) ✓
                                      cfbhN‴✓ = L.All.lookup (honestBlockCfb✓-↑∗ N₀↝⋆N′ N′↝⋆N ffN (—[]→∗ʳ⇒—[]→∗ ts⋆) (blockMaking↑ ts prfN) ps′Uniq cfN‴) b∈hbhN‴

                                  step-corruptParty↑ : blockPos sb Nᴿ ≢ blockPos b (broadcastMsgsᶜ mds N‴) ⊎ sb ≡ b
                                  step-corruptParty↑ rewrite sym $ subsetCfbPreservation cfπ bhπ cfb≢[] = ih* b∈hbhN‴

              ... | inj₂ sbₜ≡Nₜ = goal-sbₜ≡Nₜ
                where
                  N″↷↑N″[bM] : N″ ↷↑ record N″ { progress = blockMade }
                  N″↷↑N″[bM] = progress↑ (↷↑-refl)

                  uniqEoN′ : Unique (N′ .execOrder)
                  uniqEoN′ = execOrderUniqueness N₀↝⋆N′

                  sbIsHonest : Honest (sb .pid)
                  sbIsHonest = ∈-superBlocks⁻ {N} sb∈sbsN .proj₂ .proj₁

                  sbHasSuperSlot : SuperSlot (sb .slot)
                  sbHasSuperSlot = ∈-superBlocks⁻ {N} sb∈sbsN .proj₂ .proj₂

                  goal-sbₜ≡Nₜ : blockPos sb N ≢ blockPos b N ⊎ sb ≡ b
                  goal-sbₜ≡Nₜ = makeBlockGoal-sbₜ≡Nₜ (N′ .execOrder) (allPartiesHaveLocalState N₀↝⋆N′) eoSb N″↷↑N″[bM] cfN (L.SubS.filter-⊆ _ _ sb∈hbhN) b∈hbhN uniqEoN′ (—[]→∗⇒—[]→∗ʳ N′—[eoN′]↑→∗N″)
                    where
                      eoSb : length (filter (λ p → ¿ winner p (sb .slot) × Honest p ¿) (N′ .execOrder)) ≡ 1
                      eoSb = trans (sym $ ↭-length (filter-↭ _ (execOrderPreservation-↭ N₀↝⋆N′))) sbHasSuperSlot

                      makeBlockGoal-sbₜ≡Nₜ : ∀ {N*} ps →
                          L.All.All (_hasStateIn N′) ps
                        → length (filter (λ p → ¿ winner p (sb .slot) × Honest p ¿) ps) ≡ 1
                        → N* ↷↑ N
                        → CollisionFree N*
                        → sb ∈ blockHistory N*
                        → b ∈ honestBlockHistory N*
                        → Unique ps
                        → _ ⊢ N′ —[ ps ]↑→∗ʳ N*
                        → blockPos sb N* ≢ blockPos b N* ⊎ sb ≡ b
                      makeBlockGoal-sbₜ≡Nₜ {N*} [] _ p∷psSb _ _ _ _ _ = contradiction p∷psSb Nat.0≢1+n
                      makeBlockGoal-sbₜ≡Nₜ {N*} (p ∷ ps) p∷psLss p∷psSb prfN cfN* sb∈bhN* b∈hbhN* p∷psUniq (_∷ʳ_ {is = ps′} {i = p′} {s′ = N‴} {eq = eq} ts⋆ ts) = step ts
                        where
                          cfN‴ : CollisionFree N‴
                          cfN‴ = CollisionFreePrev-↑ ts cfN*

                          ps′∷ʳp′Uniq : Unique (ps′ L.∷ʳ p′)
                          ps′∷ʳp′Uniq = subst Unique eq p∷psUniq

                          ps′Uniq : Unique ps′
                          ps′Uniq = headʳ ps′∷ʳp′Uniq

                          p′∉ps′ : p′ ∉ ps′
                          p′∉ps′ = Unique[xs∷ʳx]⇒x∉xs ps′∷ʳp′Uniq

                          ps′∷ʳp′Sb : length (filter (λ p → ¿ winner p (sb .slot) × Honest p ¿) (ps′ L.∷ʳ p′)) ≡ 1
                          ps′∷ʳp′Sb = subst (λ ◆ → length (filter (λ p → ¿ winner p (sb .slot) × Honest p ¿) ◆) ≡ 1) eq p∷psSb

                          ps′∷ʳp′Lss : L.All.All (_hasStateIn N′) (ps′ L.∷ʳ p′)
                          ps′∷ʳp′Lss = subst (L.All.All (_hasStateIn N′)) eq p∷psLss

                          ps′Lss : L.All.All (_hasStateIn N′) ps′
                          ps′Lss = L.All.∷ʳ⁻ ps′∷ʳp′Lss .proj₁

                          N‴ₜ≡N′ₜ : N‴ .clock ≡ N′ .clock
                          N‴ₜ≡N′ₜ = clockPreservation-↑∗ (—[]→∗ʳ⇒—[]→∗ ts⋆)

                          sbₜ≡N‴ₜ : sb .slot ≡ N‴ .clock
                          sbₜ≡N‴ₜ rewrite sbₜ≡Nₜ | N″ₜ≡N′ₜ | sym N‴ₜ≡N′ₜ = refl

                          sbₜ≡N′ₜ : sb .slot ≡ N′ .clock
                          sbₜ≡N′ₜ rewrite sbₜ≡N‴ₜ | N‴ₜ≡N′ₜ = refl

                          ih* :
                              length (filter (λ p → ¿ winner p (sb .slot) × Honest p ¿) ps′) ≡ 1
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
                              lsN′≡lsN* = sym $ localStatePreservation-∉-↑∗ p′∉ps′ (—[]→∗ʳ⇒—[]→∗ ts⋆)
                          step (honestParty↑ {ls = ls} lsπ hp′π) with Params.winnerᵈ params {p′} {N‴ .clock}
                          ... | ⁇ (no ¬isWinner) = ih* ps′Sb sb∈bhN* b∈hbhN*
                            where
                              ¬honestWinner : ¬ (winner p′ (sb .slot) × Honest p′)
                              ¬honestWinner rewrite sbₜ≡N‴ₜ = dec-de-morgan₂ (inj₁ ¬isWinner)

                              ps′Sb : length (filter (λ p → ¿ winner p (sb .slot) × Honest p ¿) ps′) ≡ 1
                              ps′Sb rewrite sym $ filter-rejectʳ (λ p → ¿ winner p (sb .slot) × Honest p ¿) {xs = ps′} ¬honestWinner = ps′∷ʳp′Sb
                          ... | ⁇ (yes isWinner) = step-honestWinner↑
                            where
                              honestWinner : winner p′ (N′ .clock) × Honest p′
                              honestWinner rewrite N‴ₜ≡N′ₜ = isWinner , hp′π

                              ps′Sb : length (filter (λ p → ¿ winner p (N′ .clock) × Honest p ¿) ps′) ≡ 0
                              ps′Sb = Nat.suc-injective ps′Sb′
                                where
                                  ps′Sb′ : suc (length (filter (λ p → ¿ winner p (N′ .clock) × Honest p ¿) ps′)) ≡ 1
                                  ps′Sb′ = begin
                                    suc (length (filter (λ p → ¿ winner p (N′ .clock) × Honest p ¿) ps′))
                                      ≡⟨ Nat.+-comm _ 1 ⟨
                                    length (filter (λ p → ¿ winner p (N′ .clock) × Honest p ¿) ps′) + 1
                                      ≡⟨ L.length-++ (filter (λ p → ¿ winner p (N′ .clock) × Honest p ¿) ps′) {[ p′ ]} ⟨
                                    length (filter (λ p → ¿ winner p (N′ .clock) × Honest p ¿) ps′ L.∷ʳ p′)
                                      ≡⟨ cong length $ filter-acceptʳ (λ p → ¿ winner p (N′ .clock) × Honest p ¿) {xs = ps′} honestWinner ⟨
                                    length (filter (λ p → ¿ winner p (N′ .clock) × Honest p ¿) (ps′ L.∷ʳ p′))
                                      ≡⟨ subst _ sbₜ≡N′ₜ ps′∷ʳp′Sb ⟩
                                    1 ∎
                                    where open ≡-Reasoning

                              lsN′ : N′ .states ⁉ p′ ≡ just ls
                              lsN′ rewrite sym $ localStatePreservation-∉-↑∗ p′∉ps′ (—[]→∗ʳ⇒—[]→∗ ts⋆) = lsπ

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
                                      L.All.All (_hasStateIn N′) ps′
                                    → Unique ps′
                                    → N** ↷↑ N
                                    → length (filter (λ p → ¿ winner p (N′ .clock) × Honest p ¿) ps′) ≡ 0
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

                                      ps″∷ʳp″Lss : L.All.All (_hasStateIn N′) (ps″ L.∷ʳ p″)
                                      ps″∷ʳp″Lss = subst (L.All.All (_hasStateIn N′)) eq p∷psLss

                                      ps″Lss : L.All.All (_hasStateIn N′) ps″
                                      ps″Lss = L.All.∷ʳ⁻ ps″∷ʳp″Lss .proj₁

                                      ps″∷ʳp″Sb : length (filter (λ p → ¿ winner p (N′ .clock) × Honest p ¿) (ps″ L.∷ʳ p″)) ≡ 0
                                      ps″∷ʳp″Sb = subst (λ ◆ → length (filter (λ p → ¿ winner p (N′ .clock) × Honest p ¿) ◆) ≡ 0) eq p∷psSb

                                      N⁗ₜ≡N′ₜ : N⁗ .clock ≡ N′ .clock
                                      N⁗ₜ≡N′ₜ = clockPreservation-↑∗ (—[]→∗ʳ⇒—[]→∗ ts⋆′)

                                      ih** :
                                          length (filter (λ p → ¿ winner p (N′ .clock) × Honest p ¿) ps″) ≡ 0
                                        → honestBlockHistory N′ ≡ˢ honestBlockHistory N⁗
                                      ih** ps″Sb = hbhN′≡hbhN‴† ps″ ps″Lss ps″Uniq (blockMaking↑ ts′ prfN**) ps″Sb ts⋆′

                                      step† : _ ⊢ N⁗ —[ p″ ]↑→ N** → honestBlockHistory N′ ≡ˢ honestBlockHistory N**
                                      step† (unknownParty↑ ls≡◇) = contradiction ls≡◇ (subst (_≢ nothing) lsN′≡lsN** ls≢◇)
                                        where
                                          ls≢◇ : N′ .states ⁉ p″ ≢ nothing
                                          ls≢◇ ls≡◇ = contradiction (subst M.Is-just ls≡◇ (L.All.∷ʳ⁻ ps″∷ʳp″Lss .proj₂)) λ()

                                          lsN′≡lsN** : N′ .states ⁉ p″ ≡ N** .states ⁉ p″
                                          lsN′≡lsN** = sym $ localStatePreservation-∉-↑∗ p″∉ps″ (—[]→∗ʳ⇒—[]→∗ ts⋆′)
                                      step† (honestParty↑ {ls = ls} lsπ hp″π) with Params.winnerᵈ params {p″} {N⁗ .clock}
                                      ... | ⁇ (no ¬isWinner) = ih** ps″Sb
                                        where
                                          ¬p″HonestWinner : ¬ (winner p″ (N′ .clock) × Honest p″)
                                          ¬p″HonestWinner rewrite N⁗ₜ≡N′ₜ = dec-de-morgan₂ (inj₁ ¬isWinner)

                                          ps″Sb : length (filter (λ p → ¿ winner p (N′ .clock) × Honest p ¿) ps″) ≡ 0
                                          ps″Sb rewrite sym $ filter-rejectʳ (λ p → ¿ winner p (N′ .clock) × Honest p ¿) {xs = ps″} ¬p″HonestWinner = ps″∷ʳp″Sb
                                      ... | ⁇ (yes isWinner) = contradiction ps″∷ʳp″Sb (Nat.n>0⇒n≢0 ps″∷ʳp″Sb>0)
                                        where
                                          p″HonestWinner : winner p″ (N′ .clock) × Honest p″
                                          p″HonestWinner rewrite N⁗ₜ≡N′ₜ = isWinner , hp″π

                                          ps″∷ʳp″Sb>0 : length (filter (λ p → ¿ winner p (N′ .clock) × Honest p ¿) (ps″ L.∷ʳ p″)) > 0
                                          ps″∷ʳp″Sb>0 = begin-strict
                                            0 <⟨ Nat.0<1+n {_} ⟩
                                            suc (length (filter (λ p → ¿ winner p (N′ .clock) × Honest p ¿) ps″))
                                              ≡⟨ Nat.+-comm _ 1 ⟨
                                            length (filter (λ p → ¿ winner p (N′ .clock) × Honest p ¿) ps″) + 1
                                              ≡⟨ L.length-++ (filter (λ p → ¿ winner p (N′ .clock) × Honest p ¿) ps″) {[ p″ ]} ⟨
                                            length (filter (λ p → ¿ winner p (N′ .clock) × Honest p ¿) ps″ L.∷ʳ p″)
                                              ≡⟨ cong length $ filter-acceptʳ (λ p → ¿ winner p (N′ .clock) × Honest p ¿) {xs = ps″} p″HonestWinner ⟨
                                            length (filter (λ p → ¿ winner p (N′ .clock) × Honest p ¿) (ps″ L.∷ʳ p″)) ∎
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

                                          ¬p″HonestWinner : ¬ (winner p″ (N′ .clock) × Honest p″)
                                          ¬p″HonestWinner = dec-de-morgan₂ (inj₂ (corrupt⇒¬honest cp″π))

                                          ps″Sb : length (filter (λ p → ¿ winner p (N′ .clock) × Honest p ¿) ps″) ≡ 0
                                          ps″Sb rewrite sym $ filter-rejectʳ (λ p → ¿ winner p (N′ .clock) × Honest p ¿) {xs = ps″} ¬p″HonestWinner = ps″∷ʳp″Sb

                                          eqhs : honestBlockHistory N⁗ ≡ˢ honestBlockHistory (broadcastMsgsᶜ mds N⁗)
                                          eqhs = honestBlockHistoryPreservation-broadcastMsgsᶜ {N⁗} {mds} sub

                              step-honestWinner↑ : ∣ chainFromBlock sb (nb ∷ blockHistory N‴) ∣ ≢ ∣ chainFromBlock b (nb ∷ blockHistory N‴) ∣ ⊎ sb ≡ b
                              step-honestWinner↑ with ∈-∷⁻ sb∈nb∷bhN‴
                              ... | inj₂ sb∈bhN‴ = contradiction sbₜ≡N′ₜ (Nat.<⇒≢ sbₜ<N′ₜ)
                                where
                                  sb∈hbhN‴ : sb ∈ honestBlockHistory N‴
                                  sb∈hbhN‴ = L.Mem.∈-filter⁺ ¿ HonestBlock ¿¹ sb∈bhN‴ sbIsHonest

                                  sbₜ<N′ₜ : sb .slot < N′ .clock
                                  sbₜ<N′ₜ = L.All.lookup (All-resp-≡ˢ hbhN′≡hbhN‴ (noPrematureHonestBlocksAt↓ N₀↝⋆N′ ffN′ N′MsgsDelivered)) sb∈hbhN‴
                              ... | inj₁ sb≡nb with ∈-∷⁻ b∈nb∷hbhN‴
                              ... |   inj₁ b≡nb = inj₂ (trans sb≡nb (sym b≡nb))
                              ... |   inj₂ b∈hbhN‴ rewrite sb≡nb
                                with chainFromNewBlock N₀↝⋆N′ ts⋆ isWinner p′∉ps′ lsπ hp′π cfN*
                              ... |     cfbIsNb∷Best , _ = subst (λ ◆ → ∣ ◆ ∣ ≢ ∣ chainFromBlock b (nb ∷ blockHistory N‴) ∣ ⊎ nb ≡ b) (sym cfbIsNb∷Best) step-honestWinner↑′
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

                                      ffNᴿ : ForgingFree Nᴿ
                                      ffNᴿ = ForgingFreePrev Nᴿ↝⋆N′ ffN′

                                      cfNᴿ : CollisionFree Nᴿ
                                      cfNᴿ = CollisionFreePrev Nᴿ↝⋆N′ cfN′

                                      bhNᴿ⊆nb∷bhN‴ : blockHistory Nᴿ ⊆ˢ nb ∷ blockHistory N‴
                                      bhNᴿ⊆nb∷bhN‴ = L.SubS.⊆-trans (blockHistoryPreservation-↝⋆ Nᴿ↝⋆N′) (L.SubS.⊆-trans (blockHistoryPreservation-↑∗ (—[]→∗ʳ⇒—[]→∗ ts⋆)) (L.SubS.xs⊆x∷xs _ _))

                                      cfπ : BlockListCollisionFree (nb ∷ blockHistory N‴)
                                      cfπ = BlockListCollisionFree-∷ {nb ∷ blockHistory N‴} {genesisBlock} cfN*

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
                                                      π₁ = L.All.lookup (cfbInHonestTree N₀↝⋆Nᴿ ffNᴿ cfNᴿ) b∈hbhNᴿ

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
                                                          b′>ˢc = ∷-DecreasingSlots ds[b′∷c] .proj₂

                                                          b>ˢb″ : b″ ∈ c → b >ˢ b″
                                                          b>ˢb″ rewrite sym b′≡b = L.All.lookup b′>ˢc

                                                      bₜ≤N′ₜ-1 : b .slot ≤ N′ .clock ∸ 1
                                                      bₜ≤N′ₜ-1 rewrite sym (Nᴿ↝⋆⟨0⟩N′ .proj₂) = Nat.<⇒≤pred bₜ<Nᴿₜ
                                                        where
                                                          bₜ<Nᴿₜ : b .slot < Nᴿ .clock
                                                          bₜ<Nᴿₜ = L.All.lookup (noPrematureHonestBlocksAtReady N₀↝⋆Nᴿ ffNᴿ NᴿReady) b∈hbhNᴿ

                                          ∣c∣≢∣best∣ : ∣ c ∣ ≢ ∣ best ∣
                                          ∣c∣≢∣best∣ p = contradiction (subst (∣ b′ ∷ c ∣ ≤_) (sym p) ∣b′∷c∣≤∣best∣) Nat.1+n≰n
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
                                  hbhᶜN‴≡hbhN‴† {(m , _) ∷ mds} sub with ¿ HonestBlock (projBlock m) ¿
                                  ... | yes hbm = ⊆×⊇⇒≡ˢ ⊆π ⊇π
                                    where
                                      ⊆π : projBlock m ∷ honestBlockHistory (broadcastMsgsᶜ mds N‴) ⊆ˢ honestBlockHistory N‴
                                      ⊆π {b} b∈∷ with ∈-∷⁻ b∈∷
                                      ... | inj₁ b≡bₘ rewrite b≡bₘ = ∷⊆⇒∈ sub
                                      ... | inj₂ b∈hbhᶜN‴ = ≡ˢ⇒⊆×⊇ (hbhᶜN‴≡hbhN‴† {mds} (∷-⊆ sub)) .proj₁ b∈hbhᶜN‴

                                      ⊇π : honestBlockHistory N‴ ⊆ˢ projBlock m ∷ honestBlockHistory (broadcastMsgsᶜ mds N‴)
                                      ⊇π = ∷-⊆⁺ (≡ˢ⇒⊆×⊇ (hbhᶜN‴≡hbhN‴† {mds} (∷-⊆ sub)) .proj₂)
                                  ... | no _ = hbhᶜN‴≡hbhN‴† {mds} sub

                              ¬p′HonestWinner : ¬ (winner p′ (sb .slot) × Honest p′)
                              ¬p′HonestWinner = dec-de-morgan₂ (inj₂ (corrupt⇒¬honest cp′π))

                              ps′Sb : length (filter (λ p → ¿ winner p (sb .slot) × Honest p ¿) ps′) ≡ 1
                              ps′Sb rewrite sym $ filter-rejectʳ (λ p → ¿ winner p (sb .slot) × Honest p ¿) {xs = ps′} ¬p′HonestWinner = ps′∷ʳp′Sb

                              sb∈hbhN* : sb ∈ honestBlockHistory (broadcastMsgsᶜ mds N‴)
                              sb∈hbhN* = L.Mem.∈-filter⁺ ¿ HonestBlock ¿¹ sb∈bhN* sbIsHonest

                              sb∈hbhN‴ : sb ∈ honestBlockHistory N‴
                              sb∈hbhN‴ = ≡ˢ⇒⊆×⊇ hbhᶜN‴≡hbhN‴ .proj₁ sb∈hbhN*

                              sb∈bhN‴ : sb ∈ blockHistory N‴
                              sb∈bhN‴ = L.Mem.∈-filter⁻ _ {xs = blockHistory N‴} sb∈hbhN‴ .proj₁

                              b∈hbhN‴ : b ∈ honestBlockHistory N‴
                              b∈hbhN‴ = ≡ˢ⇒⊆×⊇ hbhᶜN‴≡hbhN‴ .proj₁ b∈hbhN*

                              bhπ : blockHistory N‴ ⊆ˢ blockHistory (broadcastMsgsᶜ mds N‴)
                              bhπ  = blockHistoryPreservation-broadcastMsgsᶜ mds N‴

                              cfπ : BlockListCollisionFree (blockHistory (broadcastMsgsᶜ mds N‴))
                              cfπ = BlockListCollisionFree-∷ {blockHistory (broadcastMsgsᶜ mds N‴)} {genesisBlock} cfN*

                              cfbhN‴≢[] : ∀ {b′} → b′ ∈ honestBlockHistory N‴ → chainFromBlock b′ (blockHistory N‴) ≢ []
                              cfbhN‴≢[] {b′} b′∈hbhN‴ = ✓⇒≢[] cfbhN‴✓
                                where
                                  cfbhN‴✓ : chainFromBlock b′ (blockHistory N‴) ✓
                                  cfbhN‴✓ = L.All.lookup (honestBlockCfb✓-↑∗ N₀↝⋆N′ N′↝⋆N ffN (—[]→∗ʳ⇒—[]→∗ ts⋆) (blockMaking↑ ts prfN) ps′Uniq cfN‴) b′∈hbhN‴

                              step-corruptParty↑ : blockPos sb (broadcastMsgsᶜ mds N‴) ≢ blockPos b (broadcastMsgsᶜ mds N‴) ⊎ sb ≡ b
                              step-corruptParty↑
                                rewrite
                                    sym $ subsetCfbPreservation cfπ bhπ (cfbhN‴≢[] sb∈hbhN‴)
                                  | sym $ subsetCfbPreservation cfπ bhπ (cfbhN‴≢[] b∈hbhN‴)
                                  = ih* ps′Sb sb∈bhN‴ b∈hbhN‴

      ... | advanceRound   _                  = ih
      ... | permuteParties _                  = ih
      ... | permuteMsgs    _                  = ih

superBlockPositionsUniqueness : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → ForgingFree N
  → CollisionFree N
  → Unique (map (flip blockPos N) (superBlocks N))
superBlockPositionsUniqueness {N} N₀↝⋆N ffN cfN = superBlockPositionsUniqueness′ (superBlockPositions N₀↝⋆N cfN ffN)
  where
    sbs = List Block ∋ L.deduplicate _≟_ (filter ¿ SuperBlock ¿¹ (blockHistory N))
    hbs = List Block ∋ filter ¿ HonestBlock ¿¹ (blockHistory N)

    superBlockPositionsUniqueness′ :
      L.All.All
        (λ{ (b , b′) → flip blockPos N b ≢ flip blockPos N b′ ⊎ b ≡ b′ })
        (L.cartesianProduct sbs hbs)
      →
      Unique (map (flip blockPos N) sbs)
    superBlockPositionsUniqueness′ inj = map⁺-∈ (cartesianProduct⁻ inj-sbs) sbs!
      where
        sbs! : Unique sbs
        sbs! = deduplicate-! _≟_ (filter ¿ SuperBlock ¿¹ (blockHistory N))

        inj-sbs :
          L.All.All
            (λ{ (b , b′) → flip blockPos N b ≡ flip blockPos N b′ → b ≡ b′ })
            (L.cartesianProduct sbs sbs)
        inj-sbs = L.All.map ¬A⊎B⇒A→B $ L.All.anti-mono sbs×sbs⊆sbs×hbs inj
          where
            sbs×sbs⊆sbs×hbs : L.cartesianProduct sbs sbs ⊆ˢ L.cartesianProduct sbs hbs
            sbs×sbs⊆sbs×hbs = cartesianProduct-⊆-Mono {xs = sbs} L.SubS.⊆-refl $
              let open L.SubS.⊆-Reasoning Block in begin
                sbs
                  ⊆⟨ deduplicate-⊆ _ ⟩
                filter ¿ SuperBlock ¿¹ (blockHistory N)
                  ⊆⟨ L.SubS.filter⁺′ ¿ SuperBlock ¿¹ ¿ HonestBlock ¿¹ proj₁ {xs = blockHistory N} L.SubS.⊆-refl ⟩
                hbs ∎
