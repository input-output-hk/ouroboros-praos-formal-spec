open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Safety.CommonPrefix
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Prelude.AssocList.Properties.Ext using (set-⁉)
open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot)
open import Protocol.Crypto ⦃ params ⦄ using (Hashable); open Hashable ⦃ ... ⦄
open import Protocol.Block ⦃ params ⦄
open import Protocol.Chain ⦃ params ⦄
open import Protocol.Message ⦃ params ⦄
open import Protocol.Network ⦃ params ⦄; open Envelope
open import Protocol.TreeType ⦃ params ⦄
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.ForgingFree ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.CollisionFree ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.SuperBlocks ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Safety ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Safety.SingleRoundCommonPrefix ⦃ params ⦄ ⦃ assumptions ⦄
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Ext using (Starʳ)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.Ext using (Star⇒Starʳ; Starʳ⇒Star)
open import Data.Nat.Base using (>-nonZero)
open import Data.Nat.Properties using (≤-refl; ≤-trans; *-monoʳ-≤; m≤n⇒m≤1+n; +-suc; +-identityʳ; n≮n; n≤1+n; module ≤-Reasoning)
open import Data.Nat.Properties.Ext using (pred[n]<n)
open import Data.Maybe.Properties.Ext using (Is-just⇒to-witness; ≡just⇒Is-just)
open import Data.List.Relation.Binary.Permutation.Propositional using (↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∈-resp-↭)
open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_; ≡ˢ⇒⊆×⊇)
open import Data.List.Relation.Binary.Subset.Propositional.Properties.Ext using (++⁻ˡ; ++-meet)

commonPrefix : ∀ {N₁ N₂ : GlobalState} {k : Slot} →
    N₀ ↝⋆ N₁
  → N₁ ↝⋆ N₂
  → ForgingFree N₂
  → CollisionFree N₂
  → ∀ {p₁ p₂ : Party} {ls₁ ls₂ : LocalState}
  → Honest p₁
  → Honest p₂
  → N₁ .states ⁉ p₁ ≡ just ls₁
  → N₂ .states ⁉ p₂ ≡ just ls₂
  → let bc₁ = bestChain (N₁ .clock ∸ 1) (ls₁ .tree)
        bc₂ = bestChain (N₂ .clock ∸ 1) (ls₂ .tree)
    in prune k bc₁ ⪯ bc₂
       ⊎
       ∃₂[ sl′ , sl″ ]
           sl′ ≤ k
         × N₁ .clock ≤ sl″
         × sl″ ≤ N₂ .clock
         × length (superSlotsInRange (sl′ + 1) (sl″ ∸ 1))
           ≤
           2 * length (corruptSlotsInRange (sl′ + 1) (sl″ + 1))
commonPrefix {N₁} {N₂} {k} N₀↝⋆N₁ N₁↝⋆N₂ ffN₂ cfN₂ {p₁} {p₂} {ls₁} {ls₂} hp₁ hp₂ lsp₁ lsp₂ = commonPrefixʳ {N₁} {N₂} {k} N₀↝⋆N₁ (Star⇒Starʳ N₁↝⋆N₂) ffN₂ cfN₂ {p₁} {p₂} {ls₁} {ls₂} hp₁ hp₂ lsp₁ lsp₂
  where
    open RTC; open Starʳ
    commonPrefixʳ : ∀ {N₁ N₂ : GlobalState} {k : Slot} →
        N₀ ↝⋆ N₁
      → N₁ ↝⋆ʳ N₂
      → ForgingFree N₂
      → CollisionFree N₂
      → ∀ {p₁ p₂ : Party} {ls₁ ls₂ : LocalState}
      → Honest p₁
      → Honest p₂
      → N₁ .states ⁉ p₁ ≡ just ls₁
      → N₂ .states ⁉ p₂ ≡ just ls₂
      → let bc₁ = bestChain (N₁ .clock ∸ 1) (ls₁ .tree)
            bc₂ = bestChain (N₂ .clock ∸ 1) (ls₂ .tree)
        in prune k bc₁ ⪯ bc₂
           ⊎
           ∃₂[ sl′ , sl″ ]
               sl′ ≤ k
             × N₁ .clock ≤ sl″
             × sl″ ≤ N₂ .clock
             × length (superSlotsInRange (sl′ + 1) (sl″ ∸ 1))
               ≤
               2 * length (corruptSlotsInRange (sl′ + 1) (sl″ + 1))
    commonPrefixʳ {N₁ = N} {k = k} N₀↝⋆N εʳ ffN cfN {p₁} {p₂} {ls₁} {ls₂} hp₁ hp₂ lsp₁ lsp₂
      with singleRoundCommonPrefix {N} {k} N₀↝⋆N ffN cfN {p₁} {p₂} {ls₁} {ls₂} hp₁ hp₂ lsp₁ lsp₂
    ... | inj₁ bc₁⪯bc₂ = inj₁ bc₁⪯bc₂
    ... | inj₂ (sl* , sl*≤k , prf) = inj₂ (sl* , N .clock , sl*≤k , ≤-refl , ≤-refl , ≤-trans prf (*-monoʳ-≤ 2 (slotsInRange-≤-+ ¿ CorruptSlot ¿¹ (sl* + 1) (N .clock) 1)))
    commonPrefixʳ {N₁} {N₂} {k} N₀↝⋆N₁ N₁↝⋆ʳN₂@(_◅ʳ_ {j = N′} N₁↝⋆ʳN′ N′↝N₂) ffN₂ cfN₂ {p₁} {p₂} {ls₁} {ls₂} hp₁ hp₂ lsp₁ lsp₂ = step N′↝N₂
      where
        ffN′ : ForgingFree N′
        ffN′ = ForgingFreePrev (N′↝N₂ ◅ ε) ffN₂

        cfN′ : CollisionFree N′
        cfN′ = CollisionFreePrev (N′↝N₂ ◅ ε) cfN₂

        N₀↝⋆N′ : N₀ ↝⋆ N′
        N₀↝⋆N′ = N₀↝⋆N₁ ◅◅ Starʳ⇒Star N₁↝⋆ʳN′

        Is-just-lsp₂N′ : M.Is-just (N′ .states ⁉ p₂)
        Is-just-lsp₂N′ = L.All.lookup (allPartiesHaveLocalState N₀↝⋆N′) p₂∈N′
          where
            p₂∈N′ : p₂ ∈ N′ .execOrder
            p₂∈N′ = ∈-resp-↭ (↭-sym (execOrderPreservation-↭-↝ N′↝N₂)) p₂∈N₂
              where
                N₀↝⋆N₂ : N₀ ↝⋆ N₂
                N₀↝⋆N₂ = N₀↝⋆N₁ ◅◅ Starʳ⇒Star N₁↝⋆ʳN₂

                p₂∈N₂ : p₂ ∈ N₂ .execOrder
                p₂∈N₂ = hasState⇒∈execOrder N₀↝⋆N₂ (≡just⇒Is-just lsp₂)

        ls₂′ = LocalState ∋ M.to-witness Is-just-lsp₂N′

        lsp₂N′ : N′ .states ⁉ p₂ ≡ just ls₂′
        lsp₂N′ = Is-just⇒to-witness Is-just-lsp₂N′

        bc₁      = Chain ∋ bestChain (N₁ .clock ∸ 1) (ls₁  .tree)
        bc₂      = Chain ∋ bestChain (N₂ .clock ∸ 1) (ls₂  .tree)
        bcN′ls₂  = Chain ∋ bestChain (N′ .clock ∸ 1) (ls₂  .tree)
        bcN′ls₂′ = Chain ∋ bestChain (N′ .clock ∸ 1) (ls₂′ .tree)

        bc₂✓ : bc₂ ✓
        bc₂✓ = valid (ls₂ .tree) (N₂ .clock ∸ 1)

        bcN′ls₂✓ : bcN′ls₂ ✓
        bcN′ls₂✓ = valid (ls₂ .tree) (N′ .clock ∸ 1)

        bcN′ls₂′✓ : bcN′ls₂′ ✓
        bcN′ls₂′✓ = valid (ls₂′ .tree) (N′ .clock ∸ 1)

        ih : ∀ (ls₂* : LocalState) →
         N′ .states ⁉ p₂ ≡ just ls₂* →
         prune k bc₁ ⪯ bestChain (N′ .clock ∸ 1) (ls₂* .tree)
         ⊎
         ∃₂[ sl′ , sl″ ]
             sl′ ≤ k
           × N₁ .clock ≤ sl″
           × sl″ ≤ N′ .clock
           × length (superSlotsInRange (sl′ + 1) (sl″ ∸ 1))
             ≤
             2 * length (corruptSlotsInRange (sl′ + 1) (sl″ + 1))
        ih ls₂* lsp₂* = commonPrefixʳ {N₁} {N′} {k} N₀↝⋆N₁ N₁↝⋆ʳN′ ffN′ cfN′ {ls₂ = ls₂*} hp₁ hp₂ lsp₁ lsp₂*

        step : _ → _
        step N′↝N₂ with N′↝N₂
        ... | deliverMsgs {N′} {N″} _ N′—[eoN′]↓→∗N″ = goal-↓∗
          where
            ∃[N*]N′↝[p₂]↓N* : ∃[ N* ] N′ ↝[ p₂ ]↓ N*
            ∃[N*]N′↝[p₂]↓N* = honestMsgsDelivery p₂ ls₂′ N′ , honestParty↓ lsp₂N′ hp₂

            N*p₂ = GlobalState ∋ ∃[N*]N′↝[p₂]↓N* .proj₁

            N′↝[p₂]↓N*p₂ : N′ ↝[ p₂ ]↓ N*p₂
            N′↝[p₂]↓N*p₂ = ∃[N*]N′↝[p₂]↓N* .proj₂

            lsp₂N*p₂≡ls₂ : N*p₂ .states ⁉ p₂ ≡ just ls₂
            lsp₂N*p₂≡ls₂ = trans (sym lsp₂N₂≡lsp₂N*p₂) lsp₂
              where
                lsp₂N₂≡lsp₂N*p₂ : N₂ .states ⁉ p₂ ≡ N*p₂ .states ⁉ p₂
                lsp₂N₂≡lsp₂N*p₂ = localStatePreservation-↓∗ N₀↝⋆N′ N′—[eoN′]↓→∗N″ N′↝[p₂]↓N*p₂

            allBlocksls₂-ls₂′ : allBlocks (ls₂ .tree) ≡ˢ allBlocks (ls₂′ .tree) ++ blocksDeliveredIn p₂ 𝟘 N′
            allBlocksls₂-ls₂′ = honestLocalTreeEvolution-↓ hp₂ lsp₂N′ N′↝[p₂]↓N*p₂ lsp₂N*p₂≡ls₂

            goal-↓∗ :
              prune k bc₁ ⪯ bc₂
              ⊎
              ∃₂[ sl′ , sl″ ]
                  sl′ ≤ k
                × N₁ .clock ≤ sl″
                × sl″ ≤ N₂ .clock
                × length (superSlotsInRange (sl′ + 1) (sl″ ∸ 1))
                  ≤
                  2 * length (corruptSlotsInRange (sl′ + 1) (sl″ + 1))
            goal-↓∗ rewrite clockPreservation-↓∗ N′—[eoN′]↓→∗N″ = (case ih ls₂′ lsp₂N′ of λ where
              (inj₁ bc₁⪯bcN′ls₂′) → (
                case singlePartyCommonPrefix-⪯ {k = k} N₀↝⋆N′ ffN′ cfN′ {p₂} {ls₂′} hp₂ lsp₂N′ {bcN′ls₂} {1} bcN′ls₂⊆fgb+bhN′ bcN′ls₂✓ ∣bcN′ls₂′∣≤∣bcN′ls₂∣ of λ where
                  (inj₁ bcN′ls₂′⪯bcN′ls₂) → inj₁ $ prune-⪯-trans {c₁ = bc₁} bc₁⪯bcN′ls₂′ bcN′ls₂′⪯bcN′ls₂
                  (inj₂ (sl′ , h₁ , h₂)) → inj₂ (sl′ , N′ .clock , h₁ , clockMonotonicity (Starʳ⇒Star N₁↝⋆ʳN′) , ≤-refl , h₂)
                )
              (inj₂ advπ) → inj₂ advπ)
              where
                bcN′ls₂⊆fgb+bhN′ : bcN′ls₂ ⊆ˢ filter ((_≤? N′ .clock ∸ 1 + 1) ∘ slot) (genesisBlock ∷ blockHistory N′)
                bcN′ls₂⊆fgb+bhN′ {b} b∈bcN′ls₂ = L.Mem.∈-filter⁺ ((_≤? N′ .clock ∸ 1 + 1) ∘ slot) (bcN′ls₂⊆gb+bhN′ b∈bcN′ls₂) bₜ≤N′ₜ
                  where
                    bcN′ls₂⊆gb+bhN′ : bcN′ls₂ ⊆ˢ genesisBlock ∷ blockHistory N′
                    bcN′ls₂⊆gb+bhN′ = begin
                      bcN′ls₂
                        ⊆⟨ selfContained (ls₂ .tree) (N′ .clock ∸ 1) ⟩
                      filter ((_≤? N′ .clock ∸ 1) ∘ slot) (allBlocks (ls₂ .tree))
                        ⊆⟨ L.SubS.filter-⊆ _ _ ⟩
                      allBlocks (ls₂ .tree)
                        ⊆⟨ ≡ˢ⇒⊆×⊇ allBlocksls₂-ls₂′ .proj₁ ⟩
                      allBlocks (ls₂′ .tree) ++ blocksDeliveredIn p₂ 𝟘 N′
                        ⊆⟨ t+𝟘s⊆gb+bhN′ ⟩
                      genesisBlock ∷ blockHistory N′ ∎
                      where
                        open L.SubS.⊆-Reasoning Block

                        𝟘s⊆bhN′ : blocksDeliveredIn p₂ 𝟘 N′ ⊆ˢ blockHistory N′
                        𝟘s⊆bhN′ {b} b∈𝟘s = let
                            (e , e∈𝟘s , b≡blk[e]) = L.Mem.∈-map⁻ _ b∈𝟘s
                            (e∈msgs[N′] , eIs𝟘)   = L.Mem.∈-filter⁻ _ {xs = N′ .messages} e∈𝟘s
                          in e∈msgs[N′] ∶
                            e ∈ N′ .messages                      |> L.Mem.∈-map⁺ msg ∶
                            e .msg ∈ L.map msg (N′ .messages)     |> messages⊆history N₀↝⋆N′ ∶
                            e .msg ∈ N′ .history                  |> L.Mem.∈-map⁺ projBlock {x = e .msg} ∶
                            (projBlock ∘ msg) e ∈ blockHistory N′ |> subst (_∈ blockHistory N′) (sym b≡blk[e]) ∶
                            b ∈ blockHistory N′
                          where open import Function.Reasoning

                        t+𝟘s⊆gb+bhN′ : allBlocks (ls₂′ .tree) ++ blocksDeliveredIn p₂ 𝟘 N′ ⊆ˢ genesisBlock ∷ blockHistory N′
                        t+𝟘s⊆gb+bhN′ = ++-meet
                          (begin
                            allBlocks (ls₂′ .tree)         ⊆⟨ honestLocalTreeInHonestGlobalTree N₀↝⋆N′ hp₂ lsp₂N′ ⟩
                            allBlocks (honestTree N′)      ⊆⟨ honestGlobalTreeInBlockHistory N₀↝⋆N′ ⟩
                            genesisBlock ∷ blockHistory N′ ∎)
                          (begin
                            blocksDeliveredIn p₂ 𝟘 N′      ⊆⟨ 𝟘s⊆bhN′ ⟩
                            blockHistory N′                ⊆⟨ L.SubS.xs⊆x∷xs _ _ ⟩
                            genesisBlock ∷ blockHistory N′ ∎)

                    bₜ≤N′ₜ : b .slot ≤ N′ .clock ∸ 1 + 1
                    bₜ≤N′ₜ
                      rewrite
                        +-suc (N′ .clock ∸ 1) 0
                      | +-identityʳ (N′ .clock ∸ 1)
                      = m≤n⇒m≤1+n $ L.All.lookup (bestChainSlotBounded (ls₂ .tree) (N′ .clock ∸ 1)) b∈bcN′ls₂

                ∣bcN′ls₂′∣≤∣bcN′ls₂∣ : ∣ bcN′ls₂′ ∣ ≤ ∣ bcN′ls₂ ∣
                ∣bcN′ls₂′∣≤∣bcN′ls₂∣ = optimal bcN′ls₂′ (ls₂ .tree) (N′ .clock ∸ 1) bcN′ls₂′✓ bcN′ls₂′⊆ft
                  where
                    bcN′ls₂′⊆ft : bcN′ls₂′ ⊆ˢ filter ((_≤? N′ .clock ∸ 1) ∘ slot) (allBlocks (ls₂ .tree))
                    bcN′ls₂′⊆ft = begin
                      bcN′ls₂′
                        ⊆⟨ selfContained (ls₂′ .tree) (N′ .clock ∸ 1) ⟩
                      filter ((_≤? N′ .clock ∸ 1) ∘ slot) (allBlocks (ls₂′ .tree))
                        ⊆⟨ L.SubS.filter⁺′ _ _ id $
                             begin
                               allBlocks (ls₂′ .tree)                              ⊆⟨ L.SubS.xs⊆xs++ys _ _ ⟩
                               allBlocks (ls₂′ .tree) ++ blocksDeliveredIn p₂ 𝟘 N′ ⊆⟨ ≡ˢ⇒⊆×⊇ allBlocksls₂-ls₂′ .proj₂ ⟩
                               allBlocks (ls₂ .tree)
                             ∎
                         ⟩
                      filter ((_≤? N′ .clock ∸ 1) ∘ slot) (allBlocks (ls₂ .tree)) ∎
                      where open L.SubS.⊆-Reasoning Block

        ... | makeBlock {N′} {N″} N′MsgsDelivered N′—[eoN′]↑→∗N″ = goal-↑∗
          where
            ∃[N*]N′↝[p₂]↑N* : ∃[ N* ] N′ ↝[ p₂ ]↑ N*
            ∃[N*]N′↝[p₂]↑N* = honestBlockMaking p₂ ls₂′ N′ , honestParty↑ lsp₂N′ hp₂

            N*p₂ = GlobalState ∋ ∃[N*]N′↝[p₂]↑N* .proj₁

            N′↝[p₂]↑N*p₂ : N′ ↝[ p₂ ]↑ N*p₂
            N′↝[p₂]↑N*p₂ = ∃[N*]N′↝[p₂]↑N* .proj₂

            lsp₂N*p₂≡ls₂ : N*p₂ .states ⁉ p₂ ≡ just ls₂
            lsp₂N*p₂≡ls₂ = trans (sym lsp₂N₂≡lsp₂N*p₂) lsp₂
              where
                lsp₂N₂≡lsp₂N*p₂ : N₂ .states ⁉ p₂ ≡ N*p₂ .states ⁉ p₂
                lsp₂N₂≡lsp₂N*p₂ = localStatePreservation-∈-↑∗ N₀↝⋆N′ N′—[eoN′]↑→∗N″ N′↝[p₂]↑N*p₂

            subgoal-⪯-↑∗ :
              (winner p₂ (N′ .clock)) ⁇ →
              prune k bc₁ ⪯ bcN′ls₂′ →
              prune k bc₁ ⪯ bcN′ls₂
              ⊎
              ∃₂[ sl′ , sl″ ]
                  sl′ ≤ k
                × N₁ .clock ≤ sl″
                × sl″ ≤ N′ .clock
                × length (superSlotsInRange (sl′ + 1) (sl″ ∸ 1))
                  ≤
                  2 * length (corruptSlotsInRange (sl′ + 1) (sl″ + 1))
            subgoal-⪯-↑∗ (⁇ (no ¬isWinner)) bc₁⪯bcN′ls₂′ = inj₁ bc₁⪯bcN′ls₂
              where
                opaque
                  unfolding honestBlockMaking

                  lsp₂N*p₂≡ls₂′ : _⁉_ ⦃ DecEq-Fin ⦄ (N*p₂ .states) p₂ ≡ just ls₂′
                  lsp₂N*p₂≡ls₂′ rewrite dec-no (Params.winnerᵈ params {p₂} {N′ .clock} .dec) ¬isWinner = set-⁉ (N′ .states) p₂ ls₂′

                ls₂′≡ls₂ : ls₂′ ≡ ls₂
                ls₂′≡ls₂ = sym $ M.just-injective $ subst (_≡ just ls₂′) lsp₂N*p₂≡ls₂ lsp₂N*p₂≡ls₂′

                bc₁⪯bcN′ls₂ : prune k bc₁ ⪯ bcN′ls₂
                bc₁⪯bcN′ls₂ = subst (λ ◆ → prune k bc₁ ⪯ bestChain (N′ .clock ∸ 1) (◆ .tree)) ls₂′≡ls₂ bc₁⪯bcN′ls₂′
            subgoal-⪯-↑∗ (⁇ (yes isWinner)) bc₁⪯bcN′ls₂′ =
                case singlePartyCommonPrefix-⪯ {k = k} N₀↝⋆N′ ffN′ cfN′ {p₂} {ls₂′} hp₂ lsp₂N′ {bcN′ls₂} {0} bcN′ls₂⊆fgb+bhN′ bcN′ls₂✓ ∣bcN′ls₂′∣≤∣bcN′ls₂∣ of λ where
                  (inj₁ bcN′ls₂′⪯bcN′ls₂) → inj₁ $ prune-⪯-trans {c₁ = bc₁} bc₁⪯bcN′ls₂′ bcN′ls₂′⪯bcN′ls₂
                  (inj₂ (sl′ , h₁ , h₂)) → inj₂ (sl′ , N′ .clock , h₁ , clockMonotonicity (Starʳ⇒Star N₁↝⋆ʳN′) , ≤-refl , ≤-trans h₂ (*-monoʳ-≤ 2 (h₂′ sl′)))
              where
                nb : Block
                nb = mkBlock (hash (tip bcN′ls₂′)) (N′ .clock) (txSelection (N′ .clock) p₂) p₂

                opaque
                  unfolding honestBlockMaking

                  lsp₂N*p₂≡ls₂′+nb : _⁉_ ⦃ DecEq-Fin ⦄ (N*p₂ .states) p₂ ≡ just (addBlock ls₂′ nb)
                  lsp₂N*p₂≡ls₂′+nb rewrite dec-yes (Params.winnerᵈ params {p₂} {N′ .clock} .dec) isWinner .proj₂ = set-⁉ (N′ .states) p₂ (addBlock ls₂′ nb)

                ls₂′+nb≡ls₂ : addBlock ls₂′ nb ≡ ls₂
                ls₂′+nb≡ls₂ = sym $ M.just-injective $ subst (_≡ just (addBlock ls₂′ nb)) lsp₂N*p₂≡ls₂ lsp₂N*p₂≡ls₂′+nb

                h₂′ : ∀ sl′ →
                  length (corruptSlotsInRange (sl′ + 1) (N′ .clock + 0))
                  ≤
                  length (corruptSlotsInRange (sl′ + 1) (N′ .clock + 1))
                h₂′ sl′ rewrite +-identityʳ (N′ .clock) = slotsInRange-≤-+ ¿ CorruptSlot ¿¹ (sl′ + 1) (N′ .clock) 1

                bcN′ls₂⊆fgb+bhN′ : bcN′ls₂ ⊆ˢ filter ((_≤? N′ .clock ∸ 1 + 0) ∘ slot) (genesisBlock ∷ blockHistory N′)
                bcN′ls₂⊆fgb+bhN′ {b} b∈bcN′ls₂ = L.Mem.∈-filter⁺ ((_≤? N′ .clock ∸ 1 + 0) ∘ slot) b∈gb+bhN′ bₜ≤N′ₜ-1+0
                  where
                    bₜ≤N′ₜ-1+0 : b .slot ≤ N′ .clock ∸ 1 + 0
                    bₜ≤N′ₜ-1+0 rewrite +-identityʳ (N′ .clock ∸ 1) = L.All.lookup (bestChainSlotBounded (ls₂ .tree) (N′ .clock ∸ 1)) b∈bcN′ls₂

                    b∈gb+bhN′ : b ∈ genesisBlock ∷ blockHistory N′
                    b∈gb+bhN′ = (case L.Mem.∈-++⁻ (allBlocks (ls₂′ .tree)) (bcN′ls₂⊆ls₂′+nb b∈bcN′ls₂) of λ where
                      (inj₁ p∈ls₂′) → ls₂′⊆gb+bhN′ p∈ls₂′
                      (inj₂ (here b≡nb)) → contradiction (N′ₜ<N′ₜ b≡nb) (Nat.n≮n $ N′ .clock))
                      where
                        N′ₜ<N′ₜ : b ≡ nb → N′ .clock < N′ .clock
                        N′ₜ<N′ₜ b≡nb = begin-strict
                          N′ .clock         ≡⟨⟩
                          nb .slot          ≡⟨ cong slot (sym b≡nb) ⟩
                          b .slot           ≤⟨ bₜ≤N′ₜ-1+0 ⟩
                          N′ .clock ∸ 1 + 0 ≡⟨ +-identityʳ (N′ .clock ∸ 1) ⟩
                          N′ .clock ∸ 1     <⟨ pred[n]<n ⦃ >-nonZero $ positiveClock N₀↝⋆N′ ⦄ ⟩
                          N′ .clock ∎
                          where open ≤-Reasoning

                        bcN′ls₂⊆ls₂′+nb : bcN′ls₂ ⊆ˢ allBlocks (ls₂′ .tree) ++ [ nb ]
                        bcN′ls₂⊆ls₂′+nb = begin
                          bcN′ls₂
                            ⊆⟨ selfContained (ls₂ .tree) (N′ .clock ∸ 1) ⟩
                          filter ((_≤? N′ .clock ∸ 1) ∘ slot) (allBlocks (ls₂ .tree))
                            ⊆⟨ L.SubS.filter-⊆ _ _ ⟩
                          allBlocks (ls₂ .tree)
                            ≡⟨ cong (λ ◆ → allBlocks (◆ .tree)) (sym ls₂′+nb≡ls₂) ⟩
                          allBlocks (extendTree (ls₂′ .tree) nb)
                            ⊆⟨ ≡ˢ⇒⊆×⊇ (extendable (ls₂′ .tree) nb) .proj₁ ⟩
                          allBlocks (ls₂′ .tree) ++ [ nb ] ∎
                          where open L.SubS.⊆-Reasoning Block

                        ls₂′⊆gb+bhN′ : allBlocks (ls₂′ .tree) ⊆ˢ genesisBlock ∷ blockHistory N′
                        ls₂′⊆gb+bhN′ = begin
                          allBlocks (ls₂′ .tree)         ⊆⟨ honestLocalTreeInHonestGlobalTree N₀↝⋆N′ hp₂ lsp₂N′ ⟩
                          allBlocks (honestTree N′)      ⊆⟨ honestGlobalTreeInBlockHistory N₀↝⋆N′ ⟩
                          genesisBlock ∷ blockHistory N′ ∎
                          where open L.SubS.⊆-Reasoning Block

                ∣bcN′ls₂′∣≤∣bcN′ls₂∣ : ∣ bcN′ls₂′ ∣ ≤ ∣ bcN′ls₂ ∣
                ∣bcN′ls₂′∣≤∣bcN′ls₂∣ = subst (λ ◆ → ∣ bcN′ls₂′ ∣ ≤ ∣ bestChain (N′ .clock ∸ 1) (◆  .tree) ∣) ls₂′+nb≡ls₂ ∣bcN′ls₂′∣≤∣bcN′ls₂′+nb∣
                  where
                    bcN′ls₂′+nb = Chain ∋ bestChain (N′ .clock ∸ 1) (extendTree (ls₂′ .tree) nb)

                    ∣bcN′ls₂′∣≤∣bcN′ls₂′+nb∣ : ∣ bcN′ls₂′ ∣ ≤ ∣ bcN′ls₂′+nb ∣
                    ∣bcN′ls₂′∣≤∣bcN′ls₂′+nb∣ = optimal bcN′ls₂′ (extendTree (ls₂′ .tree) nb) (N′ .clock ∸ 1) bcN′ls₂′✓ bcN′ls₂′⊆ft
                      where
                        bcN′ls₂′⊆ft : bcN′ls₂′ ⊆ˢ filter ((_≤? N′ .clock ∸ 1) ∘ slot) (allBlocks (extendTree (ls₂′ .tree) nb))
                        bcN′ls₂′⊆ft = begin
                          bcN′ls₂′
                            ⊆⟨ selfContained (ls₂′ .tree) (N′ .clock ∸ 1) ⟩
                          filter ((_≤? N′ .clock ∸ 1) ∘ slot) (allBlocks (ls₂′ .tree))
                            ⊆⟨ L.SubS.filter⁺′ _ _ id $
                                 begin
                                   allBlocks (ls₂′ .tree)                 ⊆⟨ L.SubS.xs⊆xs++ys _ _ ⟩
                                   allBlocks (ls₂′ .tree) ++ [ nb ]       ⊆⟨ ≡ˢ⇒⊆×⊇ (extendable (ls₂′ .tree) nb) .proj₂ ⟩
                                   allBlocks (extendTree (ls₂′ .tree) nb)
                                 ∎
                             ⟩
                          filter ((_≤? N′ .clock ∸ 1) ∘ slot) (allBlocks (extendTree (ls₂′ .tree) nb)) ∎
                          where open L.SubS.⊆-Reasoning Block

            goal-↑∗ :
              prune k bc₁ ⪯ bc₂
              ⊎
              ∃₂[ sl′ , sl″ ]
                  sl′ ≤ k
                × N₁ .clock ≤ sl″
                × sl″ ≤ N₂ .clock
                × length (superSlotsInRange (sl′ + 1) (sl″ ∸ 1))
                  ≤
                  2 * length (corruptSlotsInRange (sl′ + 1) (sl″ + 1))
            goal-↑∗ rewrite clockPreservation-↑∗ N′—[eoN′]↑→∗N″ = (case ih ls₂′ lsp₂N′ of λ where
              (inj₁ bc₁⪯bcN′ls₂′) → subgoal-⪯-↑∗ (Params.winnerᵈ params {p₂} {N′ .clock}) bc₁⪯bcN′ls₂′
              (inj₂ advπ) → inj₂ advπ)

        ... | advanceRound _ = (case ih ls₂ lsp₂ of λ where
          (inj₁ bc₁⪯bc₂N′) →
            case singlePartyCommonPrefix-⪯ {k = k} N₀↝⋆N′ ffN′ cfN′ {p₂} {ls₂} hp₂ lsp₂ {bc₂} {1} bc₂⊆fgb+bhN′ bc₂✓ ∣bcN′ls₂∣≤∣bc₂∣ of λ where
              (inj₁ bc₂N′⪯bc₂) → inj₁ $ prune-⪯-trans {c₁ = bc₁} bc₁⪯bc₂N′ bc₂N′⪯bc₂
              (inj₂ (sl′ , h₁ , h₂)) → inj₂ (sl′ , N′ .clock , h₁ , clockMonotonicity (Starʳ⇒Star N₁↝⋆ʳN′) , n≤1+n (N′ .clock) , h₂)
          (inj₂ (sl′ , sl″ , sl′≤k , N₁ₜ≤sl″ , sl″≤N′ₜ , advπ)) → inj₂ (sl′ , sl″ , sl′≤k , N₁ₜ≤sl″ , m≤n⇒m≤1+n sl″≤N′ₜ , advπ))
          where
            bc₂⊆fgb+bhN′ : bc₂ ⊆ˢ filter ((_≤? N′ .clock ∸ 1 + 1) ∘ slot) (genesisBlock ∷ blockHistory N′)
            bc₂⊆fgb+bhN′ {b} b∈bc₂ = L.Mem.∈-filter⁺ ((_≤? N′ .clock ∸ 1 + 1) ∘ slot) (bc₂⊆gb+bhN′ b∈bc₂) bₜ≤N′ₜ
              where
                bc₂⊆gb+bhN′ : bc₂ ⊆ˢ genesisBlock ∷ blockHistory N′
                bc₂⊆gb+bhN′ = begin
                  bc₂
                    ⊆⟨ selfContained (ls₂ .tree) (N₂ .clock ∸ 1) ⟩
                  filter ((_≤? N₂ .clock ∸ 1) ∘ slot) (allBlocks (ls₂ .tree))
                    ⊆⟨ L.SubS.filter-⊆ _ _ ⟩
                  allBlocks (ls₂ .tree)
                    ⊆⟨ honestLocalTreeInHonestGlobalTree N₀↝⋆N′ hp₂ lsp₂ ⟩
                  allBlocks (honestTree N′)
                    ⊆⟨ honestGlobalTreeInBlockHistory N₀↝⋆N′ ⟩
                  genesisBlock ∷ blockHistory N′ ∎
                  where open L.SubS.⊆-Reasoning Block

                bₜ≤N′ₜ : b .slot ≤ N′ .clock ∸ 1 + 1
                bₜ≤N′ₜ
                  rewrite
                    +-suc (N′ .clock ∸ 1) 0
                  | +-identityʳ (N′ .clock ∸ 1)
                  | Nat.suc-pred (N′ .clock) ⦃ >-nonZero $ positiveClock N₀↝⋆N′ ⦄
                  = L.All.lookup (bestChainSlotBounded (ls₂ .tree) (N′ .clock)) b∈bc₂

            ∣bcN′ls₂∣≤∣bc₂∣ : ∣ bcN′ls₂ ∣ ≤ ∣ bc₂ ∣
            ∣bcN′ls₂∣≤∣bc₂∣ = optimal bcN′ls₂ (ls₂ .tree) (N′ .clock) bcN′ls₂✓ bcN′ls₂⊆ft
              where
                bcN′ls₂⊆ft : bcN′ls₂ ⊆ˢ filter ((_≤? N′ .clock) ∘ slot) (allBlocks (ls₂ .tree))
                bcN′ls₂⊆ft = begin
                  bcN′ls₂
                    ⊆⟨ selfContained (ls₂ .tree) (N′ .clock ∸ 1) ⟩
                  filter ((_≤? N′ .clock ∸ 1) ∘ slot) (allBlocks (ls₂ .tree))
                    ⊆⟨ L.SubS.filter⁺′ _ _ Nat.≤pred⇒≤ {xs = allBlocks (ls₂ .tree)} L.SubS.⊆-refl ⟩
                  filter ((_≤? N′ .clock) ∘ slot) (allBlocks (ls₂ .tree)) ∎
                  where open L.SubS.⊆-Reasoning Block

        ... | permuteParties _ = ih ls₂ lsp₂
        ... | permuteMsgs    _ = ih ls₂ lsp₂
