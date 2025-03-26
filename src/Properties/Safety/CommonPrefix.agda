open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Safety.CommonPrefix
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot)
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
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Ext using (Starʳ)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.Ext using (Star⇒Starʳ; Starʳ⇒Star)
open import Data.Nat.Properties using (≤-refl; ≤-trans; *-monoʳ-≤; m≤n⇒m≤1+n; +-suc; +-identityʳ; +-identityˡ)
open import Data.Maybe.Properties.Ext using (Is-just⇒to-witness; ≡just⇒Is-just)
open import Data.List.Relation.Binary.Permutation.Propositional using (↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∈-resp-↭)
open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_; ≡ˢ⇒⊆×⊇)
open import Data.List.Relation.Binary.Subset.Propositional.Properties.Ext using (++⁻ˡ; ++-meet)

lcs : Chain → Chain → Chain
lcs (b ∷ c) (b′ ∷ c′) with b ≟ b′
... | yes _ = b ∷ lcs c c′
... | no  _ = []
lcs _       _         = []

singlePartyCommonPrefix : ∀ {N : GlobalState} {k : Slot} →
    N₀ ↝⋆ N
  → ForgingFree N
  → CollisionFree N
  → ∀ {p : Party} {ls : LocalState}
    → Honest p
    → N .states ⁉ p ≡ just ls
    → let bc = bestChain (N .clock ∸ 1) (ls .tree)
      in ∀ {c : Chain} {sl : Slot} →
          c ⊆ˢ filter ((_≤? N .clock ∸ 1 + sl) ∘ slot) (genesisBlock ∷ blockHistory N)
        → c ✓
        → ∣ bc ∣ ≤ ∣ c ∣
        → prune k bc ⪯ c
          ⊎
          ∃[ sl′ ]
              sl′ ≤ k
            × length (superSlotsInRange (sl′ + 1) (N .clock ∸ 1))
              ≤
              2 * length (corruptSlotsInRange (sl′ + 1) (N .clock + sl))
singlePartyCommonPrefix = {!!}

singleRoundCommonPrefix : ∀ {N : GlobalState} {k : Slot} →
    N₀ ↝⋆ N
  → ForgingFree N
  → CollisionFree N
  → ∀ {p₁ p₂ : Party} {ls₁ ls₂ : LocalState}
  → Honest p₁
  → Honest p₂
  → N .states ⁉ p₁ ≡ just ls₁
  → N .states ⁉ p₂ ≡ just ls₂
  → let bc₁ = bestChain (N .clock ∸ 1) (ls₁ .tree)
        bc₂ = bestChain (N .clock ∸ 1) (ls₂ .tree)
    in prune k bc₁ ⪯ bc₂
       ⊎
       ∃[ sl′ ]
           sl′ ≤ k
         × length (superSlotsInRange (sl′ + 1) (N .clock ∸ 1))
           ≤
           2 * length (corruptSlotsInRange (sl′ + 1) (N .clock))
singleRoundCommonPrefix = {!!}

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
    commonPrefixʳ {N₁} {N₂} {k} N₀↝⋆N₁ N₁↝⋆ʳN₂@(_◅ʳ_ {j = N′} N₁↝⋆ʳN′ N′↝N₂) ffN₂ cfN₂ {p₁} {p₂} {ls₁} {ls₂} hp₁ hp₂ lsp₁ lsp₂
        with N′↝N₂
    ... | deliverMsgs {N′} {N″} N′Ready N′—[eoN′]↓→∗N″ = step-↓∗
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

        bc₁      = Chain ∋ bestChain (N₁ .clock ∸ 1) (ls₁  .tree)
        bc₂      = Chain ∋ bestChain (N₂ .clock ∸ 1) (ls₂  .tree)
        bcN′ls₂  = Chain ∋ bestChain (N′ .clock ∸ 1) (ls₂  .tree)
        bcN′ls₂′ = Chain ∋ bestChain (N′ .clock ∸ 1) (ls₂′ .tree)

        ih :
         prune k bc₁ ⪯ bcN′ls₂′
         ⊎
         ∃₂[ sl′ , sl″ ]
             sl′ ≤ k
           × N₁ .clock ≤ sl″
           × sl″ ≤ N′ .clock
           × length (superSlotsInRange (sl′ + 1) (sl″ ∸ 1))
             ≤
             2 * length (corruptSlotsInRange (sl′ + 1) (sl″ + 1))
        ih = commonPrefixʳ {N₁} {N′} {k} N₀↝⋆N₁ N₁↝⋆ʳN′ ffN′ cfN′ hp₁ hp₂ lsp₁ lsp₂N′

        allBlocksls₂-ls₂′ : allBlocks (ls₂ .tree) ≡ˢ allBlocks (ls₂′ .tree) ++ blocksDeliveredIn p₂ 𝟘 N′
        allBlocksls₂-ls₂′ = honestLocalTreeEvolution-↓ hp₂ lsp₂N′ N′↝[p₂]↓N*p₂ lsp₂N*p₂≡ls₂

        step-↓∗ :
          prune k bc₁ ⪯ bc₂
          ⊎
          ∃₂[ sl′ , sl″ ]
              sl′ ≤ k
            × N₁ .clock ≤ sl″
            × sl″ ≤ N₂ .clock
            × length (superSlotsInRange (sl′ + 1) (sl″ ∸ 1))
              ≤
              2 * length (corruptSlotsInRange (sl′ + 1) (sl″ + 1))
        step-↓∗ rewrite clockPreservation-↓∗ N′—[eoN′]↓→∗N″ = (case ih of λ where
          (inj₁ bc₁⪯bcN′ls₂′) → (
            case singlePartyCommonPrefix {k = k} N₀↝⋆N′ ffN′ cfN′ {p₂} {ls₂′} hp₂ lsp₂N′ {bcN′ls₂} {1} π1 π2 π3 of λ where
              (inj₁ bcN′ls₂′⪯bcN′ls₂) → inj₁ $ prune-⪯-trans {c₁ = bc₁} bc₁⪯bcN′ls₂′ bcN′ls₂′⪯bcN′ls₂
              (inj₂ (sl′ , h₁ , h₂)) → inj₂ (sl′ , N′ .clock , h₁ , clockMonotonicity (Starʳ⇒Star N₁↝⋆ʳN′) , ≤-refl , h₂)
            )
          (inj₂ advπ) → inj₂ advπ)
          where
            π1 : bcN′ls₂ ⊆ˢ filter ((_≤? N′ .clock ∸ 1 + 1) ∘ slot) (genesisBlock ∷ blockHistory N′)
            π1 {b} b∈bcN′ls₂ = L.Mem.∈-filter⁺ ((_≤? N′ .clock ∸ 1 + 1) ∘ slot) (π1-1 b∈bcN′ls₂) π1-2
              where
                π1-1 : bcN′ls₂ ⊆ˢ genesisBlock ∷ blockHistory N′
                π1-1 = begin
                  bcN′ls₂
                    ⊆⟨ selfContained (ls₂ .tree) (N′ .clock ∸ 1) ⟩
                  filter ((_≤? N′ .clock ∸ 1) ∘ slot) (allBlocks (ls₂ .tree))
                    ⊆⟨ L.SubS.filter-⊆ _ _ ⟩
                  allBlocks (ls₂ .tree)
                    ⊆⟨ ≡ˢ⇒⊆×⊇ allBlocksls₂-ls₂′ .proj₁ ⟩
                  allBlocks (ls₂′ .tree) ++ blocksDeliveredIn p₂ 𝟘 N′
                    ⊆⟨ π1-1-1 ⟩
                  genesisBlock ∷ blockHistory N′ ∎
                  where
                    open L.SubS.⊆-Reasoning Block

                    π1-1-2 : blocksDeliveredIn p₂ 𝟘 N′ ⊆ˢ blockHistory N′
                    π1-1-2 {b} b∈𝟘s = let
                        (e , e∈𝟘s , b≡blk[e]) = L.Mem.∈-map⁻ _ b∈𝟘s
                        (e∈msgs[N′] , eIs𝟘)   = L.Mem.∈-filter⁻ _ {xs = N′ .messages} e∈𝟘s
                      in e∈msgs[N′] ∶
                        e ∈ N′ .messages                      |> L.Mem.∈-map⁺ msg ∶
                        e .msg ∈ L.map msg (N′ .messages)     |> messages⊆history N₀↝⋆N′ ∶
                        e .msg ∈ N′ .history                  |> L.Mem.∈-map⁺ projBlock {x = e .msg} ∶
                        (projBlock ∘ msg) e ∈ blockHistory N′ |> subst (_∈ blockHistory N′) (sym b≡blk[e]) ∶
                        b ∈ blockHistory N′
                      where open import Function.Reasoning

                    π1-1-1 : allBlocks (ls₂′ .tree) ++ blocksDeliveredIn p₂ 𝟘 N′ ⊆ˢ genesisBlock ∷ blockHistory N′
                    π1-1-1 = ++-meet
                      (begin
                        allBlocks (ls₂′ .tree)         ⊆⟨ honestLocalTreeInHonestGlobalTree N₀↝⋆N′ hp₂ lsp₂N′ ⟩
                        allBlocks (honestTree N′)      ⊆⟨ honestGlobalTreeInBlockHistory N₀↝⋆N′ ⟩
                        genesisBlock ∷ blockHistory N′ ∎)
                      (begin
                        blocksDeliveredIn p₂ 𝟘 N′      ⊆⟨ π1-1-2 ⟩
                        blockHistory N′                ⊆⟨ L.SubS.xs⊆x∷xs _ _ ⟩
                        genesisBlock ∷ blockHistory N′ ∎)

                π1-2 : b .slot ≤ N′ .clock ∸ 1 + 1
                π1-2
                  rewrite
                    +-suc (N′ .clock ∸ 1) 0
                  | +-identityʳ (N′ .clock ∸ 1)
                  = m≤n⇒m≤1+n $ L.All.lookup (bestChainSlotBounded (ls₂ .tree) (N′ .clock ∸ 1)) b∈bcN′ls₂

            π2 : bcN′ls₂ ✓
            π2 = valid (ls₂ .tree) (N′ .clock ∸ 1)

            π3 : ∣ bcN′ls₂′ ∣ ≤ ∣ bcN′ls₂ ∣
            π3 = optimal bcN′ls₂′ (ls₂ .tree) (N′ .clock ∸ 1) bcN′ls₂′✓ π3-1
              where
                bcN′ls₂′✓ : bcN′ls₂′ ✓
                bcN′ls₂′✓ = valid (ls₂′ .tree) (N′ .clock ∸ 1)

                π3-1 : bcN′ls₂′ ⊆ˢ filter ((_≤? N′ .clock ∸ 1) ∘ slot) (allBlocks (ls₂ .tree))
                π3-1 = begin
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

    ... | makeBlock x x₁ = {!!}
    ... | advanceRound x = {!!}
    ... | permuteParties x = {!!}
    ... | permuteMsgs x = {!!}
