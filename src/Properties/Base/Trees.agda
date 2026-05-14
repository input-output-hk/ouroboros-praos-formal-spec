{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled

open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Base.Trees
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
open import Properties.Base.Time ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.LocalState ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.ExecutionOrder ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Liveness.ChainGrowth ⦃ params ⦄ ⦃ assumptions ⦄ using (honestGlobalTreeInHonestLocalTree)
open import Prelude.AssocList.Properties.Ext using (set-⁉; map-⁉-∈-just)
open import Data.List.Relation.Binary.BagAndSetEquality using (∷-cong; concat-cong; map-cong; bag-=⇒; ↭⇒∼bag)
open import Data.Maybe.Properties.Ext using (Is-just⇒to-witness; ≡just⇒Is-just)
open import Data.List.Membership.Propositional.Properties.Ext using (∈-∷⁻; ∈-∷-≢⁻)
open import Data.List.Relation.Binary.Subset.Propositional.Properties.Ext using (⊆-++-comm)
open import Data.List.Relation.Binary.Permutation.Propositional using (↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∈-resp-↭; map⁺; shift; ++-comm)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties.Ext using (filter-↭)
open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_; ≡ˢ⇒⊆; ≡ˢ⇒⊇; ≡ˢ-refl)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Ext using (Starʳ)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.Ext using (Star⇒Starʳ; Starʳ⇒Star)
open import Function.Bundles using (_⇔_; Equivalence; Inverse)
open import Function.Related.Propositional as Related

opaque

  unfolding honestMsgsDelivery honestBlockMaking

  honestLocalTreeEvolution-↓ :  ∀ {N N′ : GlobalState} {p : Party} {ls ls′ : LocalState} →
      Honest p
    → N .states ⁉ p ≡ just ls
    → _ ⊢ N —[ p ]↓→ N′
    → N′ .states ⁉ p ≡ just ls′
    → allBlocks (ls′ .tree) ≡ˢ allBlocks (ls .tree) ++ blocksDeliveredIn p 𝟘 N
  honestLocalTreeEvolution-↓ {N} {N′} {p} {ls} {ls′} hp lspN N—[p]↓→N′ lspN′ with N—[p]↓→N′
  ... | unknownParty↓ ls≡◇ = contradiction ls≡◇ ls≢◇
    where
      ls≢◇ : N .states ⁉ p ≢ nothing
      ls≢◇ rewrite lspN = flip contradiction λ ()
  ... | corruptParty↓ _ cp = contradiction hp $ corrupt⇒¬honest cp
  ... | honestParty↓ {ls = ls*} ls*pN _ = goal
    where
      ls*≡ls : ls* ≡ ls
      ls*≡ls = sym $ M.just-injective $ trans (sym lspN) ls*pN

      add𝟘s : List Envelope → LocalState → LocalState
      add𝟘s es ls = L.foldr (λ m ls′ → addBlock ls′ (projBlock m)) ls (map msg (L.filter ¿ flip Immediate p ¿¹ es))

      ls+𝟘s≡ls′ : add𝟘s (N .messages) ls ≡ ls′
      ls+𝟘s≡ls′ rewrite sym ls*≡ls | set-⁉ (N .states) p (add𝟘s (N .messages) ls*) = M.just-injective lspN′

      goal : allBlocks (ls′ .tree) ≡ˢ allBlocks (ls .tree) ++ blocksDeliveredIn p 𝟘 N
      goal rewrite sym ls+𝟘s≡ls′ = goal* (N .messages)
        where
          goal* : ∀ es* →
            allBlocks (add𝟘s es* ls .tree)
            ≡ˢ
            allBlocks (ls .tree) ++ map (projBlock ∘ msg) (L.filter ¿ flip Immediate p ¿¹ es*)
          goal* [] rewrite L.++-identityʳ (allBlocks (ls .tree)) = ≡ˢ-refl
          goal* (e@(⦅ newBlock b , _ , _ ⦆) ∷ es*) with ¿ Immediate e p ¿
          ... | no  ≢𝟘 rewrite L.filter-reject ¿ flip Immediate p ¿¹ {x = e} {xs = es*} ≢𝟘 = goal* es*
          ... | yes ≡𝟘 rewrite L.filter-accept ¿ flip Immediate p ¿¹ {x = e} {xs = es*} ≡𝟘 = goal*-≡𝟘
            where
              goal*-≡𝟘 :
                allBlocks (extendTree (add𝟘s es* ls .tree) b)
                ≡ˢ
                allBlocks (tree ls) ++ b ∷ map (projBlock ∘ msg) (L.filter ¿ flip Immediate p ¿¹ es*)
              goal*-≡𝟘 {b′} = let open Related.EquationalReasoning in begin
                b′ ∈ allBlocks (extendTree (add𝟘s es* ls .tree) b)
                  ∼⟨ extendable _ _ ⟩
                b′ ∈ allBlocks (add𝟘s es* ls .tree) ++ [ b ]
                  ∼⟨ bag-=⇒ (↭⇒∼bag (++-comm _ [ b ])) ⟩
                b′ ∈ b ∷ allBlocks (add𝟘s es* ls .tree)
                  ∼⟨ ∷-cong refl (goal* es*) ⟩
                b′ ∈ b ∷ allBlocks (tree ls) ++ map (projBlock ∘ msg) (L.filter ¿ flip Immediate p ¿¹ es*)
                  ∼⟨ bag-=⇒ (↭⇒∼bag (↭-sym $ shift _ _ _)) ⟩
                b′ ∈ allBlocks (tree ls) ++ b ∷ map (projBlock ∘ msg) (L.filter ¿ flip Immediate p ¿¹ es*)
                  ∎

  honestLocalTreeEvolution-↑ : ∀ {N N′ N″ : GlobalState} {p : Party} {ls ls′ : LocalState} →
      N₀ ↝⋆ N
    → _ ⊢ N —[ N .execOrder ]↑→∗ N″
    → _ ⊢ N —[ p ]↑→ N′
    → Honest p
    → N .states ⁉ p ≡ just ls
    → N′ .states ⁉ p ≡ just ls′
    → ∃[ bs ]
          allBlocks (ls′ .tree) ≡ˢ allBlocks (ls .tree) ++ bs
        × (∀ {p′} →
              p′ ∈ N .execOrder
            → bs ⊆ˢ blocksDeliveredIn p′ 𝟙 N″)
  honestLocalTreeEvolution-↑ {N} {N′} {N″} {p} {ls} {ls′} N₀↝⋆N N—[eoN]↑→∗N″ N—[p]↑→N′ hp lspN lspN′
    with N—[p]↑→N′
  ... | unknownParty↑ ls≡◇ = contradiction ls≡◇ ls≢◇
    where
      ls≢◇ : N .states ⁉ p ≢ nothing
      ls≢◇ rewrite lspN = flip contradiction λ ()
  ... | corruptParty↑ _ cpπ = contradiction hp $ corrupt⇒¬honest cpπ
  ... | honestParty↑ {ls = ls*} ls*pN _ with Params.winnerᵈ params {p} {N .clock}
  ...   | ⁇ (no ¬isWinner) = [] , tls′≡tls+[] , λ {p′} _ {b} b∈[] → contradiction b∈[] λ ()
    where
      ls*≡ls′ : ls* ≡ ls′
      ls*≡ls′ rewrite set-⁉ (N .states) p ls* = M.just-injective lspN′

      ls*≡ls : ls* ≡ ls
      ls*≡ls = sym $ M.just-injective $ trans (sym lspN) ls*pN

      tls′≡tls+[] : allBlocks (ls′ .tree) ≡ˢ allBlocks (ls .tree) ++ []
      tls′≡tls+[] rewrite trans (sym ls*≡ls′) ls*≡ls | L.++-identityʳ (allBlocks (ls .tree)) = ≡ˢ-refl
  ...   | ⁇ (yes isWinner) = [ nb ] , tls′≡tls+nb , [nb]⊆𝟙sN″
    where
      p∈eoN : p ∈ N .execOrder
      p∈eoN = ∈-resp-↭ (execOrderPreservation-↭ N₀↝⋆N) (hasState⇔∈parties₀ N₀↝⋆N .Equivalence.to pHasInN)
        where
          pHasInN : p hasStateIn N
          pHasInN = hasStateInAltDef {N} {p} .Equivalence.to (ls , lspN)

      best : Chain
      best = bestChain (N .clock ∸ 1) (ls .tree)

      best* : Chain
      best* = bestChain (N .clock ∸ 1) (ls* .tree)

      nb : Block
      nb = mkBlock (hash (tip best)) (N .clock) (txSelection (N .clock) p) p

      nb* : Block
      nb* = mkBlock (hash (tip best*)) (N .clock) (txSelection (N .clock) p) p

      ls*≡ls : ls* ≡ ls
      ls*≡ls = sym $ M.just-injective $ trans (sym lspN) ls*pN

      ls+nb≡ls′ : addBlock ls nb ≡ ls′
      ls+nb≡ls′ rewrite sym ls*≡ls | set-⁉ (N .states) p (addBlock ls* nb*) = M.just-injective lspN′

      tls′≡tls+nb : allBlocks (ls′ .tree) ≡ˢ allBlocks (ls .tree) ++ [ nb ]
      tls′≡tls+nb rewrite sym ls+nb≡ls′ = extendable (ls .tree) nb

      [nb]⊆𝟙sN″ : ∀ {p′ : Party} → p′ ∈ N .execOrder → [ nb ] ⊆ˢ blocksDeliveredIn p′ 𝟙 N″
      [nb]⊆𝟙sN″ {p′} p′∈eoN = L.SubS.⊆-trans [nb]⊆𝟙sN′ 𝟙sN′⊆𝟙sN″
        where
          [nb]⊆𝟙sN′ : [ nb ] ⊆ˢ blocksDeliveredIn p′ 𝟙 N′
          [nb]⊆𝟙sN′ = L.SubS.∈-∷⁺ʳ {xs = []} nb∈𝟙sN′ λ ()
            where
              dlv? : Decidable¹ λ e → DeliveredIn e p′ 𝟙
              dlv? = λ e → ¿ DeliveredIn e ¿² p′ 𝟙

              mkenv : Party → Envelope
              mkenv = λ party → ⦅ newBlock nb , party , 𝟙 ⦆

              nb∈𝟙sN′ : nb ∈ blocksDeliveredIn p′ 𝟙 N′
              nb∈𝟙sN′
                rewrite
                  ls*≡ls
                | dec-yes ¿ winner p (N .clock) ¿ isWinner .proj₂
                | L.filter-++ dlv? (map mkenv (N .execOrder)) (N .messages)
                | L.map-++ (projBlock ∘ msg) (filter dlv? (map mkenv (N .execOrder))) (filter dlv? (messages N))
                  = L.Mem.∈-++⁺ˡ {ys = map (projBlock ∘ msg) (filter dlv? (messages N))} (nb∈𝟙sN′* {N .execOrder} p′∈eoN)
                where
                  nb∈𝟙sN′* : ∀ {ps*} →
                      p′ ∈ ps*
                    → nb ∈ map (projBlock ∘ msg) (filter dlv? (map mkenv ps*))
                  nb∈𝟙sN′* {[]} ()
                  nb∈𝟙sN′* {p* ∷ ps*} p′∈p*+ps* with p′ ≟ p*
                  ... | yes p′≡p*
                          rewrite
                            p′≡p*
                          | L.filter-accept
                              (λ e → ¿ DeliveredIn e ¿² p* 𝟙)
                              {x = mkenv p*}
                              {xs = map mkenv ps*}
                              (refl , refl)
                            = here refl
                  ... | no p′≢p*
                          rewrite
                            L.filter-reject
                              dlv?
                              {x = mkenv p*}
                              {xs = map mkenv ps*}
                              λ{ (_ , p*≡p′) → contradiction (sym p*≡p′) p′≢p*}
                            = nb∈𝟙sN′* {ps*} $ ∈-∷-≢⁻ p′∈p*+ps* p′≢p*

          𝟙sN′⊆𝟙sN″ : blocksDeliveredIn p′ 𝟙 N′ ⊆ˢ blocksDeliveredIn p′ 𝟙 N″
          𝟙sN′⊆𝟙sN″ rewrite dec-yes ¿ winner p (N .clock) ¿ isWinner .proj₂ =
            blocksDeliveredInEvolution-↑ N₀↝⋆N N—[eoN]↑→∗N″ N—[p]↑→N′ hp p∈eoN {p′} {𝟙}

honestLocalTreeInHonestGlobalTree : ∀ {N : GlobalState} {p : Party} {ls : LocalState} →
    N₀ ↝⋆ N
  → Honest p
  → N .states ⁉ p ≡ just ls
  → allBlocks (ls .tree) ⊆ˢ allBlocks (honestTree N)
honestLocalTreeInHonestGlobalTree {N} {p} {ls} N₀↝⋆N hp lspN =
  let open L.SubS.⊆-Reasoning Block in begin
    allBlocks (ls .tree)
      ⊆⟨ goal p∈eoN ⟩
    genesisBlock ∷ L.concatMap (blocks N) (honestParties N)
      ⊆⟨ ≡ˢ⇒⊇ (buildTreeUsesAllBlocks _) ⟩
    allBlocks (honestTree N)
      ∎
  where
    p∈eoN : p ∈ N .execOrder
    p∈eoN = ∈-resp-↭ (execOrderPreservation-↭ N₀↝⋆N) (hasState⇔∈parties₀ N₀↝⋆N .Equivalence.to pHasInN)
      where
        pHasInN : p hasStateIn N
        pHasInN = hasStateInAltDef {N} {p} .Equivalence.to (ls , lspN)

    goal : ∀ {ps*} →
        p ∈ ps*
      → allBlocks (ls .tree) ⊆ˢ genesisBlock ∷ L.concatMap (blocks N) (L.filter ¿ Honest ¿¹ ps*)
    goal {p* ∷ ps*} (here p≡p*) rewrite sym p≡p* | hp | lspN =
      L.SubS.⊆-trans (L.SubS.xs⊆xs++ys (allBlocks (ls .tree)) _) (L.SubS.xs⊆x∷xs _ _)
    goal {p* ∷ ps*} (there p∈p*+ps*) with ¿ Honest p* ¿
    ... | yes hp* =
      let
        open L.SubS.⊆-Reasoning Block
        bs = L.concatMap (blocks N) (L.filter ¿ Honest ¿¹ ps*)
      in begin
      allBlocks (ls .tree)                     ⊆⟨ goal {ps*} p∈p*+ps* ⟩
      genesisBlock ∷ bs                        ⊆⟨ L.SubS.xs⊆ys++xs _ _ ⟩
      blocks N p* ++ [ genesisBlock ] ++ bs    ≡⟨ L.++-assoc (blocks N p*) _ _ ⟨
      (blocks N p* ++ [ genesisBlock ]) ++ bs  ⊆⟨ L.SubS.++⁺ˡ _ (⊆-++-comm (blocks N p*) [ genesisBlock ]) ⟩
      (genesisBlock ∷ blocks N p*) ++ bs       ≡⟨ L.++-assoc [ genesisBlock ] (blocks N p*) _ ⟩
      genesisBlock ∷ blocks N p* ++ bs         ∎
    ... | no ¬hp* = goal {ps*} p∈p*+ps*

honestLocalTreeBlocksMonotonicity :  ∀ {N N′ : GlobalState} {p : Party} {ls ls′ : LocalState} →
    N₀ ↝⋆ N
  → Honest p
  → N .states ⁉ p ≡ just ls
  → N ↝⋆ N′
  → N′ .states ⁉ p ≡ just ls′
  → allBlocks (ls .tree) ⊆ˢ allBlocks (ls′ .tree)
honestLocalTreeBlocksMonotonicity N₀↝⋆N hp lspN N↝⋆N′ = honestLocalTreeBlocksMonotonicityʳ N₀↝⋆N hp lspN (Star⇒Starʳ N↝⋆N′)
  where
    open RTC; open Starʳ
    honestLocalTreeBlocksMonotonicityʳ :  ∀ {N N′ : GlobalState} {p : Party} {ls ls′ : LocalState} →
        N₀ ↝⋆ N
      → Honest p
      → N .states ⁉ p ≡ just ls
      → N ↝⋆ʳ N′
      → N′ .states ⁉ p ≡ just ls′
      → allBlocks (ls .tree) ⊆ˢ allBlocks (ls′ .tree)
    honestLocalTreeBlocksMonotonicityʳ {ls = ls} {ls′ = ls′} _ _ lspN εʳ lspN′ = subst ((_⊆ˢ allBlocks (ls′ .tree)) ∘ (allBlocks ∘ tree)) ls′≡ls L.SubS.⊆-refl
      where
        ls′≡ls : ls′ ≡ ls
        ls′≡ls = sym $ M.just-injective $ trans (sym lspN) lspN′
    honestLocalTreeBlocksMonotonicityʳ {N} {N′} {p} {ls} {ls′} N₀↝⋆N hp lspN (_◅ʳ_ {j = N″} N↝⋆ʳN″ N″↝N′) lspN′ = goal N″↝N′
      where
        N₀↝⋆N″ : N₀ ↝⋆ N″
        N₀↝⋆N″ = N₀↝⋆N ◅◅ Starʳ⇒Star N↝⋆ʳN″

        hasLspN″ : p hasStateIn N″
        hasLspN″ = L.All.lookup (allPartiesHaveLocalState N₀↝⋆N″) p∈N″
          where
            p∈N′ : p ∈ N′ .execOrder
            p∈N′ = hasState⇒∈execOrder (N₀↝⋆N″ ◅◅ N″↝N′ ◅ ε) (≡just⇒Is-just lspN′)

            p∈N″ : p ∈ N″ .execOrder
            p∈N″ = ∈-resp-↭ (↭-sym (execOrderPreservation-↭-↝ N″↝N′)) p∈N′

        ls″ : LocalState
        ls″ = M.to-witness hasLspN″

        lspN″ : N″ .states ⁉ p ≡ just ls″
        lspN″ = Is-just⇒to-witness hasLspN″

        ih : ∀ {ls⁺} → N″ .states ⁉ p ≡ just ls⁺ → allBlocks (ls .tree) ⊆ˢ allBlocks (ls⁺ .tree)
        ih lspN″ = honestLocalTreeBlocksMonotonicityʳ N₀↝⋆N hp lspN N↝⋆ʳN″ lspN″

        goal : N″ ↝ N′ → allBlocks (ls .tree) ⊆ˢ allBlocks (ls′ .tree)
        goal (deliverMsgs {N′ = N‴} N″Ready N″—[eoN″]↓→∗N‴) = let open L.SubS.⊆-Reasoning Block in begin
          allBlocks (ls .tree)                              ⊆⟨ ih lspN″ ⟩
          allBlocks (ls″ .tree)                             ⊆⟨ L.SubS.xs⊆xs++ys _ _ ⟩
          allBlocks (ls″ .tree) ++ blocksDeliveredIn p 𝟘 N″ ⊆⟨ ≡ˢ⇒⊇ tls′≡tls″+𝟘s ⟩
          allBlocks (ls′ .tree)                             ∎
          where
            Nᵖ : GlobalState
            Nᵖ = honestMsgsDelivery p ls″ N″

            N″↝[p]↓Nᵖ : N″ ↝[ p ]↓ Nᵖ
            N″↝[p]↓Nᵖ = honestParty↓ lspN″ hp

            lspNᵖ : Nᵖ .states ⁉ p ≡ just ls′
            lspNᵖ = trans (sym lspN‴≡lspNᵖ) lspN′
              where
                lspN‴≡lspNᵖ : N‴ .states ⁉ p ≡ Nᵖ .states ⁉ p
                lspN‴≡lspNᵖ = localStatePreservation-↓∗ N₀↝⋆N″ N″—[eoN″]↓→∗N‴ N″↝[p]↓Nᵖ

            tls′≡tls″+𝟘s : allBlocks (ls′ .tree) ≡ˢ allBlocks (ls″ .tree) ++ blocksDeliveredIn p 𝟘 N″
            tls′≡tls″+𝟘s = honestLocalTreeEvolution-↓ hp lspN″ N″↝[p]↓Nᵖ lspNᵖ
        goal (makeBlock {N″} {N‴} N″MsgsDelivered N″—[eoN″]↑→∗N‴) = L.SubS.⊆-trans (ih lspN″) tls″⊆tls′
          where
            Nᵖ : GlobalState
            Nᵖ = honestBlockMaking p ls″ N″

            N″↝[p]↑Nᵖ : N″ ↝[ p ]↑ Nᵖ
            N″↝[p]↑Nᵖ = honestParty↑ lspN″ hp

            lspNᵖ : Nᵖ .states ⁉ p ≡ just ls′
            lspNᵖ = trans (sym lspN‴≡lspNᵖ) lspN′
              where
                lspN‴≡lspNᵖ : N‴ .states ⁉ p ≡ Nᵖ .states ⁉ p
                lspN‴≡lspNᵖ = localStatePreservation-∈-↑∗ N₀↝⋆N″ N″—[eoN″]↑→∗N‴ N″↝[p]↑Nᵖ

            tls″⊆tls′ : allBlocks (ls″ .tree) ⊆ˢ allBlocks (ls′ .tree)
            tls″⊆tls′ with honestLocalTreeEvolution-↑ N₀↝⋆N″ N″—[eoN″]↑→∗N‴ N″↝[p]↑Nᵖ hp lspN″ lspNᵖ
            ... | bs , tls′≡tls″+bs , _ = let open L.SubS.⊆-Reasoning Block in begin
              allBlocks (ls″ .tree)       ⊆⟨ L.SubS.xs⊆xs++ys _ _ ⟩
              allBlocks (ls″ .tree) ++ bs ⊆⟨ ≡ˢ⇒⊇ tls′≡tls″+bs ⟩
              allBlocks (ls′ .tree)       ∎
        goal (advanceRound   _) = ih lspN′
        goal (permuteParties _) = ih lspN′
        goal (permuteMsgs    _) = ih lspN′

blockMadeAfterBlockMade : ∀ {N N′ : GlobalState} →
    N ↝⋆⟨ 0 ⟩ N′
  → N .progress ≡ blockMade
  → N′ .progress ≡ blockMade
blockMadeAfterBlockMade (N↝⋆N′ , Nₜ≡N′ₜ) = blockMadeAfterBlockMadeʳ (Star⇒Starʳ N↝⋆N′) Nₜ≡N′ₜ
  where
    open RTC; open Starʳ
    blockMadeAfterBlockMadeʳ : ∀ {N N′ : GlobalState} →
        N ↝⋆ʳ N′
      → N .clock ≡ N′ .clock
      → N .progress ≡ blockMade
      → N′ .progress ≡ blockMade
    blockMadeAfterBlockMadeʳ εʳ _ NBlockMade = NBlockMade
    blockMadeAfterBlockMadeʳ {N} {N′} (_◅ʳ_ {j = N″} N↝⋆ʳN″ N″↝N′) Nₜ≡N′ₜ NBlockMade
      with
        ih ← blockMadeAfterBlockMadeʳ N↝⋆ʳN″
      | N″↝N′
    ... | deliverMsgs {N′ = N‴} N″Ready N″—[eoN″]↓→∗N‴ = contradiction blockMade≡ready λ ()
      where
        Nₜ≡N″ₜ : N .clock ≡ N″ .clock
        Nₜ≡N″ₜ = trans Nₜ≡N′ₜ $ clockPreservation-↓∗ N″—[eoN″]↓→∗N‴

        blockMade≡ready : blockMade ≡ ready
        blockMade≡ready = trans (sym $ ih Nₜ≡N″ₜ NBlockMade) N″Ready
    ... | makeBlock     _ _ = refl
    ... | advanceRound  _   = contradiction N″ₜ<N″ₜ (Nat.<-irrefl refl)
      where
        N″ₜ<N″ₜ : N″ .clock < N″ .clock
        N″ₜ<N″ₜ rewrite sym Nₜ≡N′ₜ = clockMonotonicity (Starʳ⇒Star N↝⋆ʳN″)
    ... | permuteParties _  = ih Nₜ≡N′ₜ NBlockMade
    ... | permuteMsgs    _  = ih Nₜ≡N′ₜ NBlockMade

notReadyAfterMsgsDelivered : ∀ {N N′ : GlobalState} →
    N ↝⋆⟨ 0 ⟩ N′
  → N .progress ≡ msgsDelivered
  → N′ .progress ≢ ready
notReadyAfterMsgsDelivered (N↝⋆N′ , Nₜ≡N′ₜ) = notReadyAfterMsgsDeliveredʳ (Star⇒Starʳ N↝⋆N′) Nₜ≡N′ₜ
  where
    open RTC; open Starʳ
    notReadyAfterMsgsDeliveredʳ : ∀ {N N′ : GlobalState} →
        N ↝⋆ʳ N′
      → N .clock ≡ N′ .clock
      → N .progress ≡ msgsDelivered
      → N′ .progress ≢ ready
    notReadyAfterMsgsDeliveredʳ εʳ _ NMsgsDelivered NReady = contradiction (trans (sym NReady) NMsgsDelivered) λ ()
    notReadyAfterMsgsDeliveredʳ (_◅ʳ_ {j = N″} N↝⋆ʳN″ N″↝N′) Nₜ≡N′ₜ NMsgsDelivered
      with
        ih ← notReadyAfterMsgsDeliveredʳ N↝⋆ʳN″
      | N″↝N′
    ... | deliverMsgs    _ _ = λ ()
    ... | makeBlock      _ _ = λ ()
    ... | advanceRound   _   = contradiction N″ₜ<N″ₜ (Nat.<-irrefl refl)
      where
        N″ₜ<N″ₜ : N″ .clock < N″ .clock
        N″ₜ<N″ₜ rewrite sym Nₜ≡N′ₜ = clockMonotonicity (Starʳ⇒Star N↝⋆ʳN″)
    ... | permuteParties _    = ih Nₜ≡N′ₜ NMsgsDelivered
    ... | permuteMsgs    _    = ih Nₜ≡N′ₜ NMsgsDelivered

honestGlobalTreeBlocksPreservation : ∀ {N N′ : GlobalState} {pg : Progress} →
    N ↝⋆ N′
  → N .progress ≡ pg
  → N′ .progress ≡ pg
  → N .clock ≡ N′ .clock
  → allBlocks (honestTree N) ≡ˢ allBlocks (honestTree N′)
honestGlobalTreeBlocksPreservation = honestGlobalTreeBlocksPreservationʳ ∘ Star⇒Starʳ
  where
    open RTC; open Starʳ
    honestGlobalTreeBlocksPreservationʳ : ∀ {N N′ : GlobalState} {pg : Progress} →
        N ↝⋆ʳ N′
      → N .progress ≡ pg
      → N′ .progress ≡ pg
      → N .clock ≡ N′ .clock
      → allBlocks (honestTree N) ≡ˢ allBlocks (honestTree N′)
    honestGlobalTreeBlocksPreservationʳ εʳ _ _ _ = ≡ˢ-refl
    honestGlobalTreeBlocksPreservationʳ {N} {N′} {pg} (_◅ʳ_ {j = N″} N↝⋆ʳN″ N″↝N′) pgN pgN′ Nₜ≡N′ₜ
      with
        ih ← honestGlobalTreeBlocksPreservationʳ N↝⋆ʳN″ pgN
      | N″↝N′
    ... | deliverMsgs {N′ = N‴} N″Ready N″—[eoN″]↓→∗N‴ = contradiction refl ready≢ready
      where
        NMsgsDelivered : N .progress ≡ msgsDelivered
        NMsgsDelivered = trans pgN (sym pgN′)

        Nₜ≡N″ₜ : N .clock ≡ N″ .clock
        Nₜ≡N″ₜ = trans Nₜ≡N′ₜ $ clockPreservation-↓∗ N″—[eoN″]↓→∗N‴

        ready≢ready : ready ≢ ready
        ready≢ready = subst (_≢ ready) N″Ready $ notReadyAfterMsgsDelivered (Starʳ⇒Star N↝⋆ʳN″ , Nₜ≡N″ₜ) NMsgsDelivered
    ... | makeBlock {N″} {N‴} N″MsgsDelivered N″—[eoN″]↑→∗N‴ = contradiction blockMade≡msgsDelivered λ ()
      where
        NBlockMade : N .progress ≡ blockMade
        NBlockMade = trans pgN (sym pgN′)

        Nₜ≡N″ₜ : N .clock ≡ N″ .clock
        Nₜ≡N″ₜ = trans Nₜ≡N′ₜ $ clockPreservation-↑∗ N″—[eoN″]↑→∗N‴

        blockMade≡msgsDelivered : blockMade ≡ msgsDelivered
        blockMade≡msgsDelivered = trans (sym $ blockMadeAfterBlockMade (Starʳ⇒Star N↝⋆ʳN″ , Nₜ≡N″ₜ) NBlockMade) N″MsgsDelivered
    ... | advanceRound _ = contradiction N″ₜ<N″ₜ (Nat.<-irrefl refl)
      where
        N″ₜ<N″ₜ : N″ .clock < N″ .clock
        N″ₜ<N″ₜ rewrite sym Nₜ≡N′ₜ = clockMonotonicity (Starʳ⇒Star N↝⋆ʳN″)
    ... | permuteParties {parties = ps} eoN″↭ps = goal
      where
        goal : allBlocks (honestTree N) ≡ˢ allBlocks (honestTree N′)
        goal {b} = let open Related.EquationalReasoning in begin
          b ∈ allBlocks (honestTree N)                                        ∼⟨ ih pgN′ Nₜ≡N′ₜ ⟩
          b ∈ allBlocks (honestTree N″)                                       ∼⟨ buildTreeUsesAllBlocks _ ⟩
          b ∈ genesisBlock ∷ (L.concatMap (blocks N″) (honestParties N″))
            ∼⟨ ∷-cong refl (λ {b} → begin
               b ∈ L.concatMap (blocks N″) (honestParties N″)
                 ∼⟨ concat-cong (λ {b} → begin
                    b ∈ (L.map (blocks N″) (honestParties N″))
                      ∼⟨ bag-=⇒ $ ↭⇒∼bag $ map⁺ _ $ filter-↭ _ eoN″↭ps ⟩
                    b ∈ (L.map (blocks N′) $ L.filter ¿ Honest ¿¹ ps)
                  ∎
                  ) ⟩
               b ∈ (L.concatMap (blocks N′) $ L.filter ¿ Honest ¿¹ ps)
                 ∎
              ) ⟩
          b ∈ genesisBlock ∷ (L.concatMap (blocks N′) $ L.filter ¿ Honest ¿¹ ps) ∼⟨ SK-sym $ buildTreeUsesAllBlocks _ ⟩
          b ∈ allBlocks (honestTree N′)                                          ∎
    ... | permuteMsgs _ = ih pgN′ Nₜ≡N′ₜ

honestGlobalTreeBlockInSomeHonestLocalTree : ∀ {N : GlobalState} {b : Block} →
    N₀ ↝⋆ N
  → b ∈ allBlocks (honestTree N)
  → ∃₂[ p , ls ]
        N .states ⁉ p ≡ just ls
      × b ∈ allBlocks (ls .tree)
      × Honest p
      × p ∈ N .execOrder
honestGlobalTreeBlockInSomeHonestLocalTree {N} {b} N₀↝⋆N b∈htN
  with ≡ˢ⇒⊆ (buildTreeUsesAllBlocks $ L.concatMap (blocks N) (honestParties N)) b∈htN
... | there b∈cM = b∈cM* b∈cM
  where
    b∈cM* : ∀ {ps*} →
        b ∈ L.concatMap (blocks N) (L.filter ¿ Honest ¿¹ ps*)
      → ∃₂[ p , ls ]
            N .states ⁉ p ≡ just ls
          × b ∈ allBlocks (ls .tree)
          × Honest p
          × p ∈ ps*
    b∈cM* {p* ∷ _} b∈cM[p*+ps*] with ¿ Honest p* ¿
    ... | yes hp* with L.Mem.++-∈⇔ {xs = blocks N p*} .Equivalence.to b∈cM[p*+ps*]
    ...   | inj₁ b∈bks[p*] with N .states ⁉ p* in eq
    ...     | just ls = p* , ls , eq , b∈bks[p*] , hp* , here refl
    b∈cM* {_ ∷ ps*} _
        | _
          | inj₂ b∈cM[ps*] with b∈cM* {ps*} b∈cM[ps*]
    ...     | p′ , ls′ , lsp′N , b∈tls′ , hp′ , p′∈ps* = p′ , ls′ , lsp′N , b∈tls′ , hp′ , there p′∈ps*
    b∈cM* {_ ∷ ps*} b∈cM[ps*]
        | no ¬hp* with b∈cM* {ps*} b∈cM[ps*]
    ...   | p′ , ls′ , lsp′N , b∈tls′ , hp′ , p′∈ps* = p′ , ls′ , lsp′N , b∈tls′ , hp′ , there p′∈ps*
... | here b≡gb rewrite b≡gb with L.Mem.Any↔ .Inverse.from (execOrderHasHonest N₀↝⋆N)
...   | p , p∈eoN , hp with hasStateInAltDef {N} {p} .Equivalence.from $ L.All.lookup (allPartiesHaveLocalState N₀↝⋆N) p∈eoN
...     | ls , lspN = p , ls , lspN , genesisBlockInAllBlocks (ls .tree) , hp , p∈eoN

allBlocks-processMsgsʰ : ∀ (b : Block) (msgs : List Message) (ls : LocalState) →
  b ∈ allBlocks (processMsgsʰ msgs ls .tree) ⇔ b ∈ allBlocks (ls .tree) ++ map projBlock msgs
allBlocks-processMsgsʰ = {!!}

allBlocksExtensionAtReady : ∀ {N : GlobalState} {p p′ : Party} {ls ls′ : LocalState} →
    N₀ ↝⋆ N
  → Honest p
  → Honest p′
  → N .progress ≡ ready
  → N .states ⁉ p ≡ just ls
  → N .states ⁉ p′ ≡ just ls′
  → allBlocks (ls .tree) ⊆ˢ allBlocks (ls′ .tree) ++ blocksDeliveredIn p′ 𝟘 N
allBlocksExtensionAtReady = {!!}

opaque
  unfolding honestMsgsDelivery

  honestGlobalTreeInHonestLocalTree : ∀ {N N′ : GlobalState} {p : Party} {ls : LocalState} →
      N₀ ↝⋆ N
    → Honest p
    → N .progress ≡ ready
    → N′ .progress ≡ msgsDelivered
    → N ↝⋆⟨ 0 ⟩ N′
    → N′ .states ⁉ p ≡ just ls
    → allBlocks (honestTree N) ⊆ˢ allBlocks (ls .tree)
  honestGlobalTreeInHonestLocalTree N₀↝⋆N hp NReady N′MsgsDelivered (N↝⋆N′ , Nₜ≡N′ₜ) lspN′ =
    honestGlobalTreeInHonestLocalTreeʳ N₀↝⋆N hp NReady N′MsgsDelivered (Star⇒Starʳ N↝⋆N′) Nₜ≡N′ₜ lspN′
    where
      open RTC; open Starʳ
      honestGlobalTreeInHonestLocalTreeʳ : ∀ {N N′ : GlobalState} {p : Party} {ls : LocalState} →
          N₀ ↝⋆ N
        → Honest p
        → N .progress ≡ ready
        → N′ .progress ≡ msgsDelivered
        → N ↝⋆ʳ N′
        → N .clock ≡ N′ .clock
        → N′ .states ⁉ p ≡ just ls
        → allBlocks (honestTree N) ⊆ˢ allBlocks (ls .tree)
      honestGlobalTreeInHonestLocalTreeʳ _ _ NReady N′MsgsDelivered εʳ _ _ =
        contradiction (trans (sym NReady) N′MsgsDelivered) λ ()
      honestGlobalTreeInHonestLocalTreeʳ {N} {N′} {p} {ls} N₀↝⋆N hp NReady N′MsgsDelivered (_◅ʳ_ {j = N″} N↝⋆ʳN″ N″↝N′)
        Nₜ≡N′ₜ lspN′ = goal NReady N′MsgsDelivered N″↝N′
        where
          pHasInN″ : p hasStateIn N″
          pHasInN″ = hasState⇔-↝⋆ (N″↝N′ ◅ ε) .Equivalence.from $ hasStateInAltDef {N′} .Equivalence.to (ls , lspN′)

          goal :
              N .progress ≡ ready
            → N′ .progress ≡ msgsDelivered
            → N″ ↝ N′
            → allBlocks (honestTree N) ⊆ˢ allBlocks (ls .tree)
          goal _ _ (deliverMsgs {N′ = N°} N″Ready N″—[eoN″]↓→∗N°) = L.SubS.⊆-trans (≡ˢ⇒⊆ tbsN≡tbsN″) tbsN″⊆tbs[ls]
            where
              N₀↝⋆N″ : N₀ ↝⋆ N″
              N₀↝⋆N″ = N₀↝⋆N ◅◅ (Starʳ⇒Star N↝⋆ʳN″)

              Nₜ≡N″ₜ : N .clock ≡ N″ .clock
              Nₜ≡N″ₜ = trans Nₜ≡N′ₜ (clockPreservation-↓∗ N″—[eoN″]↓→∗N°)

              tbsN≡tbsN″ : allBlocks (honestTree N) ≡ˢ allBlocks (honestTree N″)
              tbsN≡tbsN″ = honestGlobalTreeBlocksPreservation (Starʳ⇒Star N↝⋆ʳN″) NReady N″Ready Nₜ≡N″ₜ

              tbsN″⊆tbs[ls] : allBlocks (honestTree N″) ⊆ˢ allBlocks (ls .tree)
              tbsN″⊆tbs[ls] {b} b∈tbsN″ with honestGlobalTreeBlockInSomeHonestLocalTree N₀↝⋆N″ b∈tbsN″
              ... | p′ , ls′ , ls′p′N″ , b∈tbs[ls′] , hp′ , p′∈eoN″ with hasStateInAltDef {N″} .Equivalence.from pHasInN″
              ...   | ls″ , ls″pN″ = subst (λ ◆ → b ∈ allBlocks (◆ .tree)) ls″+𝟘s≡ls b∈tbs[ls″+𝟘s]
                where
                  Nᵖ : GlobalState
                  Nᵖ = honestMsgsDelivery p ls″ N″

                  N″↝[p]↓Nᵖ : N″ ↝[ p ]↓ Nᵖ
                  N″↝[p]↓Nᵖ = honestParty↓ ls″pN″ hp

                  lspNᵖ : Nᵖ .states ⁉ p ≡ just ls
                  lspNᵖ = trans (sym $ localStatePreservation-↓∗ N₀↝⋆N″ N″—[eoN″]↓→∗N° N″↝[p]↓Nᵖ) lspN′

                  𝟘s : List Message
                  𝟘s = L.map msg (immediateMsgs p N″)

                  ls″+𝟘s : LocalState
                  ls″+𝟘s = processMsgsʰ 𝟘s ls″

                  ls″+𝟘s≡ls : ls″+𝟘s ≡ ls
                  ls″+𝟘s≡ls = M.just-injective *ls″+𝟘s≡ls
                    where
                      *ls″+𝟘s≡ls : just ls″+𝟘s ≡ just ls
                      *ls″+𝟘s≡ls rewrite sym $ set-⁉ (N″ .states) p ls″+𝟘s = lspNᵖ

                  b∈tbs[ls″+𝟘s] : b ∈ allBlocks (ls″+𝟘s .tree)
                  b∈tbs[ls″+𝟘s] = allBlocks-processMsgsʰ b 𝟘s ls″ .Equivalence.from b∈tbs[ls″]+𝟘s
                    where
                      b∈tbs[ls″]+𝟘s : b ∈ allBlocks (ls″ .tree) ++ L.map projBlock 𝟘s
                      b∈tbs[ls″]+𝟘s rewrite sym $ L.map-∘ {g = projBlock} {f = msg} (immediateMsgs p N″) =
                        allBlocksExtensionAtReady N₀↝⋆N″ hp′ hp N″Ready ls′p′N″ ls″pN″ b∈tbs[ls′]
          goal _ _ (permuteParties _) = honestGlobalTreeInHonestLocalTreeʳ N₀↝⋆N hp NReady N′MsgsDelivered N↝⋆ʳN″ Nₜ≡N′ₜ lspN′
          goal _ _ (permuteMsgs    _) = honestGlobalTreeInHonestLocalTreeʳ N₀↝⋆N hp NReady N′MsgsDelivered N↝⋆ʳN″ Nₜ≡N′ₜ lspN′

honestGlobalTreeInHonestLocalTree-↝⋆⟨1⟩ : ∀ {N N′ : GlobalState} {p : Party} {ls′ : LocalState} →
    N₀ ↝⋆ N
  → Honest p
  → N .progress ≡ ready
  → N ↝⋆⟨ 1 ⟩ N′
  → N′ .progress ≡ ready
  → N′ .states ⁉ p ≡ just ls′
  → allBlocks (honestTree N) ⊆ˢ allBlocks (ls′ .tree)
honestGlobalTreeInHonestLocalTree-↝⋆⟨1⟩ N₀↝⋆ʳN hp NReady (N↝⋆N′ , Nₜ+1≡N′ₜ) = honestGlobalTreeInHonestLocalTree-↝⋆⟨1⟩ʳ N₀↝⋆ʳN hp NReady (Star⇒Starʳ N↝⋆N′) Nₜ+1≡N′ₜ
  where
    open RTC; open Starʳ
    honestGlobalTreeInHonestLocalTree-↝⋆⟨1⟩ʳ : ∀ {N N′ : GlobalState} {p : Party} {ls′ : LocalState} →
        N₀ ↝⋆ N
      → Honest p
      → N .progress ≡ ready
      → N ↝⋆ʳ N′
      → 1 + N .clock ≡ N′ .clock
      → N′ .progress ≡ ready
      → N′ .states ⁉ p ≡ just ls′
      → allBlocks (honestTree N) ⊆ˢ allBlocks (ls′ .tree)
    honestGlobalTreeInHonestLocalTree-↝⋆⟨1⟩ʳ {N} {N′} {p} {ls′} N₀↝⋆N hp NReady (_◅ʳ_ {j = N″} N↝⋆ʳN″ N″↝N′) Nₜ+1≡N′ₜ N′Ready lspN′ with N″↝N′
    ... | advanceRound N″BlockMade = goal N↝⋆ʳN″ (Nat.suc-injective Nₜ+1≡N′ₜ) N″BlockMade lspN′
      where
        goal : ∀ {N*} →
             N ↝⋆ʳ N*
           → N .clock ≡ N* .clock
           → N* .progress ≡ blockMade
           → ∀ {ls′} →
               N* .states ⁉ p ≡ just ls′
             → allBlocks (honestTree N) ⊆ˢ allBlocks (ls′ .tree)
        goal εʳ _ N*BlockMade _ = contradiction (subst (_≡ blockMade) NReady N*BlockMade) λ ()
        goal {N*} (_◅ʳ_ {j = N‴} N↝⋆ʳN‴ N‴↝N*) Nₜ≡N*ₜ N*BlockMade {ls*} lspN*
          with N‴↝N*
        ... | makeBlock {N′ = N⁺} N‴MsgsDelivered N‴—[eoN‴]↑→∗N⁺ = L.SubS.⊆-trans htN⊆tls‴ tsl‴⊆tls*
          where
            N₀↝⋆N‴ : N₀ ↝⋆ N‴
            N₀↝⋆N‴ = N₀↝⋆N ◅◅ Starʳ⇒Star N↝⋆ʳN‴

            pHasInN‴ : p hasStateIn N‴
            pHasInN‴ = L.All.lookup (allPartiesHaveLocalState N₀↝⋆N‴) p∈N‴
              where
                p∈N‴ : p ∈ N‴ .execOrder
                p∈N‴ = ∈-resp-↭ (↭-sym (execOrderPreservation-↭-↝ N‴↝N*)) p∈N*
                  where
                    N₀↝⋆N* : N₀ ↝⋆ N*
                    N₀↝⋆N* = N₀↝⋆N‴ ◅◅ (N‴↝N* ◅ ε)

                    p∈N* : p ∈ N* .execOrder
                    p∈N* = hasState⇒∈execOrder N₀↝⋆N* (≡just⇒Is-just lspN*)

            ls‴ = LocalState ∋ M.to-witness pHasInN‴

            lspN‴ : N‴ .states ⁉ p ≡ just ls‴
            lspN‴ = Is-just⇒to-witness pHasInN‴

            Nₚ = GlobalState ∋ honestBlockMaking p ls‴ N‴

            N‴↝[p]↑Nₚ : N‴ ↝[ p ]↑ Nₚ
            N‴↝[p]↑Nₚ = honestParty↑ lspN‴ hp

            lspNₚ : Nₚ .states ⁉ p ≡ just ls*
            lspNₚ = trans (sym lspN⁺≡lspNₚ) lspN*
              where
                lspN⁺≡lspNₚ : N⁺ .states ⁉ p ≡ Nₚ .states ⁉ p
                lspN⁺≡lspNₚ = localStatePreservation-∈-↑∗ N₀↝⋆N‴ N‴—[eoN‴]↑→∗N⁺ N‴↝[p]↑Nₚ

            htN⊆tls‴ : allBlocks (honestTree N) ⊆ˢ allBlocks (ls‴ .tree)
            htN⊆tls‴ = honestGlobalTreeInHonestLocalTree N₀↝⋆N hp NReady N‴MsgsDelivered (Starʳ⇒Star N↝⋆ʳN‴ , Nₜ≡N‴ₜ) lspN‴
              where
                Nₜ≡N‴ₜ : N .clock ≡ N‴ .clock
                Nₜ≡N‴ₜ rewrite Nₜ≡N*ₜ = clockPreservation-↑∗ N‴—[eoN‴]↑→∗N⁺

            tsl‴⊆tls* : allBlocks (ls‴ .tree) ⊆ˢ allBlocks (ls* .tree)
            tsl‴⊆tls* with honestLocalTreeEvolution-↑ N₀↝⋆N‴ N‴—[eoN‴]↑→∗N⁺ N‴↝[p]↑Nₚ hp lspN‴ lspNₚ
            ... | bs , tls*≡tls‴+bs , _ = let open L.SubS.⊆-Reasoning Block in begin
              allBlocks (ls‴ .tree)       ⊆⟨ L.SubS.xs⊆xs++ys _ _ ⟩
              allBlocks (ls‴ .tree) ++ bs ⊆⟨ ≡ˢ⇒⊇ tls*≡tls‴+bs ⟩
              allBlocks (ls* .tree)       ∎

        ... | permuteParties _ = goal N↝⋆ʳN‴ Nₜ≡N*ₜ N*BlockMade lspN*
        ... | permuteMsgs    _ = goal N↝⋆ʳN‴ Nₜ≡N*ₜ N*BlockMade lspN*

    ... | permuteParties _ = honestGlobalTreeInHonestLocalTree-↝⋆⟨1⟩ʳ N₀↝⋆N hp NReady N↝⋆ʳN″ Nₜ+1≡N′ₜ N′Ready lspN′
    ... | permuteMsgs    _ = honestGlobalTreeInHonestLocalTree-↝⋆⟨1⟩ʳ N₀↝⋆N hp NReady N↝⋆ʳN″ Nₜ+1≡N′ₜ N′Ready lspN′

honestGlobalTreeInHonestLocalTree-↝⁺ : ∀ {N N′ : GlobalState} {p : Party} {ls′ : LocalState} →
    N₀ ↝⋆ N
  → Honest p
  → N .progress ≡ ready
  → N ↝⁺ N′
  → N′ .states ⁉ p ≡ just ls′
  → allBlocks (honestTree N) ⊆ˢ allBlocks (ls′ .tree)
honestGlobalTreeInHonestLocalTree-↝⁺ {N} {N′} {p} {ls′} N₀↝⋆N hp NReady (N↝⋆N′ , Nₜ<N′ₜ) lsN′p
  with ∃ReadyBetweenSlots NReady N↝⋆N′ (Nat.n≤1+n _ , Nₜ<N′ₜ)
... | N″ , N″Ready , N″ₜ≡Nₜ+1 , N↝⋆N″ , N″↝⋆N′
  with
      pHasInN″ ← hasState⇔-↝⋆ N″↝⋆N′ .Equivalence.from $ subst M.Is-just (sym lsN′p) (M.Any.just tt)
    | hasStateInAltDef {N″} .Equivalence.from pHasInN″
... | ls″ , lsN″p = L.SubS.⊆-trans htN⊆tls″ tls″⊆tls′
  where
    N₀↝⋆N″ : N₀ ↝⋆ N″
    N₀↝⋆N″ = N₀↝⋆N ◅◅ N↝⋆N″

    tls″⊆tls′ : allBlocks (ls″ .tree) ⊆ˢ allBlocks (ls′ .tree)
    tls″⊆tls′ = honestLocalTreeBlocksMonotonicity N₀↝⋆N″ hp lsN″p N″↝⋆N′ lsN′p

    htN⊆tls″ : allBlocks (honestTree N) ⊆ˢ allBlocks (ls″ .tree)
    htN⊆tls″ = honestGlobalTreeInHonestLocalTree-↝⋆⟨1⟩ N₀↝⋆N hp NReady (N↝⋆N″ , sym N″ₜ≡Nₜ+1) N″Ready lsN″p

allGBsInHonestTree₀ :
    L.All.All (_≡ genesisBlock) (allBlocks (honestTree N₀))
allGBsInHonestTree₀ = L.All.tabulate allGBsInHonestTree₀′
  where
    allGBsInHonestTree₀′ : ∀ {b} → b ∈ allBlocks (honestTree N₀) → b ≡ genesisBlock
    allGBsInHonestTree₀′ {b} b∈htN₀ with honestGlobalTreeBlockInSomeHonestLocalTree RTC.ε b∈htN₀
    ... | p , ls , lspN₀ , b∈blk[tls] , hp , p∈ps₀ = L.Any.singleton⁻ b∈[gb]
      where
        tls≡t₀ : ls .tree ≡ tree₀
        tls≡t₀ rewrite M.just-injective $ sym $ trans (sym $ map-⁉-∈-just _ p∈ps₀) lspN₀ = refl

        b∈[gb] : b ∈ [ genesisBlock ]
        b∈[gb] rewrite sym instantiated | sym tls≡t₀ = b∈blk[tls]

honestGlobalTreeBlocksMonotonicity : ∀ {N N′ : GlobalState} →
    N₀ ↝⋆ N
  → N ↝ N′
  → allBlocks (honestTree N) ⊆ˢ allBlocks (honestTree N′)
honestGlobalTreeBlocksMonotonicity {N} {N′} N₀↝⋆N N↝N′ {b} b∈htN
  with honestGlobalTreeBlockInSomeHonestLocalTree N₀↝⋆N b∈htN
... | p , ls , lspN , b∈lst , hp , p∈eoN =
    b∈cM ∶
  b ∈ L.concatMap (blocks N′) (honestParties N′)                |> L.SubS.xs⊆x∷xs _ _ ∶
  b ∈ genesisBlock ∷ L.concatMap (blocks N′) (honestParties N′) |> ≡ˢ⇒⊇ (buildTreeUsesAllBlocks _) ∶
  b ∈ allBlocks (honestTree N′)
  where
    open import Function.Reasoning
    open RTC

    p∈eoN′ : p ∈ N′ .execOrder
    p∈eoN′ = ∈-resp-↭ (execOrderPreservation-↭ (N↝N′ ◅ ε)) p∈eoN

    ∃lspN′ : ∃[ ls′ ] N′ .states ⁉ p ≡ just ls′
    ∃lspN′ = hasStateInAltDef {N′} .Equivalence.from pHasInN′
      where
        pHasInN′ : p hasStateIn N′
        pHasInN′ = hasState⇔-↝⋆ (N↝N′ ◅ ε) .Equivalence.to $ hasStateInAltDef {N} .Equivalence.to (ls , lspN)

    b∈cM : b ∈ L.concatMap (blocks N′) (honestParties N′)
    b∈cM = L.Mem.concat-∈↔ .Inverse.to (b∈cM* p∈eoN′)
      where
        b∈cM* : ∀ {ps*} → p ∈ ps* → ∃[ bs ] b ∈ bs × bs ∈ L.map (blocks N′) (L.filter ¿ Honest ¿¹ ps*)
        b∈cM* {[]} ()
        b∈cM* {p* ∷ ps*} (here p≡p*) rewrite sym p≡p* | hp with ∃lspN′
        ... | ls′ , lspN′ rewrite lspN′ = allBlocks (ls′ .tree) , b∈ls′t , here refl
          where
            b∈ls′t : b ∈ allBlocks (ls′ .tree)
            b∈ls′t = honestLocalTreeBlocksMonotonicity N₀↝⋆N hp lspN (N↝N′ ◅ ε) lspN′ b∈lst
        b∈cM* {p* ∷ ps*} (there p∈ps*) with b∈cM* {ps*} p∈ps*
        ... | bs′ , b∈bs′ , bs′∈bss[ps*] with ¿ Honest p* ¿
        ...   | yes _ = bs′ , b∈bs′ , there bs′∈bss[ps*]
        ...   | no  _ = bs′ , b∈bs′ , bs′∈bss[ps*]
