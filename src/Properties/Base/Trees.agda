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
open import Protocol.Tree ⦃ params ⦄
open import Protocol.Tree.Properties ⦃ params ⦄
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.Time ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.LocalState ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.ExecutionOrder ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.Network ⦃ params ⦄ ⦃ assumptions ⦄
open import Prelude.AssocList.Properties.Ext using (set-⁉; map-⁉-∈-just; map-⁉-≡; map-⁉-≢)
open import Prelude.STS.Properties using (—[]→∗⇒—[]→∗ʳ; —[]→∗ʳ⇒—[]→∗; —[∷ʳ]→∗-split; —[[]]→∗ʳ⇒≡)
open import Data.List.Relation.Binary.BagAndSetEquality using (∷-cong; ++-cong; concat-cong; map-cong; bag-=⇒; ↭⇒∼bag)
open import Data.Maybe.Properties.Ext using (Is-just⇒to-witness; ≡just⇒Is-just)
open import Data.List.Properties.Ext using (filter-∘-×)
open import Data.List.Membership.Propositional.Properties.Ext using (∈-∷⁻; ∈-∷-≢⁻; ∉-∷⁻)
open import Data.List.Relation.Unary.AllPairs.Properties.Ext using (headʳ)
open import Data.List.Relation.Unary.Unique.Propositional.Properties using (Unique[x∷xs]⇒x∉xs)
open import Data.List.Relation.Binary.Subset.Propositional.Properties.Ext using (⊆-++-comm; ++-meet)
open import Data.List.Relation.Binary.Permutation.Propositional using (↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∈-resp-↭; map⁺; shift; ++-comm)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties.Ext using (filter-↭; Unique-resp-↭)
open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_; ≡ˢ⇒⊆; ≡ˢ⇒⊇; ≡ˢ-refl; ≡ˢ-sym; ≡⇒≡ˢ; ⊆×≡ˢ⇒++-≡ˢ)
open import Relation.Unary using (_≐_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Ext using (Starʳ)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.Ext using (Star⇒Starʳ; Starʳ⇒Star)
open import Relation.Binary.PropositionalEquality using (≢-sym)
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

tree₀InN₀ : ∀ {p : Party} {ls : LocalState} → N₀ .states ⁉ p ≡ just ls → ls .tree ≡ tree₀
tree₀InN₀ {p} {ls} = tree₀InN₀′
  where
    tree₀InN₀′ : ∀ {ps} → map (_, it .def) ps ⁉ p ≡ just ls → ls .tree ≡ tree₀
    tree₀InN₀′ {p′ ∷ ps′} eq = case p ≟ p′ of λ where
      (yes p≡p′) →
        sym $
          cong tree $
            M.just-injective $
              trans (sym $ map-⁉-≡ _) $ subst (λ ◆ → map (_, it .def) (◆ ∷ ps′) ⁉ p ≡ just ls) (sym p≡p′) eq
      (no  p≢p′) → tree₀InN₀′ {ps′} $ trans (sym $ map-⁉-≢ _ p≢p′) eq

noImmediateMsgsIfNotReady : ∀ {N : GlobalState} (p : Party) →
    N₀ ↝⋆ N
  → N .progress ≢ ready
  → blocksDeliveredIn p 𝟘 N ≡ []
noImmediateMsgsIfNotReady = {!!}

noImmediateMsgsAfterReady : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → N .progress ≢ ready
  → L.All.All ((Fi._> (Delay ∋ 𝟘)) ∘ cd) (N .messages)
noImmediateMsgsAfterReady = {!!}

blocksDeliveredIn-⊆-↑∗ : ∀ {N N′ : GlobalState} {d : Delay} {p : Party} {ps : List Party} →
    _ ⊢ N —[ ps ]↑→∗ N′
  → blocksDeliveredIn p d N ⊆ˢ blocksDeliveredIn p d N′
blocksDeliveredIn-⊆-↑∗ = {!!}

opaque

  unfolding honestMsgsDelivery corruptMsgsDelivery

  blocksDeliveredIn-⊆-↓ : ∀ {N N′ : GlobalState} {p p′ : Party} →
      _ ⊢ N —[ p′ ]↓→ N′
    → blocksDeliveredIn p 𝟙 N ⊆ˢ blocksDeliveredIn p 𝟙 N′
  blocksDeliveredIn-⊆-↓ (unknownParty↓ _) = L.SubS.⊆-refl
  blocksDeliveredIn-⊆-↓ {N} {N′} {p} {p′} (honestParty↓ x x₁) {b} b∈𝟙s with L.Mem.∈-map⁻ _ b∈𝟙s
  ... | e , e∈𝟙s , b≡blk[e] with L.Mem.∈-filter⁻ (λ e → ¿ DeliveredIn e ¿² p 𝟙) {xs = N .messages} e∈𝟙s
  ...   | e∈msN , cd[e]≡𝟙 , rcv[e]≡p rewrite b≡blk[e] = goal e∈msN
    where
      goal : ∀ {es} →
          e ∈ es
        → projBlock (msg e) ∈ L.map (projBlock ∘ msg) (L.filter (λ e′ → ¿ DeliveredIn e′ ¿² p 𝟙) (L.filter ¿ ¬_ ∘ flip Immediate p′ ¿¹ es))
      goal {e′ ∷ es} (here e≡e′) rewrite sym e≡e′
        with ¿ ¬_ ∘ flip Immediate p′ ¿¹ e
      ... | no ≡𝟘 = contradiction (dec-de-morgan₂ (inj₁ cd[e]≢𝟘)) ≡𝟘
        where
          cd[e]≢𝟘 : e .cd ≢ 𝟘
          cd[e]≢𝟘 rewrite cd[e]≡𝟙 = λ ()
      ... | yes ≢𝟘
        rewrite
          L.filter-accept ¿ ¬_ ∘ flip Immediate p′ ¿¹ {e} {es} ≢𝟘
        | L.filter-accept (λ e′ → ¿ DeliveredIn e′ ¿² p 𝟙) {e} {L.filter ¿ ¬_ ∘ flip Immediate p′ ¿¹ es} (cd[e]≡𝟙 , rcv[e]≡p)
        = here refl
      goal {e′ ∷ es} (there e∈es)
        with ¿ ¬_ ∘ flip Immediate p′ ¿¹ e′
      ... | no  ≡𝟘 rewrite L.filter-reject ¿ ¬_ ∘ flip Immediate p′ ¿¹ {e′} {es} ≡𝟘 = goal e∈es
      ... | yes ≢𝟘 rewrite L.filter-accept ¿ ¬_ ∘ flip Immediate p′ ¿¹ {e′} {es} ≢𝟘
          with e′ .cd ≟ 𝟙 | e′ .rcv ≟ p
      ...   | yes _       | no _  = goal e∈es
      ...   | no  _       | _     = goal e∈es
      ...   | yes _       | yes _
            with e′ ≟ e
      ...     | yes e′≡e rewrite e′≡e = here refl
      ...     | no  _ = there $ goal e∈es
  blocksDeliveredIn-⊆-↓ {N} {N′} {p} {p′} (corruptParty↓ _ _) {b} b∈𝟙s
    with
      processMsgsᶜ
        (fetchNewMsgs p′ N .proj₁)
        (fetchNewMsgs p′ N .proj₂ .clock)
        (fetchNewMsgs p′ N .proj₂ .history)
        (fetchNewMsgs p′ N .proj₂ .messages)
        (fetchNewMsgs p′ N .proj₂ .advState)
  ... | newMds , _  with L.Mem.∈-map⁻ _ b∈𝟙s
  ...   | e , e∈𝟙s , b≡blk[e] with L.Mem.∈-filter⁻ (λ e → ¿ DeliveredIn e ¿² p 𝟙) {xs = N .messages} e∈𝟙s
  ...     | e∈msN , cd[e]≡𝟙 , rcv[e]≡p rewrite b≡blk[e] = goal newMds
    where
      Nᶜ : List (Message × DelayMap) → GlobalState
      Nᶜ mds = broadcastMsgsᶜ mds (removeImmediateMsgs p′ N)

      goal : ∀ mds → projBlock (msg e) ∈ L.map (projBlock ∘ msg) (L.filter (λ e′ → ¿ DeliveredIn e′ ¿² p 𝟙) (Nᶜ mds .messages))
      goal [] = goal-[] e∈msN
        where
          goal-[] : ∀ {es} →
              e ∈ es
            → projBlock (msg e) ∈ L.map (projBlock ∘ msg) (L.filter (λ e′ → ¿ DeliveredIn e′ ¿² p 𝟙) (L.filter ¿ ¬_ ∘ flip Immediate p′ ¿¹ es))
          goal-[] {e′ ∷ es} (here e≡e′) rewrite sym e≡e′
            with ¿ ¬_ ∘ flip Immediate p′ ¿¹ e
          ... | no ≡𝟘 = contradiction (dec-de-morgan₂ (inj₁ cd[e]≢𝟘)) ≡𝟘
            where
              cd[e]≢𝟘 : e .cd ≢ 𝟘
              cd[e]≢𝟘 rewrite cd[e]≡𝟙 = λ ()
          ... | yes ≢𝟘
            rewrite
              L.filter-accept ¿ ¬_ ∘ flip Immediate p′ ¿¹ {e} {es} ≢𝟘
            | L.filter-accept (λ e′ → ¿ DeliveredIn e′ ¿² p 𝟙) {e} {L.filter ¿ ¬_ ∘ flip Immediate p′ ¿¹ es} (cd[e]≡𝟙 , rcv[e]≡p)
            = here refl
          goal-[] {e′ ∷ es} (there e∈es)
            with ¿ ¬_ ∘ flip Immediate p′ ¿¹ e′
          ... | no  ≡𝟘 rewrite L.filter-reject ¿ ¬_ ∘ flip Immediate p′ ¿¹ {e′} {es} ≡𝟘 = goal-[] e∈es
          ... | yes ≢𝟘 rewrite L.filter-accept ¿ ¬_ ∘ flip Immediate p′ ¿¹ {e′} {es} ≢𝟘
              with e′ .cd ≟ 𝟙 | e′ .rcv ≟ p
          ...   | yes _       | no _  = goal-[] e∈es
          ...   | no  _       | _     = goal-[] e∈es
          ...   | yes _       | yes _
                with e′ ≟ e
          ...     | yes e′≡e rewrite e′≡e = here refl
          ...     | no  _ = there $ goal-[] e∈es
      goal ((m , φ) ∷ mds)
        rewrite
          L.filter-++ (λ e′ → ¿ DeliveredIn e′ ¿² p 𝟙) (map (λ party → ⦅ m , party , φ party .value ⦆) (Nᶜ mds .execOrder)) (Nᶜ mds .messages)
        | L.map-++
            (projBlock ∘ msg)
            (filter (λ e′ → ¿ DeliveredIn e′ ¿² p 𝟙) (map (λ party → ⦅ m , party , φ party .value ⦆) (Nᶜ mds .execOrder)))
            (filter (λ e′ → ¿ DeliveredIn e′ ¿² p 𝟙) (Nᶜ mds .messages))
        = L.Mem.++-∈⇔ .Equivalence.from (inj₂ $ goal mds)

blocksDeliveredIn-⊆-↓∗ : ∀ {N N′ : GlobalState} {p : Party} {ps : List Party} →
    _ ⊢ N —[ ps ]↓→∗ N′
  → blocksDeliveredIn p 𝟙 N ⊆ˢ blocksDeliveredIn p 𝟙 N′
blocksDeliveredIn-⊆-↓∗ = {!!}

noBlocksDeliveredIn𝟚AtReady : ∀ {N : GlobalState} {p : Party} →
    N₀ ↝⋆ N
  → N .progress ≡ ready
  → blocksDeliveredIn p 𝟚 N ≡ []
noBlocksDeliveredIn𝟚AtReady = {!!}

-- TODO: This opaque degrades the performance significatively, investigate further.
opaque

  unfolding honestMsgsDelivery corruptMsgsDelivery honestBlockMaking corruptBlockMaking

  ≥𝟘p₁×≢𝟘p₂≐≥𝟘p₁ : ∀ {d : Delay} {p₁ p₂ : Party} →
    (λ env → DeliveredIn env p₁ d × ¬ Immediate env p₂) ≐ (λ env → DeliveredIn env p₁ d)
  ≥𝟘p₁×≢𝟘p₂≐≥𝟘p₁ = {!!}

  delayedBlocksEvolution-↓* : ∀ {N N′ : GlobalState} {p₁ p₂ : Party} →
      _ ⊢ N —[ N .execOrder ]↓→∗ N′
    → Unique (N .execOrder)
    → p₁ ∈ N .execOrder
    → p₂ ∈ N .execOrder
    → ∃[ bs ]
        blocksDeliveredIn p₁ 𝟙 N′ ++ blocksDeliveredIn p₁ 𝟚 N′ ≡ˢ blocksDeliveredIn p₁ 𝟙 N ++ blocksDeliveredIn p₁ 𝟚 N ++ bs
        ×
        blocksDeliveredIn p₂ 𝟙 N′ ++ blocksDeliveredIn p₂ 𝟚 N′ ≡ˢ blocksDeliveredIn p₂ 𝟙 N ++ blocksDeliveredIn p₂ 𝟚 N ++ bs
  delayedBlocksEvolution-↓* {N} {N′} {p₁} {p₂} N—[eoN]↓→∗N′ eoN! p₁∈eoN p₂∈eoN =
    delayedBlocksEvolution-↓*ʳ (reverseView (N .execOrder)) (—[]→∗⇒—[]→∗ʳ N—[eoN]↓→∗N′) eoN!
    where
      open import Data.List.Reverse

      delayedBlocks≡ : List Block → Party → GlobalState → GlobalState → Type
      delayedBlocks≡ bs p N N′ = blocksDeliveredIn p 𝟙 N ++ blocksDeliveredIn p 𝟚 N ≡ˢ blocksDeliveredIn p 𝟙 N′ ++ blocksDeliveredIn p 𝟚 N′ ++ bs

      delayedBlocksEvolution-↓*ʳ : ∀ {N* ps} →
          Reverse ps
        → _ ⊢ N —[ ps ]↓→∗ʳ N*
        → Unique ps
        → ∃[ bs ] delayedBlocks≡ bs p₁ N* N × delayedBlocks≡ bs p₂ N* N
      delayedBlocksEvolution-↓*ʳ [] N—[ps]↓→∗ʳN* _ rewrite sym $ —[[]]→∗ʳ⇒≡ N—[ps]↓→∗ʳN* =
        [] ,
        ≡ˢ-++-identityʳ (blocksDeliveredIn p₁ 𝟙 N) (blocksDeliveredIn p₁ 𝟚 N) ,
        ≡ˢ-++-identityʳ (blocksDeliveredIn p₂ 𝟙 N) (blocksDeliveredIn p₂ 𝟚 N)
        where
          ≡ˢ-++-identityʳ : ∀ (bs bs′ : List Block) → bs ++ bs′ ≡ˢ bs ++ bs′ ++ []
          ≡ˢ-++-identityʳ bs bs′ = ≡⇒≡ˢ $ let open ≡-Reasoning in begin
            bs ++ bs′            ≡⟨ L.++-identityʳ (bs ++ bs′) ⟨
            (bs ++ bs′) ++ []    ≡⟨ L.++-assoc bs _ _ ⟩
            bs ++ bs′ ++ []      ∎
      delayedBlocksEvolution-↓*ʳ {N* = N*} (ps′ ∶ ps′r ∶ʳ p′) N—[ps′+p′]↓→∗ʳN* [ps′+p′]!
        with —[∷ʳ]→∗-split (—[]→∗ʳ⇒—[]→∗ N—[ps′+p′]↓→∗ʳN*)
      ... | N‴ , N—[ps′]↓→∗N‴ , N‴—[p′]↓→N* = goal N‴—[p′]↓→N*
        where
           ps′! : Unique ps′
           ps′! = headʳ [ps′+p′]!

           ih : ∃[ bs ] delayedBlocks≡ bs p₁ N‴ N × delayedBlocks≡ bs p₂ N‴ N
           ih = delayedBlocksEvolution-↓*ʳ ps′r (—[]→∗⇒—[]→∗ʳ N—[ps′]↓→∗N‴) ps′!

           dlv? : (p* : Party) (d : Delay) → Decidable¹ λ e′ → DeliveredIn e′ p* d
           dlv? p* d e′ = ¿ DeliveredIn e′ ¿² p* d

           is𝟘? : (p* : Party) → Decidable¹ (¬_ ∘ flip Immediate p*)
           is𝟘? p* = ¿ ¬_ ∘ flip Immediate p* ¿¹

           goal : _ ⊢ N‴ —[ p′ ]↓→ N* → ∃[ bs ] delayedBlocks≡ bs p₁ N* N × delayedBlocks≡ bs p₂ N* N
           goal (unknownParty↓ _) = ih
           goal (honestParty↓ _ _) with ih
           ... | bs , dbsN‴Np₁ , dbsN‴Np₂
             rewrite
               sym $ filter-∘-× (dlv? p₁ 𝟙) (is𝟘? p′) (N‴ .messages)
             | sym $ filter-∘-× (dlv? p₁ 𝟚) (is𝟘? p′) (N‴ .messages)
             | sym $ filter-∘-× (dlv? p₂ 𝟙) (is𝟘? p′) (N‴ .messages)
             | sym $ filter-∘-× (dlv? p₂ 𝟚) (is𝟘? p′) (N‴ .messages)
             | L.filter-≐ (λ e → dlv? p₁ 𝟙 e ×-dec is𝟘? p′ e) (dlv? p₁ 𝟙) ≥𝟘p₁×≢𝟘p₂≐≥𝟘p₁ (N‴ .messages)
             | L.filter-≐ (λ e → dlv? p₁ 𝟚 e ×-dec is𝟘? p′ e) (dlv? p₁ 𝟚) ≥𝟘p₁×≢𝟘p₂≐≥𝟘p₁ (N‴ .messages)
             | L.filter-≐ (λ e → dlv? p₂ 𝟙 e ×-dec is𝟘? p′ e) (dlv? p₂ 𝟙) ≥𝟘p₁×≢𝟘p₂≐≥𝟘p₁ (N‴ .messages)
             | L.filter-≐ (λ e → dlv? p₂ 𝟚 e ×-dec is𝟘? p′ e) (dlv? p₂ 𝟚) ≥𝟘p₁×≢𝟘p₂≐≥𝟘p₁ (N‴ .messages)
               = bs , dbsN‴Np₁ , dbsN‴Np₂
           goal (corruptParty↓ _ _) with
             processMsgsᶜ
               (fetchNewMsgs p′ N‴ .proj₁)
               (fetchNewMsgs p′ N‴ .proj₂ .clock)
               (fetchNewMsgs p′ N‴ .proj₂ .history)
               (fetchNewMsgs p′ N‴ .proj₂ .messages)
               (fetchNewMsgs p′ N‴ .proj₂ .advState)
           ... | newMds , _ = goal* newMds
             where
               Nᶜ : List (Message × DelayMap) → GlobalState
               Nᶜ mds = broadcastMsgsᶜ mds (removeImmediateMsgs p′ N‴)

               goal* : ∀ mds → ∃[ bs ] delayedBlocks≡ bs p₁ (Nᶜ mds) N × delayedBlocks≡ bs p₂ (Nᶜ mds) N
               goal* [] with ih
               ... | bs , dbsN‴Np₁ , dbsN‴Np₂
                 rewrite
                   sym $ filter-∘-× (dlv? p₁ 𝟙) (is𝟘? p′) (N‴ .messages)
                 | sym $ filter-∘-× (dlv? p₁ 𝟚) (is𝟘? p′) (N‴ .messages)
                 | sym $ filter-∘-× (dlv? p₂ 𝟙) (is𝟘? p′) (N‴ .messages)
                 | sym $ filter-∘-× (dlv? p₂ 𝟚) (is𝟘? p′) (N‴ .messages)
                 | L.filter-≐ (λ e → dlv? p₁ 𝟙 e ×-dec is𝟘? p′ e) (dlv? p₁ 𝟙) ≥𝟘p₁×≢𝟘p₂≐≥𝟘p₁ (N‴ .messages)
                 | L.filter-≐ (λ e → dlv? p₁ 𝟚 e ×-dec is𝟘? p′ e) (dlv? p₁ 𝟚) ≥𝟘p₁×≢𝟘p₂≐≥𝟘p₁ (N‴ .messages)
                 | L.filter-≐ (λ e → dlv? p₂ 𝟙 e ×-dec is𝟘? p′ e) (dlv? p₂ 𝟙) ≥𝟘p₁×≢𝟘p₂≐≥𝟘p₁ (N‴ .messages)
                 | L.filter-≐ (λ e → dlv? p₂ 𝟚 e ×-dec is𝟘? p′ e) (dlv? p₂ 𝟚) ≥𝟘p₁×≢𝟘p₂≐≥𝟘p₁ (N‴ .messages)
                   = bs , dbsN‴Np₁ , dbsN‴Np₂
               goal* ((m@(newBlock bₘ) , φ) ∷ mds)
                 with goal* mds
               ... | bs , dbsNᶜNp₁ , dbsNᶜNp₂ = projBlock m ∷ bs , dbsN†Np* p₁∈eoN dbsNᶜNp₁ , dbsN†Np* p₂∈eoN dbsNᶜNp₂
                 where
                   eoN↭eoNᶜ : N .execOrder ↭ Nᶜ mds .execOrder
                   eoN↭eoNᶜ = eoN↭eoNᶜ* mds
                     where
                       eoN↭eoNᶜ* : ∀ mds* → N .execOrder ↭ Nᶜ mds* .execOrder
                       eoN↭eoNᶜ* [] = execOrderPreservation-↭-↓∗ N—[ps′]↓→∗N‴
                       eoN↭eoNᶜ* (_ ∷ mds*) = eoN↭eoNᶜ* mds*

                   N† : GlobalState
                   N† = broadcastMsgᶜ m φ (Nᶜ mds)

                   mkenv : Party → Envelope
                   mkenv p* = ⦅ m , p* , φ p* .value ⦆

                   bs𝟙Nᶜ bs𝟙Nᶜm bs𝟚Nᶜ bs𝟚Nᶜm bs𝟙N bs𝟚N : Party → List Block
                   bs𝟙Nᶜ  p* = map (projBlock ∘ msg) (filter (dlv? p* 𝟙) (Nᶜ mds .messages))
                   bs𝟙Nᶜm p* = map (projBlock ∘ msg) (filter (dlv? p* 𝟙) (map mkenv (Nᶜ mds .execOrder)))
                   bs𝟚Nᶜ  p* = map (projBlock ∘ msg) (filter (dlv? p* 𝟚) (Nᶜ mds .messages))
                   bs𝟚Nᶜm p* = map (projBlock ∘ msg) (filter (dlv? p* 𝟚) (map mkenv (Nᶜ mds .execOrder)))
                   bs𝟙N   p* = map (projBlock ∘ msg) (filter (dlv? p* 𝟙) (N .messages))
                   bs𝟚N   p* = map (projBlock ∘ msg) (filter (dlv? p* 𝟚) (N .messages))

                   dbsN†Np* : ∀ {p*} → p* ∈ N .execOrder → delayedBlocks≡ bs p* (Nᶜ mds) N → delayedBlocks≡ (projBlock m ∷ bs) p* N† N
                   dbsN†Np* {p*} p*∈eoN dbsNᶜNp* {b}
                     rewrite
                       L.filter-++ (dlv? p* 𝟙) (map mkenv (Nᶜ mds .execOrder)) (Nᶜ mds .messages)
                     | L.map-++
                         (projBlock ∘ msg)
                         (filter (dlv? p* 𝟙) (map mkenv (Nᶜ mds .execOrder)))
                         (filter (dlv? p* 𝟙) (Nᶜ mds .messages))
                     | L.filter-++ (dlv? p* 𝟚) (map mkenv (Nᶜ mds .execOrder)) (Nᶜ mds .messages)
                     | L.map-++
                         (projBlock ∘ msg)
                         (filter (dlv? p* 𝟚) (map mkenv (Nᶜ mds .execOrder)))
                         (filter (dlv? p* 𝟚) (Nᶜ mds .messages))
                     = let open Related.EquationalReasoning in begin
                       b ∈ (bs𝟙Nᶜm p* ++ bs𝟙Nᶜ p*) ++ bs𝟚Nᶜm p* ++ bs𝟚Nᶜ p*
                         ≡⟨ cong (b ∈_) $ L.++-assoc (bs𝟙Nᶜm p*) (bs𝟙Nᶜ p*) _ ⟩
                       b ∈ bs𝟙Nᶜm p* ++ (bs𝟙Nᶜ p* ++ (bs𝟚Nᶜm p* ++ bs𝟚Nᶜ p*))
                         ≡⟨ cong (λ ◆ → b ∈ bs𝟙Nᶜm p* ++ ◆) $ sym $ L.++-assoc (bs𝟙Nᶜ p*) (bs𝟚Nᶜm p*) _ ⟩
                       b ∈ bs𝟙Nᶜm p* ++ ((bs𝟙Nᶜ p* ++ bs𝟚Nᶜm p*) ++ bs𝟚Nᶜ p*)
                         ∼⟨ ++-cong {xs₁ = bs𝟙Nᶜm p*} ≡ˢ-refl (++-cong (bag-=⇒ (↭⇒∼bag (++-comm (bs𝟙Nᶜ p*) (bs𝟚Nᶜm p*)))) ≡ˢ-refl) ⟩
                       b ∈ bs𝟙Nᶜm p* ++ ((bs𝟚Nᶜm p* ++ bs𝟙Nᶜ p*) ++ bs𝟚Nᶜ p*)
                         ≡⟨ cong (λ ◆ → b ∈ bs𝟙Nᶜm p* ++ ◆) $ L.++-assoc (bs𝟚Nᶜm p*) (bs𝟙Nᶜ p*) _ ⟩
                       b ∈ bs𝟙Nᶜm p* ++ (bs𝟚Nᶜm p* ++ (bs𝟙Nᶜ p* ++ bs𝟚Nᶜ p*))
                         ≡⟨ cong (b ∈_) $ sym $ L.++-assoc (bs𝟙Nᶜm p*) (bs𝟚Nᶜm p*) _ ⟩
                       b ∈ (bs𝟙Nᶜm p* ++ bs𝟚Nᶜm p*) ++ (bs𝟙Nᶜ p* ++ bs𝟚Nᶜ p*)
                         ∼⟨ ++-cong 𝟙Nᶜm+𝟚Nᶜm≡m ≡ˢ-refl ⟩
                       b ∈ [ projBlock m ] ++ (bs𝟙Nᶜ p* ++ bs𝟚Nᶜ p*)
                         ∼⟨ ++-cong {xs₁ = [ projBlock m ]} ≡ˢ-refl dbsNᶜNp* ⟩
                       b ∈ [ projBlock m ] ++ (bs𝟙N p* ++ bs𝟚N p* ++ bs)
                         ∼⟨ bag-=⇒ $ ↭⇒∼bag $ ++-comm [ projBlock m ] (bs𝟙N p* ++ bs𝟚N p* ++ bs) ⟩
                       b ∈ (bs𝟙N p* ++ bs𝟚N p* ++ bs) ++ [ projBlock m ]
                         ≡⟨ cong (b ∈_) $ L.++-assoc (bs𝟙N p*) _ _ ⟩
                       b ∈ bs𝟙N p* ++ (bs𝟚N p* ++ bs) ++ [ projBlock m ]
                         ≡⟨ cong (λ ◆ → b ∈ bs𝟙N p* ++ ◆) $ L.++-assoc (bs𝟚N p*) bs [ projBlock m ] ⟩
                       b ∈ bs𝟙N p* ++ bs𝟚N p* ++ bs ++ [ projBlock m ]
                         ≡⟨ cong (b ∈_) $ sym $ L.++-assoc (bs𝟙N p*) (bs𝟚N p*) _ ⟩
                       b ∈ (bs𝟙N p* ++ bs𝟚N p*) ++ bs ++ [ projBlock m ]
                         ∼⟨ ++-cong {xs₁ = bs𝟙N p* ++ bs𝟚N p*} ≡ˢ-refl (bag-=⇒ (↭⇒∼bag (++-comm bs _))) ⟩
                       b ∈ (bs𝟙N p* ++ bs𝟚N p*) ++ projBlock m ∷ bs
                         ≡⟨ cong (b ∈_) $ L.++-assoc (bs𝟙N p*) (bs𝟚N p*) _ ⟩
                       b ∈ bs𝟙N p* ++ bs𝟚N p* ++ projBlock m ∷ bs
                         ∎
                       where
                         𝟙Nᶜm+𝟚Nᶜm≡m : bs𝟙Nᶜm p* ++ bs𝟚Nᶜm p* ≡ˢ [ projBlock m ]
                         𝟙Nᶜm+𝟚Nᶜm≡m = blockDelayUniqueness φ m p* (Nᶜ mds .execOrder) p*∈eoNᶜ eoNᶜ!
                           where
                             p*∈eoNᶜ : p* ∈ Nᶜ mds .execOrder
                             p*∈eoNᶜ = (≡ˢ⇒⊆ $ bag-=⇒ $ ↭⇒∼bag eoN↭eoNᶜ) p*∈eoN

                             eoNᶜ! : Unique (Nᶜ mds .execOrder)
                             eoNᶜ! = Unique-resp-↭ eoN↭eoNᶜ eoN!

  delayedBlocksEvolution-↑* : ∀ {N N′ : GlobalState} {p₁ p₂ : Party} →
      _ ⊢ N —[ N .execOrder ]↑→∗ N′
    → Unique (N .execOrder)
    → p₁ ∈ N .execOrder
    → p₂ ∈ N .execOrder
    → ∃[ bs ]
        blocksDeliveredIn p₁ 𝟙 N′ ++ blocksDeliveredIn p₁ 𝟚 N′ ≡ˢ blocksDeliveredIn p₁ 𝟙 N ++ blocksDeliveredIn p₁ 𝟚 N ++ bs
        ×
        blocksDeliveredIn p₂ 𝟙 N′ ++ blocksDeliveredIn p₂ 𝟚 N′ ≡ˢ blocksDeliveredIn p₂ 𝟙 N ++ blocksDeliveredIn p₂ 𝟚 N ++ bs
  delayedBlocksEvolution-↑* {N} {N′} {p₁} {p₂} N—[eoN]↑→∗N′ eoN! p₁∈eoN p₂∈eoN =
    delayedBlocksEvolution-↑*ʳ (reverseView (N .execOrder)) (—[]→∗⇒—[]→∗ʳ N—[eoN]↑→∗N′) eoN!
    where
      open import Data.List.Reverse

      delayedBlocks≡ : List Block → Party → GlobalState → GlobalState → Type
      delayedBlocks≡ bs p N N′ = blocksDeliveredIn p 𝟙 N ++ blocksDeliveredIn p 𝟚 N ≡ˢ blocksDeliveredIn p 𝟙 N′ ++ blocksDeliveredIn p 𝟚 N′ ++ bs

      delayedBlocksEvolution-↑*ʳ : ∀ {N* ps} →
          Reverse ps
        → _ ⊢ N —[ ps ]↑→∗ʳ N*
        → Unique ps
        → ∃[ bs ] delayedBlocks≡ bs p₁ N* N × delayedBlocks≡ bs p₂ N* N
      delayedBlocksEvolution-↑*ʳ [] N—[ps]↑→∗ʳN* _ rewrite sym $ —[[]]→∗ʳ⇒≡ N—[ps]↑→∗ʳN* =
        [] ,
        ≡ˢ-++-identityʳ (blocksDeliveredIn p₁ 𝟙 N) (blocksDeliveredIn p₁ 𝟚 N) ,
        ≡ˢ-++-identityʳ (blocksDeliveredIn p₂ 𝟙 N) (blocksDeliveredIn p₂ 𝟚 N)
        where
          ≡ˢ-++-identityʳ : ∀ (bs bs′ : List Block) → bs ++ bs′ ≡ˢ bs ++ bs′ ++ []
          ≡ˢ-++-identityʳ bs bs′ = ≡⇒≡ˢ $ let open ≡-Reasoning in begin
            bs ++ bs′            ≡⟨ L.++-identityʳ (bs ++ bs′) ⟨
            (bs ++ bs′) ++ []    ≡⟨ L.++-assoc bs _ _ ⟩
            bs ++ bs′ ++ []      ∎
      delayedBlocksEvolution-↑*ʳ {N* = N*} (ps′ ∶ ps′r ∶ʳ p′) N—[ps′+p′]↑→∗ʳN* [ps′+p′]!
        with —[∷ʳ]→∗-split (—[]→∗ʳ⇒—[]→∗ N—[ps′+p′]↑→∗ʳN*)
      ... | N‴ , N—[ps′]↑→∗N‴ , N‴—[p′]↑→N* = goal N‴—[p′]↑→N*
        where
           ps′! : Unique ps′
           ps′! = headʳ [ps′+p′]!

           ih : ∃[ bs ] delayedBlocks≡ bs p₁ N‴ N × delayedBlocks≡ bs p₂ N‴ N
           ih = delayedBlocksEvolution-↑*ʳ ps′r (—[]→∗⇒—[]→∗ʳ N—[ps′]↑→∗N‴) ps′!

           dlv? : (p* : Party) (d : Delay) → Decidable¹ λ e′ → DeliveredIn e′ p* d
           dlv? p* d e′ = ¿ DeliveredIn e′ ¿² p* d

           eoN‴! : Unique (N‴ .execOrder)
           eoN‴! = Unique-resp-↭ (execOrderPreservation-↭-↑∗ N—[ps′]↑→∗N‴) eoN!

           goal : _ ⊢ N‴ —[ p′ ]↑→ N* → ∃[ bs ] delayedBlocks≡ bs p₁ N* N × delayedBlocks≡ bs p₂ N* N
           goal (unknownParty↑ _) = ih
           goal (honestParty↑ {ls = ls} lsπ hp′π) with Params.winnerᵈ params {p′} {N‴ .clock}
           ... | ⁇ (no ¬isWinner) = ih
           ... | ⁇ (yes isWinner)
             with ih
           ...   | bs , dbsN‴Np₁ , dbsN‴Np₂ = nb ∷ bs , dbsN*Np* p₁∈eoN dbsN‴Np₁ , dbsN*Np* p₂∈eoN dbsN‴Np₂
             where
               best : Chain
               best = bestChain (N‴ .clock ∸ 1) (ls .tree)

               nb : Block
               nb = mkBlock (hash (tip best)) (N‴ .clock) (txSelection (N‴ .clock) p′) p′

               mkenv : Party → Envelope
               mkenv p* = ⦅ newBlock nb , p* , 𝟙 ⦆

               p*∈eoN‴ : ∀ {p*} → p* ∈ N .execOrder → p* ∈ N‴ .execOrder
               p*∈eoN‴ p*∈eoN = (≡ˢ⇒⊆ $ bag-=⇒ $ ↭⇒∼bag $ execOrderPreservation-↭-↑∗ N—[ps′]↑→∗N‴) p*∈eoN

               [≡𝟚]≡[]  : ∀ p* ps* → map (projBlock ∘ msg) (filter (dlv? p* 𝟚) (map mkenv ps*)) ≡ []
               [≡𝟚]≡[] _ [] = refl
               [≡𝟚]≡[] p* (_ ∷ ps*) = [≡𝟚]≡[] p* ps*

               [≡𝟙]≡nb : ∀ {p* ps*} → Unique ps* → p* ∈ ps* → map (projBlock ∘ msg) (filter (dlv? p* 𝟙) (map mkenv ps*)) ≡ [ nb ]
               [≡𝟙]≡nb {p*} {p⁺ ∷ ps*} p⁺+ps*! (here p*≡p)
                 rewrite
                   p*≡p
                 | L.filter-accept (dlv? p⁺ 𝟙) {mkenv p⁺} {map mkenv ps*} (refl , refl)
                   = subst (λ ◆ → nb ∷ ◆ ≡ [ nb ]) (sym $ [≡𝟙]≡nb* p⁺∉ps*) refl
                 where
                   p⁺∉ps* : p⁺ ∉ ps*
                   p⁺∉ps* = Unique[x∷xs]⇒x∉xs p⁺+ps*!

                   [≡𝟙]≡nb* : ∀ {ps*} → p⁺ ∉ ps* → map (projBlock ∘ msg) (filter (dlv? p⁺ 𝟙) (map mkenv ps*)) ≡ []
                   [≡𝟙]≡nb* {[]} _ = refl
                   [≡𝟙]≡nb* {p† ∷ ps†} p⁺∉p†+ps† = (case ∉-∷⁻ p⁺∉p†+ps† of λ where
                     (p⁺≢p† , p⁺∉ps†) → helper p⁺≢p† p⁺∉ps†)
                     where
                       helper : p⁺ ≢ p† → p⁺ ∉ ps† → map (projBlock ∘ msg) (filter (dlv? p⁺ 𝟙) (map mkenv (p† ∷ ps†))) ≡ []
                       helper p⁺≢p† p⁺∉ps†
                         rewrite
                           L.filter-reject (dlv? p⁺ 𝟙) {mkenv p†} {map mkenv ps†} (dec-de-morgan₂ (inj₂ $ ≢-sym p⁺≢p†))
                           = [≡𝟙]≡nb* {ps†} p⁺∉ps†
               [≡𝟙]≡nb {p*} {p⁺ ∷ ps*} p⁺+ps*! (there p*∈ps*) = helper
                 where
                   import Data.List.Relation.Unary.Unique.Propositional as U

                   p⁺∉ps* : p⁺ ∉ ps*
                   p⁺∉ps* = Unique[x∷xs]⇒x∉xs p⁺+ps*!

                   p⁺≢p* : p⁺ ≢ p*
                   p⁺≢p* = λ p⁺≡p* → contradiction p*∈ps* (subst (_∉ ps*) p⁺≡p* p⁺∉ps*)

                   helper : map (projBlock ∘ msg) (filter (dlv? p* 𝟙) (mkenv p⁺ ∷ map mkenv ps*)) ≡ [ nb ]
                   helper
                     rewrite L.filter-reject (dlv? p* 𝟙) {mkenv p⁺} {map mkenv ps*} (dec-de-morgan₂ (inj₂ p⁺≢p*))
                       = [≡𝟙]≡nb {p*} {ps*} (U.tail p⁺+ps*!) p*∈ps*

               dbsN*Np* : ∀ {p*} → p* ∈ N .execOrder → delayedBlocks≡ bs p* N‴ N →
                  map (projBlock ∘ msg) (filter (dlv? p* 𝟙) (map mkenv (N‴ .execOrder) ++ N‴ .messages))
                  ++
                  map (projBlock ∘ msg) (filter (dlv? p* 𝟚) (map mkenv (N‴ .execOrder) ++ N‴ .messages))
                  ≡ˢ
                  map (projBlock ∘ msg) (filter (dlv? p* 𝟙) (N .messages))
                  ++
                  map (projBlock ∘ msg) (filter (dlv? p* 𝟚) (N .messages))
                  ++
                  nb ∷ bs
               dbsN*Np* {p*} prf1 prf2 {b}
                 rewrite
                   L.filter-++ (dlv? p* 𝟙) (map mkenv (N‴ .execOrder)) (N‴ .messages)
                 | L.map-++
                     (projBlock ∘ msg)
                     (filter (dlv? p* 𝟙) (map mkenv (N‴ .execOrder)))
                     (filter (dlv? p* 𝟙) (N‴ .messages))
                 | L.filter-++ (dlv? p* 𝟚) (map mkenv (N‴ .execOrder)) (N‴ .messages)
                 | L.map-++
                     (projBlock ∘ msg)
                     (filter (dlv? p* 𝟚) (map mkenv (N‴ .execOrder)))
                     (filter (dlv? p* 𝟚) (N‴ .messages))
                 | [≡𝟚]≡[] p* (N‴ .execOrder)
                 | [≡𝟙]≡nb eoN‴! (p*∈eoN‴ prf1)
                   = let open Related.EquationalReasoning in begin
                   b ∈ nb ∷ bs𝟙N‴ ++ bs𝟚N‴
                     ∼⟨ ++-cong {xs₁ = [ nb ]} ≡ˢ-refl prf2 ⟩
                   b ∈ nb ∷ bs𝟙N ++ bs𝟚N ++ bs
                     ∼⟨ ++-cong {ys₁ = bs𝟚N ++ bs} (bag-=⇒ $ ↭⇒∼bag $ ++-comm [ nb ] bs𝟙N) ≡ˢ-refl ⟩
                   b ∈ (bs𝟙N ++ [ nb ]) ++ bs𝟚N ++ bs
                     ≡⟨ cong (b ∈_) $ L.++-assoc bs𝟙N [ nb ] _ ⟩
                   b ∈ bs𝟙N ++ nb ∷ bs𝟚N ++ bs
                     ≡⟨ cong (λ ◆ → b ∈ bs𝟙N ++ ◆) $ sym $ L.++-assoc [ nb ] bs𝟚N _ ⟩
                   b ∈ bs𝟙N ++ (nb ∷ bs𝟚N) ++ bs
                     ∼⟨ ++-cong {xs₁ = bs𝟙N} ≡ˢ-refl $ ++-cong (bag-=⇒ $ ↭⇒∼bag $ ++-comm [ nb ] bs𝟚N) ≡ˢ-refl ⟩
                   b ∈ bs𝟙N ++ (bs𝟚N ++ [ nb ]) ++ bs
                     ≡⟨ cong (λ ◆ → b ∈ bs𝟙N ++ ◆) $ L.++-assoc bs𝟚N _ _ ⟩
                   b ∈ bs𝟙N ++ bs𝟚N ++ nb ∷ bs
                     ∎
                 where
                   bs𝟙N bs𝟚N bs𝟙N‴ bs𝟚N‴ : List Block
                   bs𝟙N  = map (projBlock ∘ msg) (filter (dlv? p* 𝟙) (N .messages))
                   bs𝟚N  = map (projBlock ∘ msg) (filter (dlv? p* 𝟚) (N .messages))
                   bs𝟙N‴ = map (projBlock ∘ msg) (filter (dlv? p* 𝟙) (N‴ .messages))
                   bs𝟚N‴ = map (projBlock ∘ msg) (filter (dlv? p* 𝟚) (N‴ .messages))
           -- TODO: Factor the following case out and share it with `delayedBlocksEvolution-↓*`.
           goal (corruptParty↑ _ _)  with makeBlockᶜ (N‴ .clock) (N‴ .history) (N‴ .messages) (N‴ .advState)
           ...   | newMds , _ = goal* newMds
             where
               is𝟘? : (p* : Party) → Decidable¹ (¬_ ∘ flip Immediate p*)
               is𝟘? p* = ¿ ¬_ ∘ flip Immediate p* ¿¹

               Nᶜ : List (Message × DelayMap) → GlobalState
               Nᶜ mds = broadcastMsgsᶜ mds N‴

               goal* : ∀ mds → ∃[ bs ] delayedBlocks≡ bs p₁ (Nᶜ mds) N × delayedBlocks≡ bs p₂ (Nᶜ mds) N
               goal* [] with ih
               ... | bs , dbsN‴Np₁ , dbsN‴Np₂
                 rewrite
                   sym $ filter-∘-× (dlv? p₁ 𝟙) (is𝟘? p′) (N‴ .messages)
                 | sym $ filter-∘-× (dlv? p₁ 𝟚) (is𝟘? p′) (N‴ .messages)
                 | sym $ filter-∘-× (dlv? p₂ 𝟙) (is𝟘? p′) (N‴ .messages)
                 | sym $ filter-∘-× (dlv? p₂ 𝟚) (is𝟘? p′) (N‴ .messages)
                 | L.filter-≐ (λ e → dlv? p₁ 𝟙 e ×-dec is𝟘? p′ e) (dlv? p₁ 𝟙) ≥𝟘p₁×≢𝟘p₂≐≥𝟘p₁ (N‴ .messages)
                 | L.filter-≐ (λ e → dlv? p₁ 𝟚 e ×-dec is𝟘? p′ e) (dlv? p₁ 𝟚) ≥𝟘p₁×≢𝟘p₂≐≥𝟘p₁ (N‴ .messages)
                 | L.filter-≐ (λ e → dlv? p₂ 𝟙 e ×-dec is𝟘? p′ e) (dlv? p₂ 𝟙) ≥𝟘p₁×≢𝟘p₂≐≥𝟘p₁ (N‴ .messages)
                 | L.filter-≐ (λ e → dlv? p₂ 𝟚 e ×-dec is𝟘? p′ e) (dlv? p₂ 𝟚) ≥𝟘p₁×≢𝟘p₂≐≥𝟘p₁ (N‴ .messages)
                   = bs , dbsN‴Np₁ , dbsN‴Np₂
               goal* ((m@(newBlock bₘ) , φ) ∷ mds)
                 with goal* mds
               ... | bs , dbsNᶜNp₁ , dbsNᶜNp₂ = projBlock m ∷ bs , dbsN†Np* p₁∈eoN dbsNᶜNp₁ , dbsN†Np* p₂∈eoN dbsNᶜNp₂
                 where
                   eoN↭eoNᶜ : N .execOrder ↭ Nᶜ mds .execOrder
                   eoN↭eoNᶜ = eoN↭eoNᶜ* mds
                     where
                       eoN↭eoNᶜ* : ∀ mds* → N .execOrder ↭ Nᶜ mds* .execOrder
                       eoN↭eoNᶜ* [] = execOrderPreservation-↭-↑∗ N—[ps′]↑→∗N‴
                       eoN↭eoNᶜ* (_ ∷ mds*) = eoN↭eoNᶜ* mds*

                   N† : GlobalState
                   N† = broadcastMsgᶜ m φ (Nᶜ mds)

                   mkenv : Party → Envelope
                   mkenv p* = ⦅ m , p* , φ p* .value ⦆

                   bs𝟙Nᶜ bs𝟙Nᶜm bs𝟚Nᶜ bs𝟚Nᶜm bs𝟙N bs𝟚N : Party → List Block
                   bs𝟙Nᶜ  p* = map (projBlock ∘ msg) (filter (dlv? p* 𝟙) (Nᶜ mds .messages))
                   bs𝟙Nᶜm p* = map (projBlock ∘ msg) (filter (dlv? p* 𝟙) (map mkenv (Nᶜ mds .execOrder)))
                   bs𝟚Nᶜ  p* = map (projBlock ∘ msg) (filter (dlv? p* 𝟚) (Nᶜ mds .messages))
                   bs𝟚Nᶜm p* = map (projBlock ∘ msg) (filter (dlv? p* 𝟚) (map mkenv (Nᶜ mds .execOrder)))
                   bs𝟙N   p* = map (projBlock ∘ msg) (filter (dlv? p* 𝟙) (N .messages))
                   bs𝟚N   p* = map (projBlock ∘ msg) (filter (dlv? p* 𝟚) (N .messages))

                   dbsN†Np* : ∀ {p*} → p* ∈ N .execOrder → delayedBlocks≡ bs p* (Nᶜ mds) N → delayedBlocks≡ (projBlock m ∷ bs) p* N† N
                   dbsN†Np* {p*} p*∈eoN dbsNᶜNp* {b}
                     rewrite
                       L.filter-++ (dlv? p* 𝟙) (map mkenv (Nᶜ mds .execOrder)) (Nᶜ mds .messages)
                     | L.map-++
                         (projBlock ∘ msg)
                         (filter (dlv? p* 𝟙) (map mkenv (Nᶜ mds .execOrder)))
                         (filter (dlv? p* 𝟙) (Nᶜ mds .messages))
                     | L.filter-++ (dlv? p* 𝟚) (map mkenv (Nᶜ mds .execOrder)) (Nᶜ mds .messages)
                     | L.map-++
                         (projBlock ∘ msg)
                         (filter (dlv? p* 𝟚) (map mkenv (Nᶜ mds .execOrder)))
                         (filter (dlv? p* 𝟚) (Nᶜ mds .messages))
                     = let open Related.EquationalReasoning in begin
                       b ∈ (bs𝟙Nᶜm p* ++ bs𝟙Nᶜ p*) ++ bs𝟚Nᶜm p* ++ bs𝟚Nᶜ p*
                         ≡⟨ cong (b ∈_) $ L.++-assoc (bs𝟙Nᶜm p*) (bs𝟙Nᶜ p*) _ ⟩
                       b ∈ bs𝟙Nᶜm p* ++ (bs𝟙Nᶜ p* ++ (bs𝟚Nᶜm p* ++ bs𝟚Nᶜ p*))
                         ≡⟨ cong (λ ◆ → b ∈ bs𝟙Nᶜm p* ++ ◆) $ sym $ L.++-assoc (bs𝟙Nᶜ p*) (bs𝟚Nᶜm p*) _ ⟩
                       b ∈ bs𝟙Nᶜm p* ++ ((bs𝟙Nᶜ p* ++ bs𝟚Nᶜm p*) ++ bs𝟚Nᶜ p*)
                         ∼⟨ ++-cong {xs₁ = bs𝟙Nᶜm p*} ≡ˢ-refl (++-cong (bag-=⇒ (↭⇒∼bag (++-comm (bs𝟙Nᶜ p*) (bs𝟚Nᶜm p*)))) ≡ˢ-refl) ⟩
                       b ∈ bs𝟙Nᶜm p* ++ ((bs𝟚Nᶜm p* ++ bs𝟙Nᶜ p*) ++ bs𝟚Nᶜ p*)
                         ≡⟨ cong (λ ◆ → b ∈ bs𝟙Nᶜm p* ++ ◆) $ L.++-assoc (bs𝟚Nᶜm p*) (bs𝟙Nᶜ p*) _ ⟩
                       b ∈ bs𝟙Nᶜm p* ++ (bs𝟚Nᶜm p* ++ (bs𝟙Nᶜ p* ++ bs𝟚Nᶜ p*))
                         ≡⟨ cong (b ∈_) $ sym $ L.++-assoc (bs𝟙Nᶜm p*) (bs𝟚Nᶜm p*) _ ⟩
                       b ∈ (bs𝟙Nᶜm p* ++ bs𝟚Nᶜm p*) ++ (bs𝟙Nᶜ p* ++ bs𝟚Nᶜ p*)
                         ∼⟨ ++-cong 𝟙Nᶜm+𝟚Nᶜm≡m ≡ˢ-refl ⟩
                       b ∈ [ projBlock m ] ++ (bs𝟙Nᶜ p* ++ bs𝟚Nᶜ p*)
                         ∼⟨ ++-cong {xs₁ = [ projBlock m ]} ≡ˢ-refl dbsNᶜNp* ⟩
                       b ∈ [ projBlock m ] ++ (bs𝟙N p* ++ bs𝟚N p* ++ bs)
                         ∼⟨ bag-=⇒ $ ↭⇒∼bag $ ++-comm [ projBlock m ] (bs𝟙N p* ++ bs𝟚N p* ++ bs) ⟩
                       b ∈ (bs𝟙N p* ++ bs𝟚N p* ++ bs) ++ [ projBlock m ]
                         ≡⟨ cong (b ∈_) $ L.++-assoc (bs𝟙N p*) _ _ ⟩
                       b ∈ bs𝟙N p* ++ (bs𝟚N p* ++ bs) ++ [ projBlock m ]
                         ≡⟨ cong (λ ◆ → b ∈ bs𝟙N p* ++ ◆) $ L.++-assoc (bs𝟚N p*) bs [ projBlock m ] ⟩
                       b ∈ bs𝟙N p* ++ bs𝟚N p* ++ bs ++ [ projBlock m ]
                         ≡⟨ cong (b ∈_) $ sym $ L.++-assoc (bs𝟙N p*) (bs𝟚N p*) _ ⟩
                       b ∈ (bs𝟙N p* ++ bs𝟚N p*) ++ bs ++ [ projBlock m ]
                         ∼⟨ ++-cong {xs₁ = bs𝟙N p* ++ bs𝟚N p*} ≡ˢ-refl (bag-=⇒ (↭⇒∼bag (++-comm bs _))) ⟩
                       b ∈ (bs𝟙N p* ++ bs𝟚N p*) ++ projBlock m ∷ bs
                         ≡⟨ cong (b ∈_) $ L.++-assoc (bs𝟙N p*) (bs𝟚N p*) _ ⟩
                       b ∈ bs𝟙N p* ++ bs𝟚N p* ++ projBlock m ∷ bs
                         ∎
                       where
                         𝟙Nᶜm+𝟚Nᶜm≡m : bs𝟙Nᶜm p* ++ bs𝟚Nᶜm p* ≡ˢ [ projBlock m ]
                         𝟙Nᶜm+𝟚Nᶜm≡m = blockDelayUniqueness φ m p* (Nᶜ mds .execOrder) p*∈eoNᶜ eoNᶜ!
                           where
                             p*∈eoNᶜ : p* ∈ Nᶜ mds .execOrder
                             p*∈eoNᶜ = (≡ˢ⇒⊆ $ bag-=⇒ $ ↭⇒∼bag eoN↭eoNᶜ) p*∈eoN

                             eoNᶜ! : Unique (Nᶜ mds .execOrder)
                             eoNᶜ! = Unique-resp-↭ eoN↭eoNᶜ eoN!

allBlocks+toBeDelivered≡ : ∀ {N : GlobalState} {p p′ : Party} {ls ls′ : LocalState} →
    N₀ ↝⋆ N
  → Honest p
  → Honest p′
  → N .states ⁉ p ≡ just ls
  → N .states ⁉ p′ ≡ just ls′
  → let
      blocksToBeDelivered = λ p* → blocksDeliveredIn p* 𝟘 N ++ blocksDeliveredIn p* 𝟙 N ++ blocksDeliveredIn p* 𝟚 N
    in
      allBlocks (ls .tree) ++ blocksToBeDelivered p ≡ˢ allBlocks (ls′ .tree) ++ blocksToBeDelivered p′
allBlocks+toBeDelivered≡ N₀↝⋆N hp hp′ lspN ls′p′N = allBlocks+toBeDelivered≡ʳ (Star⇒Starʳ N₀↝⋆N) hp hp′ lspN ls′p′N
  where
    open RTC; open Starʳ
    allBlocks+toBeDelivered≡ʳ : ∀ {N : GlobalState} {p p′ : Party} {ls ls′ : LocalState} →
        N₀ ↝⋆ʳ N
      → Honest p
      → Honest p′
      → N .states ⁉ p ≡ just ls
      → N .states ⁉ p′ ≡ just ls′
      → let
          blocksToBeDelivered = λ p* → blocksDeliveredIn p* 𝟘 N ++ blocksDeliveredIn p* 𝟙 N ++ blocksDeliveredIn p* 𝟚 N
        in
          allBlocks (ls .tree) ++ blocksToBeDelivered p ≡ˢ allBlocks (ls′ .tree) ++ blocksToBeDelivered p′
    allBlocks+toBeDelivered≡ʳ εʳ _ _ lspN ls′p′N
      rewrite tree₀InN₀ lspN | tree₀InN₀ ls′p′N | L.++-identityʳ (allBlocks tree₀) = ≡ˢ-refl
    allBlocks+toBeDelivered≡ʳ {N} {p} {p′} {ls} {ls′} N₀↝⋆ʳN@(_◅ʳ_ {j = N″} N₀↝⋆ʳN″ N″↝N) hp hp′ lspN ls′p′N = goal N″↝N
      where
        N₀↝⋆N″ : N₀ ↝⋆ N″
        N₀↝⋆N″ = Starʳ⇒Star N₀↝⋆ʳN″

        𝟘s 𝟙s 𝟚s : Party → GlobalState → List Block
        𝟘s p* N = blocksDeliveredIn p* 𝟘 N
        𝟙s p* N = blocksDeliveredIn p* 𝟙 N
        𝟚s p* N = blocksDeliveredIn p* 𝟚 N

        blocksToBeDelivered : Party → GlobalState → List Block
        blocksToBeDelivered p* N = 𝟘s p* N ++ 𝟙s p* N ++ 𝟚s p* N

        goal : N″ ↝ N → allBlocks (ls .tree) ++ blocksToBeDelivered p N ≡ˢ allBlocks (ls′ .tree) ++ blocksToBeDelivered p′ N
        goal (deliverMsgs {N′ = N°} N″Ready N″—[eoN″]↓→∗N°) {b} = let open Related.EquationalReasoning in begin
          b ∈ allBlocks (ls .tree) ++ blocksToBeDelivered p N
            ≡⟨ cong (λ ◆ → b ∈ allBlocks (ls .tree) ++ ◆ ++ 𝟙s p N ++ 𝟚s p N) $ 𝟘sp*≡[] p ⟩
          b ∈ allBlocks (ls .tree) ++ 𝟙s p N ++ 𝟚s p N
            ∼⟨ tls+𝟙s+𝟚sN°p≡tls+𝟙s+𝟚sN°p′ ⟩
          b ∈ allBlocks (ls′ .tree) ++ 𝟙s p′ N ++ 𝟚s p′ N
            ≡⟨ cong (λ ◆ → b ∈ allBlocks (ls′ .tree) ++ ◆ ++ 𝟙s p′ N ++ 𝟚s p′ N) $ sym $ 𝟘sp*≡[] p′ ⟩
          b ∈ allBlocks (ls′ .tree) ++ blocksToBeDelivered p′ N
            ∎
          where
            𝟘sp*≡[] : ∀ p* → 𝟘s p* N ≡ []
            𝟘sp*≡[] p* = noImmediateMsgsIfNotReady p* (Starʳ⇒Star N₀↝⋆ʳN) λ ()

            eoN″! : Unique (N″ .execOrder)
            eoN″! = execOrderUniqueness N₀↝⋆N″

            hasLsp*N″ : ∀ {p* ls*} → N .states ⁉ p* ≡ just ls* → p* hasStateIn N″
            hasLsp*N″ {p*} ls*p*N = L.All.lookup (allPartiesHaveLocalState $ Starʳ⇒Star N₀↝⋆ʳN″) p*∈N″
              where
                p*∈N : p* ∈ N .execOrder
                p*∈N = hasState⇒∈execOrder (N₀↝⋆N″ ◅◅ N″↝N ◅ ε) (≡just⇒Is-just ls*p*N)

                p*∈N″ : p* ∈ N″ .execOrder
                p*∈N″ = ∈-resp-↭ (↭-sym (execOrderPreservation-↭-↝ N″↝N)) p*∈N

            hasLspN″ : p hasStateIn N″
            hasLspN″ = hasLsp*N″ lspN

            hasLsp′N″ : p′ hasStateIn N″
            hasLsp′N″ = hasLsp*N″ ls′p′N

            p∈eoN″ : p ∈ N″ .execOrder
            p∈eoN″ = ∈-resp-↭ (execOrderPreservation-↭ N₀↝⋆N″) (hasState⇔∈parties₀ N₀↝⋆N″ .Equivalence.to hasLspN″)

            p′∈eoN″ : p′ ∈ N″ .execOrder
            p′∈eoN″ = ∈-resp-↭ (execOrderPreservation-↭ N₀↝⋆N″) (hasState⇔∈parties₀ N₀↝⋆N″ .Equivalence.to hasLsp′N″)

            ls″ ls‴ : LocalState
            ls″ = M.to-witness hasLspN″
            ls‴ = M.to-witness hasLsp′N″

            tls+𝟙s+𝟚sN°p≡tls+𝟙s+𝟚sN°p′ : allBlocks (ls .tree) ++ 𝟙s p N° ++ 𝟚s p N° ≡ˢ allBlocks (ls′ .tree) ++ 𝟙s p′ N° ++ 𝟚s p′ N°
            tls+𝟙s+𝟚sN°p≡tls+𝟙s+𝟚sN°p′ {b} with delayedBlocksEvolution-↓* N″—[eoN″]↓→∗N° eoN″! p∈eoN″ p′∈eoN″
            ... | bs , 𝟙s+𝟚sN°p≡𝟙s+𝟚sN″p+bs , 𝟙s+𝟚sN°p′≡𝟙s+𝟚sN″p′+bs = let open Related.EquationalReasoning in begin
              b ∈ allBlocks (ls .tree) ++ 𝟙s p N° ++ 𝟚s p N°
                ∼⟨ ++-cong {xs₁ = allBlocks (ls .tree)} ≡ˢ-refl 𝟙s+𝟚sN°p≡𝟙s+𝟚sN″p+bs ⟩
              b ∈ allBlocks (ls .tree) ++ 𝟙s p N″ ++ 𝟚s p N″ ++ bs
                ≡⟨ cong (λ ◆ → b ∈ allBlocks (ls .tree) ++ ◆) $ sym $ L.++-assoc (𝟙s p N″) _ _ ⟩
              b ∈ allBlocks (ls .tree) ++ (𝟙s p N″ ++ 𝟚s p N″) ++ bs
                ≡⟨ cong (b ∈_) $ L.++-assoc (allBlocks (ls .tree)) _ _ ⟨
              b ∈ (allBlocks (ls .tree) ++ 𝟙s p N″ ++ 𝟚s p N″) ++ bs
                ∼⟨ ++-cong {ys₁ = bs} tls+𝟙s+𝟚spN″≡tls′+𝟙s+𝟚sp′N″ ≡ˢ-refl ⟩
              b ∈ (allBlocks (ls′ .tree) ++ 𝟙s p′ N″ ++ 𝟚s p′ N″) ++ bs
                ≡⟨ cong (b ∈_) $ L.++-assoc (allBlocks (ls′ .tree)) _ _ ⟩
              b ∈ allBlocks (ls′ .tree) ++ (𝟙s p′ N″ ++ 𝟚s p′ N″) ++ bs
                ≡⟨ cong (λ ◆ → b ∈ allBlocks (ls′ .tree) ++ ◆) $ L.++-assoc (𝟙s p′ N″) _ _ ⟩
              b ∈ allBlocks (ls′ .tree) ++ 𝟙s p′ N″ ++ 𝟚s p′ N″ ++ bs
                ∼⟨ ++-cong {xs₁ = allBlocks (ls′ .tree)} ≡ˢ-refl (≡ˢ-sym 𝟙s+𝟚sN°p′≡𝟙s+𝟚sN″p′+bs) ⟩
              b ∈ allBlocks (ls′ .tree) ++ 𝟙s p′ N° ++ 𝟚s p′ N° ∎
                where
                  lspN″ : N″ .states ⁉ p ≡ just ls″
                  lspN″ = Is-just⇒to-witness hasLspN″

                  lsp′N″ : N″ .states ⁉ p′ ≡ just ls‴
                  lsp′N″ = Is-just⇒to-witness hasLsp′N″

                  tls+𝟙s+𝟚spN″≡tls′+𝟙s+𝟚sp′N″ : allBlocks (ls .tree) ++ 𝟙s p N″ ++ 𝟚s p N″ ≡ˢ allBlocks (ls′ .tree) ++ 𝟙s p′ N″ ++ 𝟚s p′ N″
                  tls+𝟙s+𝟚spN″≡tls′+𝟙s+𝟚sp′N″ {b} = let open Related.EquationalReasoning in begin
                    b ∈ allBlocks (ls .tree) ++ 𝟙s p N″ ++ 𝟚s p N″
                      ∼⟨ ++-cong {xs₁ = allBlocks (ls .tree)} tls≡tls″+𝟘s ≡ˢ-refl ⟩
                    b ∈ (allBlocks (ls″ .tree) ++ 𝟘s p N″) ++ 𝟙s p N″ ++ 𝟚s p N″
                      ≡⟨ cong (b ∈_) $ L.++-assoc (allBlocks (ls″ .tree)) _ _ ⟩
                    b ∈ allBlocks (ls″ .tree) ++ blocksToBeDelivered p N″
                      ∼⟨ ih ⟩
                    b ∈ allBlocks (ls‴ .tree) ++ blocksToBeDelivered p′ N″
                      ≡⟨ cong (b ∈_) $ sym $ L.++-assoc (allBlocks (ls‴ .tree)) _ _ ⟩
                    b ∈ (allBlocks (ls‴ .tree) ++ 𝟘s p′ N″) ++ 𝟙s p′ N″ ++ 𝟚s p′ N″
                      ∼⟨ ++-cong {xs₁ = allBlocks (ls‴ .tree) ++ 𝟘s p′ N″} (≡ˢ-sym tls′≡tls‴+𝟘s) ≡ˢ-refl ⟩
                    b ∈ allBlocks (ls′ .tree) ++ 𝟙s p′ N″ ++ 𝟚s p′ N″
                    ∎
                      where
                        ih : allBlocks (ls″ .tree) ++ blocksToBeDelivered p N″ ≡ˢ allBlocks (ls‴ .tree) ++ blocksToBeDelivered p′ N″
                        ih = allBlocks+toBeDelivered≡ʳ N₀↝⋆ʳN″ hp hp′ lspN″ lsp′N″

                        tls≡tls″+𝟘s : allBlocks (ls .tree) ≡ˢ allBlocks (ls″ .tree) ++ 𝟘s p N″
                        tls≡tls″+𝟘s = honestLocalTreeEvolution-↓ hp lspN″ N″↝[p]↓Nᵖ lspNᵖ
                          where
                            Nᵖ : GlobalState
                            Nᵖ  = honestMsgsDelivery p ls″ N″

                            N″↝[p]↓Nᵖ : N″ ↝[ p ]↓ Nᵖ
                            N″↝[p]↓Nᵖ = honestParty↓ lspN″ hp

                            lspNᵖ : Nᵖ .states ⁉ p ≡ just ls
                            lspNᵖ = trans (sym $ localStatePreservation-↓∗ N₀↝⋆N″ N″—[eoN″]↓→∗N° N″↝[p]↓Nᵖ) lspN

                        tls′≡tls‴+𝟘s : allBlocks (ls′ .tree) ≡ˢ allBlocks (ls‴ .tree) ++ 𝟘s p′ N″
                        tls′≡tls‴+𝟘s = honestLocalTreeEvolution-↓ hp′ lsp′N″ N″↝[p′]↓Nᵖ′ lsp′Nᵖ′
                          where
                            Nᵖ′ : GlobalState
                            Nᵖ′ = honestMsgsDelivery p′ ls‴ N″

                            N″↝[p′]↓Nᵖ′ : N″ ↝[ p′ ]↓ Nᵖ′
                            N″↝[p′]↓Nᵖ′ = honestParty↓ lsp′N″ hp′

                            lsp′Nᵖ′ : Nᵖ′ .states ⁉ p′ ≡ just ls′
                            lsp′Nᵖ′ = trans (sym $ localStatePreservation-↓∗ N₀↝⋆N″ N″—[eoN″]↓→∗N° N″↝[p′]↓Nᵖ′) ls′p′N

        goal (makeBlock {N″} {N°} N″MsgsDelivered N″—[eoN″]↑→∗N°) {b} = let open Related.EquationalReasoning in begin
          b ∈ allBlocks (ls .tree) ++ blocksToBeDelivered p N
            ≡⟨ cong (λ ◆ → b ∈ allBlocks (ls .tree) ++ ◆ ++ 𝟙s p N ++ 𝟚s p N) $ 𝟘sp*≡[] p ⟩
          b ∈ allBlocks (ls .tree) ++ 𝟙s p N ++ 𝟚s p N
            ∼⟨ tls+𝟙s+𝟚sN°p≡tls+𝟙s+𝟚sN°p′ ⟩
          b ∈ allBlocks (ls′ .tree) ++ 𝟙s p′ N ++ 𝟚s p′ N
            ≡⟨ cong (λ ◆ → b ∈ allBlocks (ls′ .tree) ++ ◆ ++ 𝟙s p′ N ++ 𝟚s p′ N) $ sym $ 𝟘sp*≡[] p′ ⟩
          b ∈ allBlocks (ls′ .tree) ++ blocksToBeDelivered p′ N
            ∎
          where
            𝟘sp*≡[] : ∀ p* → 𝟘s p* N ≡ []
            𝟘sp*≡[] p* = noImmediateMsgsIfNotReady p* (Starʳ⇒Star N₀↝⋆ʳN) λ ()

            eoN″! : Unique (N″ .execOrder)
            eoN″! = execOrderUniqueness N₀↝⋆N″

            hasLsp*N″ : ∀ {p* ls*} → N .states ⁉ p* ≡ just ls* → p* hasStateIn N″
            hasLsp*N″ {p*} ls*p*N = L.All.lookup (allPartiesHaveLocalState $ Starʳ⇒Star N₀↝⋆ʳN″) p*∈N″
              where
                p*∈N : p* ∈ N .execOrder
                p*∈N = hasState⇒∈execOrder (N₀↝⋆N″ ◅◅ N″↝N ◅ ε) (≡just⇒Is-just ls*p*N)

                p*∈N″ : p* ∈ N″ .execOrder
                p*∈N″ = ∈-resp-↭ (↭-sym (execOrderPreservation-↭-↝ N″↝N)) p*∈N

            hasLspN″ : p hasStateIn N″
            hasLspN″ = hasLsp*N″ lspN

            hasLsp′N″ : p′ hasStateIn N″
            hasLsp′N″ = hasLsp*N″ ls′p′N

            p∈eoN″ : p ∈ N″ .execOrder
            p∈eoN″ = ∈-resp-↭ (execOrderPreservation-↭ N₀↝⋆N″) (hasState⇔∈parties₀ N₀↝⋆N″ .Equivalence.to hasLspN″)

            p′∈eoN″ : p′ ∈ N″ .execOrder
            p′∈eoN″ = ∈-resp-↭ (execOrderPreservation-↭ N₀↝⋆N″) (hasState⇔∈parties₀ N₀↝⋆N″ .Equivalence.to hasLsp′N″)

            ls″ ls‴ : LocalState
            ls″ = M.to-witness hasLspN″
            ls‴ = M.to-witness hasLsp′N″

            lspN″ : N″ .states ⁉ p ≡ just ls″
            lspN″ = Is-just⇒to-witness hasLspN″

            lsp′N″ : N″ .states ⁉ p′ ≡ just ls‴
            lsp′N″ = Is-just⇒to-witness hasLsp′N″

            Nᵖ : GlobalState
            Nᵖ  = honestBlockMaking p ls″ N″

            N″↝[p]↑Nᵖ : N″ ↝[ p ]↑ Nᵖ
            N″↝[p]↑Nᵖ = honestParty↑ lspN″ hp

            lspNᵖ : Nᵖ .states ⁉ p ≡ just ls
            lspNᵖ = trans (sym $ localStatePreservation-∈-↑∗ N₀↝⋆N″ N″—[eoN″]↑→∗N° N″↝[p]↑Nᵖ) lspN

            Nᵖ′ : GlobalState
            Nᵖ′ = honestBlockMaking p′ ls‴ N″

            N″↝[p′]↑Nᵖ′ : N″ ↝[ p′ ]↑ Nᵖ′
            N″↝[p′]↑Nᵖ′ = honestParty↑ lsp′N″ hp′

            lsp′Nᵖ′ : Nᵖ′ .states ⁉ p′ ≡ just ls′
            lsp′Nᵖ′ = trans (sym $ localStatePreservation-∈-↑∗ N₀↝⋆N″ N″—[eoN″]↑→∗N° N″↝[p′]↑Nᵖ′) ls′p′N

            tls+𝟙s+𝟚sN°p≡tls+𝟙s+𝟚sN°p′ : allBlocks (ls .tree) ++ 𝟙s p N° ++ 𝟚s p N° ≡ˢ allBlocks (ls′ .tree) ++ 𝟙s p′ N° ++ 𝟚s p′ N°
            tls+𝟙s+𝟚sN°p≡tls+𝟙s+𝟚sN°p′ {b}
              with delayedBlocksEvolution-↑* N″—[eoN″]↑→∗N° eoN″! p∈eoN″ p′∈eoN″
            ... | bs , 𝟙s+𝟚sN°p≡𝟙s+𝟚sN″p+bs , 𝟙s+𝟚sN°p′≡𝟙s+𝟚sN″p′+bs
              with honestLocalTreeEvolution-↑ N₀↝⋆N″ N″—[eoN″]↑→∗N° N″↝[p]↑Nᵖ hp lspN″ lspNᵖ
            ... | bsₚ , tls≡tls″+bsₚ , πₚ
              with honestLocalTreeEvolution-↑ N₀↝⋆N″ N″—[eoN″]↑→∗N° N″↝[p′]↑Nᵖ′ hp′ lsp′N″ lsp′Nᵖ′
            ... | bsₚ′ , tls′≡tls‴+bsₚ′ , πₚ′ =
              let open Related.EquationalReasoning in begin
              b ∈ allBlocks (ls .tree) ++ 𝟙s p N° ++ 𝟚s p N°
                ∼⟨ ++-cong {xs₁ = allBlocks (ls .tree)} tls≡tls″+bsₚ ≡ˢ-refl ⟩
              b ∈ (allBlocks (ls″ .tree) ++ bsₚ) ++ 𝟙s p N° ++ 𝟚s p N°
                ∼⟨ ++-cong {xs₁ = allBlocks (ls″ .tree) ++ bsₚ} (bag-=⇒ (↭⇒∼bag (++-comm _ bsₚ))) ≡ˢ-refl ⟩
              b ∈ (bsₚ ++ allBlocks (ls″ .tree)) ++ 𝟙s p N° ++ 𝟚s p N°
                ≡⟨ cong (b ∈_) $ L.++-assoc bsₚ _ _ ⟩
              b ∈ bsₚ ++ allBlocks (ls″ .tree) ++ 𝟙s p N° ++ 𝟚s p N°
                ∼⟨ bsₚ+tls″+𝟙s+𝟚s≡bsₚ′+tls‴+𝟙s+𝟚s ⟩
              b ∈ bsₚ′ ++ allBlocks (ls‴ .tree) ++ 𝟙s p′ N° ++ 𝟚s p′ N°
                ≡⟨ cong (b ∈_) $ sym $ L.++-assoc bsₚ′ _ _ ⟩
              b ∈ (bsₚ′ ++ allBlocks (ls‴ .tree)) ++ 𝟙s p′ N° ++ 𝟚s p′ N°
                ∼⟨ ++-cong {xs₁ = bsₚ′ ++ allBlocks (ls‴ .tree)} (bag-=⇒ (↭⇒∼bag (++-comm bsₚ′ _))) ≡ˢ-refl ⟩
              b ∈ (allBlocks (ls‴ .tree) ++ bsₚ′) ++ 𝟙s p′ N° ++ 𝟚s p′ N°
                ∼⟨ ++-cong {xs₁ = allBlocks (ls‴ .tree) ++ bsₚ′} (≡ˢ-sym tls′≡tls‴+bsₚ′) ≡ˢ-refl ⟩
              b ∈ allBlocks (ls′ .tree) ++ 𝟙s p′ N° ++ 𝟚s p′ N° ∎
              where
                tls″+𝟙s+𝟚s+bs≡tls‴+𝟙s+𝟚s+bs : allBlocks (ls″ .tree) ++ 𝟙s p N″ ++ 𝟚s p N″ ++ bs ≡ˢ allBlocks (ls‴ .tree) ++ 𝟙s p′ N″ ++ 𝟚s p′ N″ ++ bs
                tls″+𝟙s+𝟚s+bs≡tls‴+𝟙s+𝟚s+bs {b} = let open Related.EquationalReasoning in begin
                  b ∈ allBlocks (ls″ .tree) ++ 𝟙s p N″ ++ 𝟚s p N″ ++ bs
                    ≡⟨ cong (b ∈_) $ aux {bs₁ = allBlocks (ls″ .tree)} {bs₂ = 𝟙s p N″} ⟩
                  b ∈ (allBlocks (ls″ .tree) ++ 𝟙s p N″ ++ 𝟚s p N″) ++ bs
                    ∼⟨ ++-cong {ys₁ = bs} tls″+𝟙s+𝟚s≡tls‴+𝟙s+𝟚s ≡ˢ-refl ⟩
                  b ∈ (allBlocks (ls‴ .tree) ++ 𝟙s p′ N″ ++ 𝟚s p′ N″) ++ bs
                    ≡⟨ cong (b ∈_) $ sym $ aux {bs₁ = allBlocks (ls‴ .tree)} {bs₂ = 𝟙s p′ N″} ⟩
                  b ∈ allBlocks (ls‴ .tree) ++ 𝟙s p′ N″ ++ 𝟚s p′ N″ ++ bs ∎
                    where
                      aux : ∀ {bs₁ bs₂ bs₃ bs₄ : List Block} →
                        bs₁ ++ bs₂ ++ bs₃ ++ bs₄ ≡ (bs₁ ++ bs₂ ++ bs₃) ++ bs₄
                      aux {bs₁} {bs₂} {bs₃} {bs₄} = let open ≡-Reasoning in begin
                        bs₁ ++ bs₂ ++ bs₃ ++ bs₄       ≡⟨ sym $ L.++-assoc bs₁ _ _ ⟩
                        (bs₁ ++ bs₂) ++ (bs₃ ++ bs₄)   ≡⟨ sym $ L.++-assoc (bs₁ ++ bs₂) _ _ ⟩
                        ((bs₁ ++ bs₂) ++ bs₃) ++ bs₄   ≡⟨ cong (_++ bs₄) $ L.++-assoc bs₁ _ _ ⟩
                        (bs₁ ++ bs₂ ++ bs₃) ++ bs₄     ∎

                      tls″+𝟙s+𝟚s≡tls‴+𝟙s+𝟚s : allBlocks (ls″ .tree) ++ 𝟙s p N″ ++ 𝟚s p N″ ≡ˢ allBlocks (ls‴ .tree) ++ 𝟙s p′ N″ ++ 𝟚s p′ N″
                      tls″+𝟙s+𝟚s≡tls‴+𝟙s+𝟚s {b} = let open Related.EquationalReasoning in begin
                        b ∈ allBlocks (ls″ .tree) ++ 𝟙s p N″ ++ 𝟚s p N″
                          ≡⟨ cong (λ ◆ → b ∈ allBlocks (ls″ .tree) ++ ◆ ++ 𝟙s p N″ ++ 𝟚s p N″) $ sym $ 𝟘sp*N″≡[] p ⟩
                        b ∈ allBlocks (ls″ .tree) ++ blocksToBeDelivered p N″
                          ∼⟨ ih ⟩
                        b ∈ allBlocks (ls‴ .tree) ++ blocksToBeDelivered p′ N″
                          ≡⟨ cong (λ ◆ → b ∈ allBlocks (ls‴ .tree) ++ ◆ ++ 𝟙s p′ N″ ++ 𝟚s p′ N″) $ 𝟘sp*N″≡[] p′ ⟩
                        b ∈ allBlocks (ls‴ .tree) ++ 𝟙s p′ N″ ++ 𝟚s p′ N″ ∎
                        where
                          𝟘sp*N″≡[] : ∀ p* → 𝟘s p* N″ ≡ []
                          𝟘sp*N″≡[] p* = noImmediateMsgsIfNotReady p* N₀↝⋆N″ (subst (_≢ ready) (sym N″MsgsDelivered) λ ())

                          ih : allBlocks (ls″ .tree) ++ blocksToBeDelivered p N″ ≡ˢ allBlocks (ls‴ .tree) ++ blocksToBeDelivered p′ N″
                          ih = allBlocks+toBeDelivered≡ʳ N₀↝⋆ʳN″ hp hp′ lspN″ lsp′N″

                bsₚ+tls″+𝟙s+𝟚s≡bsₚ′+tls‴+𝟙s+𝟚s : bsₚ ++ allBlocks (ls″ .tree) ++ 𝟙s p N° ++ 𝟚s p N° ≡ˢ bsₚ′ ++ allBlocks (ls‴ .tree) ++ 𝟙s p′ N° ++ 𝟚s p′ N°
                bsₚ+tls″+𝟙s+𝟚s≡bsₚ′+tls‴+𝟙s+𝟚s = ⊆×≡ˢ⇒++-≡ˢ {xs = bsₚ} bsₚ⊆ (≡ˢ-sym (⊆×≡ˢ⇒++-≡ˢ {xs = bsₚ′} bsₚ′⊆ tls‴+𝟙s+𝟚s≡tls″+𝟙s+𝟚s))
                  where
                    bsₚ⊆ : bsₚ ⊆ˢ bsₚ′ ++ allBlocks (ls‴ .tree) ++ 𝟙s p′ N° ++ 𝟚s p′ N°
                    bsₚ⊆ = let open L.SubS.⊆-Reasoning Block in begin
                      bsₚ                                                   ⊆⟨ πₚ p′∈eoN″ ⟩
                      𝟙s p′ N°                                              ⊆⟨ L.SubS.xs⊆xs++ys _ _ ⟩
                      𝟙s p′ N° ++ 𝟚s p′ N°                                  ⊆⟨ L.SubS.xs⊆ys++xs _ (allBlocks (ls‴ .tree)) ⟩
                      allBlocks (ls‴ .tree) ++ 𝟙s p′ N° ++ 𝟚s p′ N°         ⊆⟨ L.SubS.xs⊆ys++xs _ bsₚ′ ⟩
                      bsₚ′ ++ allBlocks (ls‴ .tree) ++ 𝟙s p′ N° ++ 𝟚s p′ N° ∎

                    bsₚ′⊆ : bsₚ′ ⊆ˢ allBlocks (ls″ .tree) ++ 𝟙s p N° ++ 𝟚s p N°
                    bsₚ′⊆ = let open L.SubS.⊆-Reasoning Block in begin
                      bsₚ′                                                  ⊆⟨ πₚ′ p∈eoN″ ⟩
                      𝟙s p N°                                               ⊆⟨ L.SubS.xs⊆xs++ys _ _ ⟩
                      𝟙s p N° ++ 𝟚s p N°                                    ⊆⟨ L.SubS.xs⊆ys++xs _ (allBlocks (ls″ .tree)) ⟩
                      allBlocks (ls″ .tree) ++ 𝟙s p N° ++ 𝟚s p N°           ∎

                    tls‴+𝟙s+𝟚s≡tls″+𝟙s+𝟚s : allBlocks (ls‴ .tree) ++ 𝟙s p′ N° ++ 𝟚s p′ N° ≡ˢ allBlocks (ls″ .tree) ++ 𝟙s p N° ++ 𝟚s p N°
                    tls‴+𝟙s+𝟚s≡tls″+𝟙s+𝟚s {b} = let open Related.EquationalReasoning in begin
                      b ∈ allBlocks (ls‴ .tree) ++ 𝟙s p′ N° ++ 𝟚s p′ N°
                        ∼⟨ ++-cong {xs₁ = allBlocks (ls‴ .tree)} ≡ˢ-refl 𝟙s+𝟚sN°p′≡𝟙s+𝟚sN″p′+bs ⟩
                      b ∈ allBlocks (ls‴ .tree) ++ 𝟙s p′ N″ ++ 𝟚s p′ N″ ++ bs
                        ∼⟨ ≡ˢ-sym tls″+𝟙s+𝟚s+bs≡tls‴+𝟙s+𝟚s+bs ⟩
                      b ∈ allBlocks (ls″ .tree) ++ 𝟙s p N″ ++ 𝟚s p N″ ++ bs
                        ∼⟨ ++-cong {xs₁ = allBlocks (ls″ .tree)} ≡ˢ-refl (≡ˢ-sym 𝟙s+𝟚sN°p≡𝟙s+𝟚sN″p+bs) ⟩
                      b ∈ allBlocks (ls″ .tree) ++ 𝟙s p N° ++ 𝟚s p N° ∎
        goal (advanceRound N″BlockMade) = goal-advanceRound
          where
            𝟙>𝟘 : (Delay ∋ 𝟙) Fi.> (Delay ∋ 𝟘)
            𝟙>𝟘 = Nat.s≤s Nat.z≤n

            𝟚>𝟘 : (Delay ∋ 𝟚) Fi.> (Delay ∋ 𝟘)
            𝟚>𝟘 = Nat.s≤s Nat.z≤n

            no𝟘s : L.All.All ((Fi._> (Delay ∋ 𝟘)) ∘ cd) (N″ .messages)
            no𝟘s = noImmediateMsgsAfterReady
                     N₀↝⋆N″
                     λ N″Ready → contradiction (trans (sym N″Ready) N″BlockMade) λ ()

            goal-advanceRound :
              allBlocks (ls .tree) ++ blocksToBeDelivered p (record (tick N″) { progress = ready })
              ≡ˢ
              allBlocks (ls′ .tree) ++ blocksToBeDelivered p′ (record (tick N″) { progress = ready })
            goal-advanceRound {b}
              rewrite
                nonImmediateBlocksPreservation {p′} {N″} {𝟙} 𝟙>𝟘 no𝟘s
              | nonImmediateBlocksPreservation {p} {N″} {𝟙} 𝟙>𝟘 no𝟘s
              | nonImmediateBlocksPreservation {p} {N″} {𝟚} 𝟚>𝟘 no𝟘s
              | nonImmediateBlocksPreservation {p′} {N″} {𝟚} 𝟚>𝟘 no𝟘s
              | no𝟚DelayMessagesAfterTick {p} {N″} N₀↝⋆N″
              | L.++-identityʳ (𝟚s p N″)
              | no𝟚DelayMessagesAfterTick {p′} {N″} N₀↝⋆N″
              | L.++-identityʳ (𝟚s p′ N″)
                = let open Related.EquationalReasoning in begin
                b ∈ allBlocks (ls .tree) ++ 𝟙s p N″ ++ 𝟚s p N″
                  ≡⟨ cong (λ ◆ → b ∈ allBlocks (ls .tree) ++ ◆ ++ 𝟙s p N″ ++ 𝟚s p N″) $ sym $ 𝟘sp*N″≡[] p ⟩
                b ∈ allBlocks (ls .tree) ++ blocksToBeDelivered p N″
                  ∼⟨ ih ⟩
                b ∈ allBlocks (ls′ .tree) ++ blocksToBeDelivered p′ N″
                  ≡⟨ cong (λ ◆ → b ∈ allBlocks (ls′ .tree) ++ ◆ ++ 𝟙s p′ N″ ++ 𝟚s p′ N″) $ 𝟘sp*N″≡[] p′ ⟩
                b ∈ allBlocks (ls′ .tree) ++ 𝟙s p′ N″ ++ 𝟚s p′ N″ ∎
                where
                  𝟘sp*N″≡[] : ∀ p* → 𝟘s p* N″ ≡ []
                  𝟘sp*N″≡[] p* = noImmediateMsgsIfNotReady p* N₀↝⋆N″ (subst (_≢ ready) (sym N″BlockMade) λ ())

                  ih : allBlocks (ls .tree) ++ blocksToBeDelivered p N″ ≡ˢ allBlocks (ls′ .tree) ++ blocksToBeDelivered p′ N″
                  ih = allBlocks+toBeDelivered≡ʳ N₀↝⋆ʳN″ hp hp′ lspN ls′p′N
        goal (permuteParties _) = allBlocks+toBeDelivered≡ʳ N₀↝⋆ʳN″ hp hp′ lspN ls′p′N
        goal (permuteMsgs {envelopes = es} msgsN″↭es) {b} = let open Related.EquationalReasoning in begin
          b ∈ allBlocks (ls .tree) ++ blocksToBeDelivered p N°
            ∼⟨ ++-cong {xs₁ = allBlocks (ls .tree)} ≡ˢ-refl $ ≡ˢ-sym (TBD≡ {p}) ⟩
          b ∈ allBlocks (ls .tree) ++ blocksToBeDelivered p N″
            ∼⟨ allBlocks+toBeDelivered≡ʳ N₀↝⋆ʳN″ hp hp′ lspN ls′p′N ⟩
          b ∈ allBlocks (ls′ .tree) ++ blocksToBeDelivered p′ N″
            ∼⟨ ++-cong {xs₁ = allBlocks (ls′ .tree)} ≡ˢ-refl $ TBD≡ {p′} ⟩
          b ∈ allBlocks (ls′ .tree) ++ blocksToBeDelivered p′ N° ∎
          where
            N° = GlobalState ∋ record N″ { messages = es }

            TBD≡ : ∀ {p} → blocksToBeDelivered p N″ ≡ˢ blocksToBeDelivered p N°
            TBD≡ {p} {b} = let open Related.EquationalReasoning in begin
              b ∈ blocksToBeDelivered p N″
                ∼⟨ ++-cong {xs₁ = 𝟘s p N″} ≡ˢ-refl $ ++-cong (TBDIn≡ {p} {𝟙}) (TBDIn≡ {p} {𝟚}) ⟩
              b ∈ 𝟘s p N″ ++ 𝟙s p N° ++ 𝟚s p N°
                ∼⟨ ++-cong {ys₁ = 𝟙s p N° ++ 𝟚s p N°} (TBDIn≡ {p} {𝟘}) ≡ˢ-refl ⟩
              b ∈ blocksToBeDelivered p N° ∎
              where
                TBDIn≡ : ∀ {p d} → blocksDeliveredIn p d N″ ≡ˢ blocksDeliveredIn p d N°
                TBDIn≡ = bag-=⇒ $ ↭⇒∼bag $ map⁺ _ $ filter-↭ _ msgsN″↭es

allBlocksExtensionAtMsgsDelivered : ∀ {N : GlobalState} {p p′ : Party} {ls ls′ : LocalState} →
    N₀ ↝⋆ N
  → Honest p
  → Honest p′
  → N .progress ≡ msgsDelivered
  → N .states ⁉ p ≡ just ls
  → N .states ⁉ p′ ≡ just ls′
  → allBlocks (ls .tree) ⊆ˢ allBlocks (ls′ .tree) ++ blocksDeliveredIn p′ 𝟙 N
allBlocksExtensionAtMsgsDelivered N₀↝⋆N hp hp′ NMsgsDelivered lspN ls′p′N =
  allBlocksExtensionAtMsgsDeliveredʳ (Star⇒Starʳ N₀↝⋆N) hp hp′ NMsgsDelivered lspN ls′p′N
  where
    open RTC; open Starʳ
    allBlocksExtensionAtMsgsDeliveredʳ : ∀ {N : GlobalState} {p p′ : Party} {ls ls′ : LocalState} →
        N₀ ↝⋆ʳ N
      → Honest p
      → Honest p′
      → N .progress ≡ msgsDelivered
      → N .states ⁉ p ≡ just ls
      → N .states ⁉ p′ ≡ just ls′
      → allBlocks (ls .tree) ⊆ˢ allBlocks (ls′ .tree) ++ blocksDeliveredIn p′ 𝟙 N
    allBlocksExtensionAtMsgsDeliveredʳ εʳ _ _ ready≡msgsDelivered _ _ = contradiction ready≡msgsDelivered λ ()
    allBlocksExtensionAtMsgsDeliveredʳ {N} {p} {p′} {ls} {ls′} (_◅ʳ_ {j = N″} N₀↝⋆ʳN″ N″↝N) hp hp′ NMsgsDelivered lspN ls′p′N =
      goal N″↝N NMsgsDelivered
      where
        N₀↝⋆N″ : N₀ ↝⋆ N″
        N₀↝⋆N″ = Starʳ⇒Star N₀↝⋆ʳN″

        pHasInN″ : p hasStateIn N″
        pHasInN″ = hasState⇔-↝⋆ (N″↝N ◅ ε) .Equivalence.from $ hasStateInAltDef {N} .Equivalence.to (ls , lspN)

        p′HasInN″ : p′ hasStateIn N″
        p′HasInN″ = hasState⇔-↝⋆ (N″↝N ◅ ε) .Equivalence.from $ hasStateInAltDef {N} .Equivalence.to (ls′ , ls′p′N)

        goal :
            N″ ↝ N
          → N .progress ≡ msgsDelivered
          → allBlocks (ls .tree) ⊆ˢ allBlocks (ls′ .tree) ++ blocksDeliveredIn p′ 𝟙 N
        goal (permuteParties _) _ = allBlocksExtensionAtMsgsDeliveredʳ N₀↝⋆ʳN″ hp hp′ NMsgsDelivered lspN ls′p′N
        goal (permuteMsgs {envelopes = es} msgsN″↭es) _ = goal-permuteMsgs
          where
            bs₁ bs₂ : List Block
            bs₁ = allBlocks (ls′ .tree) ++ blocksDeliveredIn p′ 𝟙 N″
            bs₂ = allBlocks (ls′ .tree) ++ blocksDeliveredIn p′ 𝟙 record N″ { messages = es }

            bs₁≡bs₂ : bs₁ ≡ˢ bs₂
            bs₁≡bs₂ = ++-cong K-refl $ λ {b} → let open Related.EquationalReasoning in begin
              b ∈ blocksDeliveredIn p′ 𝟙 N″
                ∼⟨ bag-=⇒ $ ↭⇒∼bag $ map⁺ _ $ filter-↭ _ msgsN″↭es ⟩
              b ∈ blocksDeliveredIn p′ 𝟙 record N″ { messages = es }  ∎

            goal-permuteMsgs : allBlocks (ls .tree) ⊆ˢ bs₂
            goal-permuteMsgs =
              L.SubS.⊆-trans
                (allBlocksExtensionAtMsgsDeliveredʳ N₀↝⋆ʳN″ hp hp′ NMsgsDelivered lspN ls′p′N)
                (≡ˢ⇒⊆ bs₁≡bs₂)
        goal (deliverMsgs {N′ = N°} N″Ready N″—[eoN″]↓→∗N°) _ =
          case hasStateInAltDef {N″} .Equivalence.from pHasInN″ of λ where
            (ls″ , ls″pN″) → case hasStateInAltDef {N″} .Equivalence.from p′HasInN″ of λ where
              (ls‴ , ls‴p′N″) → goal-deliverMsgs ls″ ls‴ ls″pN″ ls‴p′N″
                where
                  goal-deliverMsgs : ∀ (ls″ ls‴ : LocalState) →
                      N″ .states ⁉ p ≡ just ls″
                    → N″ .states ⁉ p′ ≡ just ls‴
                    → allBlocks (ls .tree) ⊆ˢ allBlocks (ls′ .tree) ++ blocksDeliveredIn p′ 𝟙 N°
                  goal-deliverMsgs ls″ ls‴ ls″pN″ ls‴p′N″ {b} b∈tls =
                      b∈tls ∶
                    b ∈ allBlocks (ls .tree)
                      |> ≡ˢ⇒⊆ tls≡tls″+𝟘s ∶
                    b ∈ allBlocks (ls″ .tree) ++ blocksDeliveredIn p 𝟘 N″
                      |> L.SubS.xs⊆xs++ys _ _ ∶
                    b ∈ (allBlocks (ls″ .tree) ++ blocksDeliveredIn p 𝟘 N″) ++ blocksDeliveredIn p 𝟙 N″
                      |> (L.SubS.⊆-reflexive $ L.++-assoc (allBlocks (ls″ .tree)) _ _) ∶
                    b ∈ allBlocks (ls″ .tree) ++ blocksDeliveredIn p 𝟘 N″ ++ blocksDeliveredIn p 𝟙 N″
                      |> ≡ˢ⇒⊆ tls″+𝟘s+𝟙s≡tls‴+𝟘s+𝟙s ∶
                    b ∈ allBlocks (ls‴ .tree) ++ blocksDeliveredIn p′ 𝟘 N″ ++ blocksDeliveredIn p′ 𝟙 N″
                      |> (L.SubS.⊆-reflexive $ sym $ L.++-assoc (allBlocks (ls‴ .tree)) _ _) ∶
                    b ∈ (allBlocks (ls‴ .tree) ++ blocksDeliveredIn p′ 𝟘 N″) ++ blocksDeliveredIn p′ 𝟙 N″
                      |> (L.SubS.++⁺ʳ _ $ blocksDeliveredIn-⊆-↓∗ N″—[eoN″]↓→∗N°) ∶
                    b ∈ (allBlocks (ls‴ .tree) ++ blocksDeliveredIn p′ 𝟘 N″) ++ blocksDeliveredIn p′ 𝟙 N°
                      |> L.SubS.++⁺ˡ (blocksDeliveredIn p′ 𝟙 N°) (≡ˢ⇒⊇ tls′≡tls‴+𝟘s) ∶
                    b ∈ allBlocks (ls′ .tree) ++ blocksDeliveredIn p′ 𝟙 N°
                    where
                      open import Function.Reasoning

                      blocksToBeDelivered : GlobalState → Party → List Block
                      blocksToBeDelivered N p = blocksDeliveredIn p 𝟘 N ++ blocksDeliveredIn p 𝟙 N ++ blocksDeliveredIn p 𝟚 N

                      tls″+𝟘s+𝟙s≡tls‴+𝟘s+𝟙s :
                        allBlocks (ls″ .tree) ++ blocksDeliveredIn p 𝟘 N″ ++ blocksDeliveredIn p 𝟙 N″
                        ≡ˢ
                        allBlocks (ls‴ .tree) ++ blocksDeliveredIn p′ 𝟘 N″ ++ blocksDeliveredIn p′ 𝟙 N″
                      tls″+𝟘s+𝟙s≡tls‴+𝟘s+𝟙s {b} = let open Related.EquationalReasoning in begin
                        b ∈ allBlocks (ls″ .tree) ++ blocksDeliveredIn p 𝟘 N″ ++ blocksDeliveredIn p 𝟙 N″
                          ≡⟨ cong (λ ◆ → b ∈ allBlocks (ls″ .tree) ++ blocksDeliveredIn p 𝟘 N″ ++ ◆) $ sym $ L.++-identityʳ _ ⟩
                        b ∈ allBlocks (ls″ .tree) ++ blocksDeliveredIn p 𝟘 N″ ++ blocksDeliveredIn p 𝟙 N″ ++ []
                          ≡⟨ cong (λ ◆ → b ∈ allBlocks (ls″ .tree) ++ blocksDeliveredIn p 𝟘 N″ ++ blocksDeliveredIn p 𝟙 N″ ++ ◆) $
                               sym $ noBlocksDeliveredIn𝟚AtReady N₀↝⋆N″ N″Ready ⟩
                        b ∈ allBlocks (ls″ .tree) ++ blocksToBeDelivered N″ p
                          ∼⟨ allBlocks+toBeDelivered≡ N₀↝⋆N″ hp hp′ ls″pN″ ls‴p′N″ ⟩
                        b ∈ allBlocks (ls‴ .tree) ++ blocksToBeDelivered N″ p′
                          ≡⟨ cong (λ ◆ → b ∈ allBlocks (ls‴ .tree) ++ blocksDeliveredIn p′ 𝟘 N″ ++ blocksDeliveredIn p′ 𝟙 N″ ++ ◆) $
                               noBlocksDeliveredIn𝟚AtReady N₀↝⋆N″ N″Ready ⟩
                        b ∈ allBlocks (ls‴ .tree) ++ blocksDeliveredIn p′ 𝟘 N″ ++ blocksDeliveredIn p′ 𝟙 N″ ++ []
                          ≡⟨ cong (λ ◆ → b ∈ allBlocks (ls‴ .tree) ++ blocksDeliveredIn p′ 𝟘 N″ ++ ◆) $ L.++-identityʳ _ ⟩
                        b ∈ allBlocks (ls‴ .tree) ++ blocksDeliveredIn p′ 𝟘 N″ ++ blocksDeliveredIn p′ 𝟙 N″  ∎

                      tls≡tls″+𝟘s : allBlocks (ls .tree) ≡ˢ allBlocks (ls″ .tree) ++ blocksDeliveredIn p 𝟘 N″
                      tls≡tls″+𝟘s = honestLocalTreeEvolution-↓ hp ls″pN″ N″↝[p]↓Nᵖ lspNᵖ
                        where
                          Nᵖ : GlobalState
                          Nᵖ = honestMsgsDelivery p ls″ N″

                          N″↝[p]↓Nᵖ : N″ ↝[ p ]↓ Nᵖ
                          N″↝[p]↓Nᵖ = honestParty↓ ls″pN″ hp

                          lspNᵖ : Nᵖ .states ⁉ p ≡ just ls
                          lspNᵖ = trans (sym $ localStatePreservation-↓∗ N₀↝⋆N″ N″—[eoN″]↓→∗N° N″↝[p]↓Nᵖ) lspN

                      tls′≡tls‴+𝟘s : allBlocks (ls′ .tree) ≡ˢ allBlocks (ls‴ .tree) ++ blocksDeliveredIn p′ 𝟘 N″
                      tls′≡tls‴+𝟘s = honestLocalTreeEvolution-↓ hp′ ls‴p′N″ N″↝[p′]↓Nᵖ′ ls′p′Nᵖ′
                        where
                          Nᵖ′ : GlobalState
                          Nᵖ′ = honestMsgsDelivery p′ ls‴ N″

                          N″↝[p′]↓Nᵖ′ : N″ ↝[ p′ ]↓ Nᵖ′
                          N″↝[p′]↓Nᵖ′ = honestParty↓ ls‴p′N″ hp′

                          ls′p′Nᵖ′ : Nᵖ′ .states ⁉ p′ ≡ just ls′
                          ls′p′Nᵖ′ = trans (sym $ localStatePreservation-↓∗ N₀↝⋆N″ N″—[eoN″]↓→∗N° N″↝[p′]↓Nᵖ′) ls′p′N

allBlocksExtensionAtBlockMade : ∀ {N : GlobalState} {p p′ : Party} {ls ls′ : LocalState} →
    N₀ ↝⋆ N
  → Honest p
  → Honest p′
  → N .progress ≡ blockMade
  → N .states ⁉ p ≡ just ls
  → N .states ⁉ p′ ≡ just ls′
  → allBlocks (ls .tree) ⊆ˢ allBlocks (ls′ .tree) ++ blocksDeliveredIn p′ 𝟙 N
allBlocksExtensionAtBlockMade N₀↝⋆N hp hp′ NBlockMade lspN ls′p′N =
  allBlocksExtensionAtBlockMadeʳ (Star⇒Starʳ N₀↝⋆N) hp hp′ NBlockMade lspN ls′p′N
  where
    open RTC; open Starʳ
    allBlocksExtensionAtBlockMadeʳ : ∀ {N : GlobalState} {p p′ : Party} {ls ls′ : LocalState} →
        N₀ ↝⋆ʳ N
      → Honest p
      → Honest p′
      → N .progress ≡ blockMade
      → N .states ⁉ p ≡ just ls
      → N .states ⁉ p′ ≡ just ls′
      → allBlocks (ls .tree) ⊆ˢ allBlocks (ls′ .tree) ++ blocksDeliveredIn p′ 𝟙 N
    allBlocksExtensionAtBlockMadeʳ εʳ _ _ ready≡blockMade _ _ = contradiction ready≡blockMade λ ()
    allBlocksExtensionAtBlockMadeʳ {N} {p} {p′} {ls} {ls′} (_◅ʳ_ {j = N″} N₀↝⋆ʳN″ N″↝N) hp hp′ NBlockMade lspN ls′p′N =
      goal N″↝N NBlockMade
      where
        N₀↝⋆N″ : N₀ ↝⋆ N″
        N₀↝⋆N″ = Starʳ⇒Star N₀↝⋆ʳN″

        pHasInN″ : p hasStateIn N″
        pHasInN″ = hasState⇔-↝⋆ (N″↝N ◅ ε) .Equivalence.from $ hasStateInAltDef {N} .Equivalence.to (ls , lspN)

        p′HasInN″ : p′ hasStateIn N″
        p′HasInN″ = hasState⇔-↝⋆ (N″↝N ◅ ε) .Equivalence.from $ hasStateInAltDef {N} .Equivalence.to (ls′ , ls′p′N)

        goal :
            N″ ↝ N
          → N .progress ≡ blockMade
          → allBlocks (ls .tree) ⊆ˢ allBlocks (ls′ .tree) ++ blocksDeliveredIn p′ 𝟙 N
        goal (permuteParties _) _ = allBlocksExtensionAtBlockMadeʳ N₀↝⋆ʳN″ hp hp′ NBlockMade lspN ls′p′N
        goal (permuteMsgs {envelopes = es} msgsN″↭es) _ = goal-permuteMsgs
          where
            bs₁ bs₂ : List Block
            bs₁ = allBlocks (ls′ .tree) ++ blocksDeliveredIn p′ 𝟙 N″
            bs₂ = allBlocks (ls′ .tree) ++ blocksDeliveredIn p′ 𝟙 record N″ { messages = es }

            bs₁≡bs₂ : bs₁ ≡ˢ bs₂
            bs₁≡bs₂ = ++-cong K-refl $ λ {b} → let open Related.EquationalReasoning in begin
              b ∈ blocksDeliveredIn p′ 𝟙 N″
                ∼⟨ bag-=⇒ $ ↭⇒∼bag $ map⁺ _ $ filter-↭ _ msgsN″↭es ⟩
              b ∈ blocksDeliveredIn p′ 𝟙 record N″ { messages = es }  ∎

            goal-permuteMsgs : allBlocks (ls .tree) ⊆ˢ bs₂
            goal-permuteMsgs =
              L.SubS.⊆-trans
                (allBlocksExtensionAtBlockMadeʳ N₀↝⋆ʳN″ hp hp′ NBlockMade lspN ls′p′N)
                (≡ˢ⇒⊆ bs₁≡bs₂)
        goal (makeBlock {N′ = N°} N″MsgsDelivered N″—[eoN″]↑→∗N°) _ =
          case hasStateInAltDef {N″} .Equivalence.from pHasInN″ of λ where
            (ls″ , ls″pN″) → case hasStateInAltDef {N″} .Equivalence.from p′HasInN″ of λ where
              (ls‴ , ls‴p′N″) →
                goal-makeBlock ls″ ls‴ ls″pN″ ls‴p′N″
                where
                  goal-makeBlock : ∀ (ls″ ls‴ : LocalState) →
                      N″ .states ⁉ p ≡ just ls″
                    → N″ .states ⁉ p′ ≡ just ls‴
                    → allBlocks (ls .tree) ⊆ˢ allBlocks (ls′ .tree) ++ blocksDeliveredIn p′ 𝟙 N°
                  goal-makeBlock ls″ ls‴ ls″pN″ ls‴p′N″ =
                    case honestLocalTreeEvolution-↑ N₀↝⋆N″ N″—[eoN″]↑→∗N° N″↝[p]↑Nᵖ hp ls″pN″ lspNᵖ of λ where
                      (bs , tls≡tls″+bs , bs⊆1s) →
                        case honestLocalTreeEvolution-↑ N₀↝⋆N″ N″—[eoN″]↑→∗N° N″↝[p′]↑Nᵖ′ hp′ ls‴p′N″ ls′p′Nᵖ′ of λ where
                          (bs′ , tls′≡tls‴+bs′ , bs′⊆1s) → goal-makeBlock′ bs bs′ tls≡tls″+bs tls′≡tls‴+bs′ bs⊆1s bs′⊆1s
                    where
                      Nᵖ Nᵖ′ : GlobalState
                      Nᵖ  = honestBlockMaking p ls″ N″
                      Nᵖ′ = honestBlockMaking p′ ls‴ N″

                      N″↝[p]↑Nᵖ : N″ ↝[ p ]↑ Nᵖ
                      N″↝[p]↑Nᵖ = honestParty↑ ls″pN″ hp

                      N″↝[p′]↑Nᵖ′ : N″ ↝[ p′ ]↑ Nᵖ′
                      N″↝[p′]↑Nᵖ′ = honestParty↑ ls‴p′N″ hp′

                      lspNᵖ : Nᵖ .states ⁉ p ≡ just ls
                      lspNᵖ = trans (sym $ localStatePreservation-∈-↑∗ N₀↝⋆N″ N″—[eoN″]↑→∗N° N″↝[p]↑Nᵖ) lspN

                      ls′p′Nᵖ′ : Nᵖ′ .states ⁉ p′ ≡ just ls′
                      ls′p′Nᵖ′ = trans (sym $ localStatePreservation-∈-↑∗ N₀↝⋆N″ N″—[eoN″]↑→∗N° N″↝[p′]↑Nᵖ′) ls′p′N

                      p∈eoN″ : p ∈ N″ .execOrder
                      p∈eoN″ = ∈-resp-↭ (execOrderPreservation-↭ N₀↝⋆N″) (hasState⇔∈parties₀ N₀↝⋆N″ .Equivalence.to pHasInN″)

                      p′∈eoN″ : p′ ∈ N″ .execOrder
                      p′∈eoN″ = ∈-resp-↭ (execOrderPreservation-↭ N₀↝⋆N″) (hasState⇔∈parties₀ N₀↝⋆N″ .Equivalence.to p′HasInN″)

                      𝟙s : List Block
                      𝟙s = blocksDeliveredIn p′ 𝟙 N°

                      open import Function.Reasoning

                      goal-makeBlock′ : ∀ (bs bs′ : List Block) →
                          allBlocks (ls .tree) ≡ˢ allBlocks (ls″ .tree) ++ bs
                        → allBlocks (ls′ .tree) ≡ˢ allBlocks (ls‴ .tree) ++ bs′
                        → (∀ {p*} → p* ∈ N″ .execOrder → bs ⊆ˢ blocksDeliveredIn p* 𝟙 N°)
                        → (∀ {p*} → p* ∈ N″ .execOrder → bs′ ⊆ˢ blocksDeliveredIn p* 𝟙 N°)
                        → allBlocks (ls .tree) ⊆ˢ allBlocks (ls′ .tree) ++ 𝟙s
                      goal-makeBlock′ bs bs′ tls≡tls″+bs tls′≡tls‴+bs′ bs⊆1s bs′⊆1s {b} b∈tls =
                          b∈tls ∶
                        b ∈ allBlocks (ls .tree)
                          |> ≡ˢ⇒⊆ tls≡tls″+bs ∶
                        b ∈ allBlocks (ls″ .tree) ++ bs
                          |> ++-meet tls″⊆ (L.SubS.⊆-trans (bs⊆1s p′∈eoN″) (L.SubS.xs⊆ys++xs _ _)) ∶
                        b ∈ (allBlocks (ls‴ .tree) ++ bs′) ++ 𝟙s
                          |> L.SubS.++⁺ˡ 𝟙s (≡ˢ⇒⊇ tls′≡tls‴+bs′) ∶
                        b ∈ allBlocks (ls′ .tree) ++ 𝟙s
                        where
                           tls″⊆ : allBlocks (ls″ .tree) ⊆ˢ (allBlocks (ls‴ .tree) ++ bs′) ++ 𝟙s
                           tls″⊆ {b} b∈tls″ with ¿ b ∈ bs′ ¿
                           ... | no b∉bs′ =
                             L.SubS.⊆-trans
                               (allBlocksExtensionAtMsgsDelivered N₀↝⋆N″ hp hp′ N″MsgsDelivered ls″pN″ ls‴p′N″)
                               (L.SubS.⊆-trans (L.SubS.++⁺ʳ _ (blocksDeliveredIn-⊆-↑∗ N″—[eoN″]↑→∗N°)) tls‴⊆) $
                               b∈tls″
                             where
                               tls‴⊆ : allBlocks (ls‴ .tree) ++ 𝟙s ⊆ˢ (allBlocks (ls‴ .tree) ++ bs′) ++ 𝟙s
                               tls‴⊆ = let open L.SubS.⊆-Reasoning Block in begin
                                 allBlocks (ls‴ .tree) ++ 𝟙s
                                   ⊆⟨ L.SubS.xs⊆xs++ys _ _ ⟩
                                 (allBlocks (ls‴ .tree) ++ blocksDeliveredIn p′ 𝟙 N°) ++ bs′
                                   ≡⟨ L.++-assoc _ (blocksDeliveredIn p′ 𝟙 N°) bs′ ⟩
                                 allBlocks (ls‴ .tree) ++ (blocksDeliveredIn p′ 𝟙 N° ++ bs′)
                                   ⊆⟨ L.SubS.++⁺ʳ (allBlocks (ls‴ .tree)) $ ⊆-++-comm 𝟙s bs′ ⟩
                                 allBlocks (ls‴ .tree) ++ (bs′ ++ 𝟙s)
                                   ≡⟨ L.++-assoc _ bs′ 𝟙s ⟨
                                 (allBlocks (ls‴ .tree) ++ bs′) ++ 𝟙s ∎
                           ... | yes b∈bs′ = L.Mem.∈-++⁺ˡ $ L.Mem.∈-++⁺ʳ (allBlocks (ls‴ .tree)) b∈bs′

allBlocksExtensionAtReady : ∀ {N : GlobalState} {p p′ : Party} {ls ls′ : LocalState} →
    N₀ ↝⋆ N
  → Honest p
  → Honest p′
  → N .progress ≡ ready
  → N .states ⁉ p ≡ just ls
  → N .states ⁉ p′ ≡ just ls′
  → allBlocks (ls .tree) ⊆ˢ allBlocks (ls′ .tree) ++ blocksDeliveredIn p′ 𝟘 N
allBlocksExtensionAtReady N₀↝⋆N hp hp′ NReady lspN ls′p′N =
  allBlocksExtensionAtReadyʳ (Star⇒Starʳ N₀↝⋆N) hp hp′ NReady lspN ls′p′N
  where
    open RTC; open Starʳ
    allBlocksExtensionAtReadyʳ : ∀ {N : GlobalState} {p p′ : Party} {ls ls′ : LocalState} →
        N₀ ↝⋆ʳ N
      → Honest p
      → Honest p′
      → N .progress ≡ ready
      → N .states ⁉ p ≡ just ls
      → N .states ⁉ p′ ≡ just ls′
      → allBlocks (ls .tree) ⊆ˢ allBlocks (ls′ .tree) ++ blocksDeliveredIn p′ 𝟘 N
    allBlocksExtensionAtReadyʳ εʳ _ _ _ lspN ls′p′N
      rewrite tree₀InN₀ lspN | tree₀InN₀ ls′p′N | L.++-identityʳ (allBlocks tree₀) = L.SubS.⊆-refl
    allBlocksExtensionAtReadyʳ {N} {p} {p′} {ls} {ls′} (_◅ʳ_ {j = N″} N₀↝⋆ʳN″ N″↝N) hp hp′ NReady lspN ls′p′N =
      goal N″↝N NReady
      where
        goal :
            N″ ↝ N
          → N .progress ≡ ready
          → allBlocks (ls .tree) ⊆ˢ allBlocks (ls′ .tree) ++ blocksDeliveredIn p′ 𝟘 N
        goal (permuteParties _) _ = allBlocksExtensionAtReadyʳ N₀↝⋆ʳN″ hp hp′ NReady lspN ls′p′N
        goal (permuteMsgs {envelopes = es} msgsN″↭es) _ = goal-permuteMsgs
          where
            bs₁ bs₂ : List Block
            bs₁ = allBlocks (ls′ .tree) ++ blocksDeliveredIn p′ 𝟘 N″
            bs₂ = allBlocks (ls′ .tree) ++ blocksDeliveredIn p′ 𝟘 record N″ { messages = es }

            bs₁≡bs₂ : bs₁ ≡ˢ bs₂
            bs₁≡bs₂ = ++-cong K-refl $ λ {b} → let open Related.EquationalReasoning in begin
              b ∈ blocksDeliveredIn p′ 𝟘 N″
                ∼⟨ bag-=⇒ $ ↭⇒∼bag $ map⁺ _ $ filter-↭ _ msgsN″↭es ⟩
              b ∈ blocksDeliveredIn p′ 𝟘 record N″ { messages = es }  ∎

            goal-permuteMsgs : allBlocks (ls .tree) ⊆ˢ bs₂
            goal-permuteMsgs = L.SubS.⊆-trans (allBlocksExtensionAtReadyʳ N₀↝⋆ʳN″ hp hp′ NReady lspN ls′p′N) (≡ˢ⇒⊆ bs₁≡bs₂)
        goal (advanceRound N″BlockMade) _ = goal-advanceRound
          where
            𝟙>𝟘 : (Delay ∋ 𝟙) Fi.> (Delay ∋ 𝟘)
            𝟙>𝟘 = Nat.s≤s Nat.z≤n

            no𝟘s : L.All.All ((Fi._> (Delay ∋ 𝟘)) ∘ cd) (N″ .messages)
            no𝟘s = noImmediateMsgsAfterReady
                     (Starʳ⇒Star N₀↝⋆ʳN″)
                     λ N″Ready → contradiction (trans (sym N″Ready) N″BlockMade) λ ()

            goal-advanceRound :
              allBlocks (ls .tree) ⊆ˢ allBlocks (ls′ .tree) ++ blocksDeliveredIn p′ 𝟘 (record (tick N″) { progress = ready })
            goal-advanceRound rewrite nonImmediateBlocksPreservation {p′} {N″} {𝟙} 𝟙>𝟘 no𝟘s =
              allBlocksExtensionAtBlockMade (Starʳ⇒Star N₀↝⋆ʳN″) hp hp′ N″BlockMade  lspN ls′p′N

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
  → N ↝⋆ N′
  → allBlocks (honestTree N) ⊆ˢ allBlocks (honestTree N′)
honestGlobalTreeBlocksMonotonicity {N} {N′} N₀↝⋆N N↝⋆N′ {b} b∈htN
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
    p∈eoN′ = ∈-resp-↭ (execOrderPreservation-↭ N↝⋆N′) p∈eoN

    ∃lspN′ : ∃[ ls′ ] N′ .states ⁉ p ≡ just ls′
    ∃lspN′ = hasStateInAltDef {N′} .Equivalence.from pHasInN′
      where
        pHasInN′ : p hasStateIn N′
        pHasInN′ = hasState⇔-↝⋆ N↝⋆N′ .Equivalence.to $ hasStateInAltDef {N} .Equivalence.to (ls , lspN)

    b∈cM : b ∈ L.concatMap (blocks N′) (honestParties N′)
    b∈cM = L.Mem.concat-∈↔ .Inverse.to (b∈cM* p∈eoN′)
      where
        b∈cM* : ∀ {ps*} → p ∈ ps* → ∃[ bs ] b ∈ bs × bs ∈ L.map (blocks N′) (L.filter ¿ Honest ¿¹ ps*)
        b∈cM* {[]} ()
        b∈cM* {p* ∷ ps*} (here p≡p*) rewrite sym p≡p* | hp with ∃lspN′
        ... | ls′ , lspN′ rewrite lspN′ = allBlocks (ls′ .tree) , b∈ls′t , here refl
          where
            b∈ls′t : b ∈ allBlocks (ls′ .tree)
            b∈ls′t = honestLocalTreeBlocksMonotonicity N₀↝⋆N hp lspN N↝⋆N′ lspN′ b∈lst
        b∈cM* {p* ∷ ps*} (there p∈ps*) with b∈cM* {ps*} p∈ps*
        ... | bs′ , b∈bs′ , bs′∈bss[ps*] with ¿ Honest p* ¿
        ...   | yes _ = bs′ , b∈bs′ , there bs′∈bss[ps*]
        ...   | no  _ = bs′ , b∈bs′ , bs′∈bss[ps*]

honestTreeChainLengthMonotonicity : ∀ {N N′ : GlobalState} →
    N₀ ↝⋆ N
  → N ↝⋆ N′
  → length (honestTreeChain N) ≤ length (honestTreeChain N′)
honestTreeChainLengthMonotonicity {N} {N′} N₀↝⋆N N↝⋆N′ =
  allBlocks⊆×≤ˢ⇒|bestChain|≤
    (honestGlobalTreeBlocksMonotonicity N₀↝⋆N N↝⋆N′)
    (Nat.∸-monoˡ-≤ 1 (clockMonotonicity N↝⋆N′))

module _ {T : Type} ⦃ _ : Tree T ⦄ where

  extendTreeLength : ∀ (t : T) (b : Block) →
    let s = b .slot in
      length (bestChain s (extendTree t b)) ≡ 1 + length (bestChain (s ∸ 1) t)
  extendTreeLength = {!!}
