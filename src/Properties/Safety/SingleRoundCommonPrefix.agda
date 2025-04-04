{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled

open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Safety.SingleRoundCommonPrefix
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

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
open import Data.List.Relation.Binary.Suffix.Heterogeneous using (Suffix; here; there; tail)
open import Data.List.Relation.Binary.Pointwise as Pointwise using (Pointwise-≡⇒≡; ≡⇒Pointwise-≡)
open import Function.Bundles
open Function.Bundles.Equivalence using (to)
open import Data.List.Properties.Ext using ([]≢∷ʳ; ≢[]⇒∷)
open import Relation.Binary.PropositionalEquality.Core using (≢-sym)

opaque

  lcs : Chain → Chain → Chain
  lcs c₁ c₂ with c₁ ⪯? c₂
  ... | yes _ = c₁
  ... | no  _ with c₁
  ... |   _ ∷ c₁′ = lcs c₁′ c₂
  ... |   []      = []

  lcs-⪯ˡ : ∀ (c₁ c₂ : Chain) → lcs c₁ c₂ ⪯ c₁
  lcs-⪯ˡ c₁ c₂ with c₁ ⪯? c₂
  ... | yes _ = ⪯-refl
  ... | no  _ with c₁
  ... |   _ ∷ c₁′ = there (lcs-⪯ˡ c₁′ c₂)
  ... |   []      = ⪯-refl

  lcs-⪯ʳ : ∀ (c₁ c₂ : Chain) → lcs c₁ c₂ ⪯ c₂
  lcs-⪯ʳ c₁ c₂ with c₁ ⪯? c₂
  ... | yes p = p
  ... | no  _ with c₁
  ... |   _ ∷ c₁′ = lcs-⪯ʳ c₁′ c₂
  ... |   []      with c₂
  ... |   _ ∷ c₂′ = there (lcs-⪯ʳ [] c₂′)
  ... |   []      = ⪯-refl

  lcs-join : ∀ {c₁ c₂ c : Chain} → c ⪯ c₁ → c ⪯ c₂ → c ⪯ lcs c₁ c₂
  lcs-join {[]}       {c₂} {c} p₁ p₂ = p₁
  lcs-join {b₁ ∷ c₁′} {c₂} {c} p₁ p₂ with (b₁ ∷ c₁′) ⪯? c₂
  ... | yes _ = p₁
  ... | no  p = lcs-join {c₁′} {c₂} {c} p₃ p₂
    where
      p₃ : c ⪯ c₁′
      p₃ with c ≟ b₁ ∷ c₁′
      ... | yes eq = contradiction (subst (_⪯ c₂) eq p₂) p
      ... | no neq = ≢∷×⪯∷⇒⪯ neq p₁

  join-lcs : ∀ {c₁ c₂ c : Chain} → c ⪯ lcs c₁ c₂ → c ⪯ c₁ × c ⪯ c₂
  join-lcs {[]}     {c₂} {c} (here c≐[]) rewrite Pointwise-≡⇒≡ c≐[] = []⪯ , []⪯
  join-lcs {b ∷ c₁} {c₂} {c} p with (b ∷ c₁) ⪯? c₂
  ... | yes q = p , ⪯-trans p q
  ... | no ¬q with join-lcs {c₁} {c₂} {c} p
  ... |   c⪯c₁ , c⪯c₂ = there c⪯c₁ , c⪯c₂

  gb⪯lcs : ∀ {c₁ c₂ : Chain} → c₁ ✓ → c₂ ✓ → [ genesisBlock ] ⪯ lcs c₁ c₂
  gb⪯lcs c₁✓ c₂✓ = lcs-join (✓⇒gb⪯ c₁✓) (✓⇒gb⪯ c₂✓)

  lcs≢[] : ∀ {c₁ c₂ : Chain} → c₁ ✓ → c₂ ✓ → lcs c₁ c₂ ≢ []
  lcs≢[] c₁✓ c₂✓ with ⪯⇔∃ .to (gb⪯lcs c₁✓ c₂✓)
  ... | (c , c++gb≡lcs) = subst (_≢ []) c++gb≡lcs (≢-sym []≢∷ʳ)

  lcs-✓ : ∀ {c₁ c₂ : Chain} → c₁ ✓ → c₂ ✓ → lcs c₁ c₂ ✓
  lcs-✓ {c₁} {c₂} c₁✓ c₂✓ with ≢[]⇒∷ (lcs≢[] c₁✓ c₂✓) | ⪯⇔∃ .to (lcs-⪯ˡ c₁ c₂)
  ... | (b , c′ , lcs≡b∷c′) | (c , c++lcs≡c₁) = subst _✓ (sym lcs≡b∷c′) b∷c′✓
    where
      c++b∷c′≡c₁ : c ++ b ∷ c′ ≡ c₁
      c++b∷c′≡c₁ rewrite lcs≡b∷c′ = c++lcs≡c₁

      c++b∷c′✓ : (c ++ b ∷ c′) ✓
      c++b∷c′✓ = subst _✓ (sym c++b∷c′≡c₁) c₁✓

      b∷c′✓ : (b ∷ c′) ✓
      b∷c′✓ = ✓-++ʳ c++b∷c′✓

adversaryHasAdvantage : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → ForgingFree N
  → CollisionFree N
  → ∀ {p : Party} {ls : LocalState}
    → Honest p
    → N .states ⁉ p ≡ just ls
    → ∀ {c : Chain} {sl : Slot} →
        let bc = bestChain (N .clock ∸ 1) (ls .tree)
            b* = tip (lcs bc c)
        in
            c ⊆ˢ filter ((_≤? N .clock ∸ 1 + sl) ∘ slot) (genesisBlock ∷ blockHistory N)
          → c ✓
          → ∣ bc ∣ ≤ ∣ c ∣
          → ∃[ sl′ ]
                sl′ ≤ b* .slot
              × length (superSlotsInRange (sl′ + 1) (N .clock ∸ 1))
                ≤
                2 * length (corruptSlotsInRange (sl′ + 1) (N .clock + sl))
adversaryHasAdvantage = {!!}

singlePartyCommonPrefix-⪯×⪰ : ∀ {N : GlobalState} {k : Slot} →
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
        → (prune k bc ⪯ c × prune k c ⪯ bc)
          ⊎
          ∃[ sl′ ]
              sl′ ≤ k
            × length (superSlotsInRange (sl′ + 1) (N .clock ∸ 1))
              ≤
              2 * length (corruptSlotsInRange (sl′ + 1) (N .clock + sl))
singlePartyCommonPrefix-⪯×⪰ {N} {k} N₀↝⋆N ffN cfN {p} {ls} hp lsp {c} {sl} c⊆fgb∷bhN c✓ ∣bc∣≤∣c∣ = goal
  where
    bc = bestChain (N .clock ∸ 1) (ls .tree)
    b* = tip (lcs bc c)

    bc✓ : bc ✓
    bc✓ = valid (ls .tree) (N .clock ∸ 1)

    goal : _
    goal with Nat.≤-total (b* .slot) k
    ... | inj₁ b*ₜ≤k = (case adversaryHasAdvantage {N} N₀↝⋆N ffN cfN {p} {ls} hp lsp {c} {sl} c⊆fgb∷bhN c✓ ∣bc∣≤∣c∣ of λ where
      (sl′ , sl′≤b*ₜ , advπ) → inj₂ (sl′ , Nat.≤-trans sl′≤b*ₜ b*ₜ≤k , advπ))
    ... | inj₂ k≤b*ₜ = inj₁ $ ⪯-trans bc⪯lcs[bc,c] lcs[bc,c]⪯c , ⪯-trans c⪯lcs[bc,c] lcs[bc,c]⪯bc
      where
        lcs[bc,c]⪯c : lcs bc c ⪯ c
        lcs[bc,c]⪯c = lcs-⪯ʳ bc c

        lcs[bc,c]⪯bc : lcs bc c ⪯ bc
        lcs[bc,c]⪯bc = lcs-⪯ˡ bc c

        lcs[bc,c]✓ : lcs bc c ✓
        lcs[bc,c]✓ = lcs-✓ bc✓ c✓

        c*⪯lcs[bc,c] : ∀ {c* : Chain} → c* ✓ → lcs bc c ⪯ c* → prune k c* ⪯ lcs bc c
        c*⪯lcs[bc,c] {c*} c*✓ lcs[bc,c]⪯c* with lcs bc c in eq
        ... | [] = contradiction eq (lcs≢[] bc✓ c✓)
        ... | b ∷ c′ with ⪯⇔∃ .to lcs[bc,c]⪯c*
        ... |   (c″ , c″++b∷c′≡c*) = pkc*⪯b∷c′
          where
            ds[c″++b∷c′] : DecreasingSlots (c″ ++ b ∷ c′)
            ds[c″++b∷c′] = ✓⇒ds $ subst _✓ (sym c″++b∷c′≡c*) c*✓

            ds[b∷c′] : DecreasingSlots (b ∷ c′)
            ds[b∷c′] = ++-DecreasingSlots ds[c″++b∷c′] .proj₂ .proj₁

            pkc″≡[] : prune k c″ ≡ []
            pkc″≡[] = pkc″≡[]′ c″ b<ˢc″
              where
                b<ˢc″ : L.All.All (_>ˢ b) c″
                b<ˢc″ = L.All.map L.All.head $ ++-DecreasingSlots {c = c″} {c′ = b ∷ c′} ds[c″++b∷c′] .proj₂ .proj₂

                pkc″≡[]′ : ∀ (c″ : Chain) → L.All.All (_>ˢ b) c″ → prune k c″ ≡ []
                pkc″≡[]′ [] _ = refl
                pkc″≡[]′ (b″ ∷ c″) b<ˢ[b″∷c″] with ih ← pkc″≡[]′ c″ (L.All.tail b<ˢ[b″∷c″]) | b″ .slot ≤? k
                ... | yes b″ₜ≤k rewrite L.filter-accept ((_≤? k) ∘ slot) {x = b″} {xs = c″} b″ₜ≤k = contradiction k<k (Nat.<-irrefl {k} refl)
                  where
                    b<ˢb″ : b″ >ˢ b
                    b<ˢb″ = L.All.head b<ˢ[b″∷c″]

                    b″ₜ≡k : b″ .slot ≡ k
                    b″ₜ≡k = Nat.≤-antisym b″ₜ≤k $ Nat.≤-trans k≤b*ₜ (Nat.<⇒≤ b<ˢb″)

                    k<k : k < k
                    k<k = Nat.≤-<-trans k≤b*ₜ $ subst (b .slot <_) b″ₜ≡k b<ˢb″
                ... | no ¬b″ₜ≤k rewrite L.filter-reject ((_≤? k) ∘ slot) {x = b″} {xs = c″} ¬b″ₜ≤k = ih

            pk[c*]≡pk[b∷c′] : prune k c* ≡ prune k (b ∷ c′)
            pk[c*]≡pk[b∷c′] = begin
              prune k c*                     ≡⟨ cong (prune k) c″++b∷c′≡c* ⟨
              prune k (c″ ++ b ∷ c′)         ≡⟨ L.filter-++ _ c″ (b ∷ c′) ⟩
              prune k c″ ++ prune k (b ∷ c′) ≡⟨ cong (_++ prune k (b ∷ c′)) pkc″≡[] ⟩
              []         ++ prune k (b ∷ c′) ≡⟨ L.++-identityˡ _ ⟩
              prune k (b ∷ c′)               ∎
              where open ≡-Reasoning

            pkc*⪯b∷c′ : prune k c* ⪯ (b ∷ c′)
            pkc*⪯b∷c′ rewrite pk[c*]≡pk[b∷c′] = prune-⪯ k ds[b∷c′]

        c⪯lcs[bc,c] : prune k c ⪯ lcs bc c
        c⪯lcs[bc,c] = c*⪯lcs[bc,c] c✓ lcs[bc,c]⪯c

        bc⪯lcs[bc,c] : prune k bc ⪯ lcs bc c
        bc⪯lcs[bc,c] = c*⪯lcs[bc,c] bc✓ lcs[bc,c]⪯bc

singlePartyCommonPrefix-⪯ : ∀ {N : GlobalState} {k : Slot} →
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
singlePartyCommonPrefix-⪯ {N} {k} N₀↝⋆N ffN cfN {p} {ls} hp lsp {c} {sl} c⊆fgb∷bhN c✓ ∣bc∣≤∣c∣ =
  case singlePartyCommonPrefix-⪯×⪰ {N} {k} N₀↝⋆N ffN cfN {p} {ls} hp lsp {c} {sl} c⊆fgb∷bhN c✓ ∣bc∣≤∣c∣ of λ where
    (inj₁ p) → inj₁ (p .proj₁)
    (inj₂ p) → inj₂ p

singlePartyCommonPrefix-⪰ : ∀ {N : GlobalState} {k : Slot} →
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
        → prune k c ⪯ bc
          ⊎
          ∃[ sl′ ]
              sl′ ≤ k
            × length (superSlotsInRange (sl′ + 1) (N .clock ∸ 1))
              ≤
              2 * length (corruptSlotsInRange (sl′ + 1) (N .clock + sl))
singlePartyCommonPrefix-⪰ {N} {k} N₀↝⋆N ffN cfN {p} {ls} hp lsp {c} {sl} c⊆fgb∷bhN c✓ ∣bc∣≤∣c∣ =
  case singlePartyCommonPrefix-⪯×⪰ {N} {k} N₀↝⋆N ffN cfN {p} {ls} hp lsp {c} {sl} c⊆fgb∷bhN c✓ ∣bc∣≤∣c∣ of λ where
    (inj₁ p) → inj₁ (p .proj₂)
    (inj₂ p) → inj₂ p

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
singleRoundCommonPrefix {N} {k} N₀↝⋆N ffN cfN {p₁} {p₂} {ls₁} {ls₂} hp₁ hp₂ lsp₁ lsp₂ = goal
  where
    bc₁ = bestChain (N .clock ∸ 1) (ls₁ .tree)
    bc₂ = bestChain (N .clock ∸ 1) (ls₂ .tree)

    bc⊆fg∷bhN : ∀ ls p hp lsp → bestChain (N .clock ∸ 1) (ls .tree) ⊆ˢ filter ((_≤? N .clock ∸ 1 + 0) ∘ slot) (genesisBlock ∷ blockHistory N)
    bc⊆fg∷bhN ls p hp lsp {b} b∈bc = L.Mem.∈-filter⁺ ((_≤? N .clock ∸ 1 + 0) ∘ slot) (π1 b∈bc) π2
      where
        π1 : bestChain (N .clock ∸ 1) (ls .tree) ⊆ˢ genesisBlock ∷ blockHistory N
        π1 = begin
          bestChain (N .clock ∸ 1) (ls .tree)
            ⊆⟨ selfContained (ls .tree) (N .clock ∸ 1) ⟩
          filter ((_≤? N .clock ∸ 1) ∘ slot) (allBlocks (ls .tree))
            ⊆⟨ L.SubS.filter-⊆ _ _ ⟩
          allBlocks (ls .tree)
            ⊆⟨ honestLocalTreeInHonestGlobalTree {p = p} N₀↝⋆N hp lsp ⟩
          allBlocks (honestTree N)
            ⊆⟨ honestGlobalTreeInBlockHistory N₀↝⋆N ⟩
          genesisBlock ∷ blockHistory N ∎
          where open L.SubS.⊆-Reasoning Block

        π2 : b .slot ≤ N .clock ∸ 1 + 0
        π2
          rewrite
            Nat.+-suc (N .clock ∸ 1) 0
          | Nat.+-identityʳ (N .clock ∸ 1)
          = L.All.lookup (bestChainSlotBounded (ls .tree) (N .clock ∸ 1)) b∈bc

    Goal-◆ = λ ◆ →
      prune k bc₁ ⪯ bc₂
      ⊎
      ∃[ sl′ ]
          sl′ ≤ k
        × length (superSlotsInRange (sl′ + 1) (N .clock ∸ 1))
          ≤
          2 * length (corruptSlotsInRange (sl′ + 1) ◆)

    goal : Goal-◆ (N .clock)
    goal with Nat.≤-total ∣ bc₁ ∣ ∣ bc₂ ∣
    ... | inj₁ ∣bc₁∣≤∣bc₂∣ = subst Goal-◆ (Nat.+-identityʳ _) $ singlePartyCommonPrefix-⪯ {k = k} N₀↝⋆N ffN cfN {p₁} {ls₁} hp₁ lsp₁ {bc₂} {0} (bc⊆fg∷bhN ls₂ p₂ hp₂ lsp₂) bc₂✓ ∣bc₁∣≤∣bc₂∣
      where
        bc₂✓ : bc₂ ✓
        bc₂✓ = valid (ls₂ .tree) (N .clock ∸ 1)

    ... | inj₂ ∣bc₂∣≤∣bc₁∣ = subst Goal-◆ (Nat.+-identityʳ _) $ singlePartyCommonPrefix-⪰ {k = k} N₀↝⋆N ffN cfN {p₂} {ls₂} hp₂ lsp₂ {bc₁} {0} (bc⊆fg∷bhN ls₁ p₁ hp₁ lsp₁) bc₁✓ ∣bc₂∣≤∣bc₁∣
      where
        bc₁✓ : bc₁ ✓
        bc₁✓ = valid (ls₁ .tree) (N .clock ∸ 1)
