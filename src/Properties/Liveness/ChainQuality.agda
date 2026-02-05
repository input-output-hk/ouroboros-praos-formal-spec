{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled

open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Liveness.ChainQuality
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot)
open import Protocol.Block ⦃ params ⦄
open import Protocol.Chain ⦃ params ⦄
open import Protocol.Tree ⦃ params ⦄
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Protocol.Chain.Properties ⦃ params ⦄
open import Protocol.Tree.Properties ⦃ params ⦄
open import Properties.Base.ForgingFree ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.CollisionFree ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.SuperBlocks ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.Time ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Liveness.ChainGrowth ⦃ params ⦄ ⦃ assumptions ⦄
open import Data.List.Membership.Propositional.Properties.Ext using (Any⇒Is-just∘find)
--open import Data.List.Membership.Propositional using (lose)
open import Data.List.Relation.Unary.All.Properties.Ext using (All-∁-filter; All-reverse⁻)
open import Data.List.Properties.Ext using (++-injective; find-∃; find-∃ʳ; find-∄; ι-++)
open import Data.List.Ext using (ι)
open import Data.Maybe.Properties.Ext using (Is-just⇒to-witness)
open import Data.Nat.Properties.Ext using (n>0⇒pred[n]<n)

pastBestChainLength : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → ForgingFree N
  → CollisionFree N
  → ∀ {p : Party} {ls : LocalState}
    → Honest p
    → N .states ⁉ p ≡ just ls
    → ∀ {b : Block} {cₕ cₜ : Chain}
      → HonestBlock b
      → cₕ ++ b ∷ cₜ ≡ bestChain (N .clock ∸ 1) (ls .tree)
      → ∃₂[ N′ , p′ ]
          N₀ ↝⋆ N′
        × N′ ↝⋆ N
        × N′ .clock ≡ suc (b .slot)
        × N′ .progress ≡ ready
        × Honest p′
        × ∃[ ls′ ]
            N′ .states ⁉ p′ ≡ just ls′
          × length (bestChain (N′ .clock ∸ 1) (ls′ .tree)) ≡ length (b ∷ cₜ)
pastBestChainLength = {!!}

pastBestChainLength′ : ∀ {N N′ : GlobalState} →
    N₀ ↝⋆ N′
  → N′ ↝⋆ N
  → ForgingFree N
  → CollisionFree N
  → N′ .progress ≡ ready
  → ∀ {p : Party} {ls : LocalState}
    → Honest p
    → N .states ⁉ p ≡ just ls
    → ∀ {b : Block} {cₕ cₜ : Chain}
      → HonestBlock b
      → N′ .clock ≤ b .slot
      → cₕ ++ b ∷ cₜ ≡ bestChain (N .clock ∸ 1) (ls .tree)
      → ∃₂[ N″ , p′ ]
          N′ ↝⋆ N″
        × N″ ↝⋆ N
        × N″ .clock ≡ suc (b .slot)
        × N″ .progress ≡ ready
        × Honest p′
        × ∃[ ls′ ]
            N″ .states ⁉ p′ ≡ just ls′
          × length (bestChain (N″ .clock ∸ 1) (ls′ .tree)) ≡ length (b ∷ cₜ)
pastBestChainLength′ = {!!}

honestBlocksLowerBound : ∀ {sl₁ sl₂ : Slot} {bs : List Block} {w : ℕ} →
    L.All.All (λ b → sl₁ ≤ b .slot × b .slot < sl₂) bs
  → CorrectBlocks bs
  → DecreasingSlots bs
  → length (corruptSlotsInRange sl₁ sl₂) + w ≤ length bs
  → w ≤ length (honestBlocks bs)
honestBlocksLowerBound = {!!}

chainQuality : ∀ {N : GlobalState} →
    N₀ ↝⋆ N
  → ForgingFree N
  → CollisionFree N
  → ∀ {p : Party} {ls : LocalState}
    → Honest p
    → N .states ⁉ p ≡ just ls
    → let bc = bestChain (N .clock ∸ 1) (ls .tree)
      in ∀ {bᵢ bⱼ : Block} {c′ : Chain} {w : ℕ}
      → let c = Chain ∋ (bⱼ ∷ c′ L.∷ʳ bᵢ)
        in ∀ {cₜ cₕ : Chain}
        → bc ≡ cₜ ++ c ++ cₕ
        → (∀ {sl₁ sl₂ : Slot} →
             bⱼ .slot ∸ suc (bᵢ .slot) ≤ sl₂ ∸ sl₁ →
               length (corruptSlotsInRange sl₁ sl₂) + w ≤ length (luckySlotsInRange sl₁ sl₂))
        → w ∸ 1 ≤ length (honestBlocks c)
chainQuality {N} N₀↝⋆N ffN cfN {p} {ls} hp lspN {bᵢ} {bⱼ} {c′} {w} {cₜ} {cₕ} bc≡cₜ+c+cₕ adv
  with w
... | Nat.zero = Nat.z≤n
... | w@(suc w′) with ✓⇒gbIsHead $ valid (ls .tree) (N .clock ∸ 1)
...   | bc′ , bc′+gb≡bc = w-1≤|hb[c]|
  where
    cᴬ = bᵢ ∷ cₕ
    cᴮ = cₜ ++ bⱼ ∷  c′
    c = Chain ∋ bⱼ ∷ c′ L.∷ʳ bᵢ
    bc = bestChain (N .clock ∸ 1) (ls .tree)

    ∃[c″]cᴬ≡c″+gb : ∃[ c″ ] cᴬ ≡ c″ ++ [ genesisBlock ]
    ∃[c″]cᴬ≡c″+gb = (case ∃[bc″]cᴮ+cᴬ≡cᴮ+bc″+gb of λ where
      (bc″ , cᴮ+cᴬ≡cᴮ+bc″+gb) → (bc″ , ++-injective {xs = cᴮ} {zs = cᴮ} refl cᴮ+cᴬ≡cᴮ+bc″+gb .proj₂))
      where
        ∃[bc″]cᴮ+cᴬ≡cᴮ+bc″+gb : ∃[ bc″ ] cᴮ ++ cᴬ ≡ cᴮ ++ (bc″ ++ [ genesisBlock ])
        ∃[bc″]cᴮ+cᴬ≡cᴮ+bc″+gb = (case ∃[bc″]bc′≡cᴮ+bc″ of λ where
          (bc″ , bc′≡cᴮ+bc″) →
            (bc″ , (subst (cᴮ ++ cᴬ ≡_) (L.++-assoc cᴮ _ _)
                  $ subst (λ ◆ → cᴮ ++ cᴬ ≡ ◆ ++ [ genesisBlock ]) bc′≡cᴮ+bc″ cᴮ+cᴬ≡bc′+gb)))
          where
            cᴮ+cᴬ≡bc′+gb : cᴮ ++ cᴬ ≡ bc′ ++ [ genesisBlock ]
            cᴮ+cᴬ≡bc′+gb = let open ≡-Reasoning in begin
              (cₜ ++ (bⱼ ∷ c′)) ++ cᴬ             ≡⟨ L.++-assoc cₜ _ _ ⟩
              cₜ ++ ((bⱼ ∷ c′) ++ cᴬ)             ≡⟨ cong (cₜ ++_) $ L.++-assoc [ bⱼ ] c′ _ ⟩
              cₜ ++ (bⱼ ∷ (c′ ++ cᴬ))             ≡⟨ cong (λ ◆ → cₜ ++ ([ bⱼ ] ++ ◆)) (sym $ L.++-assoc c′ _ _) ⟩          
              cₜ ++ (bⱼ ∷ ((c′ ++ [ bᵢ ]) ++ cₕ)) ≡⟨ sym $ trans bc′+gb≡bc bc≡cₜ+c+cₕ ⟩
              bc′ ++ [ genesisBlock ]             ∎

            ∃[bc″]bc′≡cᴮ+bc″ : ∃[ bc″ ] bc′ ≡ cᴮ ++ bc″
            ∃[bc″]bc′≡cᴮ+bc″ = goal* cᴮ+cᴬ≡bc′+gb
              where
                goal* : ∀ {bᵢ* cᴮ* bc′* cₕ} → cᴮ* ++ [ bᵢ* ] ++ cₕ ≡ bc′* ++ [ genesisBlock ] → ∃[ bc″ ] bc′* ≡ cᴮ* ++ bc″
                goal* {_}   {cᴮ*} {bc′*} {[]}     eq
                  rewrite sym $ L.∷ʳ-injectiveˡ cᴮ* bc′* eq = [] , (sym $ L.++-identityʳ cᴮ* )
                goal* {bᵢ*} {cᴮ*} {bc′*} {b ∷ cₕ} eq
                  with goal* {b} {cᴮ* ++ [ bᵢ* ]} {bc′*} {cₕ}
                         (subst (_≡ bc′* ++ [ genesisBlock ]) (sym $ L.++-assoc cᴮ* _ _) eq)
                ... | bc″ , eq′
                  rewrite L.++-assoc cᴮ* [ bᵢ* ] bc″ = bᵢ* ∷ bc″ , eq′

    -- The last honest block in cᴬ exists...
    lastHonestBlockIncᴬIsJust : M.Is-just $ L.find ¿ HonestBlock ¿¹ cᴬ
    lastHonestBlockIncᴬIsJust with ∃[c″]cᴬ≡c″+gb
    ... | c″ , cᴬ≡c″+gb = subst (M.Is-just ∘ L.find ¿ HonestBlock ¿¹) (sym cᴬ≡c″+gb) lastHonestBlockIncᴬIsJust′
      where
        lastHonestBlockIncᴬIsJust′ : M.Is-just $ L.find ¿ HonestBlock ¿¹ (c″ ++ [ genesisBlock ])
        lastHonestBlockIncᴬIsJust′ = Any⇒Is-just∘find ¿ HonestBlock ¿¹ {xs = c″ ++ [ genesisBlock ]}
                                       $ L.Mem.lose (L.Mem.∈-++⁺ʳ c″ (here refl)) genesisHonesty

    -- ... and we call it bᵢ′.
    bᵢ′ = Block ∋ M.to-witness lastHonestBlockIncᴬIsJust

    w-1≤|hb[c]| : w ∸ 1 ≤ length (honestBlocks c)
    w-1≤|hb[c]| with find-∃ ¿ HonestBlock ¿¹ {xs = bᵢ ∷ cₕ} (Is-just⇒to-witness lastHonestBlockIncᴬIsJust)
    ... | cᴬ₁ , cᴬ₂ , cᴬ₁+bᵢ′+cᴬ₂≡cᴬ , hbᵢ′ , ¬hb[cᴬ₁] = Nat.≤-trans w-1≤|hb[bⱼ+c′+cᴬ₁]| |hb[bⱼ+c′+cᴬ₁]|≤|hb[c]|
      where
        open import Function.Reasoning

        cᴬ✓ : cᴬ ✓
        cᴬ✓ =
            valid (ls .tree) (N .clock ∸ 1) ∶
          bc ✓
            |> subst _✓ bc≡cₜ+c+cₕ ∶
          (cₜ ++ bⱼ ∷ c′ L.∷ʳ bᵢ ++ cₕ) ✓
            |> subst (λ ◆ → (cₜ ++ ◆ ++ cₕ) ✓) (L.++-assoc [ bⱼ ] c′ [ bᵢ ]) ∶
          (cₜ ++ (bⱼ ∷ c′ L.∷ʳ bᵢ) ++ cₕ) ✓
            |> subst _✓ (sym $ L.++-assoc cₜ _ _) ∶
          ((cₜ ++ (bⱼ ∷ c′ L.∷ʳ bᵢ)) ++ cₕ) ✓
            |> subst (λ ◆ → (◆ ++ cₕ) ✓) (sym $ L.++-assoc cₜ _ _) ∶
          (((cₜ ++ bⱼ ∷ c′) L.∷ʳ bᵢ) ++ cₕ) ✓
            |> (subst _✓ $ L.++-assoc (cₜ ++ bⱼ ∷ c′) _ _) ∶
          ((cₜ ++ bⱼ ∷ c′) ++ cᴬ) ✓
            |> ✓-++ʳ ∶
          cᴬ ✓

        bᵢ′ₜ≤bᵢₜ : bᵢ′ .slot ≤ bᵢ .slot
        bᵢ′ₜ≤bᵢₜ = bᵢ′ₜ≤bᵢₜ* cᴬ₁+bᵢ′+cᴬ₂≡cᴬ cᴬ✓
          where
            bᵢ′ₜ≤bᵢₜ* : ∀ {cᴬ₁*} → cᴬ₁* ++ bᵢ′ ∷ cᴬ₂ ≡ cᴬ → cᴬ ✓ → bᵢ′ .slot ≤ bᵢ .slot
            bᵢ′ₜ≤bᵢₜ* {[]}        eq _ rewrite L.∷-injectiveˡ eq = Nat.≤-refl
            bᵢ′ₜ≤bᵢₜ* {b* ∷ cᴬ₁*} eq cᴬ✓ =
              subst (λ ◆ → bᵢ′ .slot ≤ ◆ .slot) (L.∷-injectiveˡ eq) (Nat.<⇒≤ $ L.All.head $ L.All.++⁻ʳ cᴬ₁* b*>ˢcᴬ₁*+bᵢ′+cᴬ₂)
              where
                b*>ˢcᴬ₁*+bᵢ′+cᴬ₂ : L.All.All (b* >ˢ_) (cᴬ₁* ++ bᵢ′ ∷ cᴬ₂)
                b*>ˢcᴬ₁*+bᵢ′+cᴬ₂ = ∷-DecreasingSlots (✓⇒ds (subst _✓ (sym eq) cᴬ✓)) .proj₂

        |hb[bⱼ+c′+cᴬ₁]|≤|hb[c]| : length (honestBlocks (bⱼ ∷ c′ ++ cᴬ₁)) ≤ length (honestBlocks c)
        |hb[bⱼ+c′+cᴬ₁]|≤|hb[c]| = let open Nat.≤-Reasoning in begin
          length (honestBlocks (bⱼ ∷ c′ ++ cᴬ₁))
            ≡⟨ cong length $ L.filter-++ ¿ HonestBlock ¿¹ (bⱼ ∷ c′) _ ⟩
          length (honestBlocks (bⱼ ∷ c′) ++ honestBlocks cᴬ₁)
            ≡⟨ L.length-++ (honestBlocks (bⱼ ∷ c′)) ⟩
          length (honestBlocks (bⱼ ∷ c′)) + length (honestBlocks cᴬ₁)
            ≤⟨ Nat.+-monoʳ-≤ _ |hb[cᴬ₁]|≤|hb[bᵢ]| ⟩
          length (honestBlocks (bⱼ ∷ c′)) + length (honestBlocks [ bᵢ ])
            ≡⟨ L.length-++ (honestBlocks (bⱼ ∷ c′)) ⟨
          length (honestBlocks (bⱼ ∷ c′) ++ honestBlocks [ bᵢ ])
            ≡⟨ cong length $ L.filter-++ ¿ HonestBlock ¿¹ (bⱼ ∷ c′) _ ⟨
          length (honestBlocks c) ∎
            where
              |hb[cᴬ₁]|≡0 : length (honestBlocks cᴬ₁) ≡ 0
              |hb[cᴬ₁]|≡0 rewrite All-∁-filter {P? = ¿ HonestBlock ¿¹} ¬hb[cᴬ₁] = refl

              |hb[cᴬ₁]|≤|hb[bᵢ]| : length (honestBlocks cᴬ₁) ≤ length (honestBlocks [ bᵢ ])
              |hb[cᴬ₁]|≤|hb[bᵢ]| = Nat.≤-trans {j = 0} (subst (_≤ 0) (sym |hb[cᴬ₁]|≡0) Nat.z≤n) Nat.z≤n

        suf+bᵢ′+cᴬ₂≡bc : (cₜ ++ bⱼ ∷ c′ ++ cᴬ₁) ++ (bᵢ′ ∷ cᴬ₂) ≡ bc
        suf+bᵢ′+cᴬ₂≡bc = let open ≡-Reasoning in begin
          (cₜ ++ bⱼ ∷ c′ ++ cᴬ₁) ++ bᵢ′ ∷ cᴬ₂        ≡⟨ cong (_++ bᵢ′ ∷ cᴬ₂) (sym $ L.++-assoc cₜ _ _) ⟩
          ((cₜ ++ bⱼ ∷ c′) ++ cᴬ₁) ++ bᵢ′ ∷ cᴬ₂      ≡⟨ L.++-assoc (cₜ ++ bⱼ ∷ c′) _ _ ⟩
          (cₜ ++ bⱼ ∷ c′) ++ (cᴬ₁ ++ bᵢ′ ∷ cᴬ₂)      ≡⟨ sym $ cong ((cₜ ++ bⱼ ∷ c′) ++_) (sym cᴬ₁+bᵢ′+cᴬ₂≡cᴬ) ⟩
          (cₜ ++ bⱼ ∷ c′) ++ bᵢ ∷ cₕ                 ≡⟨ L.++-assoc cₜ _ _ ⟩
          cₜ ++ bⱼ ∷ c′ ++ bᵢ ∷ cₕ                   ≡⟨ cong (cₜ ++_) $ L.++-assoc (bⱼ ∷ c′) _ _ ⟨
          cₜ ++ bⱼ ∷ c′ L.∷ʳ bᵢ ++ cₕ                ≡⟨ bc≡cₜ+c+cₕ ⟨
          bc                                         ∎

        bᵢ′ₜ<bⱼₜ : bᵢ′ .slot < bⱼ .slot
        bᵢ′ₜ<bⱼₜ = L.All.head $ L.All.++⁻ʳ cᴬ₁ $ L.All.++⁻ʳ c′ bⱼ>ˢc′+cᴬ₁+bᵢ′+cᴬ₂
          where
            [bⱼ+c′+cᴬ₁+bᵢ′+cᴬ₂]✓ : (bⱼ ∷ c′ ++ cᴬ₁ ++ bᵢ′ ∷ cᴬ₂) ✓
            [bⱼ+c′+cᴬ₁+bᵢ′+cᴬ₂]✓ =
                                                          valid (ls .tree) (N .clock ∸ 1) ∶
              bc ✓                                     |> subst _✓ (sym suf+bᵢ′+cᴬ₂≡bc) ∶
              ((cₜ ++ bⱼ ∷ c′ ++ cᴬ₁) ++ bᵢ′ ∷ cᴬ₂) ✓  |> subst _✓ (L.++-assoc cₜ _ _) ∶
              (cₜ ++ (bⱼ ∷ c′ ++ cᴬ₁) ++ bᵢ′ ∷ cᴬ₂) ✓  |> ✓-++ʳ ∶
              ((bⱼ ∷ c′ ++ cᴬ₁) ++ bᵢ′ ∷ cᴬ₂) ✓        |> subst _✓ (L.++-assoc (bⱼ ∷ c′) _ _) ∶
              (bⱼ ∷ c′ ++ cᴬ₁ ++ bᵢ′ ∷ cᴬ₂) ✓

            bⱼ>ˢc′+cᴬ₁+bᵢ′+cᴬ₂ : L.All.All (bⱼ >ˢ_) (c′ ++ cᴬ₁ ++ bᵢ′ ∷ cᴬ₂)
            bⱼ>ˢc′+cᴬ₁+bᵢ′+cᴬ₂ = ∷-DecreasingSlots (✓⇒ds [bⱼ+c′+cᴬ₁+bᵢ′+cᴬ₂]✓) .proj₂

        w-1≤|hb[bⱼ+c′+cᴬ₁]| : w ∸ 1 ≤ length (honestBlocks (bⱼ ∷ c′ ++ cᴬ₁))
        w-1≤|hb[bⱼ+c′+cᴬ₁]| with pastBestChainLength N₀↝⋆N ffN cfN {p} {ls} hp lspN hbᵢ′ suf+bᵢ′+cᴬ₂≡bc
        ... | Nᵢ′ , pᵢ′ , N₀↝⋆Nᵢ′ , Nᵢ′↝⋆N , Nᵢ′ₜ≡bᵢ′ₜ+1 , Nᵢ′Ready , hpᵢ′ , π with π
        ...   | lsᵢ′ , lspᵢ′Nᵢ′ , |bcᵢ′|≡|bᵢ′+cᴬ₂| with L.find ¿ HonestBlock ¿¹ $ L.reverse (cₜ L.∷ʳ bⱼ) in eqf
        --      Case (a): There is no honest block in the front of the chain.
        ...     | nothing = subst ((w ∸ 1 ≤_) ∘ length) (sym hb[bⱼ+c′+cᴬ₁]≡hb[suf]) w-1≤|hb[suf]|
          where
            bcᵢ′ = bestChain (Nᵢ′ .clock ∸ 1) (lsᵢ′ .tree)

            ¬hb[cₜ+bⱼ] : L.All.All (¬_ ∘ HonestBlock) (L.reverse (cₜ L.∷ʳ bⱼ))
            ¬hb[cₜ+bⱼ] = L.All.¬Any⇒All¬ _ $ find-∄ ¿ HonestBlock ¿¹ eqf

            hb[bⱼ+c′+cᴬ₁]≡hb[suf] : honestBlocks (bⱼ ∷ c′ ++ cᴬ₁) ≡ honestBlocks (cₜ ++ bⱼ ∷ c′ ++ cᴬ₁)
            hb[bⱼ+c′+cᴬ₁]≡hb[suf] = let open ≡-Reasoning in begin
              honestBlocks (bⱼ ∷ c′ ++ cᴬ₁)
                ≡⟨ cong (_++ honestBlocks (bⱼ ∷ c′ ++ cᴬ₁)) (sym hb[cₜ]≡[]) ⟩
              honestBlocks cₜ ++ honestBlocks (bⱼ ∷ c′ ++ cᴬ₁)
                ≡⟨ L.filter-++ _ cₜ _ ⟨
              honestBlocks (cₜ ++ bⱼ ∷ c′ ++ cᴬ₁) ∎
                where
                  hb[cₜ]≡[] : honestBlocks cₜ ≡ []
                  hb[cₜ]≡[] = All-∁-filter $ L.All.++⁻ˡ cₜ $ All-reverse⁻ ¬hb[cₜ+bⱼ]

            bⱼ∈bc : bⱼ ∈ bc
            bⱼ∈bc = subst (bⱼ ∈_) (sym bc≡cₜ+c+cₕ) $ L.Mem.∈-++⁺ʳ cₜ (here refl)

            Nᵢ′↝⁺N : Nᵢ′ ↝⁺ N
            Nᵢ′↝⁺N = Nᵢ′↝⋆N , Nᵢ′<ˢN
              where
                Nᵢ′<ˢN : Nᵢ′ .clock < N .clock
                Nᵢ′<ˢN rewrite Nᵢ′ₜ≡bᵢ′ₜ+1 = Nat.≤-<-trans bᵢ′ₜ<Nₜ-1 (n>0⇒pred[n]<n (positiveClock N₀↝⋆N))
                  where
                    bᵢ′ₜ<Nₜ-1 : bᵢ′ .slot < N .clock ∸ 1
                    bᵢ′ₜ<Nₜ-1 = Nat.<-≤-trans bᵢ′ₜ<bⱼₜ bⱼₜ≤Nₜ-1
                      where
                        bⱼₜ≤Nₜ-1 : bⱼ .slot ≤ N .clock ∸ 1
                        bⱼₜ≤Nₜ-1 = L.Mem.∈-filter⁻
                                     _
                                     {xs = allBlocks (ls .tree)}
                                     (selfContained (ls .tree) (N .clock ∸ 1) bⱼ∈bc)
                                     .proj₂

            [bⱼ:bᵢ]InAdvRange : bⱼ .slot ∸ suc (bᵢ .slot) ≤ (N .clock ∸ 1) ∸ suc (bᵢ′ .slot)
            [bⱼ:bᵢ]InAdvRange =
              Nat.∸-mono
                (bⱼ  .slot ≤ N .clock ∸ 1   ∋ L.All.lookup (bestChainSlotBounded (ls .tree) (N .clock ∸ 1)) bⱼ∈bc)
                (bᵢ′ .slot < suc (bᵢ .slot) ∋ Nat.≤-<-trans bᵢ′ₜ≤bᵢₜ (Nat.n<1+n _))

            cs[Nᵢ′:N⦈ = corruptSlotsInRange (Nᵢ′ .clock) (N .clock ∸ 1)
            cs[Nᵢ′:N] = corruptSlotsInRange (Nᵢ′ .clock) (N .clock)
            ls[Nᵢ′:N⦈ = luckySlotsInRange   (Nᵢ′ .clock) (N .clock ∸ 1)

            [Nᵢ′:N]Adv : length cs[Nᵢ′:N⦈ + w ≤ length ls[Nᵢ′:N⦈
            [Nᵢ′:N]Adv rewrite Nᵢ′ₜ≡bᵢ′ₜ+1 = adv {suc (bᵢ′ .slot)} {N .clock ∸ 1} [bⱼ:bᵢ]InAdvRange

            w-1≤|hb[suf]| : w ∸ 1 ≤ length (honestBlocks (cₜ ++ bⱼ ∷ c′ ++ cᴬ₁))
            w-1≤|hb[suf]| = honestBlocksLowerBound
                              {Nᵢ′ .clock}
                              {N .clock}
                              {cₜ ++ bⱼ ∷ c′ ++ cᴬ₁}
                              {w ∸ 1}
                              sufIn[Nᵢ′ₜ:Nₜ]
                              cb[suf]
                              ds[suf]
                              |cs[Nᵢ′:N]|+w-1≤|suf|
              where
                |cs[Nᵢ′:N⦈|+w≤|suf| : length cs[Nᵢ′:N⦈ + w ≤ length (cₜ ++ bⱼ ∷ c′ ++ cᴬ₁)
                |cs[Nᵢ′:N⦈|+w≤|suf| =
                    chainGrowth
                      N₀↝⋆Nᵢ′
                      Nᵢ′↝⁺N
                      Nᵢ′Ready
                      hpᵢ′
                      lspᵢ′Nᵢ′
                      hp
                      lspN
                      {w = length cs[Nᵢ′:N⦈ + w}
                      [Nᵢ′:N]Adv ∶
                  length bcᵢ′ + (length cs[Nᵢ′:N⦈ + w) ≤ length bc
                    |> subst ((_≤ length bc) ∘ (_+ (length cs[Nᵢ′:N⦈ + w))) |bcᵢ′|≡|bᵢ′+cᴬ₂| ∶
                  length (bᵢ′ ∷ cᴬ₂) + (length cs[Nᵢ′:N⦈ + w) ≤ length bc
                    |> (subst ((length (bᵢ′ ∷ cᴬ₂) + (length cs[Nᵢ′:N⦈ + w) ≤_) ∘ length) $ sym suf+bᵢ′+cᴬ₂≡bc) ∶
                  length (bᵢ′ ∷ cᴬ₂) + (length cs[Nᵢ′:N⦈ + w) ≤ length ((cₜ ++ bⱼ ∷ c′ ++ cᴬ₁) ++ (bᵢ′ ∷ cᴬ₂))
                    |> subst (length (bᵢ′ ∷ cᴬ₂) + (length cs[Nᵢ′:N⦈ + w) ≤_) (L.length-++ (cₜ ++ bⱼ ∷ c′ ++ cᴬ₁)) ∶
                  length (bᵢ′ ∷ cᴬ₂) + (length cs[Nᵢ′:N⦈ + w) ≤ length (cₜ ++ bⱼ ∷ c′ ++ cᴬ₁) + length (bᵢ′ ∷ cᴬ₂)
                    |> subst (length (bᵢ′ ∷ cᴬ₂) + (length cs[Nᵢ′:N⦈ + w) ≤_) (Nat.+-comm _ (length (bᵢ′ ∷ cᴬ₂))) ∶
                  length (bᵢ′ ∷ cᴬ₂) + (length cs[Nᵢ′:N⦈ + w) ≤ length (bᵢ′ ∷ cᴬ₂) + length (cₜ ++ bⱼ ∷ c′ ++ cᴬ₁)
                    |> Nat.+-cancelˡ-≤ _ _ _ ∶
                  length cs[Nᵢ′:N⦈ + w ≤ length (cₜ ++ bⱼ ∷ c′ ++ cᴬ₁)

                [suf+bᵢ′+cᴬ₂]✓ : ((cₜ ++ bⱼ ∷ c′ ++ cᴬ₁) ++ (bᵢ′ ∷ cᴬ₂)) ✓
                [suf+bᵢ′+cᴬ₂]✓ = subst _✓ (sym suf+bᵢ′+cᴬ₂≡bc) $ valid (ls .tree) (N .clock ∸ 1)

                |cs[Nᵢ′:N]|+w-1≤|suf| : length cs[Nᵢ′:N] + (w ∸ 1) ≤ length (cₜ ++ bⱼ ∷ c′ ++ cᴬ₁)
                |cs[Nᵢ′:N]|+w-1≤|suf| = Nat.≤-trans π₂ |cs[Nᵢ′:N⦈|+w≤|suf|
                  where
                    π₀ : N .clock ∸ Nᵢ′ .clock ≡ N .clock ∸ 1 ∸ Nᵢ′ .clock + 1
                    π₀ = let open ≡-Reasoning in sym $ begin
                      N .clock ∸ 1 ∸ Nᵢ′ .clock + 1       ≡⟨ cong (_+ 1) $ Nat.∸-+-assoc (N .clock) 1 (Nᵢ′ .clock) ⟩
                      N .clock ∸ (1 + Nᵢ′ .clock) + 1     ≡⟨ cong (λ ◆ → N .clock ∸ ◆ + 1) $ Nat.+-comm 1 _ ⟩
                      N .clock ∸ (Nᵢ′ .clock + 1) + 1     ≡⟨ cong (_+ 1) $ sym $ Nat.∸-+-assoc (N .clock) (Nᵢ′ .clock) 1 ⟩
                      (N .clock ∸ Nᵢ′ .clock) ∸ 1 + 1     ≡⟨ Nat.+-suc (N .clock ∸ Nᵢ′ .clock ∸ 1) 0 ⟩
                      suc (N .clock ∸ Nᵢ′ .clock ∸ 1 + 0) ≡⟨ cong suc $ Nat.+-identityʳ (N .clock ∸ Nᵢ′ .clock ∸ 1) ⟩
                      suc (N .clock ∸ Nᵢ′ .clock ∸ 1)     ≡⟨ Nat.suc-pred (N .clock ∸ Nᵢ′ .clock) ⦃ Nat.>-nonZero Nₜ-Nᵢ′ₜ>0 ⦄ ⟩
                      N .clock ∸ Nᵢ′ .clock               ∎
                        where
                          Nᵢ′<ˢNₜ : Nᵢ′ .clock < N .clock
                          Nᵢ′<ˢNₜ rewrite Nᵢ′ₜ≡bᵢ′ₜ+1 = Nat.≤-<-trans bᵢ′<ˢNₜ-1 (n>0⇒pred[n]<n (positiveClock N₀↝⋆N))
                            where
                              bᵢ′<ˢNₜ-1 : bᵢ′ .slot < N .clock ∸ 1
                              bᵢ′<ˢNₜ-1 = Nat.<-≤-trans bᵢ′ₜ<bⱼₜ bⱼₜ≤Nₜ-1
                                where
                                  bⱼₜ≤Nₜ-1 : bⱼ .slot ≤ N .clock ∸ 1
                                  bⱼₜ≤Nₜ-1 = L.All.lookup (bestChainSlotBounded (ls .tree) (N .clock ∸ 1)) bⱼ∈bc

                          Nₜ-Nᵢ′ₜ>0 : N .clock ∸ Nᵢ′ .clock > 0
                          Nₜ-Nᵢ′ₜ>0 = Nat.m<n⇒0<n∸m Nᵢ′<ˢNₜ

                    π₁ : length cs[Nᵢ′:N] + (w ∸ 1)
                         ≡
                         length cs[Nᵢ′:N⦈ + length (filter ¿ CorruptSlot ¿¹ [ Nᵢ′ .clock + (N .clock ∸ 1 ∸ Nᵢ′ .clock) ])
                           + (w ∸ 1)
                    π₁ rewrite
                         π₀
                       | ι-++ (Nᵢ′ .clock) (N .clock ∸ 1 ∸ Nᵢ′ .clock) 1
                       = let open ≡-Reasoning in begin
                      length (
                        filter ¿ CorruptSlot ¿¹
                        (
                          ι (Nᵢ′ .clock) (N .clock ∸ 1 ∸ Nᵢ′ .clock)
                          ++
                          [ Nᵢ′ .clock + (N .clock ∸ 1 ∸ Nᵢ′ .clock) ]
                        )
                      ) + (w ∸ 1)
                        ≡⟨ cong ((_+ (w ∸ 1)) ∘ length) $ L.filter-++ _ (ι (Nᵢ′ .clock) (N .clock ∸ 1 ∸ Nᵢ′ .clock)) _ ⟩
                      length (
                        cs[Nᵢ′:N⦈
                        ++
                        filter ¿ CorruptSlot ¿¹ [ Nᵢ′ .clock + (N .clock ∸ 1 ∸ Nᵢ′ .clock) ]
                      )
                      + (w ∸ 1)
                        ≡⟨ cong (_+ (w ∸ 1)) $ L.length-++ cs[Nᵢ′:N⦈ ⟩
                      length cs[Nᵢ′:N⦈
                      +
                      length (filter ¿ CorruptSlot ¿¹ [ Nᵢ′ .clock + (N .clock ∸ 1 ∸ Nᵢ′ .clock) ])
                      + (w ∸ 1)
                        ∎

                    π₂ : length cs[Nᵢ′:N] + (w ∸ 1) ≤ length cs[Nᵢ′:N⦈ + w
                    π₂ rewrite
                         π₁
                       | Nat.+-assoc
                           (length cs[Nᵢ′:N⦈)
                           (length (filter ¿ CorruptSlot ¿¹ [ clock Nᵢ′ + (clock N ∸ 1 ∸ clock Nᵢ′) ]))
                           w′
                        = Nat.+-monoʳ-≤ (length cs[Nᵢ′:N⦈) goal
                      where
                        goal : length (filter ¿ CorruptSlot ¿¹ [ Nᵢ′ .clock + (N .clock ∸ 1 ∸ Nᵢ′ .clock) ]) + (w ∸ 1) ≤ w
                        goal with ¿ CorruptSlot ¿¹ (Nᵢ′ .clock + (N .clock ∸ 1 ∸ Nᵢ′ .clock))
                        ... | no _  = Nat.<⇒≤ $ Nat.n<1+n _
                        ... | yes _ = Nat.≤-refl

                sufIn[Nᵢ′ₜ:Nₜ] : L.All.All (λ b → Nᵢ′ .clock ≤ b .slot × b .slot < N .clock) (cₜ ++ bⱼ ∷ c′ ++ cᴬ₁)
                sufIn[Nᵢ′ₜ:Nₜ] = L.All.tabulate ϕ
                  where
                    ϕ : ∀ {b} → b ∈ cₜ ++ bⱼ ∷ c′ ++ cᴬ₁ → Nᵢ′ .clock ≤ b .slot × b .slot < N .clock
                    ϕ {b} b∈[cₜ+bⱼ+c′+cᴬ₁] =  Nᵢ′≤ˢb , b<ˢN
                      where
                        Nᵢ′≤ˢb : Nᵢ′ .clock ≤ b .slot
                        Nᵢ′≤ˢb rewrite Nᵢ′ₜ≡bᵢ′ₜ+1 = bᵢ′<ˢb b∈[cₜ+bⱼ+c′+cᴬ₁] (✓⇒ds [suf+bᵢ′+cᴬ₂]✓)
                          where
                            bᵢ′<ˢb : ∀ {c*} → b ∈ c* → DecreasingSlots (c* ++ bᵢ′ ∷ cᴬ₂) → bᵢ′ .slot < b .slot
                            bᵢ′<ˢb {[]}      ()          _
                            bᵢ′<ˢb {b* ∷ c*} (here b≡b*) q rewrite b≡b* =
                              L.All.lookup (∷-DecreasingSlots q .proj₂) bᵢ′∈c*+bᵢ′+cᴬ₂
                              where
                                bᵢ′∈c*+bᵢ′+cᴬ₂ : bᵢ′ ∈ c* ++ bᵢ′ ∷ cᴬ₂
                                bᵢ′∈c*+bᵢ′+cᴬ₂ = L.Mem.∈-++⁺ʳ _ $ L.Mem.∈-++⁺ˡ {xs = [ bᵢ′ ]} {ys = cᴬ₂} (here refl)
                            bᵢ′<ˢb {b* ∷ c*} (there b∈c*) q = bᵢ′<ˢb {c*} b∈c* (∷-DecreasingSlots q .proj₁)

                        b<ˢN : b .slot < N .clock
                        b<ˢN = Nat.≤-<-trans
                                 (L.All.lookup (bestChainSlotBounded (ls .tree) (N .clock ∸ 1)) b∈bc)
                                 (n>0⇒pred[n]<n (positiveClock N₀↝⋆N))
                          where
                            b∈bc : b ∈ bc
                            b∈bc = subst (b ∈_) suf+bᵢ′+cᴬ₂≡bc $ L.Mem.∈-++⁺ˡ {ys = bᵢ′ ∷ cᴬ₂} b∈[cₜ+bⱼ+c′+cᴬ₁]

                cb[suf] : CorrectBlocks (cₜ ++ bⱼ ∷ c′ ++ cᴬ₁)
                cb[suf] = L.All.++⁻ˡ _ $ ✓⇒cb [suf+bᵢ′+cᴬ₂]✓

                ds[suf] : DecreasingSlots (cₜ ++ bⱼ ∷ c′ ++ cᴬ₁)
                ds[suf] = ++-DecreasingSlots (✓⇒ds [suf+bᵢ′+cᴬ₂]✓) .proj₁

        --      Case (b): There is an honest, first block bⱼ′ in the front of the chain.
        ...     | just bⱼ′ = case find-∃ʳ ¿ HonestBlock ¿¹ {xs = cₜ L.∷ʳ bⱼ} eqf of goal
          where
            goal : ∃[ cᴮ′₁ ] ∃[ cᴮ′₂ ]
                       cᴮ′₁ ++ bⱼ′ ∷ cᴮ′₂ ≡ cₜ L.∷ʳ bⱼ
                     × HonestBlock bⱼ′
                     × L.All.All (¬_ ∘ HonestBlock) cᴮ′₂
                     → w ∸ 1 ≤ length (honestBlocks (bⱼ ∷ c′ ++ cᴬ₁))
            goal (cᴮ′₁ , cᴮ′₂ , cᴮ′₁+bⱼ′+cᴮ′₂≡cₜ+bⱼ , hbⱼ′ , ¬hb[cᴮ′₂]) =
              Nat.≤-trans
                w-1≤|hb[cᴮ′₂+c′+cᴬ₁]|
                |hb[cᴮ′₂+c′+cᴬ₁]|≤|hb[bⱼ+c′+cᴬ₁]|
              where
                |hb[cᴮ′₂+c′+cᴬ₁]|≤|hb[bⱼ+c′+cᴬ₁]| :
                  length (honestBlocks (cᴮ′₂ ++ c′ ++ cᴬ₁)) ≤ length (honestBlocks (bⱼ ∷ c′ ++ cᴬ₁))
                |hb[cᴮ′₂+c′+cᴬ₁]|≤|hb[bⱼ+c′+cᴬ₁]| = let open Nat.≤-Reasoning in begin
                  length (honestBlocks (cᴮ′₂ ++ c′ ++ cᴬ₁))
                    ≡⟨ cong length $ L.filter-++ ¿ HonestBlock ¿¹ cᴮ′₂ _ ⟩
                  length (honestBlocks cᴮ′₂ ++ honestBlocks (c′ ++ cᴬ₁))
                    ≡⟨ L.length-++ $ honestBlocks cᴮ′₂ ⟩
                  length (honestBlocks cᴮ′₂) + length (honestBlocks (c′ ++ cᴬ₁))
                    ≡⟨ cong (_+ length (honestBlocks (c′ ++ cᴬ₁))) |hb[cᴮ′₂]|≡0 ⟩
                  length (honestBlocks (c′ ++ cᴬ₁))
                    ≤⟨ |hb[c′+cᴬ₁]|≤|hb[bⱼ+c′+cᴬ₁]| ⟩
                  length (honestBlocks (bⱼ ∷ c′ ++ cᴬ₁))
                  ∎
                    where
                      |hb[cᴮ′₂]|≡0 : length (honestBlocks cᴮ′₂) ≡ 0
                      |hb[cᴮ′₂]|≡0 rewrite All-∁-filter {P? = ¿ HonestBlock ¿¹} ¬hb[cᴮ′₂] = refl                      

                      |hb[c′+cᴬ₁]|≤|hb[bⱼ+c′+cᴬ₁]| : length (honestBlocks (c′ ++ cᴬ₁)) ≤ length (honestBlocks (bⱼ ∷ c′ ++ cᴬ₁))
                      |hb[c′+cᴬ₁]|≤|hb[bⱼ+c′+cᴬ₁]| with ¿ HonestBlock bⱼ ¿
                      ... | no  _ = Nat.≤-refl
                      ... | yes _ = Nat.n≤1+n _

                suf′+bᵢ′+cᴬ₂≡bc : cᴮ′₁ ++ bⱼ′ ∷ (cᴮ′₂ ++ c′ ++ cᴬ₁ ++ bᵢ′ ∷ cᴬ₂) ≡ bc
                suf′+bᵢ′+cᴬ₂≡bc = let open ≡-Reasoning in sym $ begin
                  bc
                    ≡⟨ suf+bᵢ′+cᴬ₂≡bc ⟨
                   (cₜ ++   bⱼ ∷            c′ ++ cᴬ₁) ++ bᵢ′ ∷ cᴬ₂
                    ≡⟨ cong (_++ (bᵢ′ ∷ cᴬ₂)) $ sym $ L.++-assoc cₜ _ _ ⟩
                  ((cₜ L.∷ʳ bⱼ) ++          c′ ++ cᴬ₁) ++ bᵢ′ ∷ cᴬ₂
                    ≡⟨ cong! (sym cᴮ′₁+bⱼ′+cᴮ′₂≡cₜ+bⱼ) ⟩
                  ((cᴮ′₁ ++ bⱼ′ ∷ cᴮ′₂) ++  c′ ++ cᴬ₁) ++ bᵢ′ ∷ cᴬ₂
                    ≡⟨ L.++-assoc (cᴮ′₁ ++ bⱼ′ ∷ cᴮ′₂) _ _ ⟩
                   (cᴮ′₁ ++ bⱼ′ ∷ cᴮ′₂) ++ (c′ ++ cᴬ₁) ++ bᵢ′ ∷ cᴬ₂
                    ≡⟨ cong ((cᴮ′₁ ++ bⱼ′ ∷ cᴮ′₂) ++_) $ L.++-assoc c′ _ _ ⟩
                   (cᴮ′₁ ++ bⱼ′ ∷ cᴮ′₂) ++  c′ ++ cᴬ₁ ++  bᵢ′ ∷ cᴬ₂
                    ≡⟨ L.++-assoc cᴮ′₁ _ _ ⟩
                    cᴮ′₁ ++ bⱼ′ ∷ cᴮ′₂  ++  c′ ++ cᴬ₁ ++  bᵢ′ ∷ cᴬ₂ ∎
                    where open import Tactic.Cong

                [suf′+bᵢ′+cᴬ₂]✓ : (cᴮ′₁ ++ bⱼ′ ∷ cᴮ′₂  ++  c′ ++ cᴬ₁ ++  bᵢ′ ∷ cᴬ₂) ✓
                [suf′+bᵢ′+cᴬ₂]✓ = subst _✓ (sym suf′+bᵢ′+cᴬ₂≡bc) $ valid (ls .tree) (N .clock ∸ 1)

                bⱼ′>ˢcᴮ′₂+c′+cᴬ₁+bᵢ′+cᴬ₂ : L.All.All (bⱼ′ >ˢ_) (cᴮ′₂ ++ c′ ++ cᴬ₁ ++ bᵢ′ ∷ cᴬ₂)
                bⱼ′>ˢcᴮ′₂+c′+cᴬ₁+bᵢ′+cᴬ₂ = ∷-DecreasingSlots (✓⇒ds $ ✓-++ʳ [suf′+bᵢ′+cᴬ₂]✓) .proj₂

                Nᵢ′ₜ≤bⱼ′ₜ : Nᵢ′ .clock ≤ bⱼ′ .slot
                Nᵢ′ₜ≤bⱼ′ₜ rewrite Nᵢ′ₜ≡bᵢ′ₜ+1 =
                  L.All.head $ L.All.++⁻ʳ cᴬ₁ $ L.All.++⁻ʳ c′ $ L.All.++⁻ʳ cᴮ′₂ bⱼ′>ˢcᴮ′₂+c′+cᴬ₁+bᵢ′+cᴬ₂

                w-1≤|hb[cᴮ′₂+c′+cᴬ₁]| : w ∸ 1 ≤ length (honestBlocks (cᴮ′₂ ++ c′ ++ cᴬ₁))
                w-1≤|hb[cᴮ′₂+c′+cᴬ₁]|
                  with
                    pastBestChainLength′
                      N₀↝⋆Nᵢ′
                      Nᵢ′↝⋆N
                      ffN
                      cfN
                      Nᵢ′Ready
                      {p}
                      {ls}
                      hp
                      lspN
                      {bⱼ′}
                      {cᴮ′₁}
                      {cᴮ′₂ ++ c′ ++ cᴬ₁ ++ bᵢ′ ∷ cᴬ₂}
                      hbⱼ′
                      Nᵢ′ₜ≤bⱼ′ₜ
                      suf′+bᵢ′+cᴬ₂≡bc
                ... | Nⱼ′ , pⱼ′ , Nᵢ′↝⋆Nⱼ′ , Nⱼ′↝⋆N , Nⱼ′ₜ≡bⱼ′ₜ+1 , Nⱼ′Ready , hpⱼ′ , π with π
                ...   | lsⱼ′ , lspⱼ′Nⱼ′ , |bcⱼ′|≡|bⱼ′+cᴮ′₂+c′+cᴬ₁+bᵢ′+cᴬ₂| =
                        honestBlocksLowerBound
                          {Nᵢ′ .clock}
                          {Nⱼ′ .clock ∸ 1}
                          {cᴮ′₂ ++ c′ ++ cᴬ₁}
                          suf′In[Nᵢ′ₜ:Nⱼ′ₜ⦈
                          cb[suf′]
                          ds[suf′]
                          |cs[Nᵢ′:Nⱼ′⦈|+w-1≤|suf′|
                  where
                    bcᵢ′ = bestChain (Nᵢ′ .clock ∸ 1) (lsᵢ′ .tree)
                    bcⱼ′ = bestChain (Nⱼ′ .clock ∸ 1) (lsⱼ′ .tree)

                    cs[Nᵢ′:Nⱼ′⦈ = corruptSlotsInRange (Nᵢ′ .clock) (Nⱼ′ .clock ∸ 1)
                    ls[Nᵢ′:Nⱼ′⦈ = luckySlotsInRange   (Nᵢ′ .clock) (Nⱼ′ .clock ∸ 1)

                    bⱼ∈bⱼ′+cᴮ′₂ : bⱼ ∈ bⱼ′ ∷ cᴮ′₂
                    bⱼ∈bⱼ′+cᴮ′₂ = bⱼ∈bⱼ′*+cᴮ′₂* cᴮ′₂ cᴮ′₁+bⱼ′+cᴮ′₂≡cₜ+bⱼ
                      where
                        bⱼ∈bⱼ′*+cᴮ′₂* : ∀ {cᴮ′₁* cₜ* bⱼ′*} cᴮ′₂* → cᴮ′₁* ++ bⱼ′* ∷ cᴮ′₂* ≡ cₜ* L.∷ʳ bⱼ → bⱼ ∈ bⱼ′* ∷ cᴮ′₂*
                        bⱼ∈bⱼ′*+cᴮ′₂* [] eq rewrite L.∷ʳ-injectiveʳ _ _ eq = here refl
                        bⱼ∈bⱼ′*+cᴮ′₂* {cᴮ′₁*} {cₜ*} {bⱼ′*} (b* ∷ cᴮ′₂*) eq =
                          L.Mem.∈-++⁺ʳ [ bⱼ′* ] (bⱼ∈bⱼ′*+cᴮ′₂* {cᴮ′₁* L.∷ʳ bⱼ′*} {cₜ*} {b*} cᴮ′₂* eq′)
                          where
                            eq′ : cᴮ′₁* L.∷ʳ bⱼ′* ++ b* ∷ cᴮ′₂* ≡ cₜ* L.∷ʳ bⱼ
                            eq′ rewrite sym $ L.++-assoc cᴮ′₁* [ bⱼ′* ] (b* ∷ cᴮ′₂*) = eq

                    bⱼ≤ˢbⱼ′ : bⱼ .slot ≤ bⱼ′ .slot
                    bⱼ≤ˢbⱼ′ with bⱼ∈bⱼ′+cᴮ′₂
                    ... | here bⱼ≡bⱼ′ rewrite bⱼ≡bⱼ′ = Nat.≤-refl
                    ... | there bⱼ∈cᴮ′₂ = Nat.<⇒≤ $ L.All.lookup (L.All.++⁻ˡ cᴮ′₂ bⱼ′>ˢcᴮ′₂+c′+cᴬ₁+bᵢ′+cᴬ₂) bⱼ∈cᴮ′₂

                    Nᵢ′↝⁺Nⱼ′ : Nᵢ′ ↝⁺ Nⱼ′
                    Nᵢ′↝⁺Nⱼ′ rewrite Nᵢ′ₜ≡bᵢ′ₜ+1 | Nⱼ′ₜ≡bⱼ′ₜ+1 = Nᵢ′↝⋆Nⱼ′ , bᵢ′ₜ+1<bⱼ′ₜ+1
                      where
                        bᵢ′ₜ+1<bⱼ′ₜ+1 : suc (bᵢ′ .slot) < suc (bⱼ′ .slot)
                        bᵢ′ₜ+1<bⱼ′ₜ+1 = Nat.s<s $ Nat.<-≤-trans bᵢ′ₜ<bⱼₜ bⱼ≤ˢbⱼ′

                    [bᵢ′+1:bⱼ′]InAdvRange : bⱼ .slot ∸ suc (bᵢ .slot) ≤ bⱼ′ .slot ∸ suc (bᵢ′ .slot)
                    [bᵢ′+1:bⱼ′]InAdvRange = Nat.∸-mono bⱼ≤ˢbⱼ′ (Nat.s≤s bᵢ′ₜ≤bᵢₜ)

                    [Nᵢ′:Nⱼ′⦈Adv : length cs[Nᵢ′:Nⱼ′⦈ + w ≤ length (luckySlotsInRange (Nᵢ′ .clock) (Nⱼ′ .clock ∸ 1))
                    [Nᵢ′:Nⱼ′⦈Adv
                      rewrite
                        cong Nat.pred Nⱼ′ₜ≡bⱼ′ₜ+1
                      | Nᵢ′ₜ≡bᵢ′ₜ+1
                      = adv {suc (bᵢ′ .slot)} {bⱼ′ .slot} [bᵢ′+1:bⱼ′]InAdvRange

                    |cs[Nᵢ′:Nⱼ′⦈|+w-1≤|suf′| : length cs[Nᵢ′:Nⱼ′⦈ + (w ∸ 1) ≤ length (cᴮ′₂ ++ c′ ++ cᴬ₁)
                    |cs[Nᵢ′:Nⱼ′⦈|+w-1≤|suf′| =
                        chainGrowth
                          N₀↝⋆Nᵢ′
                          Nᵢ′↝⁺Nⱼ′
                          Nᵢ′Ready
                          hpᵢ′
                          lspᵢ′Nᵢ′
                          hpⱼ′
                          lspⱼ′Nⱼ′
                          {w = length cs[Nᵢ′:Nⱼ′⦈ + w}
                          [Nᵢ′:Nⱼ′⦈Adv ∶
                      length bcᵢ′ + (length cs[Nᵢ′:Nⱼ′⦈ + w) ≤ length bcⱼ′
                        |> subst ((_≤ length bcⱼ′) ∘ (_+ (length cs[Nᵢ′:Nⱼ′⦈ + w))) |bcᵢ′|≡|bᵢ′+cᴬ₂| ∶
                      length (bᵢ′ ∷ cᴬ₂) + (length cs[Nᵢ′:Nⱼ′⦈ + w) ≤ length bcⱼ′
                        |> subst (length (bᵢ′ ∷ cᴬ₂) + (length cs[Nᵢ′:Nⱼ′⦈ + w) ≤_) |bcⱼ′|≡|bⱼ′+cᴮ′₂+c′+cᴬ₁+bᵢ′+cᴬ₂| ∶
                      length (bᵢ′ ∷ cᴬ₂) + (length cs[Nᵢ′:Nⱼ′⦈ + w) ≤ length (bⱼ′ ∷ cᴮ′₂ ++ c′ ++ cᴬ₁ ++ bᵢ′ ∷ cᴬ₂)
                        |> subst (λ ◆ → length (bᵢ′ ∷ cᴬ₂) + ◆ ≤ length (bⱼ′ ∷ cᴮ′₂ ++ c′ ++ cᴬ₁ ++ bᵢ′ ∷ cᴬ₂))
                            (Nat.+-comm _ w) ∶
                      length (bᵢ′ ∷ cᴬ₂) + (w + length cs[Nᵢ′:Nⱼ′⦈) ≤ length (bⱼ′ ∷ cᴮ′₂ ++ c′ ++ cᴬ₁ ++ bᵢ′ ∷ cᴬ₂)
                        |> subst ((length (bᵢ′ ∷ cᴬ₂) + (w + length cs[Nᵢ′:Nⱼ′⦈) ≤_) ∘ length)
                             (sym $ L.++-assoc (bⱼ′ ∷ cᴮ′₂) c′ _) ∶
                      length (bᵢ′ ∷ cᴬ₂) + (w + length cs[Nᵢ′:Nⱼ′⦈) ≤ length ((bⱼ′ ∷ cᴮ′₂ ++ c′) ++ (cᴬ₁ ++ bᵢ′ ∷ cᴬ₂))
                        |> subst ((length (bᵢ′ ∷ cᴬ₂) + (w + length cs[Nᵢ′:Nⱼ′⦈) ≤_) ∘ length)
                             (sym $ L.++-assoc (bⱼ′ ∷ cᴮ′₂ ++ c′) _ _) ∶
                      length (bᵢ′ ∷ cᴬ₂) + (w + length cs[Nᵢ′:Nⱼ′⦈) ≤ length (((bⱼ′ ∷ cᴮ′₂ ++ c′) ++ cᴬ₁) ++ bᵢ′ ∷ cᴬ₂)
                        |> subst (length (bᵢ′ ∷ cᴬ₂) + (w + length cs[Nᵢ′:Nⱼ′⦈) ≤_)
                             (L.length-++ ((bⱼ′ ∷ cᴮ′₂ ++ c′) ++ cᴬ₁)) ∶
                      length (bᵢ′ ∷ cᴬ₂)
                        + (w + length cs[Nᵢ′:Nⱼ′⦈) ≤ length (((bⱼ′ ∷ cᴮ′₂ ++ c′) ++ cᴬ₁))
                        + length (bᵢ′ ∷ cᴬ₂)
                        |> subst (length (bᵢ′ ∷ cᴬ₂) + (w + length cs[Nᵢ′:Nⱼ′⦈) ≤_) (Nat.+-comm _ (length (bᵢ′ ∷ cᴬ₂))) ∶
                      length (bᵢ′ ∷ cᴬ₂)
                        + (w + length cs[Nᵢ′:Nⱼ′⦈) ≤ length (bᵢ′ ∷ cᴬ₂)
                        + length (((bⱼ′ ∷ cᴮ′₂ ++ c′) ++ cᴬ₁))
                        |> Nat.+-cancelˡ-≤ (length (bᵢ′ ∷ cᴬ₂)) _ _ ∶
                      w + length cs[Nᵢ′:Nⱼ′⦈ ≤ length (((bⱼ′ ∷ cᴮ′₂ ++ c′) ++ cᴬ₁))
                        |> subst (_≤ length (((bⱼ′ ∷ cᴮ′₂ ++ c′) ++ cᴬ₁))) (Nat.+-comm w _) ∶
                      length cs[Nᵢ′:Nⱼ′⦈ + w ≤ length (((bⱼ′ ∷ cᴮ′₂ ++ c′) ++ cᴬ₁))
                        |> subst ((length cs[Nᵢ′:Nⱼ′⦈ + w ≤_) ∘ length) (L.++-assoc (bⱼ′ ∷ cᴮ′₂) c′ _) ∶
                      length cs[Nᵢ′:Nⱼ′⦈ + w ≤ length (bⱼ′ ∷ cᴮ′₂ ++ c′ ++ cᴬ₁)
                        |> subst ((length cs[Nᵢ′:Nⱼ′⦈ + w ≤_) ∘ length) (L.++-assoc [ bⱼ′ ] cᴮ′₂ _) ∶
                      length cs[Nᵢ′:Nⱼ′⦈ + w ≤ suc (length (cᴮ′₂ ++ c′ ++ cᴬ₁))
                        |> Nat.∸-monoˡ-≤ 1 ∶
                      length cs[Nᵢ′:Nⱼ′⦈ + w ∸ 1 ≤ length (cᴮ′₂ ++ c′ ++ cᴬ₁)
                        |> subst (_≤ length (cᴮ′₂ ++ c′ ++ cᴬ₁)) (Nat.+-∸-assoc (length cs[Nᵢ′:Nⱼ′⦈) (Nat.s≤s Nat.z≤n)) ∶
                      length cs[Nᵢ′:Nⱼ′⦈ + (w ∸ 1) ≤ length (cᴮ′₂ ++ c′ ++ cᴬ₁)

                    eq-prf : cᴮ′₂ ++ c′ ++ cᴬ₁ ++ bᵢ′ ∷ cᴬ₂ ≡ (cᴮ′₂ ++ c′ ++ cᴬ₁) ++ bᵢ′ ∷ cᴬ₂
                    eq-prf
                      rewrite
                        L.++-assoc cᴮ′₂ (c′ ++ cᴬ₁) (bᵢ′ ∷ cᴬ₂)
                      | L.++-assoc c′ cᴬ₁ (bᵢ′ ∷ cᴬ₂)
                      = refl

                    [suf″+bᵢ′+cᴬ₂]✓ : ((cᴮ′₁ L.∷ʳ bⱼ′) ++ (cᴮ′₂ ++ c′ ++ cᴬ₁) ++ bᵢ′ ∷ cᴬ₂) ✓
                    [suf″+bᵢ′+cᴬ₂]✓
                      rewrite
                        sym eq-prf
                      | L.++-assoc cᴮ′₁ [ bⱼ′ ] (cᴮ′₂ ++ c′ ++ cᴬ₁ ++ bᵢ′ ∷ cᴬ₂)
                      = [suf′+bᵢ′+cᴬ₂]✓

                    ds[suf′+bᵢ′+cᴬ₂] : DecreasingSlots ((cᴮ′₂ ++ c′ ++ cᴬ₁) ++ bᵢ′ ∷ cᴬ₂)
                    ds[suf′+bᵢ′+cᴬ₂] = ++-DecreasingSlots {c = cᴮ′₁ L.∷ʳ bⱼ′} (✓⇒ds $ [suf″+bᵢ′+cᴬ₂]✓) .proj₂ .proj₁

                    suf′In[Nᵢ′ₜ:Nⱼ′ₜ⦈ : L.All.All (λ b → Nᵢ′ .clock ≤ b .slot × b .slot < Nⱼ′ .clock ∸ 1) (cᴮ′₂ ++ c′ ++ cᴬ₁)
                    suf′In[Nᵢ′ₜ:Nⱼ′ₜ⦈ rewrite cong Nat.pred Nⱼ′ₜ≡bⱼ′ₜ+1 | Nᵢ′ₜ≡bᵢ′ₜ+1 = L.All.tabulate ϕ
                      where
                        ϕ : ∀ {b} → b ∈ cᴮ′₂ ++ c′ ++ cᴬ₁ → bᵢ′ .slot < b .slot × b .slot < bⱼ′ .slot
                        ϕ {b} b∈[cᴮ′₂+c′+cᴬ₁] = bᵢ′<ˢb , b<ˢbⱼ′
                          where
                            bᵢ′<ˢb : bᵢ′ .slot < b .slot
                            bᵢ′<ˢb = bᵢ′<ˢb* b∈[cᴮ′₂+c′+cᴬ₁] ds[suf′+bᵢ′+cᴬ₂]
                              where

                                bᵢ′<ˢb* : ∀ {c*} → b ∈ c* → DecreasingSlots (c* ++ bᵢ′ ∷ cᴬ₂) → bᵢ′ .slot < b .slot
                                bᵢ′<ˢb* {[]}      ()           _
                                bᵢ′<ˢb* {b* ∷ c*} (here b≡b*)  q rewrite b≡b* =
                                  nonAdjacentBlocksDecreasingSlots {cₕ = []} {cₘ = c*} {cₜ = cᴬ₂} {b₁ = b*} {b₂ = bᵢ′} q
                                bᵢ′<ˢb* {b* ∷ c*} (there b∈c*) q = bᵢ′<ˢb* {c*} b∈c* (∷-DecreasingSlots q .proj₁)

                            b<ˢbⱼ′ : b .slot < bⱼ′ .slot
                            b<ˢbⱼ′ = L.All.lookup bⱼ′>ˢcᴮ′₂+c′+cᴬ₁+bᵢ′+cᴬ₂ b∈prf
                              where
                                b∈prf : b ∈ cᴮ′₂ ++ c′ ++ cᴬ₁ ++ bᵢ′ ∷ cᴬ₂
                                b∈prf rewrite eq-prf = L.Mem.∈-++⁺ˡ {ys = bᵢ′ ∷ cᴬ₂} b∈[cᴮ′₂+c′+cᴬ₁]

                    cb[suf′] : CorrectBlocks (cᴮ′₂ ++ c′ ++ cᴬ₁)
                    cb[suf′] = L.All.++⁻ˡ (cᴮ′₂ ++ c′ ++ cᴬ₁) $ L.All.++⁻ʳ (cᴮ′₁ L.∷ʳ bⱼ′) $ ✓⇒cb [suf″+bᵢ′+cᴬ₂]✓

                    ds[suf′] : DecreasingSlots (cᴮ′₂ ++ c′ ++ cᴬ₁)
                    ds[suf′] = ++-DecreasingSlots {c = cᴮ′₂ ++ c′ ++ cᴬ₁} ds[suf′+bᵢ′+cᴬ₂] .proj₁
