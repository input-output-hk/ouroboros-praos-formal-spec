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
open import Protocol.Tree ⦃ params ⦄
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.ForgingFree ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.CollisionFree ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.SuperBlocks ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.BlockHistory ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.Trees ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Base.Time ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Safety.BlockPositions ⦃ params ⦄ ⦃ assumptions ⦄
open import Properties.Safety.ChainFromBlock ⦃ params ⦄ ⦃ assumptions ⦄
open import Data.Sum.Algebra.Ext using ([B⊎C]×A⇒[AxB]⊎C; [A⊎B]×¬A⇒B)
open import Data.Nat.Properties.Ext using (n≤pred[m]⇒n<m; n>0⇒pred[n]<n; suc≗+1)
open import Data.List.Ext using (ι)
open import Data.List.Properties.Ext using ([]≢∷ʳ; ≢[]⇒∷; find-∃; ι-reverse; ι-++; ++-injective; ι-length; ∈-ι⁺)
open import Data.List.Membership.Propositional.Properties.Ext using (∈-∷-≢⁻; ∈-∷⁻)
open import Data.List.Relation.Binary.Subset.Propositional.Properties.Ext using (++⁻ʳ)
open import Data.List.Relation.Binary.Sublist.Propositional.Properties using (map⁺)
open import Data.List.Relation.Binary.Sublist.Propositional.Properties.Ext using (Unique-resp-⊇; filter-⊆)
open import Data.List.Relation.Binary.Suffix.Heterogeneous using (Suffix; here; there; tail)
open import Data.List.Relation.Binary.Pointwise as Pointwise using (Pointwise-≡⇒≡; ≡⇒Pointwise-≡)
open import Data.List.Relation.Binary.SetEquality using (≡ˢ-sym; ≡ˢ⇒⊆×⊇; Any-resp-≡ˢ; reverse-≡ˢ)
open import Data.List.Relation.Unary.Unique.Propositional.Properties.Ext using (Unique-⊆-#≤)
import Data.Maybe.Relation.Unary.Any as M using (Any)
open import Data.Maybe.Properties.Ext using (Is-just⇒to-witness)
open import Function.Bundles
open Function.Bundles.Equivalence using (to)
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

bestChain⊆gb+blockHistory : ∀ {N : GlobalState} {ls : LocalState} {p : Party} →
    N₀ ↝⋆ N
  → Honest p
  → N .states ⁉ p ≡ just ls
  → bestChain (N .clock ∸ 1) (ls .tree) ⊆ˢ genesisBlock ∷ blockHistory N
bestChain⊆gb+blockHistory {N} {ls} {p} N₀↝⋆N hp lsp = begin
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
adversaryHasAdvantage {N} N₀↝⋆N ffN cfN {p} {ls} hp lsp {c} {sl} c⊆fgb∷bhN c✓ ∣bc∣≤∣c∣ = goal
  where
    Nₜ>0 = positiveClock N₀↝⋆N

    bc  = bestChain (N .clock ∸ 1) (ls .tree)
    b*  = tip (lcs bc c)
    mb′ = L.find ¿ HonestBlock ¿¹ (lcs bc c) -- the last honest block in the longest common stem

    bc✓ : bc ✓
    bc✓ = valid (ls .tree) (N .clock ∸ 1)

    bc⊆gb∷bhN : bc ⊆ˢ genesisBlock ∷ blockHistory N
    bc⊆gb∷bhN = bestChain⊆gb+blockHistory N₀↝⋆N hp lsp

    c⊆gb∷bhN : c ⊆ˢ genesisBlock ∷ blockHistory N
    c⊆gb∷bhN = L.SubS.⊆-trans c⊆fgb∷bhN $ L.SubS.filter-⊆ ((_≤? N .clock ∸ 1 + sl) ∘ slot) (genesisBlock ∷ blockHistory N)

    lcs✓ : lcs bc c ✓
    lcs✓ = lcs-✓ bc✓ c✓

    -- The last honest block in the longest common stem exists...
    mb′IsJust : M.Is-just mb′
    mb′IsJust with ⪯⇔∃ .to (gb⪯lcs bc✓ c✓)
    ... | c′ , c′+gb≡lcs rewrite sym c′+gb≡lcs = mb′IsJust′ c′
      where
        mb′IsJust′ : ∀ c′ → M.Is-just $ L.find ¿ HonestBlock ¿¹ (c′ ++ [ genesisBlock ])
        mb′IsJust′ [] rewrite genesisHonesty = M.Any.just _
        mb′IsJust′ (b″ ∷ c′) with ¿ HonestBlock b″ ¿
        ... | yes hb″ rewrite hb″ = M.Any.just _
        ... | no ¬hb″ rewrite dec-no ¿ HonestBlock b″ ¿ ¬hb″ = mb′IsJust′ c′

    -- ... and we call it b′. In the following, we choose sl′ to be use b′.
    b′ = Block ∋ M.to-witness mb′IsJust

    goal : _
    goal with find-∃ ¿ HonestBlock ¿¹ {xs = lcs bc c} (Is-just⇒to-witness mb′IsJust)
    ... | c₁ , c₂ , c₁+b′+c₂≡lcs , hb′ , ¬hb[c₁] = b′ .slot , b′ₜ≤b*ₜ , advπ
      where
        b′ₜ≤b*ₜ : b′ .slot ≤ b* .slot
        b′ₜ≤b*ₜ with ⪯⇔∃ .to $ lcs-⪯ˡ bc c
        ... | c₃ , c₃+lcs≡bc = subst (λ ◆ → b′ .slot ≤ tip ◆ .slot) c₁+b′+c₂≡lcs $ b′ₜ≤tipₜ c₃+c₁+b′+c₂✓
          where
            c₃+c₁+b′+c₂✓ : (c₃ ++ c₁ ++ [ b′ ] ++ c₂) ✓
            c₃+c₁+b′+c₂✓ rewrite c₁+b′+c₂≡lcs = subst _✓ (sym c₃+lcs≡bc) bc✓

            b′ₜ≤tipₜ : ∀ {c*} → (c₃ ++ c* ++ [ b′ ] ++ c₂) ✓ → b′ .slot ≤ tip (c* ++ [ b′ ] ++ c₂) .slot
            b′ₜ≤tipₜ {[]}      _ = Nat.≤-refl
            b′ₜ≤tipₜ {b″ ∷ c*} p = Nat.<⇒≤ $ L.All.head $ L.All.++⁻ʳ c* b″>ˢc*+b′+c₂
              where
                b″>ˢc*+b′+c₂ : L.All.All (b″ >ˢ_) (c* ++ b′ ∷ c₂)
                b″>ˢc*+b′+c₂ = ∷-DecreasingSlots (✓⇒ds (✓-++ʳ p)) .proj₂

        ss[b′ₜ+1:Nₜ-1]  = superSlotsInRange (b′ .slot + 1) (N .clock ∸ 1)
        cs[b′ₜ+1:Nₜ+sl] = corruptSlotsInRange (b′ .slot + 1) (N .clock + sl)

        advπ : length ss[b′ₜ+1:Nₜ-1] ≤ 2 * length cs[b′ₜ+1:Nₜ+sl]
        advπ with ⪯⇔∃ .to $ lcs-⪯ˡ bc c | ⪯⇔∃ .to $ lcs-⪯ʳ bc c
        ... | c₃ , c₃+lcs≡bc | c₄ , c₄+lcs≡c = Nat.≤-trans advπ₁ advπ₂
          where
            bc≡c₃+c₁+b′+c₂ : bc ≡ c₃ ++ c₁ ++ [ b′ ] ++ c₂
            bc≡c₃+c₁+b′+c₂ rewrite c₁+b′+c₂≡lcs | c₃+lcs≡bc = refl

            c≡c₄+c₁+b′+c₂ : c ≡ c₄ ++ c₁ ++ [ b′ ] ++ c₂
            c≡c₄+c₁+b′+c₂ rewrite c₁+b′+c₂≡lcs | c₄+lcs≡c = refl

            c₃+c₁+b′+c₂✓ : (c₃ ++ c₁ ++ [ b′ ] ++ c₂) ✓
            c₃+c₁+b′+c₂✓ = subst _✓ bc≡c₃+c₁+b′+c₂ bc✓

            c₄+c₁+b′+c₂✓ : (c₄ ++ c₁ ++ [ b′ ] ++ c₂) ✓
            c₄+c₁+b′+c₂✓ = subst _✓ c≡c₄+c₁+b′+c₂ c✓

            corruptBlocks : Chain → Chain
            corruptBlocks = filter ¿ CorruptBlock ¿¹

            areCorruptBlocks : ∀ c → L.All.All CorruptBlock (corruptBlocks c)
            areCorruptBlocks = L.All.all-filter _

            mapBlockPos = L.map (flip blockPos N)

            b′∈bc : b′ ∈ bc
            b′∈bc =
                L.Mem.∈-insert (c₃ ++ c₁) ∶
              b′ ∈ (c₃ ++ c₁) ++ b′ ∷ c₂
                |> subst (b′ ∈_) (L.++-assoc c₃ _ _) ∶
              b′ ∈ c₃ ++ c₁ ++ b′ ∷ c₂
                |> subst (b′ ∈_) (sym bc≡c₃+c₁+b′+c₂) ∶
              b′ ∈ bc
              where open import Function.Reasoning

            -- We now show that each corrupt slot can be used at least once in each branch.

            -- We show that the number of corrupt blocks in both chains must be greater than
            -- or equal to the number of honest blocks (as no honest super block goes on both chains).
            advπ₁ : length ss[b′ₜ+1:Nₜ-1] ≤ ∣ c₁ ∣ + ∣ corruptBlocks c₃ ∣ + ∣ corruptBlocks c₄ ∣
            advπ₁ = subst (_≤ ∣ c₁ ∣ + ∣ corruptBlocks c₃ ∣ + ∣ corruptBlocks c₄ ∣) (sym $ superSlots≡superBlocks N₀↝⋆N ffN 0<b′ₜ+1 Nₜ-1≤Nₜ) advπ₁′
              where
                0<b′ₜ+1 : 0 < b′ .slot + 1
                0<b′ₜ+1 = subst (0 <_) (Nat.+-comm 1 (b′ .slot)) Nat.z<s

                Nₜ-1≤Nₜ : N .clock ∸ 1 ≤ N .clock
                Nₜ-1≤Nₜ = Nat.pred[n]≤n

                sb[b′ₜ+1:Nₜ-1] = superBlocksInRange N (b′ .slot + 1) (N .clock ∸ 1)

                advπ₁′ : ∣ sb[b′ₜ+1:Nₜ-1] ∣ ≤ ∣ c₁ ∣ + ∣ corruptBlocks c₃ ∣ + ∣ corruptBlocks c₄ ∣
                advπ₁′
                  rewrite
                      sym $ L.length-map (flip blockPos N) sb[b′ₜ+1:Nₜ-1]
                    | sym $ L.length-++ c₁ {corruptBlocks c₃}
                    | sym $ L.length-++ (c₁ ++ corruptBlocks c₃) {corruptBlocks c₄}
                    | L.++-assoc c₁ (corruptBlocks c₃) (corruptBlocks c₄)
                    | sym $ L.length-map (flip blockPos N) (c₁ ++ corruptBlocks c₃ ++ corruptBlocks c₄)
                    = Unique-⊆-#≤ psb[ρ]Uniq psb[ρ]⊆p[c₁+cc₃+cc₄]
                  where
                    psb[ρ] = mapBlockPos sb[b′ₜ+1:Nₜ-1]
                    psb[N] = mapBlockPos (superBlocks N)

                    -- Uniqueness of positions of superblocks
                    psb[ρ]Uniq : Unique psb[ρ]
                    psb[ρ]Uniq = Unique-resp-⊇ psb[ρ]⊑psb[N] psb[N]Uniq
                      where
                        psb[N]Uniq : Unique psb[N]
                        psb[N]Uniq = superBlockPositionsUniqueness N₀↝⋆N ffN cfN

                        psb[ρ]⊑psb[N] : psb[ρ] ⊑ psb[N]
                        psb[ρ]⊑psb[N] = map⁺ (flip blockPos N) (filter-⊆ _ (superBlocks N))

                    psb[ρ]⊆p[c₁+cc₃+cc₄] : psb[ρ] ⊆ˢ mapBlockPos (c₁ ++ corruptBlocks c₃ ++ corruptBlocks c₄)
                    psb[ρ]⊆p[c₁+cc₃+cc₄] {bp} bp∈psb[ρ] with L.Mem.∈-map⁻ _ bp∈psb[ρ]
                    ... | sb , sb∈sb[ρ] , bp≡bp[sb]
                      rewrite
                        bp≡bp[sb]
                      | L.map-++ (flip blockPos N) c₁ (corruptBlocks c₃ ++ corruptBlocks c₄)
                      | L.map-++ (flip blockPos N) (corruptBlocks c₃) (corruptBlocks c₄)
                        =
                            p[sb]∈lcs⊎cp[c₃+c₄] ∶
                          blockPos sb N < (1 + ∣ b′ ∷ c₂ ∣) + ∣ c₁ ∣
                          ⊎
                          blockPos sb N ∈ mapBlockPos (corruptBlocks c₃)
                          ⊎
                          blockPos sb N ∈ mapBlockPos (corruptBlocks c₄)
                            |> (⊎-map₁ p[sb]∈p[c₁]) ∶
                          blockPos sb N ∈ mapBlockPos c₁
                          ⊎
                          blockPos sb N ∈ mapBlockPos (corruptBlocks c₃)
                          ⊎
                          blockPos sb N ∈ mapBlockPos (corruptBlocks c₄)
                            |> (⊎-map₂ $ L.Mem.++-∈⇔ .Equivalence.from) ∶
                          blockPos sb N ∈ mapBlockPos c₁
                          ⊎
                          blockPos sb N ∈
                            mapBlockPos (corruptBlocks c₃)
                            ++
                            mapBlockPos (corruptBlocks c₄)
                            |> L.Mem.++-∈⇔ .Equivalence.from ∶
                          blockPos sb N ∈
                            mapBlockPos c₁
                            ++
                            mapBlockPos (corruptBlocks c₃)
                            ++
                            mapBlockPos (corruptBlocks c₄)
                      where
                        open import Function.Reasoning

                        sb∈sbsN : sb ∈ superBlocks N
                        sb∈sbsN = L.Mem.∈-filter⁻ (λ b → ¿ b′ .slot + 1 ≤ b .slot × b .slot < N .clock ∸ 1 ¿) sb∈sb[ρ] .proj₁

                        sb∈hbhN : sb ∈ honestBlockHistory N
                        sb∈hbhN = superBlocks⊆honestBlockHistory N sb∈sbsN

                        sb∈gb+hbhN : sb ∈ genesisBlock ∷ honestBlockHistory N
                        sb∈gb+hbhN = there sb∈hbhN

                        sb∈ρ : b′ .slot + 1 ≤ sb .slot × sb .slot < N .clock ∸ 1
                        sb∈ρ = L.Mem.∈-filter⁻ (λ b → ¿ b′ .slot + 1 ≤ b .slot × b .slot < N .clock ∸ 1 ¿) {xs = superBlocks N} sb∈sb[ρ] .proj₂

                        ∣p[c*]∣≡∣ιʳ[c*]∣ : ∀ c* n → length (mapBlockPos c*) ≡ length (L.reverse (ι n ∣ c* ∣))
                        ∣p[c*]∣≡∣ιʳ[c*]∣ c* n = begin
                          length (mapBlockPos c*)         ≡⟨ L.length-map _ c* ⟩
                          ∣ c* ∣                          ≡⟨ ι-length _ _ ⟨
                          length (ι n ∣ c* ∣)             ≡⟨ L.length-reverse (ι n ∣ c* ∣) ⟨
                          length (L.reverse (ι n ∣ c* ∣)) ∎
                          where open ≡-Reasoning

                        ∣c*+c₁+b′+c₂∣≡∣b′+c₂+c₁+c*∣ : ∀ c* → ∣ c* ++ c₁ ++ b′ ∷ c₂ ∣ ≡ ∣ b′ ∷ c₂ ++ c₁ ++ c* ∣
                        ∣c*+c₁+b′+c₂∣≡∣b′+c₂+c₁+c*∣ c* = begin
                          ∣ c* ++ c₁ ++ b′ ∷ c₂ ∣         ≡⟨ L.length-++ c* ⟩
                          ∣ c* ∣ + ∣ c₁ ++ b′ ∷ c₂ ∣      ≡⟨ cong (∣ c* ∣ +_) $ L.length-++ c₁ ⟩
                          ∣ c* ∣ + (∣ c₁ ∣ + ∣ b′ ∷ c₂ ∣) ≡⟨ solve 3 (λ n m o → n :+ (m :+ o) := o :+ (m :+ n)) refl (∣ c* ∣) (∣ c₁ ∣) (∣ b′ ∷ c₂ ∣) ⟩
                          ∣ b′ ∷ c₂ ∣ + (∣ c₁ ∣ + ∣ c* ∣) ≡⟨ cong (∣ b′ ∷ c₂ ∣ +_) $ sym $ L.length-++ c₁ ⟩
                          ∣ b′ ∷ c₂ ∣ + ∣ c₁ ++ c* ∣      ≡⟨ L.length-++ (b′ ∷ c₂) ⟨
                          ∣ b′ ∷ c₂ ++ c₁ ++ c* ∣         ∎
                          where
                            open ≡-Reasoning
                            open import Data.Nat.Solver using (module +-*-Solver)
                            open +-*-Solver

                        p[c*+c₁+b′+c₂]≡ιʳ : ∀ {c* c⁺} →
                            c* ++ lcs bc c ≡ c⁺
                          → mapBlockPos c⁺ ≡ L.reverse (ι 1 ∣ c⁺ ∣)
                          → mapBlockPos (c* ++ c₁ ++ b′ ∷ c₂) ≡ L.reverse (ι 1 ∣ b′ ∷ c₂ ++ c₁ ++ c* ∣)
                        p[c*+c₁+b′+c₂]≡ιʳ {c*} {c⁺} c*+lcs≡c⁺ eq⁺ = begin
                          mapBlockPos (c* ++ c₁ ++ b′ ∷ c₂)
                            ≡⟨ cong (mapBlockPos ∘ (c* ++_)) c₁+b′+c₂≡lcs ⟩
                          mapBlockPos (c* ++ lcs bc c)
                            ≡⟨ cong! c*+lcs≡c⁺ ⟩
                          mapBlockPos c⁺
                            ≡⟨ eq⁺ ⟩
                          L.reverse (ι 1 ∣ c⁺ ∣)
                            ≡⟨ cong! c*+lcs≡c⁺ ⟨
                          L.reverse (ι 1 ∣ c* ++ lcs bc c ∣)
                            ≡⟨ cong (λ ◆ → L.reverse (ι 1 ∣ c* ++ ◆ ∣)) c₁+b′+c₂≡lcs ⟨
                          L.reverse (ι 1 ∣ c* ++ c₁ ++ b′ ∷ c₂ ∣)
                            ≡⟨ cong (L.reverse ∘ ι 1) (∣c*+c₁+b′+c₂∣≡∣b′+c₂+c₁+c*∣ c*) ⟩
                          L.reverse (ι 1 ∣ b′ ∷ c₂ ++ c₁ ++ c* ∣) ∎
                            where
                              open ≡-Reasoning
                              open import Tactic.Cong

                        p[c₁]≡ιʳ×p[c₃]≡ιʳ :
                            mapBlockPos c₁ ≡ L.reverse (ι (1 + ∣ b′ ∷ c₂ ∣)          ∣ c₁ ∣)
                          × mapBlockPos c₃ ≡ L.reverse (ι (1 + ∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣) ∣ c₃ ∣)
                        p[c₁]≡ιʳ×p[c₃]≡ιʳ =
                          case ++-injective (∣p[c*]∣≡∣ιʳ[c*]∣ c₃ _) p[c₃]+p[c₁]+p[b′+c₂]≡ιʳ of λ where
                            (p[c₃]≡ιʳ , p[c₁]≡p[b′+c₂]) →
                              case ++-injective (∣p[c*]∣≡∣ιʳ[c*]∣ c₁ _) p[c₁]≡p[b′+c₂] of λ where
                                (p[c₁]≡ιʳ , _) → p[c₁]≡ιʳ , p[c₃]≡ιʳ
                          where
                            open ≡-Reasoning
                            open import Tactic.Cong

                            p[c₃+c₁+b′+c₂]≡ιʳ : mapBlockPos (c₃ ++ c₁ ++ b′ ∷ c₂) ≡ L.reverse (ι 1 ∣ b′ ∷ c₂ ++ c₁ ++ c₃ ∣)
                            p[c₃+c₁+b′+c₂]≡ιʳ = p[c*+c₁+b′+c₂]≡ιʳ c₃+lcs≡bc $ cfbLenghtsIsCountdown {blockHistory N} cfN bc✓ bc⊆gb∷bhN

                            p[c₃]+p[c₁]+p[b′+c₂]≡ιʳ :
                                   mapBlockPos c₃
                                ++ mapBlockPos c₁
                                ++ mapBlockPos (b′ ∷ c₂)
                              ≡
                                   L.reverse (ι (1 + ∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣) ∣ c₃ ∣)
                                ++ L.reverse (ι (1 + ∣ b′ ∷ c₂ ∣) ∣ c₁ ∣)
                                ++ L.reverse (ι 1 ∣ b′ ∷ c₂ ∣)
                            p[c₃]+p[c₁]+p[b′+c₂]≡ιʳ = begin
                              mapBlockPos c₃ ++ mapBlockPos c₁ ++ mapBlockPos (b′ ∷ c₂)
                                ≡⟨ cong! (sym $ L.map-++ _ c₁ _) ⟩
                              mapBlockPos c₃ ++ mapBlockPos (c₁ ++ b′ ∷ c₂)
                                ≡⟨ cong! (sym $ L.map-++ _ c₃ _) ⟩
                              mapBlockPos (c₃ ++ c₁ ++ b′ ∷ c₂)
                                ≡⟨ p[c₃+c₁+b′+c₂]≡ιʳ ⟩
                              L.reverse (ι 1 ∣ b′ ∷ c₂ ++ c₁ ++ c₃ ∣)
                                ≡⟨ cong (L.reverse ∘ ι 1) (L.length-++ (b′ ∷ c₂)) ⟩
                              L.reverse (ι 1 (∣ b′ ∷ c₂ ∣ + ∣ c₁ ++ c₃ ∣))
                                ≡⟨ cong L.reverse $ ι-++ 1 ∣ b′ ∷ c₂ ∣ ∣ c₁ ++ c₃ ∣ ⟩
                              L.reverse (ι 1 ∣ b′ ∷ c₂ ∣ ++ ι (1 + ∣ b′ ∷ c₂ ∣) ∣ c₁ ++ c₃ ∣)
                                ≡⟨ cong! (L.length-++ c₁) ⟩
                              L.reverse (ι 1 ∣ b′ ∷ c₂ ∣ ++ ι (1 + ∣ b′ ∷ c₂ ∣) (∣ c₁ ∣ + ∣ c₃ ∣))
                                ≡⟨ cong! (ι-++ (1 + ∣ b′ ∷ c₂ ∣) ∣ c₁ ∣ ∣ c₃ ∣) ⟩
                              L.reverse (ι 1 ∣ b′ ∷ c₂ ∣ ++ ι (1 + ∣ b′ ∷ c₂ ∣) ∣ c₁ ∣ ++ ι (1 + ∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣) ∣ c₃ ∣)
                                ≡⟨ L.reverse-++ (ι 1 ∣ b′ ∷ c₂ ∣) _ ⟩
                                 L.reverse (ι (1 + ∣ b′ ∷ c₂ ∣) ∣ c₁ ∣ ++ ι (1 + ∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣) ∣ c₃ ∣)
                              ++ L.reverse (ι 1 ∣ b′ ∷ c₂ ∣)
                                ≡⟨ cong! (L.reverse-++ (ι (1 + ∣ b′ ∷ c₂ ∣) ∣ c₁ ∣) _) ⟩
                                 (L.reverse (ι (1 + ∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣) ∣ c₃ ∣) ++ L.reverse (ι (1 + ∣ b′ ∷ c₂ ∣) ∣ c₁ ∣))
                              ++ L.reverse (ι 1 ∣ b′ ∷ c₂ ∣)
                                ≡⟨ L.++-assoc (L.reverse (ι (1 + ∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣) ∣ c₃ ∣)) _ _ ⟩
                                 L.reverse (ι (1 + ∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣) ∣ c₃ ∣)
                              ++ L.reverse (ι (1 + ∣ b′ ∷ c₂ ∣) ∣ c₁ ∣)
                              ++ L.reverse (ι 1 ∣ b′ ∷ c₂ ∣)
                              ∎

                        p[c₁]≡ιʳ : mapBlockPos c₁ ≡ L.reverse (ι (1 + ∣ b′ ∷ c₂ ∣) ∣ c₁ ∣)
                        p[c₁]≡ιʳ = p[c₁]≡ιʳ×p[c₃]≡ιʳ .proj₁

                        p[c₃]≡ιʳ : mapBlockPos c₃ ≡ L.reverse (ι (1 + ∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣) ∣ c₃ ∣)
                        p[c₃]≡ιʳ = p[c₁]≡ιʳ×p[c₃]≡ιʳ .proj₂

                        p[c₄]≡ιʳ : mapBlockPos c₄ ≡ L.reverse (ι (1 + ∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣) ∣ c₄ ∣)
                        p[c₄]≡ιʳ = proj₁ $ ++-injective (∣p[c*]∣≡∣ιʳ[c*]∣ c₄ _) $ begin
                          mapBlockPos c₄ ++ mapBlockPos (c₁ ++ b′ ∷ c₂)
                            ≡⟨ L.map-++ _ c₄ _ ⟨
                          mapBlockPos (c₄ ++ c₁ ++ b′ ∷ c₂)
                            ≡⟨ p[c*+c₁+b′+c₂]≡ιʳ c₄+lcs≡c $ cfbLenghtsIsCountdown {blockHistory N} cfN c✓ c⊆gb∷bhN ⟩
                          L.reverse (ι 1 ∣ b′ ∷ c₂ ++ c₁ ++ c₄ ∣)
                            ≡⟨ cong! (sym $ L.++-assoc (b′ ∷ c₂) c₁ _) ⟩
                          L.reverse (ι 1 ∣ (b′ ∷ c₂ ++ c₁) ++ c₄ ∣)
                            ≡⟨ cong! (L.length-++ (b′ ∷ c₂ ++ c₁)) ⟩
                          L.reverse (ι 1 (∣ b′ ∷ c₂ ++ c₁ ∣ + ∣ c₄ ∣))
                            ≡⟨ cong! (L.length-++ (b′ ∷ c₂)) ⟩
                          L.reverse (ι 1 (∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣ + ∣ c₄ ∣))
                            ≡⟨ cong! (ι-++ 1 (∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣) ∣ c₄ ∣) ⟩
                          L.reverse (ι 1 (∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣) ++ ι (1 + ∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣) ∣ c₄ ∣)
                            ≡⟨ L.reverse-++ (ι 1 (∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣)) _ ⟩
                          L.reverse (ι (1 + ∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣) ∣ c₄ ∣) ++ L.reverse (ι 1 (∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣)) ∎
                          where
                            open ≡-Reasoning
                            open import Tactic.Cong

                            blcf[bhN] : BlockListCollisionFree (blockHistory N)
                            blcf[bhN] = BlockListCollisionFree-⊆ (L.SubS.xs⊆x∷xs (blockHistory N) _) cfN

                        p[sb]∈p[c₁] : blockPos sb N < (1 + ∣ b′ ∷ c₂ ∣) + ∣ c₁ ∣ → blockPos sb N ∈ mapBlockPos c₁
                        p[sb]∈p[c₁] p =
                              p ∶
                            blockPos sb N < (1 + ∣ b′ ∷ c₂ ∣) + ∣ c₁ ∣
                              |> ∣b′+c₂∣<p[sb] ,_ ∶
                            (1 + ∣ b′ ∷ c₂ ∣ ≤ blockPos sb N × blockPos sb N < (1 + ∣ b′ ∷ c₂ ∣) + ∣ c₁ ∣)
                              |> uncurry′ ∈-ι⁺ ∶
                            blockPos sb N ∈ ι (1 + ∣ b′ ∷ c₂ ∣) ∣ c₁ ∣
                              |> reverse-≡ˢ (ι (1 + ∣ b′ ∷ c₂ ∣) ∣ c₁ ∣) .Equivalence.from ∶
                            blockPos sb N ∈ L.reverse (ι (1 + ∣ b′ ∷ c₂ ∣) ∣ c₁ ∣)
                              |> subst (blockPos sb N ∈_) (sym p[c₁]≡ιʳ) ∶
                            blockPos sb N ∈ mapBlockPos c₁
                           where
                             -- The super block was aware of b′ when mined
                             ∣b′+c₂∣<p[sb] : ∣ b′ ∷ c₂ ∣ < blockPos sb N
                             ∣b′+c₂∣<p[sb] = subst ((_< blockPos sb N) ∘ ∣_∣) (sym b′+c₂≡cfb[b′]) p[b′]<p[sb]
                               where
                                 b′+c₂≡cfb[b′] : b′ ∷ c₂ ≡ chainFromBlock b′ (blockHistory N)
                                 b′+c₂≡cfb[b′] = sym $ cfbInBlockListIsSubset cfN b′+c₂✓ c₂⊆gb+bhN
                                   where
                                     b′+c₂✓ : (b′ ∷ c₂) ✓
                                     b′+c₂✓ =
                                         c₃+c₁+b′+c₂✓ ∶
                                       (c₃ ++ c₁ ++ b′ ∷ c₂) ✓
                                         |> subst _✓ (sym $ L.++-assoc c₃ _ _) ∶
                                       ((c₃ ++ c₁) ++ b′ ∷ c₂) ✓
                                         |> ✓-++ʳ {c = c₃ ++ c₁} ∶
                                       (b′ ∷ c₂) ✓

                                     c₂⊆gb+bhN : c₂ ⊆ˢ genesisBlock ∷ blockHistory N
                                     c₂⊆gb+bhN = L.SubS.⊆-trans c₂⊆bc bc⊆gb∷bhN
                                       where
                                         c₂⊆bc : c₂ ⊆ˢ bc
                                         c₂⊆bc = begin
                                           c₂                         ⊆⟨ L.SubS.xs⊆ys++xs _ _ ⟩
                                           (c₃ ++ c₁ ++ [ b′ ]) ++ c₂ ≡⟨ L.++-assoc c₃ _ _ ⟩
                                           c₃ ++ (c₁ ++ [ b′ ]) ++ c₂ ≡⟨ cong (c₃ ++_) $ L.++-assoc c₁ _ _ ⟩
                                           c₃ ++ c₁ ++ [ b′ ] ++ c₂   ≡⟨ bc≡c₃+c₁+b′+c₂ ⟨
                                           bc ∎
                                          where open L.SubS.⊆-Reasoning Block

                                 p[b′]<p[sb] : blockPos b′ N < blockPos sb N
                                 p[b′]<p[sb] = L.All.lookup (olderBlocksHaveSmallerPositions {N} {sb} N₀↝⋆N ffN cfN sb∈gb+hbhN) b′∈[sb>ˢ]gb+hbhN
                                   where
                                     b′∈[sb>ˢ]gb+hbhN : b′ ∈ filter ¿ sb >ˢ_ ¿¹ (genesisBlock ∷ honestBlockHistory N)
                                     b′∈[sb>ˢ]gb+hbhN = L.Mem.∈-filter⁺ ¿ sb >ˢ_ ¿¹ b′∈gb+hbhN sb>ˢb′
                                       where
                                         sb>ˢb′ : sb >ˢ b′
                                         sb>ˢb′ rewrite suc≗+1 (b′ .slot) = sb∈ρ .proj₁

                                         b′∈gb+hbhN : b′ ∈ genesisBlock ∷ honestBlockHistory N
                                         b′∈gb+hbhN with b′ ≟ genesisBlock
                                         ... | yes b′≡gb = here b′≡gb
                                         ... | no  b′≢gb = there $ L.Mem.∈-filter⁺ ¿ HonestBlock ¿¹ b′∈bhN hb′
                                           where
                                             b′∈bhN : b′ ∈ blockHistory N
                                             b′∈bhN = ∈-∷-≢⁻ (bc⊆gb∷bhN b′∈bc) b′≢gb

                        N₀↝⁺N : N₀ ↝⁺ N
                        N₀↝⁺N = N₀↝⋆N , N₀ₜ<t (N .clock) (sb∈ρ .proj₂)
                          where
                            N₀ₜ<t : ∀ t → sb .slot < t ∸ 1 → N₀ .clock < t
                            N₀ₜ<t (suc (suc _)) _ = Nat.s≤s (Nat.s≤s Nat.z≤n)

                        p[sb]∈lcs⊎cp[c₃+c₄] :
                          blockPos sb N < (1 + ∣ b′ ∷ c₂ ∣) + ∣ c₁ ∣
                          ⊎
                          blockPos sb N ∈ mapBlockPos (corruptBlocks c₃)
                          ⊎
                          blockPos sb N ∈ mapBlockPos (corruptBlocks c₄)
                        p[sb]∈lcs⊎cp[c₃+c₄] with blockPos sb N <? (1 + ∣ b′ ∷ c₂ ∣) + ∣ c₁ ∣
                        ... | yes p = inj₁ p
                        ... | no ¬p with ∃ReadyInPreviousRound N₀↝⁺N
                        ... |   Nᴿ , N₀↝⋆Nᴿ , Nᴿ↝⋆N , NᴿReady , Nᴿₜ≡Nₜ-1 = inj₂ p[sb]∈cp[c₃+c₄]
                          where
                            sb∈hbhNᴿ : sb ∈ honestBlockHistory Nᴿ
                            sb∈hbhNᴿ = L.SubS.filter-⊆ _ _ $
                                sb∈hbhN ∶
                              sb ∈ honestBlockHistory N
                                |> flip (L.Mem.∈-filter⁺ _) (subst (sb .slot <_) (sym Nᴿₜ≡Nₜ-1) (sb∈ρ .proj₂)) ∶
                              sb ∈ filter (λ b′ → b′ .slot <? Nᴿ .clock) (honestBlockHistory N)
                                |> ≡ˢ⇒⊆×⊇ (honestBlocksBelowSlotPreservation N₀↝⋆Nᴿ Nᴿ↝⋆N ffN) .proj₂ ∶
                              sb ∈ filter (λ b′ → b′ .slot <? Nᴿ .clock) (honestBlockHistory Nᴿ)

                            ffNᴿ : ForgingFree Nᴿ
                            ffNᴿ = ForgingFreePrev Nᴿ↝⋆N ffN

                            cfNᴿ : CollisionFree Nᴿ
                            cfNᴿ = CollisionFreePrev Nᴿ↝⋆N cfN

                            p[sb]≤∣bc∣ : blockPos sb N ≤ ∣ bc ∣
                            p[sb]≤∣bc∣ = optimal (chainFromBlock sb (blockHistory N)) (ls .tree) (N .clock ∸ 1) cfb[sb]✓ cfb[sb]⊆t
                              where
                                Nₜ-1<Nₜ : N .clock ∸ 1 < N .clock
                                Nₜ-1<Nₜ = n>0⇒pred[n]<n (positiveClock N₀↝⋆N)

                                cfb[sb]✓ : chainFromBlock sb (blockHistory N) ✓
                                cfb[sb]✓ = honestBlockCfb✓ N₀↝⋆N ffN cfN (superBlocks⊆honestBlockHistory N sb∈sbsN)

                                cfb[sb]⊆t : chainFromBlock sb (blockHistory N) ⊆ˢ filter (λ b″ → b″ .slot ≤? N .clock ∸ 1) (allBlocks (ls .tree))
                                cfb[sb]⊆t {b″} b″∈cfb = L.Mem.∈-filter⁺ _ {xs = allBlocks (ls .tree)} b″∈t b″ₜ≤Nₜ-1
                                  where
                                    b″∈t : b″ ∈ allBlocks (ls .tree)
                                    b″∈t = L.SubS.⊆-trans cfb[sb]⊆ht ht⊆lt b″∈cfb[sb]Nᴿ
                                      where
                                        b″∈cfb[sb]Nᴿ : b″ ∈ chainFromBlock sb (blockHistory Nᴿ)
                                        b″∈cfb[sb]Nᴿ = subst (b″ ∈_) (sym cfb[sb]Nᴿ≡cfb[sb]N) b″∈cfb
                                          where
                                            cfb[sb]Nᴿ≡cfb[sb]N : chainFromBlock sb (blockHistory Nᴿ) ≡ chainFromBlock sb (blockHistory N)
                                            cfb[sb]Nᴿ≡cfb[sb]N = subsetCfbPreservation cfhN bhNᴿ⊆bhN cfb[sb]Nᴿ≢[]
                                              where
                                                cfhN : BlockListCollisionFree (blockHistory N)
                                                cfhN = BlockListCollisionFree-∷ {blockHistory N} {genesisBlock} cfN

                                                bhNᴿ⊆bhN : blockHistory Nᴿ ⊆ˢ blockHistory N
                                                bhNᴿ⊆bhN = blockHistoryPreservation-↝⋆ Nᴿ↝⋆N

                                                cfb[sb]Nᴿ≢[] : chainFromBlock sb (blockHistory Nᴿ) ≢ []
                                                cfb[sb]Nᴿ≢[] = subst (_≢ []) (✓⇒gbIsHead cfb[sb]Nᴿ✓ .proj₂) (≢-sym []≢∷ʳ)
                                                  where
                                                    cfb[sb]Nᴿ✓ : chainFromBlock sb (blockHistory Nᴿ) ✓
                                                    cfb[sb]Nᴿ✓ = L.All.lookup (L.All.tabulate $ λ {b} → honestBlockCfb✓ N₀↝⋆Nᴿ ffNᴿ cfNᴿ) sb∈hbhNᴿ

                                        cfb[sb]⊆ht : chainFromBlock sb (blockHistory Nᴿ) ⊆ˢ allBlocks (honestTree Nᴿ)
                                        cfb[sb]⊆ht = L.All.lookup (cfbInHonestTree N₀↝⋆Nᴿ ffNᴿ cfNᴿ) sb∈hbhNᴿ

                                        ht⊆lt : allBlocks (honestTree Nᴿ) ⊆ˢ allBlocks (ls .tree)
                                        ht⊆lt = honestGlobalTreeInHonestLocalTree-↝⁺ N₀↝⋆Nᴿ hp NᴿReady Nᴿ↝⁺N lsp
                                          where
                                            Nᴿ↝⁺N : Nᴿ ↝⁺ N
                                            Nᴿ↝⁺N rewrite Nᴿₜ≡Nₜ-1 = Nᴿ↝⋆N , Nₜ-1<Nₜ

                                    b″ₜ≤Nₜ-1 : b″ .slot ≤ N .clock ∸ 1
                                    b″ₜ≤Nₜ-1 = Nat.<⇒≤pred b″ₜ<Nₜ
                                      where
                                        b″ₜ<Nₜ : b″ .slot < N .clock
                                        b″ₜ<Nₜ = Nat.<-≤-trans b″ₜ<Nₜ-1 (Nat.<⇒≤ Nₜ-1<Nₜ)
                                          where
                                            cfb[sb]≢[] : chainFromBlock sb (blockHistory N) ≢ []
                                            cfb[sb]≢[] = subst (_≢ []) (✓⇒gbIsHead cfb[sb]✓ .proj₂) (≢-sym []≢∷ʳ)

                                            b″ₜ<Nₜ-1 : b″ .slot < N .clock ∸ 1
                                            b″ₜ<Nₜ-1 with cfbStartsWithBlock {sb} {blockHistory N} cfb[sb]≢[]
                                            ... | c′ , cfb≡sb+c′ = case ∈-∷⁻ (subst (b″ ∈_) cfb≡sb+c′ b″∈cfb) of λ where
                                                  (inj₁ b″≡sb) → subst ((_< N .clock ∸ 1) ∘ slot) (sym b″≡sb) (sb∈ρ .proj₂)
                                                  (inj₂ b″∈c′) → Nat.<-trans (sb>ˢb″ b″∈c′) (sb∈ρ .proj₂)
                                              where
                                                sb>ˢb″ : b″ ∈ c′ → sb >ˢ b″
                                                sb>ˢb″ b″∈c′ with L.Mem.∈-∃++ b″∈c′
                                                ... | c′ₕ , c′ₜ , c′≡c′ₕ+b″+c′ₜ =
                                                    cfb[sb]✓ ∶
                                                  chainFromBlock sb (blockHistory N) ✓
                                                    |> subst _✓ cfb≡sb+c′ ∶
                                                  (sb ∷ c′) ✓
                                                    |> subst (_✓ ∘ (sb ∷_)) c′≡c′ₕ+b″+c′ₜ ∶
                                                  (sb ∷ c′ₕ ++ b″ ∷ c′ₜ) ✓
                                                    |> ✓⇒ds ∶
                                                  DecreasingSlots (sb ∷ c′ₕ ++ b″ ∷ c′ₜ)
                                                    |> proj₂ ∘ ∷-DecreasingSlots ∶
                                                  L.All.All (sb >ˢ_) (c′ₕ ++ b″ ∷ c′ₜ)
                                                    |> L.All.++⁻ʳ c′ₕ ∶
                                                  L.All.All (sb >ˢ_) (b″ ∷ c′ₜ)
                                                    |> L.All.head ∶
                                                  sb >ˢ b″

                            p[sb]∈p[c*] : ∀ {c* c⁺} →
                                c⁺ ≡ c* ++ c₁ ++ b′ ∷ c₂
                              → mapBlockPos c* ≡ L.reverse (ι (1 + ∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣) ∣ c* ∣)
                              → blockPos sb N ≤ ∣ c⁺ ∣
                              → blockPos sb N ∈ mapBlockPos c*
                            p[sb]∈p[c*] {c*} {c⁺} eq⁺ p[c*]≡ιʳ p[sb]≤∣c⁺∣ =
                                p[sb]≤∣c⁺∣ ∶
                              blockPos sb N ≤ ∣ c⁺ ∣
                                |> subst (blockPos sb N ≤_) eq ∶
                              blockPos sb N ≤ ∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣ + ∣ c* ∣
                                |> Nat.s<s ∶
                              blockPos sb N < suc ∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣ + ∣ c* ∣
                                |> Nat.≮⇒≥ ¬p ,_ ∶
                              blockPos sb N ≥ (1 + ∣ b′ ∷ c₂ ∣) + ∣ c₁ ∣ × blockPos sb N < suc ∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣ + ∣ c* ∣
                                |> uncurry′ ∈-ι⁺ ∶
                              blockPos sb N ∈ ι (1 + ∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣) ∣ c* ∣
                                |> reverse-≡ˢ (ι (1 + ∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣) ∣ c* ∣) .Equivalence.from ∶
                              blockPos sb N ∈ L.reverse (ι (1 + ∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣) ∣ c* ∣)
                                |> subst (blockPos sb N ∈_) (sym p[c*]≡ιʳ) ∶
                              blockPos sb N ∈ mapBlockPos c*
                              where
                                eq : ∣ c⁺ ∣ ≡ ∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣ + ∣ c* ∣
                                eq = let open ≡-Reasoning in begin
                                  ∣ c⁺ ∣                          ≡⟨ cong ∣_∣ eq⁺ ⟩
                                  ∣ c* ++ c₁ ++ b′ ∷ c₂ ∣         ≡⟨ ∣c*+c₁+b′+c₂∣≡∣b′+c₂+c₁+c*∣ c* ⟩
                                  ∣ b′ ∷ c₂ ++ c₁ ++ c* ∣         ≡⟨ L.length-++ (b′ ∷ c₂) ⟩
                                  ∣ b′ ∷ c₂ ∣ + ∣ c₁ ++ c* ∣      ≡⟨ cong (∣ b′ ∷ c₂ ∣ +_) $ L.length-++ c₁ ⟩
                                  ∣ b′ ∷ c₂ ∣ + (∣ c₁ ∣ + ∣ c* ∣) ≡⟨ Nat.+-assoc _ ∣ c₁ ∣ ∣ c* ∣ ⟨
                                  ∣ b′ ∷ c₂ ∣ + ∣ c₁ ∣ + ∣ c* ∣   ∎

                            p[sb]∈p[c₃] : blockPos sb N ∈ mapBlockPos c₃
                            p[sb]∈p[c₃] = p[sb]∈p[c*] bc≡c₃+c₁+b′+c₂ p[c₃]≡ιʳ p[sb]≤∣bc∣

                            p[sb]∈p[c₄] : blockPos sb N ∈ mapBlockPos c₄
                            p[sb]∈p[c₄] = p[sb]∈p[c*] c≡c₄+c₁+b′+c₂ p[c₄]≡ιʳ (Nat.≤-trans p[sb]≤∣bc∣ ∣bc∣≤∣c∣)

                            b″∈c*+lcs⇒b″≢gb : ∀ {c*} {b″} →
                                b″ ∈ c*
                              → (c* ++ c₁ ++ b′ ∷ c₂) ✓
                              → b″ ≢ genesisBlock
                            b″∈c*+lcs⇒b″≢gb {c*} {b″} b″∈c* c*+c₁+b′+c₂✓ b″≡gb = contradiction b′ₜ<0 Nat.n≮0
                              where
                                b′ₜ<0 : b′ .slot < 0
                                b′ₜ<0 with L.Mem.∈-∃++ b″∈c*
                                ... | cₕ , cₜ , c*≡cₕ+b″+cₜ = subst (_> b′ .slot) genesisBlockSlot gb>ˢb′
                                  where
                                    dsπ : DecreasingSlots (cₕ ++ b″ ∷ (cₜ ++ c₁) ++ b′ ∷ c₂)
                                    dsπ =
                                        ✓⇒ds c*+c₁+b′+c₂✓ ∶
                                      DecreasingSlots (c* ++ c₁ ++ b′ ∷ c₂)
                                        |> subst (DecreasingSlots ∘ (_++ c₁ ++ b′ ∷ c₂)) c*≡cₕ+b″+cₜ ∶
                                      DecreasingSlots ((cₕ ++ b″ ∷ cₜ) ++ c₁ ++ b′ ∷ c₂)
                                        |> subst DecreasingSlots (sym $ L.++-assoc _ c₁ (b′ ∷ c₂)) ∶
                                      DecreasingSlots (((cₕ ++ b″ ∷ cₜ) ++ c₁) ++ b′ ∷ c₂)
                                        |> subst (DecreasingSlots ∘ (_++ b′ ∷ c₂) ) (L.++-assoc _ (b″ ∷ cₜ) _) ∶
                                      DecreasingSlots ((cₕ ++ (b″ ∷ cₜ ++ c₁)) ++ b′ ∷ c₂)
                                        |> subst DecreasingSlots (L.++-assoc _ (b″ ∷ cₜ ++ c₁) _) ∶
                                      DecreasingSlots (cₕ ++ b″ ∷ (cₜ ++ c₁) ++ b′ ∷ c₂)

                                    gb>ˢb′ : genesisBlock >ˢ b′
                                    gb>ˢb′ = subst (_>ˢ b′) b″≡gb $ nonAdjacentBlocksDecreasingSlots dsπ

                            c₃⊆bhN : c₃ ⊆ˢ blockHistory N
                            c₃⊆bhN = L.SubS.⊆-trans c₃⊆htN-gb (honestGlobalTreeButGBInBlockHistory N₀↝⋆N)
                              where
                                c₃⊆htN-gb : c₃ ⊆ˢ filter ¿ _≢ genesisBlock ¿¹ (allBlocks (honestTree N))
                                c₃⊆htN-gb {b″} b″∈c₃ = L.Mem.∈-filter⁺ _ (c₃⊆ˢhtN b″∈c₃) b″≢gb
                                  where
                                    c₃⊆ˢhtN : c₃ ⊆ˢ allBlocks (honestTree N)
                                    c₃⊆ˢhtN = let open L.SubS.⊆-Reasoning Block in begin
                                      c₃
                                        ⊆⟨ L.SubS.xs⊆xs++ys _ _ ⟩
                                      c₃ ++ lcs bc c
                                        ≡⟨ c₃+lcs≡bc ⟩
                                      bc
                                        ⊆⟨ selfContained (ls .tree) (N .clock ∸ 1) ⟩
                                      filter (λ b → slot b ≤? (N .clock ∸ 1)) (allBlocks (ls .tree))
                                        ⊆⟨ L.SubS.filter-⊆ _ _ ⟩
                                      allBlocks (ls .tree)
                                        ⊆⟨ honestLocalTreeInHonestGlobalTree N₀↝⋆N hp lsp ⟩
                                      allBlocks (honestTree N) ∎

                                    b″≢gb : b″ ≢ genesisBlock
                                    b″≢gb = b″∈c*+lcs⇒b″≢gb b″∈c₃ c₃+c₁+b′+c₂✓

                            c₄⊆bhN : c₄ ⊆ˢ blockHistory N
                            c₄⊆bhN {b″} b″∈c₄ = case L.Mem.∈-filter⁻ ((_≤? N .clock ∸ 1 + sl) ∘ slot) {xs = genesisBlock ∷ blockHistory N} (c⊆fgb∷bhN {b″} b″∈c) of λ where
                                (b″∈gb+bhN , _) → case ∈-∷⁻ b″∈gb+bhN of λ where
                                  (inj₁ b″≡gb)  → contradiction b″≡gb b″≢gb
                                  (inj₂ b″∈bhN) → b″∈bhN
                              where
                                b″∈c : b″ ∈ c
                                b″∈c rewrite sym c₄+lcs≡c = L.SubS.xs⊆xs++ys _ _ b″∈c₄

                                b″≢gb : b″ ≢ genesisBlock
                                b″≢gb = b″∈c*+lcs⇒b″≢gb b″∈c₄ c₄+c₁+b′+c₂✓

                            p[sb]∈cp[c₃+c₄] :
                              blockPos sb N ∈ mapBlockPos (corruptBlocks c₃)
                              ⊎
                              blockPos sb N ∈ mapBlockPos (corruptBlocks c₄)
                            p[sb]∈cp[c₃+c₄]
                              with L.Mem.∈-map⁻ _ p[sb]∈p[c₃]
                            ... | bˢ₃ , bˢ₃∈c₃ , p[sb]≡p[bˢ₃]
                              with L.Mem.∈-map⁻ _ p[sb]∈p[c₄]
                            ... | bˢ₄ , bˢ₄∈c₄ , p[sb]≡p[bˢ₄] =
                              case eitherCorrupt of λ where
                                (inj₁ cbˢ₃) → inj₁ $ L.Mem.∈-map∘filter⁺ (flip blockPos N) _ (bˢ₃ , bˢ₃∈c₃ , p[sb]≡p[bˢ₃] , cbˢ₃)
                                (inj₂ cbˢ₄) → inj₂ $ L.Mem.∈-map∘filter⁺ (flip blockPos N) _ (bˢ₄ , bˢ₄∈c₄ , p[sb]≡p[bˢ₄] , cbˢ₄)
                               where
                                 eitherCorrupt : CorruptBlock bˢ₃ ⊎ CorruptBlock bˢ₄
                                 eitherCorrupt
                                   with ¿ CorruptBlock bˢ₃ ¿      | ¿ CorruptBlock bˢ₄ ¿
                                 ... | yes cbˢ₃                   | _                    = inj₁ cbˢ₃
                                 ... | no _                       | yes cbˢ₄             = inj₂ cbˢ₄
                                 ... | no ¬cbˢ₃                   | no ¬cbˢ₄
                                   with L.Mem.∈-∃++ bˢ₃∈c₃        | L.Mem.∈-∃++ bˢ₄∈c₄
                                 ... | cₕ₃ , cₜ₃ , c₃≡cₕ₃+bˢ₃+cₜ₃ | cₕ₄ , cₜ₄ , c₄≡cₕ₄+bˢ₄+cₜ₄
                                   = contradiction bˢ₄+cₜ₄+lcs⪯lcs (++-¬-⪯ (lcs bc c) {bˢ₄ ∷ cₜ₄} λ ())
                                   where
                                     sb≡bˢ : ∀ {bˢ} →
                                         bˢ ∈ blockHistory N
                                       → blockPos sb N ≡ blockPos bˢ N
                                       → ¬ CorruptBlock bˢ
                                       → sb ≡ bˢ
                                     sb≡bˢ {bˢ} bˢ∈bhN p[sb]≡p[bˢ] ¬cbˢ =
                                       [A⊎B]×¬A⇒B
                                         (L.All.lookup (superBlockPositions N₀↝⋆N cfN ffN) [sb,bˢ]∈sbN×hbhN)
                                         (_$ p[sb]≡p[bˢ])
                                       where
                                         hbˢ : HonestBlock bˢ
                                         hbˢ = ¬corrupt⇒honest ¬cbˢ

                                         [sb,bˢ]∈sbN×hbhN : (sb , bˢ) ∈ L.cartesianProduct (superBlocks N) (honestBlockHistory N)
                                         [sb,bˢ]∈sbN×hbhN = L.Mem.∈-cartesianProduct⁺ sb∈sbsN (L.Mem.∈-filter⁺ _ bˢ∈bhN hbˢ)

                                     sb≡bˢ₃ : sb ≡ bˢ₃
                                     sb≡bˢ₃ = sb≡bˢ (c₃⊆bhN bˢ₃∈c₃) p[sb]≡p[bˢ₃] ¬cbˢ₃

                                     sb≡bˢ₄ : sb ≡ bˢ₄
                                     sb≡bˢ₄ = sb≡bˢ (c₄⊆bhN bˢ₄∈c₄) p[sb]≡p[bˢ₄] ¬cbˢ₄

                                     cₕ₃+bˢ₃+cₜ₃+lcs≡bc : cₕ₃ ++ bˢ₃ ∷ cₜ₃ ++ lcs bc c ≡ bc
                                     cₕ₃+bˢ₃+cₜ₃+lcs≡bc = let open ≡-Reasoning in begin
                                       cₕ₃ ++ bˢ₃ ∷ cₜ₃ ++ lcs bc c   ≡⟨ L.++-assoc _ (bˢ₃ ∷ cₜ₃) _ ⟨
                                       (cₕ₃ ++ bˢ₃ ∷ cₜ₃) ++ lcs bc c ≡⟨ cong (_++ lcs bc c) (sym c₃≡cₕ₃+bˢ₃+cₜ₃) ⟩
                                       c₃ ++ lcs bc c                 ≡⟨ c₃+lcs≡bc ⟩
                                       bc ∎

                                     cₕ₄+bˢ₄+cₜ₄+lcs≡c : cₕ₄ ++ bˢ₄ ∷ cₜ₄ ++ lcs bc c ≡ c
                                     cₕ₄+bˢ₄+cₜ₄+lcs≡c = let open ≡-Reasoning in begin
                                       cₕ₄ ++ bˢ₄ ∷ cₜ₄ ++ lcs bc c   ≡⟨ L.++-assoc _ (bˢ₄ ∷ cₜ₄) _ ⟨
                                       (cₕ₄ ++ bˢ₄ ∷ cₜ₄) ++ lcs bc c ≡⟨ cong (_++ lcs bc c) (sym c₄≡cₕ₄+bˢ₄+cₜ₄) ⟩
                                       c₄ ++ lcs bc c                 ≡⟨ c₄+lcs≡c ⟩
                                       c ∎

                                     bˢ₃+cₜ₃+lcs⪯bc : (bˢ₃ ∷ cₜ₃ ++ lcs bc c) ⪯ bc
                                     bˢ₃+cₜ₃+lcs⪯bc = let open ⪯-Reasoning in begin
                                       bˢ₃ ∷ cₜ₃ ++ lcs bc c          ≲⟨ ⪯-++ _ cₕ₃ ⟩
                                       cₕ₃ ++ bˢ₃ ∷ cₜ₃ ++ lcs bc c   ≡⟨ cₕ₃+bˢ₃+cₜ₃+lcs≡bc ⟩
                                       bc ∎

                                     bˢ₄+cₜ₄+lcs⪯c : (bˢ₄ ∷ cₜ₄ ++ lcs bc c) ⪯ c
                                     bˢ₄+cₜ₄+lcs⪯c = let open ⪯-Reasoning in begin
                                       bˢ₄ ∷ cₜ₄ ++ lcs bc c          ≲⟨ ⪯-++ _ cₕ₄ ⟩
                                       cₕ₄ ++ bˢ₄ ∷ cₜ₄ ++ lcs bc c   ≡⟨ cₕ₄+bˢ₄+cₜ₄+lcs≡c ⟩
                                       c ∎

                                     cₜ₃+lcs≡cₜ₄+lcs : cₜ₃ ++ lcs bc c ≡ cₜ₄ ++ lcs bc c
                                     cₜ₃+lcs≡cₜ₄+lcs = ≡tips⇒≡chains N₀↝⋆N cfN sb+cₜ₃+lcs✓ sb+cₜ₄+lcs✓ cₜ₃+lcs⊆gb+bhN cₜ₄+lcs⊆gb+bhN
                                       where
                                         sb+cₜ₃+lcs✓ : (sb ∷ cₜ₃ ++ lcs bc c) ✓
                                         sb+cₜ₃+lcs✓ rewrite sb≡bˢ₃ = ✓-++ʳ $ subst _✓ (sym cₕ₃+bˢ₃+cₜ₃+lcs≡bc) bc✓

                                         sb+cₜ₄+lcs✓ : (sb ∷ cₜ₄ ++ lcs bc c) ✓
                                         sb+cₜ₄+lcs✓ rewrite sb≡bˢ₄ = ✓-++ʳ $ subst _✓ (sym cₕ₄+bˢ₄+cₜ₄+lcs≡c) c✓

                                         cₜ₃+lcs⊆gb+bhN : cₜ₃ ++ lcs bc c ⊆ˢ genesisBlock ∷ blockHistory N
                                         cₜ₃+lcs⊆gb+bhN = L.SubS.⊆-trans cₜ₃+lcs⊆ˢbc bc⊆gb∷bhN
                                           where
                                             cₜ₃+lcs⊆ˢbc : cₜ₃ ++ lcs bc c ⊆ˢ bc
                                             cₜ₃+lcs⊆ˢbc = L.SubS.⊆-trans (L.SubS.xs⊆x∷xs _ _) (⪯⇒⊆ˢ bˢ₃+cₜ₃+lcs⪯bc)

                                         cₜ₄+lcs⊆gb+bhN : cₜ₄ ++ lcs bc c ⊆ˢ genesisBlock ∷ blockHistory N
                                         cₜ₄+lcs⊆gb+bhN = L.SubS.⊆-trans cₜ₄+lcs⊆ˢc c⊆gb∷bhN
                                           where
                                             cₜ₄+lcs⊆ˢc : cₜ₄ ++ lcs bc c ⊆ˢ c
                                             cₜ₄+lcs⊆ˢc = L.SubS.⊆-trans (L.SubS.xs⊆x∷xs _ _) (⪯⇒⊆ˢ bˢ₄+cₜ₄+lcs⪯c)

                                     bˢ₄+cₜ₄+lcs⪯lcs : (bˢ₄ ∷ cₜ₄ ++ lcs bc c) ⪯ lcs bc c
                                     bˢ₄+cₜ₄+lcs⪯lcs = lcs-join bˢ₄+cₜ₄+lcs⪯bc bˢ₄+cₜ₄+lcs⪯c
                                       where
                                         bˢ₄+cₜ₄+lcs⪯bc : (bˢ₄ ∷ cₜ₄ ++ lcs bc c) ⪯ bc
                                         bˢ₄+cₜ₄+lcs⪯bc = let open ⪯-Reasoning in begin
                                           bˢ₄ ∷ cₜ₄ ++ lcs bc c ≡⟨ cong (_∷ cₜ₄ ++ lcs bc c) (trans (sym sb≡bˢ₄) (sb≡bˢ₃)) ⟩
                                           bˢ₃ ∷ cₜ₄ ++ lcs bc c ≡⟨ cong (bˢ₃ ∷_) (sym cₜ₃+lcs≡cₜ₄+lcs) ⟩
                                           bˢ₃ ∷ cₜ₃ ++ lcs bc c ≲⟨ bˢ₃+cₜ₃+lcs⪯bc ⟩
                                           bc ∎

            advπ₂ : ∣ c₁ ∣ + ∣ corruptBlocks c₃ ∣ + ∣ corruptBlocks c₄ ∣ ≤ 2 * length cs[b′ₜ+1:Nₜ+sl]
            advπ₂ = subst (λ ◆ → ∣ c₁ ∣ + ∣ corruptBlocks c₃ ∣ + ∣ corruptBlocks c₄ ∣ ≤ 2 * length ◆) (sym $ slotsInRange-filter-++ _ b′ₜ+1≤b*ₜ+1 b*ₜ+1≤Nₜ+sl) advπ₂′
              where
                b′ₜ+1≤b*ₜ+1 : b′ .slot + 1 ≤ b* .slot + 1
                b′ₜ+1≤b*ₜ+1 = Nat.+-monoˡ-≤ 1 b′ₜ≤b*ₜ

                b*ₜ+1≤Nₜ+sl : b* .slot + 1 ≤ N .clock + sl
                b*ₜ+1≤Nₜ+sl rewrite Nat.+-comm (b* .slot) 1 = Nat.<-≤-trans tipₜ<Nₜ (Nat.m≤m+n (N .clock) sl)
                  where
                    tipₜ<Nₜ : tip (lcs bc c) .slot < N .clock
                    tipₜ<Nₜ = n≤pred[m]⇒n<m ⦃ Nat.>-nonZero Nₜ>0 ⦄ tipₜ≤Nₜ-1
                      where
                        tip∈bc : tip (lcs bc c) ∈ bc
                        tip∈bc = ⪯⇒⊆ˢ (lcs-⪯ˡ bc c) (tip-∈ lcs✓)

                        tipₜ≤Nₜ-1 : tip (lcs bc c) .slot ≤ N .clock ∸ 1
                        tipₜ≤Nₜ-1 = L.All.lookup (bestChainSlotBounded (ls .tree) (N .clock ∸ 1)) tip∈bc

                cs[b′ₜ+1:b*ₜ+1] = corruptSlotsInRange (b′ .slot + 1) (b* .slot + 1)
                cs[b*ₜ+1:Nₜ+sl] = corruptSlotsInRange (b* .slot + 1) (N .clock + sl)

                advπ₂′ :
                  ∣ c₁ ∣ + ∣ corruptBlocks c₃ ∣ + ∣ corruptBlocks c₄ ∣
                  ≤
                  2 * length (cs[b′ₜ+1:b*ₜ+1] ++ cs[b*ₜ+1:Nₜ+sl])
                advπ₂′ = let open Nat.≤-Reasoning in begin
                  ∣ c₁ ∣ + ∣ corruptBlocks c₃ ∣ + ∣ corruptBlocks c₄ ∣    ≡⟨ Nat.+-assoc ∣ c₁ ∣ _ _ ⟩
                  ∣ c₁ ∣ + (∣ corruptBlocks c₃ ∣ + ∣ corruptBlocks c₄ ∣)  ≤⟨ ∣c₁+cc₃+cc₄∣≤2*∣cs₁∣+2*∣cs₂∣ ⟩
                  2 * length cs[b′ₜ+1:b*ₜ+1] + 2 * length cs[b*ₜ+1:Nₜ+sl] ≡⟨ Nat.*-distribˡ-+ 2 (length cs[b′ₜ+1:b*ₜ+1]) _ ⟨
                  2 * (length cs[b′ₜ+1:b*ₜ+1] + length cs[b*ₜ+1:Nₜ+sl])   ≡⟨ cong (2 *_) (L.length-++ cs[b′ₜ+1:b*ₜ+1]) ⟨
                  2 * length (cs[b′ₜ+1:b*ₜ+1] ++ cs[b*ₜ+1:Nₜ+sl]) ∎
                  where
                    ∣c₁∣≤2*∣cs∣ : ∣ c₁ ∣ ≤ 2 * length cs[b′ₜ+1:b*ₜ+1]
                    ∣c₁∣≤2*∣cs∣ = let open Nat.≤-Reasoning in begin
                      ∣ c₁ ∣
                        ≡⟨ Nat.+-identityˡ _ ⟩
                      0 + ∣ c₁ ∣
                        ≤⟨ Nat.+-mono-≤
                             (begin
                               0 ≤⟨ Nat.z≤n ⟩
                               length cs[b′ₜ+1:b*ₜ+1] ∎)
                             (begin
                               ∣ c₁ ∣ ≤⟨ ∣c₁∣≤∣cs∣ ⟩
                               1 * length cs[b′ₜ+1:b*ₜ+1] ∎) ⟩
                      2 * length cs[b′ₜ+1:b*ₜ+1] ∎
                        where
                          ∣c₁∣≤∣cs∣ : ∣ c₁ ∣ ≤ 1 * length cs[b′ₜ+1:b*ₜ+1]
                          ∣c₁∣≤∣cs∣
                            rewrite
                              Nat.*-identityˡ (length cs[b′ₜ+1:b*ₜ+1])
                            | sym $ L.length-map slot c₁
                            = Unique-⊆-#≤ s[c₁]Uniq s[c₁]⊆cs[b′ₜ+1:b*ₜ+1]
                            where
                              s[c₁] = map slot c₁

                              s[c₁]Uniq : Unique s[c₁]
                              s[c₁]Uniq = DecreasingSlots⇒UniqueSlots ds[c₁]
                                where
                                  ds[c₁] : DecreasingSlots c₁
                                  ds[c₁] = ++-DecreasingSlots (++-DecreasingSlots {c₃} (✓⇒ds c₃+c₁+b′+c₂✓) .proj₂ .proj₁) .proj₁

                              s[c₁]⊆cs[b′ₜ+1:b*ₜ+1] : s[c₁] ⊆ˢ cs[b′ₜ+1:b*ₜ+1]
                              s[c₁]⊆cs[b′ₜ+1:b*ₜ+1] {sl} sl∈s[c₁] with L.Mem.∈-map⁻ _ sl∈s[c₁]
                              ... | b″ , b″∈c₁ , sl≡b″ₜ rewrite sl≡b″ₜ = L.Mem.∈-filter⁺ ¿ CorruptSlot ¿¹ b″ₜ∈[b′ₜ+1:b*ₜ+1] cb″ₜ
                                where
                                  b″ₜ∈[b′ₜ+1:b*ₜ+1] : b″ .slot ∈ slotsInRange (b′ .slot + 1) (b* .slot + 1)
                                  b″ₜ∈[b′ₜ+1:b*ₜ+1] = slotsInRange-∈ b′ₜ+1≤b″ₜ b″ₜ<b*ₜ+1
                                    where
                                      open import Function.Reasoning
                                      b′ₜ+1≤b″ₜ : b′ .slot + 1 ≤ b″ .slot
                                      b′ₜ+1≤b″ₜ = b′ₜ+1≤b″ₜ′ b″∈c₁ (✓⇒ds c₃+c₁+b′+c₂✓)
                                        where
                                          b′ₜ+1≤b″ₜ′ : ∀ {c⁺} → b″ ∈ c⁺ → DecreasingSlots (c₃ ++ c⁺ ++ b′ ∷ c₂) → b′ .slot + 1 ≤ b″ .slot
                                          b′ₜ+1≤b″ₜ′ {b⁺ ∷ c⁺} b″∈b⁺∷c⁺ ds[c₃+b⁺+c⁺+b′+c₂] with L.Mem.∈-∃++ b″∈b⁺∷c⁺
                                          ... | cₕ , cₜ , b⁺∷c⁺≡cₕ+b″+cₜ =
                                              ds[c₃+b⁺+c⁺+b′+c₂] ∶
                                            DecreasingSlots (c₃ ++ b⁺ ∷ c⁺ ++ b′ ∷ c₂)
                                              |> proj₁ ∘ proj₂ ∘ ++-DecreasingSlots ∶
                                            DecreasingSlots (b⁺ ∷ c⁺ ++ b′ ∷ c₂)
                                              |> subst (DecreasingSlots ∘ (_++ b′ ∷ c₂)) b⁺∷c⁺≡cₕ+b″+cₜ ∶
                                            DecreasingSlots ((cₕ ++ b″ ∷ cₜ) ++ b′ ∷ c₂)
                                              |> subst DecreasingSlots (L.++-assoc cₕ _ _) ∶
                                            DecreasingSlots (cₕ ++ b″ ∷ cₜ ++ b′ ∷ c₂)
                                              |> proj₁ ∘ proj₂ ∘ ++-DecreasingSlots ∶
                                            DecreasingSlots (b″ ∷ cₜ ++ b′ ∷ c₂)
                                              |> proj₂ ∘ ∷-DecreasingSlots ∶
                                            L.All.All (b″ >ˢ_) (cₜ ++ b′ ∷ c₂)
                                              |> L.All.++⁻ʳ cₜ ∶
                                            L.All.All (b″ >ˢ_) (b′ ∷ c₂)
                                              |> L.All.head ∶
                                            b″ >ˢ b′
                                              |> (subst (b″ .slot ≥_) $ Nat.+-comm 1 (b′ .slot)) ∶
                                            b′ .slot + 1 ≤ b″ .slot

                                      b″ₜ<b*ₜ+1 : b″ .slot < b* .slot + 1
                                      b″ₜ<b*ₜ+1 =
                                          ✓⇒ds c₃+c₁+b′+c₂✓ ∶
                                        DecreasingSlots (c₃ ++ c₁ ++ b′ ∷ c₂)
                                          |> proj₁ ∘ proj₂ ∘ ++-DecreasingSlots {c₃} ∶
                                        DecreasingSlots (c₁ ++ b′ ∷ c₂)
                                          |> b″ₜ<b*ₜ+1′ b″∈c₁ ∶
                                        b″ .slot < tip (c₁ ++ b′ ∷ c₂) .slot + 1
                                          |> subst (λ ◆ → b″ .slot < tip ◆ .slot + 1) c₁+b′+c₂≡lcs ∶
                                        b″ .slot < b* .slot + 1
                                        where
                                          b″ₜ<b*ₜ+1′ : ∀ {c⁺} → b″ ∈ c⁺ → DecreasingSlots (c⁺ ++ b′ ∷ c₂) → b″ .slot < tip (c⁺ ++ b′ ∷ c₂) .slot + 1
                                          b″ₜ<b*ₜ+1′ {b⁺ ∷ c⁺} b″∈b⁺∷c⁺ ds[b⁺+c⁺+b′+c₂] with L.Mem.∈-∃++ b″∈b⁺∷c⁺
                                          ... | [] , cₜ , b⁺∷c⁺≡b″∷cₜ =
                                              Nat.n<1+n (b″ .slot) ∶
                                            b″ .slot < suc (b″ .slot)
                                              |> subst (b″ .slot <_) (Nat.+-comm 1 _) ∶
                                            b″ .slot < b″ .slot + 1
                                              |> subst (λ ◆ → b″ .slot < ◆ .slot + 1) (L.∷-injectiveˡ $ sym b⁺∷c⁺≡b″∷cₜ) ∶
                                            b″ .slot < b⁺ .slot + 1

                                          ... | bₕ ∷ cₕ , cₜ , b⁺∷c⁺≡bₕ+cₕ+b″+cₜ =
                                              ds[b⁺+c⁺+b′+c₂] ∶
                                            DecreasingSlots (b⁺ ∷ c⁺ ++ b′ ∷ c₂)
                                              |> subst (DecreasingSlots ∘ (_++ b′ ∷ c₂)) b⁺∷c⁺≡bₕ+cₕ+b″+cₜ ∶
                                            DecreasingSlots ((bₕ ∷ cₕ ++ b″ ∷ cₜ) ++ b′ ∷ c₂)
                                              |> subst DecreasingSlots (L.++-assoc (bₕ ∷ cₕ) _ _) ∶
                                            DecreasingSlots (bₕ ∷ cₕ ++ b″ ∷ cₜ ++ b′ ∷ c₂)
                                              |> proj₂ ∘ ∷-DecreasingSlots ∶
                                            L.All.All (bₕ >ˢ_) (cₕ ++ b″ ∷ cₜ ++ b′ ∷ c₂)
                                              |> L.All.++⁻ʳ cₕ ∶
                                            L.All.All (bₕ >ˢ_) (b″ ∷ cₜ ++ b′ ∷ c₂)
                                              |> L.All.head ∶
                                            bₕ >ˢ b″
                                              |> subst (_>ˢ b″) (L.∷-injectiveˡ $ sym b⁺∷c⁺≡bₕ+cₕ+b″+cₜ) ∶
                                            b″ .slot < b⁺ .slot
                                              |> flip Nat.<-trans (Nat.n<1+n (b⁺ .slot)) ∶
                                            b″ .slot < suc (b⁺ .slot)
                                              |> subst (b″ .slot <_) (Nat.+-comm 1 _) ∶
                                            b″ .slot < b⁺ .slot + 1

                                  cb″ₜ : CorruptSlot (b″ .slot)
                                  cb″ₜ = L.Any.tabulate⁺ (b″ .pid) (b″ₚWon , cb″ₚ)
                                    where
                                      b″ₚWon : winner (b″ .pid) (b″ .slot)
                                      b″ₚWon = L.All.lookup cb[c₁] b″∈c₁
                                        where
                                          cb[c₁] : CorrectBlocks c₁
                                          cb[c₁] = L.All.++⁻ c₁ (L.All.++⁻ c₃ (✓⇒cb c₃+c₁+b′+c₂✓) .proj₂) .proj₁

                                      cb″ₚ : Corrupt (b″ .pid)
                                      cb″ₚ = ¬honest⇒corrupt $ L.All.lookup ¬hb[c₁] b″∈c₁

                    ∣cc₃+cc₄∣≤2*∣cs∣ : ∣ corruptBlocks c₃ ∣ + ∣ corruptBlocks c₄ ∣ ≤ 2 * length cs[b*ₜ+1:Nₜ+sl]
                    ∣cc₃+cc₄∣≤2*∣cs∣ rewrite Nat.+-identityʳ (length cs[b*ₜ+1:Nₜ+sl]) = Nat.+-mono-≤ ∣cc₃∣≤∣cs∣ ∣cc₄∣≤∣cs∣
                      where
                        ∣cc*∣≤∣cs∣ : ∀ {c*} →
                            (c* ++ c₁ ++ b′ ∷ c₂) ✓
                          → (∀ {sl′ b″} → sl′ ∈ map slot (corruptBlocks c*) → b″ ∈ corruptBlocks c* → b″ .slot < N .clock + sl)
                          → ∣ corruptBlocks c* ∣ ≤ length cs[b*ₜ+1:Nₜ+sl]
                        ∣cc*∣≤∣cs∣ {c*} c*+c₁+b′+c₂✓ b″ₜ<Nₜ+sl rewrite sym $ L.length-map slot (corruptBlocks c*) = Unique-⊆-#≤ scb[c*]Uniq scb[c*]⊆cs
                            where
                              scb[c*] = map slot (corruptBlocks c*)

                              scb[c*]Uniq : Unique scb[c*]
                              scb[c*]Uniq = Unique-resp-⊇ scb[c*]⊑s[c*] s[c*]Uniq
                                where
                                  ds[c*] : DecreasingSlots c*
                                  ds[c*] = ++-DecreasingSlots {c*} (✓⇒ds c*+c₁+b′+c₂✓) .proj₁

                                  s[c*]Uniq : Unique (map slot c*)
                                  s[c*]Uniq = DecreasingSlots⇒UniqueSlots ds[c*]

                                  scb[c*]⊑s[c*] : scb[c*] ⊑ map slot c*
                                  scb[c*]⊑s[c*] = map⁺ _ $ filter-⊆ _ c*

                              scb[c*]⊆cs : scb[c*] ⊆ˢ cs[b*ₜ+1:Nₜ+sl]
                              scb[c*]⊆cs {sl′} sl′∈scb[c*] with L.Mem.∈-map⁻ _ sl′∈scb[c*]
                              ... | b″ , b″∈cb[c*] , sl′≡b″ₜ rewrite sl′≡b″ₜ = L.Mem.∈-filter⁺ ¿ CorruptSlot ¿¹ b″∈[b*ₜ+1:Nₜ+sl] cb″ₜ
                                where
                                  b″∈c* : b″ ∈ c*
                                  b″∈c* = L.Mem.∈-filter⁻ _ b″∈cb[c*] .proj₁

                                  b″∈[b*ₜ+1:Nₜ+sl] : b″ .slot ∈ slotsInRange (b* .slot + 1) (N .clock + sl)
                                  b″∈[b*ₜ+1:Nₜ+sl] = slotsInRange-∈ b*ₜ+1≤b″ₜ (b″ₜ<Nₜ+sl sl′∈scb[c*] b″∈cb[c*])
                                    where
                                      c₁+b′+c₂≢[] : c₁ ++ b′ ∷ c₂ ≢ []
                                      c₁+b′+c₂≢[] = contraposition (L.++-conicalʳ c₁ (b′ ∷ c₂)) λ ()

                                      open import Function.Reasoning
                                      b*ₜ+1≤b″ₜ : b* .slot + 1 ≤ b″ .slot
                                      b*ₜ+1≤b″ₜ with L.Mem.∈-∃++ b″∈c* | ≢[]⇒∷ c₁+b′+c₂≢[]
                                      ... | cₕ , cₜ , c*≡cₕ+b″+cₜ | b⁺ , c⁺ , c₁+b′+c₂≡b⁺+c⁺ =
                                          ✓⇒ds c*+c₁+b′+c₂✓ ∶
                                        DecreasingSlots (c* ++ c₁ ++ b′ ∷ c₂)
                                          |> subst (DecreasingSlots ∘ (_++ c₁ ++ b′ ∷ c₂)) c*≡cₕ+b″+cₜ ∶
                                        DecreasingSlots ((cₕ ++ b″ ∷ cₜ) ++ c₁ ++ b′ ∷ c₂)
                                          |> subst DecreasingSlots (L.++-assoc cₕ _ _) ∶
                                        DecreasingSlots (cₕ ++ b″ ∷ cₜ ++ c₁ ++ b′ ∷ c₂)
                                          |> proj₁ ∘ proj₂ ∘ ++-DecreasingSlots {cₕ} ∶
                                        DecreasingSlots (b″ ∷ cₜ ++ c₁ ++ b′ ∷ c₂)
                                          |> proj₂ ∘ ∷-DecreasingSlots ∶
                                        L.All.All (b″ >ˢ_) (cₜ ++ c₁ ++ b′ ∷ c₂)
                                          |> L.All.++⁻ʳ cₜ ∶
                                        L.All.All (b″ >ˢ_) (c₁ ++ b′ ∷ c₂)
                                          |> subst (L.All.All (b″ >ˢ_)) c₁+b′+c₂≡b⁺+c⁺ ∶
                                        L.All.All (b″ >ˢ_) (b⁺ ∷ c⁺)
                                          |> L.All.head ∶
                                        b″ >ˢ b⁺
                                          |> subst (b″ >ˢ_) b⁺≡b* ∶
                                        b″ >ˢ b*
                                          |> subst (_≤ b″ .slot) (Nat.+-comm 1 _) ∶
                                        b* .slot + 1 ≤ b″ .slot
                                          where
                                            b⁺≡b* : b⁺ ≡ b*
                                            b⁺≡b* = sym $ cong tip (trans (sym c₁+b′+c₂≡lcs) c₁+b′+c₂≡b⁺+c⁺)

                                  cb″ₜ : CorruptSlot (b″ .slot)
                                  cb″ₜ = L.Any.tabulate⁺ (b″ .pid) (b″ₚWon , cb″ₚ)
                                    where
                                      b″ₚWon : winner (b″ .pid) (b″ .slot)
                                      b″ₚWon = L.All.lookup cb[cb[c*]] b″∈cb[c*]
                                        where
                                          cb[c*] : CorrectBlocks c*
                                          cb[c*] = L.All.++⁻ c* (✓⇒cb c*+c₁+b′+c₂✓) .proj₁

                                          cb[cb[c*]] : CorrectBlocks (corruptBlocks c*)
                                          cb[cb[c*]] = L.All.filter⁺ _ cb[c*]

                                      cb″ₚ : Corrupt (b″ .pid)
                                      cb″ₚ = L.All.lookup (areCorruptBlocks c*) b″∈cb[c*]

                        ∣cc₃∣≤∣cs∣ : ∣ corruptBlocks c₃ ∣ ≤ length cs[b*ₜ+1:Nₜ+sl]
                        ∣cc₃∣≤∣cs∣ = ∣cc*∣≤∣cs∣ {c₃} c₃+c₁+b′+c₂✓ b″ₜ<Nₜ+sl
                          where
                            b″ₜ<Nₜ+sl : ∀ {sl′ b″} → sl′ ∈ map slot (corruptBlocks c₃) → b″ ∈ corruptBlocks c₃ → b″ .slot < N .clock + sl
                            b″ₜ<Nₜ+sl {sl′} {b″} _ b″∈cb[c₃] = Nat.<-≤-trans b″ₜ<Nₜ (Nat.m≤m+n (N .clock) sl)
                              where
                                b″∈c₃ : b″ ∈ c₃
                                b″∈c₃ = L.Mem.∈-filter⁻ _ b″∈cb[c₃] .proj₁

                                b″∈bc : b″ ∈ bc
                                b″∈bc = subst (b″ ∈_) c₃+lcs≡bc $ L.Mem.∈-++⁺ˡ b″∈c₃

                                b″ₜ≤Nₜ-1 : b″ .slot ≤ N .clock ∸ 1
                                b″ₜ≤Nₜ-1 = L.All.lookup (bestChainSlotBounded (ls .tree) (N .clock ∸ 1)) b″∈bc

                                b″ₜ<Nₜ : b″ .slot < N .clock
                                b″ₜ<Nₜ = n≤pred[m]⇒n<m ⦃ Nat.>-nonZero Nₜ>0 ⦄ b″ₜ≤Nₜ-1

                        ∣cc₄∣≤∣cs∣ : ∣ corruptBlocks c₄ ∣ ≤ length cs[b*ₜ+1:Nₜ+sl]
                        ∣cc₄∣≤∣cs∣ = ∣cc*∣≤∣cs∣ {c₄} c₄+c₁+b′+c₂✓ b″ₜ<Nₜ+sl
                          where
                            b″ₜ<Nₜ+sl : ∀ {sl′ b″} → sl′ ∈ map slot (corruptBlocks c₄) → b″ ∈ corruptBlocks c₄ → b″ .slot < N .clock + sl
                            b″ₜ<Nₜ+sl {sl′} {b″} _ b″∈cb[c₄] = let open Nat.≤-Reasoning in begin-strict
                              b″ .slot          ≤⟨ b″ₜ≤Nₜ-1+sl ⟩
                              N .clock ∸ 1 + sl ≡⟨ Nat.+-∸-comm {N .clock} sl {1} Nₜ>0 ⟨
                              N .clock + sl ∸ 1 <⟨ (n>0⇒pred[n]<n $ Nat.m≤n⇒m≤n+o sl Nₜ>0) ⟩
                              N .clock + sl     ∎
                              where
                                b″∈c₄ : b″ ∈ c₄
                                b″∈c₄ = L.Mem.∈-filter⁻ _ b″∈cb[c₄] .proj₁

                                b″∈c : b″ ∈ c
                                b″∈c = subst (b″ ∈_) c₄+lcs≡c $ L.Mem.∈-++⁺ˡ b″∈c₄

                                b″ₜ≤Nₜ-1+sl : b″ .slot ≤ N .clock ∸ 1 + sl
                                b″ₜ≤Nₜ-1+sl = L.Mem.∈-filter⁻ ((_≤? N .clock ∸ 1 + sl) ∘ slot) {xs = genesisBlock ∷ blockHistory N} (c⊆fgb∷bhN b″∈c) .proj₂

                    ∣c₁+cc₃+cc₄∣≤2*∣cs₁∣+2*∣cs₂∣ :
                      ∣ c₁ ∣ + (∣ corruptBlocks c₃ ∣ + ∣ corruptBlocks c₄ ∣)
                      ≤
                      2 * length cs[b′ₜ+1:b*ₜ+1] + 2 * length cs[b*ₜ+1:Nₜ+sl]
                    ∣c₁+cc₃+cc₄∣≤2*∣cs₁∣+2*∣cs₂∣ = Nat.+-mono-≤ ∣c₁∣≤2*∣cs∣ ∣cc₃+cc₄∣≤2*∣cs∣

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
        π1 = bestChain⊆gb+blockHistory N₀↝⋆N hp lsp

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
