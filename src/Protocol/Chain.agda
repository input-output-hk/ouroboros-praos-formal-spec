open import Protocol.Prelude using (Default)
open import Protocol.Params using (Params)
open import Protocol.Crypto using (Hashable)
open import Protocol.Block using (Block)

module Protocol.Chain
  ⦃ params : _ ⦄ (open Params params)
  ⦃ _ : Hashable Block ⦄
  ⦃ _ : Default Block ⦄
  where

open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot)
open import Protocol.Block ⦃ params ⦄ hiding (Block)
open Hashable ⦃ ... ⦄
open import Data.List.Relation.Binary.Suffix.Heterogeneous using (Suffix; here; there; _++ˢ_)
open import Data.List.Relation.Binary.Suffix.Heterogeneous.Properties using (++⁺; suffix?)
open import Data.List.Relation.Binary.Suffix.Homogeneous.Properties using (isPreorder)
open import Relation.Binary.Definitions using (Reflexive; Transitive)
open import Relation.Binary.Structures using (IsPreorder)
open import Relation.Binary.PropositionalEquality.Properties renaming (isPreorder to ≡-isPreorder)
open import Relation.Binary.Bundles using (Preorder)
import Relation.Binary.Reasoning.Preorder as ≲-Reasoning
open import Relation.Binary.Reasoning.Syntax
open import Data.List.Relation.Binary.Pointwise as Pointwise using (Pointwise; ≡⇒Pointwise-≡; Pointwise-≡⇒≡)
open import Data.List.Properties.Ext using (≢[]⇒∷)
open import Data.List.Membership.Propositional.Properties.Ext using (x∈x∷xs)

genesisBlock : Block
genesisBlock = it .def

Chain : Type
Chain = List Block

tip : Chain → Block
tip []      = genesisBlock
tip (b ∷ _) = b

CorrectBlocks : Pred Chain _
CorrectBlocks = L.All.All CorrectBlock

prune : Slot → Chain → Chain
prune sl c = filter ((_≤? sl) ∘ slot) c

_⪯_ : Rel Chain _
_⪯_ = Suffix _≡_

⪯-isPreorder : IsPreorder (Pointwise _≡_) _⪯_
⪯-isPreorder = isPreorder ≡-isPreorder

⪯-preorder : Preorder _ _ _
⪯-preorder = record
  { isPreorder = ⪯-isPreorder
  }

⪯-refl : Reflexive _⪯_
⪯-refl = PO.reflexive (≡⇒Pointwise-≡ refl)
  where module PO = IsPreorder ⪯-isPreorder

⪯-trans : Transitive _⪯_
⪯-trans = PO.trans
  where module PO = IsPreorder ⪯-isPreorder

module ⪯-Reasoning where

  private module Base = ≲-Reasoning ⪯-preorder

  open Base public
    hiding (step-≈; step-≈˘; step-≈-⟩; step-≈-⟨; step-≲; step-∼)
    renaming (≲-go to ⪯-go; ≈-go to ≋-go)

  open ≲-syntax _IsRelatedTo_ _IsRelatedTo_ ⪯-go public
  open ≋-syntax _IsRelatedTo_ _IsRelatedTo_ ≋-go public

[]⪯ : ∀ {c : Chain} → [] ⪯ c
[]⪯ {[]}    = ⪯-refl
[]⪯ {b ∷ c} = there ([]⪯ {c})

⪯-++ : ∀ (c₁ c₂ : Chain) → c₁ ⪯ (c₂ ++ c₁)
⪯-++ _ c₂ = c₂ ++ˢ ⪯-refl

module _ where

  open import Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.Ext using (Suffix⇒Sublist)
  import Data.List.Relation.Binary.Subset.Setoid.Properties as Subset
  open import Relation.Binary.PropositionalEquality.Properties using (setoid)

  ⪯⇒⊆ˢ : ∀ {c₁ c₂ : Chain} → c₁ ⪯ c₂ → c₁ ⊆ˢ c₂
  ⪯⇒⊆ˢ = Subset.Sublist⇒Subset (setoid _) ∘ Suffix⇒Sublist _≡_

open import Function.Bundles using (_⇔_; mk⇔; Equivalence)

⪯∷⇔≡⊎⪯ : ∀ {c₁ c₂ : Chain} {b : Block} → c₁ ⪯ (b ∷ c₂) ⇔ (c₁ ≡ b ∷ c₂ ⊎ c₁ ⪯ c₂)
⪯∷⇔≡⊎⪯ {c₁} {c₂} {b} = mk⇔ to from
  where
    to : c₁ ⪯ (b ∷ c₂) → c₁ ≡ b ∷ c₂ ⊎ c₁ ⪯ c₂
    to (here c₁≐b∷c₂) = inj₁ (Pointwise-≡⇒≡ c₁≐b∷c₂)
    to (there c₁⪯c₂) = inj₂ c₁⪯c₂

    from : c₁ ≡ b ∷ c₂ ⊎ c₁ ⪯ c₂ → c₁ ⪯ (b ∷ c₂)
    from (inj₁ c₁≡b∷c₂) = here (≡⇒Pointwise-≡ c₁≡b∷c₂)
    from (inj₂ c₁⪯c₂) = there c₁⪯c₂

≢∷×⪯∷⇒⪯ : ∀ {c₁ c₂ : Chain} {b : Block} → c₁ ≢ b ∷ c₂ → c₁ ⪯ (b ∷ c₂) → c₁ ⪯ c₂
≢∷×⪯∷⇒⪯ c₁≢b∷c₂ (here c₁≐b∷c₂) = contradiction (Pointwise-≡⇒≡ c₁≐b∷c₂) c₁≢b∷c₂
≢∷×⪯∷⇒⪯ c₁≢b∷c₂ (there c₁⪯c₂) = c₁⪯c₂

⪯⇔∃ : ∀ {c₁ c₂ : Chain} → c₁ ⪯ c₂ ⇔ (∃[ c ] c ++ c₁ ≡ c₂)
⪯⇔∃ {c₁} {c₂} = mk⇔ to from
  where
    to : ∀ {c₁ c₂ : Chain} → c₁ ⪯ c₂ → ∃[ c ] c ++ c₁ ≡ c₂
    to (here c₁≐c₂) rewrite Pointwise-≡⇒≡ c₁≐c₂ = [] , refl
    to {c₁} {b ∷ c₂} (there c₁⪯c₂) with to c₁⪯c₂
    ... | c , c++c₁≡c₂ = b ∷ c , cong (b ∷_) c++c₁≡c₂

    from : ∀ {c₁ c₂ : Chain} → ∃[ c ] c ++ c₁ ≡ c₂ → c₁ ⪯ c₂
    from {c₁} {[]} (c , c++c₁≡[]) rewrite L.++-conicalʳ c c₁ c++c₁≡[] = []⪯
    from {c₁} {b ∷ c₂} (c , c++c₁≡b∷c₂) with c ≟ []
    ... | yes c≡[] = here $ ≡⇒Pointwise-≡ $ subst (λ ◆ → ◆ ++ c₁ ≡ b ∷ c₂) c≡[] c++c₁≡b∷c₂
    ... | no  c≢[] with ≢[]⇒∷ c≢[]
    ... |   (_ , c′ , c≡_∷c′) = there $ from (c′ , L.∷-injective (subst (λ ◆ → ◆ ++ c₁ ≡ b ∷ c₂) c≡_∷c′ c++c₁≡b∷c₂) .proj₂)

++-¬-⪯ : ∀ (c₁ : Chain) {c₂ : Chain} → c₂ ≢ [] → ¬ (c₂ ++ c₁) ⪯ c₁
++-¬-⪯ c₁ {[]}     []≢[]   = contradiction refl []≢[]
++-¬-⪯ c₁ {b ∷ c₂} b∷c₂≢[] b+c₂+c₁⪯c₁ with ⪯⇔∃ .Equivalence.to b+c₂+c₁⪯c₁
... | c′ , c′+b+c₂+c₁≡c₁ = contradiction (L.++-identityˡ-unique (c′ ++ b ∷ c₂) (sym $ trans (L.++-assoc c′ (b ∷ c₂) c₁) c′+b+c₂+c₁≡c₁)) (contraposition (L.++-conicalʳ c′ (b ∷ c₂)) λ ())

_⪯?_ : Decidable² _⪯_
c₁ ⪯? c₂ = suffix? _≟_ c₁ c₂

prune-⪯-trans : ∀ {c₁ c₂ c₃ : Chain} {sl : Slot} →
    prune sl c₁ ⪯ c₂
  → prune sl c₂ ⪯ c₃
  → prune sl c₁ ⪯ c₃
prune-⪯-trans {c₁} {c₂} {c₃} {sl} c₁↯sl⪯c₂ c₂↯sl⪯c₃
  with ⪯⇔∃ .Equivalence.to c₁↯sl⪯c₂ | ⪯⇔∃ .Equivalence.to c₂↯sl⪯c₃
...  | c₄ , c₄+c₁↯sl≡c₂              | c₅ , c₅++c₂↯sl≡c₃
  = ⪯⇔∃ .Equivalence.from (c₅ ++ prune sl c₄ , [c₅+c₄↯sl]+c₁↯sl≡c₃)
  where
    [c₅+c₄↯sl]+c₁↯sl≡c₃ : (c₅ ++ prune sl c₄) ++ prune sl c₁ ≡ c₃
    [c₅+c₄↯sl]+c₁↯sl≡c₃ = let open ≡-Reasoning in begin
      (c₅ ++ prune sl c₄) ++ prune sl c₁            ≡⟨ cong ((c₅ ++ prune sl c₄) ++_) (sym $ L.filter-idem _ c₁) ⟩
      (c₅ ++ prune sl c₄) ++ prune sl (prune sl c₁) ≡⟨ L.++-assoc c₅ _ _ ⟩
      c₅ ++ prune sl c₄ ++ prune sl (prune sl c₁)   ≡⟨ cong (c₅ ++_) (sym $ L.filter-++ _ c₄ _) ⟩
      c₅ ++ prune sl (c₄ ++ prune sl c₁)            ≡⟨ cong (λ ◆ → c₅ ++ prune sl ◆) c₄+c₁↯sl≡c₂ ⟩
      c₅ ++ prune sl c₂                             ≡⟨ c₅++c₂↯sl≡c₃ ⟩
      c₃                                            ∎

_⟵_ : Rel Block _
b ⟵ b′ = prev b ≡ hash b′

-- NOTE: Very similar to Data.List.Relation.Unary.Linked. Also, perhaps we can use Data.List.Relation.Unary.AllPairs.
ProperlyLinked : Chain → Type
ProperlyLinked []            = ⊥
ProperlyLinked (b ∷ [])      = b ≡ genesisBlock
ProperlyLinked (b ∷ b′ ∷ bs) = b ⟵ b′ × ProperlyLinked (b′ ∷ bs)

{-
instance

  ProperlyLinked? : ProperlyLinked ⁇¹
  ProperlyLinked? {[]}         .dec = no id
  ProperlyLinked? {[ b ]}      .dec = b ≟ genesisBlock
  ProperlyLinked? {b ∷ b′ ∷ c} .dec = ¿ b ⟵ b′ ¿ ×-dec ProperlyLinked? {b′ ∷ c} .dec
-}

ProperlyLinked⇒≢[] : ∀ {c : Chain} → ProperlyLinked c → c ≢ []
ProperlyLinked⇒≢[] {_ ∷ _} _ = λ ()

ProperlyLinked⇒gbIsHead : ∀ {c : Chain} → ProperlyLinked c → ∃[ c′ ] c′ L.∷ʳ genesisBlock ≡ c
ProperlyLinked⇒gbIsHead {[ b ]} b≡gb rewrite b≡gb = [] , refl
ProperlyLinked⇒gbIsHead {b ∷ b′ ∷ c} pl with ProperlyLinked⇒gbIsHead {b′ ∷ c} (pl .proj₂)
... | c′ , pl′ = b ∷ c′ , cong (b ∷_) pl′

ProperlyLinked-++⁻ : ∀ c {c′} → c′ ≢ [] → ProperlyLinked (c ++ c′) → ProperlyLinked c′
ProperlyLinked-++⁻ []           {_}      _  p2 = p2
ProperlyLinked-++⁻ [ _ ]        {[]}     p1 _  = contradiction refl p1
ProperlyLinked-++⁻ [ _ ]        {_ ∷ _}  _  p2 = p2 .proj₂
ProperlyLinked-++⁻ (b ∷ b′ ∷ c) {c′}     p1 p2 = ProperlyLinked-++⁻ (b′ ∷ c) {c′} p1 (p2 .proj₂)

-- NOTE: Similar to instantiating Data.List.Relation.Unary.Sorted.TotalOrder
-- with ≤-isTotalOrder from from Data.Nat.Properties, but in our case we need
-- < instead of ≤.
open import Data.List.Relation.Unary.Linked
DecreasingSlots = Linked _>ˢ_

open import Data.List.Relation.Unary.AllPairs
open import Data.List.Relation.Unary.Linked.Properties using (Linked⇒AllPairs; AllPairs⇒Linked)
open import Data.List.Relation.Unary.AllPairs.Properties.Ext using (++⁻)

++-DecreasingSlots : ∀ {c c′ : Chain} → DecreasingSlots (c ++ c′) → DecreasingSlots c × DecreasingSlots c′ × L.All.All (λ b → L.All.All (b >ˢ_) c′) c
++-DecreasingSlots {c} {c′} p with ++⁻ {xs = c} {ys = c′} $ Linked⇒AllPairs (λ {b b′ b″} → >ˢ-trans {b} {b′} {b″}) p
... | (p₁ , p₂ , p₃) = (AllPairs⇒Linked p₁ , AllPairs⇒Linked p₂ , p₃)

∷-DecreasingSlots : ∀ {c : Chain} {b : Block} → DecreasingSlots (b ∷ c) → DecreasingSlots c × L.All.All (b >ˢ_) c
∷-DecreasingSlots {c} {b} p with ++-DecreasingSlots {c = [ b ]} {c′ = c} p
... | (_ , p₂ , p₃) = p₂ , L.All.head p₃

DecreasingSlots⇒UniqueSlots : ∀ {c : Chain} → DecreasingSlots c → Unique (L.map slot c)
DecreasingSlots⇒UniqueSlots {[]}    _       = AllPairs.[]
DecreasingSlots⇒UniqueSlots {b ∷ c} ds[b∷c] with ∷-DecreasingSlots ds[b∷c]
... | ds[c] , b>ˢc = L.All.map⁺ (L.All.map Nat.>⇒≢ b>ˢc) AllPairs.∷ DecreasingSlots⇒UniqueSlots ds[c]

nonAdjacentBlocksDecreasingSlots : ∀ {cₕ cₘ cₜ : Chain} {b₁ b₂ : Block} →
    DecreasingSlots (cₕ ++ b₁ ∷ cₘ ++ b₂ ∷ cₜ)
  → b₁ >ˢ b₂
nonAdjacentBlocksDecreasingSlots {cₕ} {cₘ} {cₜ} {b₁} {b₂} dsπ =
    dsπ ∶
  DecreasingSlots (cₕ ++ b₁ ∷ cₘ ++ b₂ ∷ cₜ)
    |> proj₁ ∘ proj₂ ∘ ++-DecreasingSlots {cₕ} ∶
  DecreasingSlots (b₁ ∷ cₘ ++ b₂ ∷ cₜ)
    |> proj₂ ∘ ∷-DecreasingSlots ∶
  L.All.All (b₁ >ˢ_) (cₘ ++ b₂ ∷ cₜ)
    |> L.All.++⁻ʳ cₘ ∶
  L.All.All (b₁ >ˢ_) (b₂ ∷ cₜ)
    |> L.All.head ∶
  b₁ >ˢ b₂
  where open import Function.Reasoning

DecreasingSlots-∈ : ∀ {c c′ : Chain} {b b′ : Block} → DecreasingSlots (c ++ c′) → b ∈ c → b′ ∈ c′ → b >ˢ b′
DecreasingSlots-∈ {c} {c′} {b} {b′} ds[c++c′] b∈c b′∈c′ with L.Mem.∈-∃++ b∈c | L.Mem.∈-∃++ b′∈c′
... | cₕ , cₜ , c≡cₕ+b+cₜ | cₕ′ , cₜ′ , c′≡cₕ′+b′+cₜ′ = nonAdjacentBlocksDecreasingSlots ds
  where
    open ≡-Reasoning

    eq : (cₕ ++ b ∷ cₜ) ++ (cₕ′ ++ b′ ∷ cₜ′) ≡ cₕ ++ b ∷ (cₜ ++ cₕ′) ++ b′ ∷ cₜ′
    eq = begin
      (cₕ ++ b ∷ cₜ) ++ (cₕ′ ++ b′ ∷ cₜ′) ≡⟨ L.++-assoc _ (b ∷ cₜ) _ ⟩
      cₕ ++ b ∷ (cₜ ++ (cₕ′ ++ b′ ∷ cₜ′)) ≡⟨ cong ((cₕ ++_) ∘ (b ∷_)) (sym $ L.++-assoc cₜ cₕ′ _) ⟩
      cₕ ++ b ∷ (cₜ ++ cₕ′) ++ b′ ∷ cₜ′   ∎

    ds : DecreasingSlots (cₕ ++ b ∷ (cₜ ++ cₕ′) ++ b′ ∷ cₜ′)
    ds rewrite c≡cₕ+b+cₜ | c′≡cₕ′+b′+cₜ′ | sym eq = ds[c++c′]

opaque
  _✓ : Pred Chain 0ℓ
  c ✓ = CorrectBlocks c × ProperlyLinked c × DecreasingSlots c

  ✓⇒cb : ∀ {c : Chain} → c ✓ → CorrectBlocks c
  ✓⇒cb (cb , _ , _) = cb

  ✓⇒ds : ∀ {c : Chain} → c ✓ → DecreasingSlots c
  ✓⇒ds (_ , _ , ds) = ds

  ✓⇒≢[] : ∀ {c : Chain} → c ✓ → c ≢ []
  ✓⇒≢[] (_ , pl , _) = ProperlyLinked⇒≢[] pl

  ✓⇒gbIsHead : ∀ {c : Chain} → c ✓ → ∃[ c′ ] c′ L.∷ʳ genesisBlock ≡ c
  ✓⇒gbIsHead (_ , pl , _) = ProperlyLinked⇒gbIsHead pl

  ✓-∷ : ∀ {b b′ : Block} {c : Chain} → (CorrectBlock b × b ⟵ b′ × b >ˢ b′ × (b′ ∷ c) ✓) ⇔ (b ∷ b′ ∷ c) ✓
  ✓-∷ {b} {b′} {c} = mk⇔ to from
    where
      to : CorrectBlock b × b ⟵ b′ × b >ˢ b′ × (b′ ∷ c) ✓ → (b ∷ b′ ∷ c) ✓
      to (cbb , b⟵b′ , b>b′ , cb[b′∷c] , pl[b′∷c] , ds[b′∷c]) = cbb ∷ cb[b′∷c] , (b⟵b′ , pl[b′∷c]) , b>b′ ∷ ds[b′∷c]

      from : ∀ {c : Chain} → (b ∷ b′ ∷ c) ✓ → CorrectBlock b × b ⟵ b′ × b >ˢ b′ × (b′ ∷ c) ✓
      from {[]} (cbb ∷ cb[b′] , (b⟵b′ , b′≡gb) , b>b′ ∷ ds[b′]) = cbb , b⟵b′ , b>b′ , (cb[b′] , b′≡gb , ds[b′])
      from {b″ ∷ c′} (cbb ∷ cb[b′∷b″∷c′] , (b⟵b′ , pl[b′∷b″∷c′]) , b>b′ ∷ ds[b′∷b″∷c′]) = cbb , b⟵b′ , b>b′ , (cb[b′∷b″∷c′] , pl[b′∷b″∷c′] , ds[b′∷b″∷c′])

  open Function.Bundles.Equivalence using (from)

  ✓-++ʳ : ∀ {b : Block} {c c′ : Chain} → (c ++ b ∷ c′) ✓ → (b ∷ c′) ✓
  ✓-++ʳ {b} {[]}          {c′} p = p
  ✓-++ʳ {b} {[ b′ ]}      {c′} p = from ✓-∷ p .proj₂ .proj₂ .proj₂
  ✓-++ʳ {b} {b′ ∷ b″ ∷ c} {c′} p = ✓-++ʳ {b} {b″ ∷ c} {c′} (from ✓-∷ p .proj₂ .proj₂ .proj₂)

  ✓⇒gb⪯ : ∀ {c : Chain} → c ✓ → [ genesisBlock ] ⪯ c
  ✓⇒gb⪯ c✓ = let c′ , c′∷gb≡c = ✓⇒gbIsHead c✓ in subst ([ genesisBlock ] ⪯_) c′∷gb≡c $ ⪯-++ [ genesisBlock ] c′

  tip-∈ : ∀ {c : Chain} → c ✓ → tip c ∈ c
  tip-∈ {[]}    p = contradiction p $ contraposition (✓⇒≢[] {[]}) (contradiction refl)
  tip-∈ {b ∷ c} p = x∈x∷xs c

  pruneIdentity : ∀ {c : Chain} {b : Block} {sl : Slot} →
      b .slot ≤ sl
    → DecreasingSlots (b ∷ c)
    → prune sl (b ∷ c) ≡ b ∷ c
  pruneIdentity {c} {b} {sl} bₜ≤sl ds[b+c]
    rewrite
      L.filter-accept ((_≤? sl) ∘ slot) {x = b} {xs = c} bₜ≤sl
      = cong (b ∷_) (goal p)
    where
      p : L.All.All (_>ˢ_ b) c
      p = ∷-DecreasingSlots ds[b+c] .proj₂

      goal : ∀ {c : Chain} → L.All.All (_>ˢ_ b) c → prune sl c ≡ c
      goal {[]}      _    = refl
      goal {b′ ∷ c′} p    = let open ≡-Reasoning in begin
        prune sl (b′ ∷ c′)  ≡⟨ L.filter-accept ((_≤? sl) ∘ slot) {x = b′} {xs = c′} b′ₜ≤sl ⟩
        b′ ∷ prune sl c′    ≡⟨ cong (b′ ∷_) ih ⟩
        b′ ∷ c′             ∎
        where
          ih : prune sl c′ ≡ c′
          ih = goal {c′} (L.All.tail p)

          b′ₜ≤sl : b′ .slot ≤ sl
          b′ₜ≤sl = Nat.<⇒≤ $ Nat.<-≤-trans (L.All.head p) bₜ≤sl

  prune-⪯ : ∀ {c : Chain} (sl : Slot) → DecreasingSlots c → prune sl c ⪯ c
  prune-⪯ {[]}      _  _        = ⪯-refl
  prune-⪯ {b′ ∷ c′} sl ds[b′+c] with b′ .slot ≤? sl
  ... | yes b′ₜ≤sl rewrite pruneIdentity b′ₜ≤sl ds[b′+c] = ⪯-refl
  ... | no  b′ₜ≰sl rewrite L.filter-reject ((_≤? sl) ∘ slot) {x = b′} {xs = c′} b′ₜ≰sl = ⪯-trans ih (⪯-++ c′ [ b′ ])
    where
      ih : prune sl c′ ⪯ c′
      ih = prune-⪯ {c′} sl (∷-DecreasingSlots ds[b′+c] .proj₁)

{-# TERMINATING #-}
-- TODO: Prove termination using `WellFounded`.
chainFromBlock : Block → List Block → Chain
chainFromBlock b bs =
  if b == genesisBlock
    then
      [ b ]
    else
      if (b .prev == hash genesisBlock)
        then
          [ b ⨾ genesisBlock ]
        else
          case L.findᵇ ((b .prev ==_) ∘ hash) bs of λ where
            nothing   → []
            (just b′) →
              case chainFromBlock b′ (L.filterᵇ (not ∘ (_== b′)) bs) of
                λ where
                []          → []
                (b′′ ∷ bs′) → b ∷ b′′ ∷ bs′
{----
chainFromBlock′ : ℕ → Block → List Block → Chain
chainFromBlock′ 0       _ _  = []
chainFromBlock′ (suc n) b bs =
  if b == genesisBlock
    then
      [ b ]
    else
      if (b .prev == hash genesisBlock)
        then
          [ b ⨾ genesisBlock ]
        else
          case L.findᵇ ((b .prev ==_) ∘ hash) bs of λ where
            nothing   → []
            (just b′) →
              case chainFromBlock′ n b′ (L.filterᵇ (not ∘ (_== b′)) bs) of
                λ where
                []          → []
                (b′′ ∷ bs′) → b ∷ b′′ ∷ bs′

chainFromBlock : Block → List Block → Chain
chainFromBlock b bs = chainFromBlock′ (length bs) b bs
--------}

cfbStartsWithBlock : ∀ {b : Block} {bs : List Block} → chainFromBlock b bs ≢ [] → ∃[ bs′ ] chainFromBlock b bs ≡ b ∷ bs′
cfbStartsWithBlock {b} {bs} cfbbs≢[]
  with b == genesisBlock
... | true = [] , refl
... | false with ¿ b ⟵ genesisBlock ¿ᵇ
... |   true = [ genesisBlock ] , refl
... |   false with L.findᵇ (λ b″ → ¿ b ⟵ b″ ¿ᵇ) bs in eqf
... |     nothing = contradiction refl cfbbs≢[]
... |     just b′ with chainFromBlock b′ (L.filterᵇ (not ∘ (_== b′)) bs) in eqcfb
... |       [] = contradiction refl cfbbs≢[]
... |       b′′ ∷ bs′′ = b′′ ∷ bs′′ , refl
