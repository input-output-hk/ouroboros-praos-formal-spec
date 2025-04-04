{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled

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
open import Data.List.Relation.Binary.Pointwise as Pointwise using (Pointwise; ≡⇒Pointwise-≡; Pointwise-≡⇒≡)
open import Data.List.Properties.Ext using (≢[]⇒∷)

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

⪯-refl : Reflexive _⪯_
⪯-refl = PO.reflexive (≡⇒Pointwise-≡ refl)
  where module PO = IsPreorder ⪯-isPreorder

⪯-trans : Transitive _⪯_
⪯-trans = PO.trans
  where module PO = IsPreorder ⪯-isPreorder

[]⪯ : ∀ {c : Chain} → [] ⪯ c
[]⪯ {[]}    = ⪯-refl
[]⪯ {b ∷ c} = there ([]⪯ {c})

⪯-++ : ∀ (c₁ c₂ : Chain) → c₁ ⪯ (c₂ ++ c₁)
⪯-++ _ c₂ = c₂ ++ˢ ⪯-refl

open import Function.Bundles using (_⇔_; mk⇔)

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

_⪯?_ : Decidable² _⪯_
c₁ ⪯? c₂ = suffix? _≟_ c₁ c₂

prune-⪯-trans : ∀ {c₁ c₂ c₃ : Chain} {sl : Slot} →
    prune sl c₁ ⪯ c₂
  → prune sl c₂ ⪯ c₃
  → prune sl c₁ ⪯ c₃
prune-⪯-trans = {!!}

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

open import Data.List.Relation.Unary.Linked.Properties using (Linked⇒AllPairs; AllPairs⇒Linked)
open import Data.List.Relation.Unary.AllPairs.Properties.Ext using (++⁻)

++-DecreasingSlots : ∀ {c c′ : Chain} → DecreasingSlots (c ++ c′) → DecreasingSlots c × DecreasingSlots c′ × L.All.All (λ b → L.All.All (b >ˢ_) c′) c
++-DecreasingSlots {c} {c′} p with ++⁻ {xs = c} {ys = c′} $ Linked⇒AllPairs (λ {b b′ b″} → >ˢ-trans {b} {b′} {b″}) p
... | (p₁ , p₂ , p₃) = (AllPairs⇒Linked p₁ , AllPairs⇒Linked p₂ , p₃)

∷-DecreasingSlots : ∀ {c : Chain} {b : Block} → DecreasingSlots (b ∷ c) → DecreasingSlots c × L.All.All (b >ˢ_) c
∷-DecreasingSlots {c} {b} p with ++-DecreasingSlots {c = [ b ]} {c′ = c} p
... | (_ , p₂ , p₃) = p₂ , L.All.head p₃

opaque
  _✓ : Pred Chain 0ℓ
  c ✓ = CorrectBlocks c × ProperlyLinked c × DecreasingSlots c

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

  pruneIdentity : ∀ {c : Chain} {b : Block} {sl : Slot} →
      b .slot ≤ sl
    → DecreasingSlots (b ∷ c)
    → prune sl (b ∷ c) ≡ b ∷ c
  pruneIdentity = {!!}

  prune-⪯ : ∀ {c : Chain} (sl : Slot) → DecreasingSlots c → prune sl c ⪯ c
  prune-⪯ = {!!}

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
... | false with b .prev == hash genesisBlock
... |   true = [ genesisBlock ] , refl
... |   false with L.findᵇ ((b .prev ==_) ∘ hash) bs in eqf
... |     nothing = contradiction refl cfbbs≢[]
... |     just b′ with chainFromBlock b′ (L.filterᵇ (not ∘ (_== b′)) bs) in eqcfb
... |       [] = contradiction refl cfbbs≢[]
... |       b′′ ∷ bs′′ = b′′ ∷ bs′′ , refl
