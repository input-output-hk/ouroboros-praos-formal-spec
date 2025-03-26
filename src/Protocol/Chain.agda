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
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)

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
_⪯_ = Prefix (λ _ _ → ⊤)

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

opaque
  _✓ : Pred Chain 0ℓ
  c ✓ = CorrectBlocks c × ProperlyLinked c × DecreasingSlots c

  ✓⇒≢[] : ∀ {c : Chain} → c ✓ → c ≢ []
  ✓⇒≢[] (_ , pl , _) = ProperlyLinked⇒≢[] pl

  ✓⇒gbIsHead : ∀ {c : Chain} → c ✓ → ∃[ c′ ] c′ L.∷ʳ genesisBlock ≡ c
  ✓⇒gbIsHead (_ , pl , _) = ProperlyLinked⇒gbIsHead pl

  open import Function.Bundles using (_⇔_; mk⇔)

  ✓-∷ : ∀ {b b′ : Block} {c : Chain} → (CorrectBlock b × b ⟵ b′ × b >ˢ b′ × (b′ ∷ c) ✓) ⇔ (b ∷ b′ ∷ c) ✓
  ✓-∷ {b} {b′} {c} = mk⇔ to from
    where
      to : CorrectBlock b × b ⟵ b′ × b >ˢ b′ × (b′ ∷ c) ✓ → (b ∷ b′ ∷ c) ✓
      to (cbb , b⟵b′ , b>b′ , cb[b′∷c] , pl[b′∷c] , ds[b′∷c]) = cbb ∷ cb[b′∷c] , (b⟵b′ , pl[b′∷c]) , b>b′ ∷ ds[b′∷c]

      from : ∀ {c : Chain} → (b ∷ b′ ∷ c) ✓ → CorrectBlock b × b ⟵ b′ × b >ˢ b′ × (b′ ∷ c) ✓
      from {[]} (cbb ∷ cb[b′] , (b⟵b′ , b′≡gb) , b>b′ ∷ ds[b′]) = cbb , b⟵b′ , b>b′ , (cb[b′] , b′≡gb , ds[b′])
      from {b″ ∷ c′} (cbb ∷ cb[b′∷b″∷c′] , (b⟵b′ , pl[b′∷b″∷c′]) , b>b′ ∷ ds[b′∷b″∷c′]) = cbb , b⟵b′ , b>b′ , (cb[b′∷b″∷c′] , pl[b′∷b″∷c′] , ds[b′∷b″∷c′])

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
