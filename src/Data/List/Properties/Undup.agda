module Data.List.Properties.Undup where

open import Function.Base using (_∘_; _∘₂_; _$_; _∋_; const; case_of_)
open import Relation.Nullary.Decidable.Core using (yes; no; ¬?)
open import Relation.Nullary.Negation using (¬_; contradiction; contraposition)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Unary.Properties using (_∩?_)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_; _≗_; sym; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Nat using (suc; pred; _+_; _∸_; _<_; >-nonZero)
open import Data.Nat.Properties using (suc-pred)
open import Data.List using (List; []; _∷_; _++_; deduplicate; filter)
open import Data.List.Ext using (count; undup)
open import Data.List.Properties using (filter-all; filter-++; filter-reject)
open import Data.List.Properties.Ext using (filter-∘-×; count-accept-∷; count-reject-∷)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-∃++; ∈-deduplicate⁻; ∈-filter⁺; ∈-length)
open import Data.List.Membership.Propositional.Properties.Ext using (∈-undup⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All.Properties.Core using (¬Any⇒All¬; All¬⇒¬Any)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.Unique.Propositional.Properties using (Unique[x∷xs]⇒x∉xs)
open import Data.List.Relation.Unary.Unique.Propositional.Properties.Ext using (++⁻)
open import Data.List.Relation.Unary.Unique.DecPropositional.Properties.Ext using (undup-!)
open import Data.List.Relation.Binary.Disjoint.Propositional.Properties using (Disjoint⇒AllAll)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties.Ext using (Unique-resp-↭; ∈-∃↭; count-↭; filter-↭)
open import Class.DecEq using (DecEq)
open DecEq ⦃...⦄

module _ {a} {A : Set a} ⦃ _ : DecEq A ⦄ where

  open import Data.List.Membership.DecPropositional (_≟_ {A = A}) using (_∈?_)

  undup-[] : ∀ {xs : List A} → undup xs ≡ [] → xs ≡ []
  undup-[] {xs = []} = const refl
  undup-[] {xs = x ∷ xs} p with x ∈? xs
  ... | yes x∈xs = contradiction x∈xs x∉xs
    where
      xs≡[] : xs ≡ []
      xs≡[] = undup-[] {xs = xs} p

      x∉xs : x ∉ xs
      x∉xs rewrite xs≡[] = λ ()
  ... | no x∉xs = contradiction p λ ()

  opaque
    unfolding count

    count-filter : ∀ {ℓ} {P : Pred A ℓ} (P? : Decidable P) xs {x} →
      count P? (filter (¬? ∘ (x ≟_)) xs) ≡ count (P? ∩? (¬? ∘ (x ≟_))) xs
    count-filter P? xs {x} rewrite filter-∘-× P? (¬? ∘ (x ≟_)) xs = refl

  count-∩? : ∀ {ℓ} {P : Pred A ℓ} (P? : Decidable P) {xs x} → x ∈ xs → ∃[ ys ] undup xs ↭ x ∷ ys × count (P? ∩? (¬? ∘ (x ≟_))) (undup xs) ≡ count P? ys
  count-∩? P? {xs} {x} x∈xs with ∈-∃↭ (∈-undup⁺ x∈xs)
  ... | ys , udxs↭x∷ys = ys , udxs↭x∷ys , (begin
    count (P? ∩? (¬? ∘ (x ≟_))) (undup xs)     ≡⟨ count-filter _ _ ⟨
    count P? (filter (¬? ∘ (x ≟_)) (undup xs)) ≡⟨ count-↭ P? $ filter-↭ _ udxs↭x∷ys ⟩
    count P? (filter (¬? ∘ (x ≟_)) (x ∷ ys))   ≡⟨ cong (count P?) $ filter-reject (¬? ∘ (x ≟_)) (contradiction refl) ⟩
    count P? (filter (¬? ∘ (x ≟_)) ys)         ≡⟨ cong (count P?) $ filter-all _ (¬Any⇒All¬ _ x∉ys) ⟩
    count P? ys                                ∎)
    where
      [x∷ys]! : Unique (x ∷ ys)
      [x∷ys]! = Unique-resp-↭ udxs↭x∷ys $ undup-! {xs = xs}

      x∉ys : x ∉ ys
      x∉ys = Unique[x∷xs]⇒x∉xs [x∷ys]!

  count-∩?-yes : ∀ {ℓ} {P : Pred A ℓ} (P? : Decidable P) {xs x} → x ∈ xs → P x → count (P? ∩? (¬? ∘ (x ≟_))) (undup xs) ≡ pred (count P? (undup xs))
  count-∩?-yes P? {xs} {x} x∈xs Px with count-∩? P? {xs} {x} x∈xs
  ... | ys , udxs↭x∷ys , eq = begin
    count (P? ∩? (¬? ∘ (x ≟_))) (undup xs)     ≡⟨ eq ⟩
    count P? ys                                ≡⟨⟩
    pred (suc (count P? ys))                   ≡⟨ cong pred $ sym (count-accept-∷ _ Px) ⟩
    pred (count P? (x ∷ ys))                   ≡⟨ cong pred $ sym (count-↭ P? udxs↭x∷ys) ⟩
    pred (count P? (undup xs))                 ∎

  count-∩?-no : ∀ {ℓ} {P : Pred A ℓ} (P? : Decidable P) {xs x} → x ∈ xs → ¬ P x → count (P? ∩? (¬? ∘ (x ≟_))) (undup xs) ≡ count P? (undup xs)
  count-∩?-no P? {xs} {x} x∈xs ¬Px with count-∩? P? {xs} {x} x∈xs
  ... | ys , udxs↭x∷ys , eq = begin
    count (P? ∩? (¬? ∘ (x ≟_))) (undup xs)     ≡⟨ eq ⟩
    count P? ys                                ≡⟨ count-reject-∷ _ ¬Px ⟨
    count P? (x ∷ ys)                          ≡⟨ count-↭ P? udxs↭x∷ys ⟨
    count P? (undup xs)                        ∎

  count-undup : ∀ {ℓ} {P : Pred A ℓ} (P? : Decidable P) → count P? ∘ undup ≗ count P? ∘ deduplicate _≟_
  count-undup _ [] = refl
  count-undup {P = P} P? (x ∷ xs) with x ∈? xs
  ... | yes x∈xs = (case P? x of λ where
    (yes Px) → begin
      count P? (undup xs)                                      ≡⟨ suc-pred (count P? (undup xs)) ⦃ >-nonZero (cnt>0 Px)⦄ ⟨
      suc (pred (count P? (undup xs)))                         ≡⟨ cong suc $ sym (count-∩?-yes P? x∈xs Px) ⟩
      1 + count (P? ∩? (¬? ∘ (x ≟_))) (undup xs)               ≡⟨ cong suc (count-undup (P? ∩? (¬? ∘ (x ≟_))) _) ⟩
      1 + count (P? ∩? (¬? ∘ (x ≟_))) (deduplicate _≟_ xs)     ≡⟨ cong suc (sym $ count-filter _ _) ⟩
      1 + count P? (filter (¬? ∘ (x ≟_)) (deduplicate _≟_ xs)) ≡⟨ count-accept-∷ _ Px ⟨
      count P? (x ∷ filter (¬? ∘ (x ≟_)) (deduplicate _≟_ xs)) ∎
    (no ¬Px) → begin
      count P? (undup xs)                                      ≡⟨ count-∩?-no P? x∈xs ¬Px ⟨
      count (P? ∩? (¬? ∘ (x ≟_))) (undup xs)                   ≡⟨ count-undup (P? ∩? (¬? ∘ (x ≟_))) _ ⟩
      count (P? ∩? (¬? ∘ (x ≟_))) (deduplicate _≟_ xs)         ≡⟨ count-filter _ _ ⟨
      count P? (filter (¬? ∘ (x ≟_)) (deduplicate _≟_ xs))     ≡⟨ count-reject-∷ _ ¬Px ⟨
      count P? (x ∷ filter (¬? ∘ (x ≟_)) (deduplicate _≟_ xs)) ∎)
    where
      opaque
        unfolding count

        cnt>0 : P x → 0 < count P? (undup xs)
        cnt>0 Px = ∈-length $ ∈-filter⁺ P? (∈-undup⁺ x∈xs) Px
  ... | no x∉xs with x∉dxs ← contraposition (∈-deduplicate⁻ _≟_ _) x∉xs | P? x
  ... |   yes Px = begin
    count P? (x ∷ undup xs)                                   ≡⟨ count-accept-∷ _ Px ⟩
    1 + count P? (undup xs)                                   ≡⟨ cong suc (count-undup P? xs) ⟩
    1 + count P? (deduplicate _≟_ xs)                         ≡⟨ count-accept-∷ _ Px ⟨
    count P? (x ∷ deduplicate _≟_ xs)                         ≡⟨ cong (count P? ∘ (x ∷_)) $ filter-all _ (¬Any⇒All¬ _ x∉dxs) ⟨
    count P? (x ∷ filter (¬? ∘ (x ≟_)) (deduplicate _≟_ xs)) ∎
  ... |   no ¬Px = begin
    count P? (x ∷ undup xs)                                   ≡⟨ count-reject-∷ _ ¬Px ⟩
    count P? (undup xs)                                       ≡⟨ count-undup P? xs ⟩
    count P? (deduplicate _≟_ xs)                             ≡⟨ count-reject-∷ _ ¬Px ⟨
    count P? (x ∷ deduplicate _≟_ xs)                         ≡⟨ cong (count P? ∘ (x ∷_)) $ filter-all _ (¬Any⇒All¬ _ x∉dxs) ⟨
    count P? (x ∷ filter (¬? ∘ (x ≟_)) (deduplicate _≟_ xs)) ∎
