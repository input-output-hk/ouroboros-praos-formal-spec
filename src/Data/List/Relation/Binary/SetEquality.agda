module Data.List.Relation.Binary.SetEquality where

-- Set equality from BagAndSetEquality.
-- TODO: Perhaps use set theory library?

open import Level using (0ℓ)
open import Function.Base using (id; _∋_; _∘_)
open import Function.Related.Propositional using (K-refl; SK-sym; K-trans; ≡⇒)
open import Function.Bundles using (mk⇔)
open import Relation.Unary using (Pred)
open import Relation.Binary.Core using (Rel; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.Definitions using (_Respects_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool)
open import Data.List.Base using (List; []; _∷_; filter; deduplicate; cartesianProduct; reverse; length)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.All.Properties using (anti-mono)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (filter⁺′; Any-resp-⊆)
open import Data.List.Relation.Binary.Subset.Propositional.Properties.Ext using (cartesianProduct-⊆-Mono; deduplicate⁺′)
open import Data.List.Relation.Binary.BagAndSetEquality as BS hiding (set; Kind)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (↭-reverse; ↭-length)
open import Data.List.Membership.Propositional.Properties using (∈-deduplicate⁻; ∈-deduplicate⁺)
open import Class.DecEq using (DecEq; _≟_)

private variable
  A : Set
  xs ys : List A

infix 4 _≡ˢ_
_≡ˢ_ : Rel (List A) 0ℓ
_≡ˢ_ = _∼[ BS.set ]_

≡ˢ-refl = K-refl

≡ˢ-sym = SK-sym

≡ˢ-trans = K-trans

≡⇒≡ˢ : xs ≡ ys → xs ≡ˢ ys
≡⇒≡ˢ refl = ≡⇒ {k = BS.set} refl

⊆×⊇⇒≡ˢ : xs ⊆ ys → ys ⊆ xs → xs ≡ˢ ys
⊆×⊇⇒≡ˢ xs⊆ys ys⊆xs = mk⇔ xs⊆ys ys⊆xs

≡ˢ⇒⊆×⊇ : xs ≡ˢ ys → xs ⊆ ys × ys ⊆ xs
≡ˢ⇒⊆×⊇ p = to p , from p
  where open Function.Bundles.Equivalence

open import Relation.Unary using (Decidable) renaming (_⊆_ to _⋐_)
import Relation.Binary.Definitions as B

open import Relation.Unary using (_≐_)

filter-cong₂ : ∀ {p q} {P : Pred A p} {Q : Pred A q} (P? : Decidable P) (Q? : Decidable Q) → P ≐ Q → xs ≡ˢ ys → filter P? xs ≡ˢ filter Q? ys
filter-cong₂ P? Q? (P⋐Q , Q⋐P) xs≡ˢys with ≡ˢ⇒⊆×⊇ xs≡ˢys
... | xs⊆ys , ys⊆xs = ⊆×⊇⇒≡ˢ (filter⁺′ P? Q? P⋐Q xs⊆ys) (filter⁺′ Q? P? Q⋐P ys⊆xs)

filter-cong : ∀ {ℓ} {P : Pred A ℓ} {P? : Decidable P} → (filter P?) Preserves _≡ˢ_ ⟶ _≡ˢ_
filter-cong {P? = P?} = filter-cong₂ P? P? (id , id)

deduplicate-cong : ∀ ⦃ _ : DecEq A ⦄ → (deduplicate {A = A} _≟_) Preserves _≡ˢ_ ⟶ _≡ˢ_
deduplicate-cong xs≡ˢys with ≡ˢ⇒⊆×⊇ xs≡ˢys
... | xs⊆ys , ys⊆xs = ⊆×⊇⇒≡ˢ (deduplicate⁺′ xs⊆ys) (deduplicate⁺′ ys⊆xs)

deduplicate-id : ∀ ⦃ _ : DecEq A ⦄ (xs : List A) → deduplicate _≟_ xs ≡ˢ xs
deduplicate-id xs = ⊆×⊇⇒≡ˢ (∈-deduplicate⁻ _≟_ xs) (∈-deduplicate⁺ _≟_)

cartesianProduct-cong : (cartesianProduct {A = A} {B = A}) Preserves₂ _≡ˢ_ ⟶ _≡ˢ_ ⟶ _≡ˢ_
cartesianProduct-cong xs≡ˢxs′ ys≡ˢys′ =
  ⊆×⊇⇒≡ˢ
    (cartesianProduct-⊆-Mono (≡ˢ⇒⊆×⊇ xs≡ˢxs′ .proj₁) (≡ˢ⇒⊆×⊇ ys≡ˢys′ .proj₁))
    (cartesianProduct-⊆-Mono (≡ˢ⇒⊆×⊇ xs≡ˢxs′ .proj₂) (≡ˢ⇒⊆×⊇ ys≡ˢys′ .proj₂))

All-resp-≡ˢ : ∀ {ℓ} {P : Pred A ℓ} → (All P) Respects _≡ˢ_
All-resp-≡ˢ eq = anti-mono (≡ˢ⇒⊆×⊇ eq .proj₂)

Any-resp-≡ˢ : ∀ {ℓ} {P : Pred A ℓ} → (Any P) Respects _≡ˢ_
Any-resp-≡ˢ eq = Any-resp-⊆ (≡ˢ⇒⊆×⊇ eq .proj₁)

reverse-≡ˢ : ∀ (xs : List A) → reverse xs ≡ˢ xs
reverse-≡ˢ = BS.bag-=⇒ ∘ BS.↭⇒∼bag ∘ ↭-reverse

{--- TODO: Continue later perhaps...
-- NOTE: We cannot generalize `R` and `P` to be of any level since `Prelude.DecEq` requires `A` to be `Set` only.
-- We could fix this by using `Class.DecEq` but `Prelude.AssocList` uses `Prelude.DecEq` instead.
module Test {k} {A : Set} {xs ys : List A} ⦃ _ : DecEq A ⦄ where
  import Relation.Binary.Definitions as B
  open import Relation.Unary using (Decidable)
  import Function.Related.Propositional as Related
  import Function.Bundles as FB

  filter↔ : ∀ {P Q : Pred A 0ℓ} (xs : List A) (Q? : Decidable Q) → L.Any.Any P xs FB.↔ L.Any.Any P (L.filter Q? xs)

  filter-cong : ∀ {P : Pred A 0ℓ} (P? : Decidable P) → xs ∼[ k ] ys → L.filter P? xs ∼[ k ] L.filter P? ys
  filter-cong = {!!}

  deduplicate⁺∘deduplicate⁻ : ∀ {R : Rel A 0ℓ} {P : Pred A 0ℓ} (xs : List A) (R? : B.Decidable R) (resp : P B.Respects (flip R)) (p : L.Any.Any P (L.deduplicate R? xs)) → L.Any.deduplicate⁺ R? resp (L.Any.deduplicate⁻ R? p) ≡ p
  deduplicate⁺∘deduplicate⁻ (x ∷ xs) R? resp (here px) = refl
  deduplicate⁺∘deduplicate⁻ {R = R} {P = P} (x′ ∷ xs) R? resp (there p) = {!!}
    where
      _ : ∀ {x y} → R y x → P x → P y
      _ = resp
      lem0 : ∀ xs → L.Any.Any P (filter (λ x → ¬? (R? x′ x)) (L.deduplicate R? xs)) → L.Any.Any P (L.deduplicate R? xs)
      lem0 [] = id
      lem0 (x ∷ xs) prf with not (does (R? x′ x))
      ... | false = {!!}
      ... | true = {!!} -- use filter ∘ filter ≡ filter
      ih : L.Any.deduplicate⁺ R? resp (L.Any.deduplicate⁻ R? (lem0 xs p)) ≡ lem0 xs p
      ih = deduplicate⁺∘deduplicate⁻ xs R? resp (lem0 xs p)

  deduplicate⁻∘deduplicate⁺ : ∀ {R : Rel A 0ℓ} {P : Pred A 0ℓ} (xs : List A) (R? : B.Decidable R) (resp : P B.Respects (flip R)) (p : L.Any.Any P xs) → L.Any.deduplicate⁻ R? (L.Any.deduplicate⁺ R? resp p) ≡ p
  deduplicate⁻∘deduplicate⁺ = {!!}

  deduplicate↔ : ∀ {R : Rel A 0ℓ} {P : Pred A 0ℓ} (xs : List A) (R? : B.Decidable R) → P B.Respects (flip R) → L.Any.Any P xs FB.↔ L.Any.Any P (L.deduplicate R? xs)
  deduplicate↔ xs R? pres = FB.mk↔ₛ′ (L.Any.deduplicate⁺ R? pres) (L.Any.deduplicate⁻ R?) (deduplicate⁺∘deduplicate⁻ xs R? pres) (deduplicate⁻∘deduplicate⁺ xs R? pres)

  deduplicate-cong : xs ∼[ k ] ys → L.deduplicate _≟_ xs ∼[ k ] L.deduplicate _≟_ ys
  deduplicate-cong xs≈ys {x} = begin
    x ∈ L.deduplicate _≟_ xs ↔⟨ (SK-sym $ deduplicate↔ xs _≟_ resp ) ⟩
    x ∈ xs                   ∼⟨ L.Any.Any-cong (↔⇒ ∘ \_ → K-refl) xs≈ys ⟩
    x ∈ ys                   ↔⟨ deduplicate↔ ys _≟_ resp ⟩
    x ∈ L.deduplicate _≟_ ys ∎
    where
      open Related.EquationalReasoning; open Related using (↔⇒)
      resp : (_≡_ x) B.Respects (flip _≡_)
      resp p refl = sym p
----}
