module Data.List.Properties.Ext where

open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (+-identityʳ; +-suc; ≤⇒≯; m≤n⇒m<n∨m≡n; +-cancelˡ-≡; ≤-refl; m<m+n; <⇒≤)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_; module ≡-Reasoning)
open import Data.Maybe using (nothing)
open import Data.List using (List; []; [_]; _∷_; _∷ʳ_; _++_; map; filter; length; updateAt; _[_]%=_; lookup; findᵇ; find; upTo; downFrom; reverse; foldr; deduplicate; replicate; head)
open import Data.List.Ext using (ι; count; undup)
open import Data.List.Properties using (∷ʳ-injective; filter-++; filter-accept; filter-reject; ++-identityʳ; unfold-reverse; ++-cancelˡ; ∷-injectiveˡ; ∷-injectiveʳ; reverse-selfInverse; length-map; length-downFrom; length-reverse; filter-all; filter-none; reverse-++; ++-assoc)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-deduplicate⁻)
open import Data.List.Membership.Propositional.Properties.Ext using (∈-∷⁻; ∉-filter⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; tabulate) renaming (map to mapA)
open import Data.List.Relation.Unary.All.Properties using (∷ʳ⁺)
open import Data.List.Relation.Unary.All.Properties.Ext using (All-∁∅)
open import Relation.Unary using (Pred; Decidable; ∅; Empty)
open import Relation.Unary.Properties using (_∩?_; ∁?)
open import Relation.Nullary.Negation using (¬_; contradiction; contraposition)
open import Relation.Nullary.Decidable.Core using (does; yes; no; _×-dec_; ¬?)
open import Data.List.Relation.Unary.All.Properties.Core using (¬Any⇒All¬)
open import Level using (Level)
open import Function.Base using (_∘_; _$_; _∋_; const)
open import Relation.Binary.PropositionalEquality using (_≡_; _≗_; sym; cong; subst; module ≡-Reasoning)
open import Data.Fin using (Fin; cast) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (subst-is-cast)
open import Data.Fin.Properties.Ext using (suc-≢-injective)
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Class.DecEq using (DecEq)
open DecEq ⦃...⦄

private variable
  ℓ a : Level
  A : Set a
  x y : A
  xs ys zs ws : List A
  P Q : Pred A ℓ

-- the standard library version is strangely for f : A → A → A
foldr-preservesʳ' : ∀ {A B : Set} {P : B → Set} {f : A → B → B} →
  (∀ x {y} → P y → P (f x y)) → ∀ {e} → P e → ∀ xs → P (foldr f e xs)
foldr-preservesʳ' pres Pe []       = Pe
foldr-preservesʳ' pres Pe (_ ∷ xs) = pres _ (foldr-preservesʳ' pres Pe xs)

[]≢∷ʳ : [] ≢ xs ∷ʳ x
[]≢∷ʳ {xs = []} ()
[]≢∷ʳ {xs = _ ∷ _} ()

filter-∅ : ∀ {ℓ} {A : Set ℓ} (∅? : Decidable ∅) (xs : List A) → filter ∅? xs ≡ []
filter-∅ ∅? = filter-none ∅? ∘ All-∁∅

filter-Empty : ∀ {ℓ ℓ′} {A : Set ℓ} {P : Pred A ℓ′} (P? : Decidable P) → Empty P → ∀ (xs : List A) → filter P? xs ≡ []
filter-Empty {P = P} P? P≡∅ xs = filter-none P? {xs = xs} $ tabulate λ {x} _ → P≡∅ x

filter-∘-comm : (P? : Decidable P) (Q? : Decidable Q) → filter P? ∘ filter Q? ≗ filter Q? ∘ filter P?
filter-∘-comm P? Q? [] = refl
filter-∘-comm P? Q? (x ∷ xs) with ih ← filter-∘-comm P? Q? xs | does (P? x) in eqp | does (Q? x) in eqq
... | true  | true  rewrite eqp | eqq | ih = refl
... | true  | false rewrite eqq | ih       = refl
... | false | true  rewrite eqp | ih       = refl
... | false | false rewrite ih             = refl

filter-∘-× : (P? : Decidable P) (Q? : Decidable Q) → filter (P? ∩? Q?) ≗ filter P? ∘ filter Q?
filter-∘-× P? Q? [] = refl
filter-∘-× P? Q? (x ∷ xs) with ih ← filter-∘-× P? Q? xs | does (P? x) in eqp | does (Q? x) in eqq
... | true  | true  rewrite eqp | ih = refl
... | true  | false rewrite ih       = refl
... | false | true  rewrite eqp | ih = refl
... | false | false rewrite ih       = refl

filter-deduplicate-comm : ∀ ⦃ _ : DecEq A ⦄ {ℓ} {P : Pred A ℓ} {P? : Decidable P} → filter P? ∘ deduplicate _≟_ ≗ deduplicate  _≟_ ∘ filter P?
filter-deduplicate-comm [] = refl
filter-deduplicate-comm {P? = P?} (x ∷ xs) with P? x
... | yes Px rewrite filter-∘-comm P? (¬? ∘ _≟_ x) (deduplicate _≟_ xs) | filter-deduplicate-comm {P? = P?} xs = refl
... | no ¬Px rewrite filter-∘-comm P? (¬? ∘ _≟_ x) (deduplicate _≟_ xs) | filter-deduplicate-comm {P? = P?} xs = filter-all _ (¬Any⇒All¬ _ $ contraposition (∈-deduplicate⁻ _ _) (∉-filter⁺ xs ¬Px))

length-updateAt : ∀ xs k (f : A → A) → length (updateAt xs k f) ≡ length xs
length-updateAt (x ∷ xs) fzero    f = refl
length-updateAt (x ∷ xs) (fsuc k) f = cong suc (length-updateAt xs k f)

length-%= : ∀ {A : Set} xs k (f : A → A) → length (xs [ k ]%= f) ≡ length xs
length-%= = length-updateAt

updateAt-updates : ∀ {f : A → A} xs (i : Fin (length xs)) → lookup xs i ≡ x → lookup (updateAt xs i f) (cast (sym (length-updateAt xs i f)) i) ≡ f x
updateAt-updates {f = f} (x′ ∷ xs) fzero eq = cong f eq
updateAt-updates (x′ ∷ xs) (fsuc i) eq = updateAt-updates xs i eq

updateAt-minimal : ∀ {f : A → A} xs (i j : Fin (length xs)) → i ≢ j → lookup xs i ≡ x → lookup (updateAt xs j f) (cast (sym (length-updateAt xs j f)) i) ≡ x
updateAt-minimal (x ∷ xs) fzero fzero i≢j = contradiction refl i≢j
updateAt-minimal (x ∷ xs) fzero (fsuc j) i≢j refl = refl
updateAt-minimal {f = f} (x ∷ _ ∷ xs) (fsuc i) fzero i≢j refl
  rewrite
    sym $ subst-is-cast (sym (length-updateAt (x ∷ xs) fzero f)) i
    = refl
updateAt-minimal (x ∷ xs) (fsuc i) (fsuc j) i≢j refl = updateAt-minimal xs i j (suc-≢-injective i≢j) refl

lookup∘updateAt : ∀ (xs : List A) (i : Fin (length xs)) {f : A → A} →
                  lookup (updateAt xs i f) (cast (sym (length-updateAt xs i f)) i) ≡ f (lookup xs i)
lookup∘updateAt xs i = updateAt-updates xs i refl

lookup∘updateAt′ : ∀ (xs : List A) (i j : Fin (length xs)) {f : A → A} →
                   i ≢ j →
                   lookup (updateAt xs j f) (cast (sym (length-updateAt xs j f)) i) ≡ lookup xs i
lookup∘updateAt′ xs i j i≢j = updateAt-minimal xs i j i≢j refl

updateAt-id-local : ∀ (xs : List A) (i : Fin (length xs)) {f : A → A} →
                    f (lookup xs i) ≡ lookup xs i → updateAt xs i f ≡ xs
updateAt-id-local [] () eq
updateAt-id-local (x ∷ xs) fzero eq = cong (_∷ xs) eq
updateAt-id-local (x ∷ xs) (fsuc i) eq = cong (x ∷_) (updateAt-id-local xs i eq)

Px-findᵇ⁻ : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {P : A → Bool} {xs : List A} {x : A} → findᵇ P xs ≡ just x → P x ≡ true
Px-findᵇ⁻ {P = P} {xs = x′ ∷ xs′} {x = x} eqf with x ≟ x′
... | yes x≡x′ with P x′ in Px′
... |   false = Px-findᵇ⁻ {P = P} {xs = xs′} eqf
... |   true  = subst _ (sym x≡x′) Px′
Px-findᵇ⁻ {P = P} {xs = x′ ∷ xs′} eqf
    | no x≢x′ with P x′
... |   false = Px-findᵇ⁻ {P = P} {xs = xs′} eqf
... |   true  = contradiction (just-injective eqf) (contraposition sym x≢x′)

module _ {a p} {A : Set a} ⦃ _ : DecEq A ⦄ {P : Pred A p} (P? : Decidable P) where

  Px-find⁻ : ∀ {xs : List A} {x : A} → find P? xs ≡ just x → P x
  Px-find⁻ {xs = []} eqf = contradiction eqf λ ()
  Px-find⁻ {xs = x′ ∷ xs′} eqf with P? x′
  ... | yes Px′ = subst _ (just-injective eqf) Px′
  ... | no ¬Px′ = Px-find⁻ {xs = xs′} eqf

∷≢[] : x ∷ xs ≢ (List A ∋ [])
∷≢[] ()

≢[]⇒∷ : xs ≢ [] → ∃[ y ] ∃[ ys ] xs ≡ y ∷ ys
≢[]⇒∷ {xs = []}     p = contradiction refl p
≢[]⇒∷ {xs = x ∷ xs} p = x , xs , refl

length0⇒[] : ∀ {a} {A : Set a} {xs : List A} → length xs ≡ 0 → xs ≡ []
length0⇒[] {xs = []} p = refl

all-reverse : ∀ {ℓ ℓ′} {A : Set ℓ} {P : Pred A ℓ′} (P? : Decidable P) {xs : List A} → All P xs → All P (reverse xs)
all-reverse P? {xs = []} All.[] = All.[]
all-reverse P? {xs = x ∷ xs} (Px All.∷ Pxs) rewrite reverse-++ [ x ] xs = ∷ʳ⁺ (all-reverse P?{xs = xs} Pxs) Px

module _ (P? : Decidable P) where

 filter-rejectʳ : ∀ {x xs} → ¬ P x → filter P? (xs ∷ʳ x) ≡ filter P? xs
 filter-rejectʳ {x} {xs} ¬Px rewrite filter-++ P? xs [ x ] | filter-reject P? {x} {[]} ¬Px = ++-identityʳ _

 filter-acceptʳ : ∀ {x xs} → P x → filter P? (xs ∷ʳ x) ≡ filter P? xs ∷ʳ x
 filter-acceptʳ {x} {xs} ¬Px rewrite filter-++ P? xs [ x ] | filter-accept P? {x} {[]} ¬Px = refl

 find-∃ : ∀ {x xs} → find P? xs ≡ just x → ∃[ ys ] ∃[ zs ] ys ++ [ x ] ++ zs ≡ xs × P x × All (¬_ ∘ P) ys
 find-∃ {x} {x′ ∷ xs} p with P? x′
 ... | yes Px′ = [] , xs , subst (λ ◆ → x ∷ xs ≡ ◆ ∷ xs) (sym $ just-injective p) refl , subst P (just-injective p) Px′ , All.[]
 ... | no ¬Px′ with find-∃ {x} {xs} p
 ... |   (ys′ , zs′ , ys′+x+zs′≡xs , Px , ¬Pys′) = x′ ∷ ys′ , zs′ , cong (x′ ∷_) ys′+x+zs′≡xs , Px , ¬Px′ All.∷ ¬Pys′

 find-∃ʳ : ∀ {x xs} → find P? (reverse xs) ≡ just x → ∃[ ys ] ∃[ zs ] ys ++ [ x ] ++ zs ≡ xs × P x × All (¬_ ∘ P) zs
 find-∃ʳ {x} {xs} p with find-∃ {xs = reverse xs} p
 ... | ys , zs , ys+x+zs≡rev[xs] , Px , ¬Pys = reverse zs , reverse ys , eq , Px , all-reverse (¬? ∘ P?) ¬Pys
   where
     eq : reverse zs ++ x ∷ reverse ys ≡ xs
     eq rewrite sym $ reverse-++ ys [ x ] | sym $ reverse-++ (ys ∷ʳ x) zs | ++-assoc ys [ x ] zs = subst (reverse (ys ++ x ∷ zs) ≡_) (reverse-selfInverse refl) (cong reverse ys+x+zs≡rev[xs])

 open import Data.List.Relation.Unary.Any using (Any; here; there)

 find-∄ : ∀ {xs} → find P? xs ≡ nothing → ¬ Any P xs
 find-∄ {[]} _ = λ ()
 find-∄ {x ∷ xs} p with P? x
 ... | yes Px = contradiction p λ ()
 ... | no ¬Px = λ{ (here Px) → contradiction Px ¬Px ; (there q) → contradiction q (find-∄ {xs} p) }

++-injective : ∀ {xs ys zs ws : List A} → length xs ≡ length zs → xs ++ ys ≡ zs ++ ws → xs ≡ zs × ys ≡ ws
++-injective {xs = []} {zs = zs} p q rewrite length0⇒[] {xs = zs} (sym p) = refl , q
++-injective {xs = x ∷ xs} {ys = ys} {zs = z ∷ zs} {ws = ws} p q with ++-injective {xs = xs} {ys = ys} {zs = zs} {ws = ws} (+-cancelˡ-≡ 1 _ _ p) (∷-injectiveʳ q)
... | p1 , p2 rewrite ∷-injectiveˡ q | p1 = refl , p2

-- NOTE: Good to have, but not needed for now.
{--
module _ ⦃ _ : DecEq A ⦄ where

  open import Data.List.Membership.DecPropositional (_≟_ {A = A}) using (_∈?_)

  deduplicate-++ : ∀ (xs ys : List A) → deduplicate _≟_ (xs ++ ys) ≡ deduplicate _≟_ xs ++ filter (_∈? xs) (deduplicate _≟_ ys)
  deduplicate-++ = {!!}
--}

------------------------------------------------------------------------
-- ι

ι-++ : ∀ (n m₁ m₂ : ℕ) → ι n (m₁ + m₂) ≡ ι n m₁ ++ ι (n + m₁) m₂
ι-++ n zero     m₂ rewrite +-identityʳ n = refl
ι-++ n (suc m₁) m₂ rewrite ι-++ (suc n) m₁ m₂ | +-suc n m₁ = refl

∈-ι⁺ : ∀ {n m i} → n ≤ i → i < n + m → i ∈ ι n m
∈-ι⁺ {n} {zero}  {i} n≤i i<n+0 rewrite +-identityʳ n = contradiction i<n+0 (≤⇒≯ n≤i)
∈-ι⁺ {n} {suc m} {i} n≤i i<n+sm with m≤n⇒m<n∨m≡n n≤i
... | inj₁ n<i = there $ ∈-ι⁺ {suc n} {m} {i} n<i (subst (i <_) (+-suc n m) i<n+sm)
... | inj₂ n≡i = here $ sym n≡i

∈-ι⁻ : ∀ {n m i} → i ∈ ι n m → n ≤ i × i < n + m
∈-ι⁻ {n} {suc m} {i} p with ∈-∷⁻ p
... | inj₁ i≡n rewrite i≡n = ≤-refl , m<m+n _ (s≤s z≤n)
... | inj₂ q with ∈-ι⁻ {suc n} {m} {i} q
... |  q₁ , q₂ = <⇒≤ q₁ , subst (suc i ≤_) (sym $ +-suc n m) q₂

ι-reverse : ∀ n m → reverse (ι n m) ≡ map (_+ n) (downFrom m)
ι-reverse n zero    = refl
ι-reverse n (suc m) = begin
  reverse (ι n (suc m))             ≡⟨⟩
  reverse (n ∷ ι (suc n) m)         ≡⟨ unfold-reverse n (ι (suc n) m) ⟩
  reverse (ι (suc n) m) ∷ʳ n        ≡⟨ (cong (_∷ʳ n) $ ι-reverse (suc n) m) ⟩
  map (_+ suc n) (downFrom m) ∷ʳ n  ≡⟨ lemma n m ⟩
  (m + n) ∷ map (_+ n) (downFrom m) ≡⟨⟩
  map (_+ n) (downFrom (suc m))     ∎
  where
    open ≡-Reasoning
    lemma : ∀ n m → map (_+ suc n) (downFrom m) ∷ʳ n ≡ m + n ∷ map (_+ n) (downFrom m)
    lemma n zero = refl
    lemma n (suc m) = begin
      map (_+ suc n) (downFrom (suc m)) ∷ʳ n       ≡⟨⟩
      m + suc n ∷ map (_+ suc n) (downFrom m) ∷ʳ n ≡⟨ cong (m + suc n ∷_) (lemma n m) ⟩
      m + suc n ∷ m + n ∷ map (_+ n) (downFrom m)  ≡⟨⟩
      m + suc n ∷ map (_+ n) (downFrom (suc m))    ≡⟨ cong (_∷ map (_+ n) (downFrom (suc m))) (+-suc m n) ⟩
      suc m + n ∷ map (_+ n) (downFrom (suc m))    ∎

ι-reverseʳ : ∀ n m → ι n m ≡ reverse (map (_+ n) (downFrom m))
ι-reverseʳ n m = sym $ reverse-selfInverse {x = ι n m} {y = map (_+ n) (downFrom m)} (ι-reverse n m)

ι-length : ∀ n m → length (ι n m) ≡ m
ι-length n m
  rewrite
    ι-reverseʳ n m
  | length-reverse (map (_+ n) (downFrom m))
  | length-map (_+ n) (downFrom m)
  | length-downFrom m = refl

ι-∷ʳ : ∀ n m → ι n m ∷ʳ (n + m) ≡ ι n (suc m)
ι-∷ʳ n 0       rewrite +-identityʳ n              = refl
ι-∷ʳ n (suc m) rewrite +-suc n m | ι-∷ʳ (suc n) m = refl

------------------------------------------------------------------------
-- count

open import Data.Product.Base using (proj₂)
open import Relation.Unary using (∁)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Nullary.Decidable using (dec-yes)
open import Data.List.Properties using (length-++)
open import Data.Nat.Properties.Ext using (suc≗+1)

module _ (P? : Decidable P) where

  opaque

    unfolding count

    count-accept-∷ : ∀ {x xs} → P x → count P? (x ∷ xs) ≡ suc (count P? xs)
    count-accept-∷ {x} {xs} Px rewrite filter-accept P? {x} {xs} Px = refl

    count-reject-∷ : ∀ {x xs} → ¬ P x → count P? (x ∷ xs) ≡ count P? xs
    count-reject-∷ {x} {xs} ¬Px rewrite filter-reject P? {x} {xs} ¬Px = refl

    count-accept-∷ʳ : ∀ {x xs} → P x → count P? (xs ∷ʳ x) ≡ suc (count P? xs)
    count-accept-∷ʳ {x} {xs} Px rewrite filter-++ P? xs [ x ] with P? x
    ... | yes _ rewrite length-++ (filter P? xs) {[ x ]} = sym $ suc≗+1 (count P? xs)
    ... | no ¬Px = contradiction Px ¬Px

    count-reject-∷ʳ : ∀ {x xs} → ¬ P x → count P? (xs ∷ʳ x) ≡ count P? xs
    count-reject-∷ʳ {x} {xs} ¬Px rewrite filter-++ P? xs [ x ] with P? x
    ... | yes Px = contradiction Px ¬Px
    ... | no _ rewrite ++-identityʳ (filter P? xs) = refl

    count-Empty : Empty P → ∀ xs → count P? xs ≡ 0
    count-Empty P≡∅ xs rewrite filter-Empty P? P≡∅ xs = refl

    count-none : ∀ {xs} → count P? xs ≡ 0 → All (∁ P) xs
    count-none {[]} _ = All.[]
    count-none {x ∷ xs} p with P? x
    ... | yes Px = contradiction p λ ()
    ... | no ¬Px = ¬Px All.∷ count-none {xs} p

    count-partition : ∀ xs → count P? xs + count (∁? P?) xs ≡ length xs
    count-partition [] = refl
    count-partition (x ∷ xs) with P? x
    ... | yes Px = cong suc (count-partition xs)
    ... | no ¬Px rewrite +-suc (count P? xs) (count (∁? P?) xs) = cong suc (count-partition xs)

replicate-map-const : ∀ {a b} {A : Set a} {B : Set b} {xs : List A} {x : B} {n : ℕ} → replicate (length xs) x ≡ map (const x) xs
replicate-map-const {xs = []}              = refl
replicate-map-const {xs = x′ ∷ xs} {x} {n} = cong (x ∷_) (replicate-map-const {xs = xs} {x} {n})

head-++ : ∀ {a} {A : Set a} {x : A} {xs ys : List A} → head xs ≡ just x → head (xs ++ ys) ≡ just x
head-++ {xs = x ∷ xs} refl = refl

map-[] : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {xs : List A} → map f xs ≡ [] → xs ≡ []
map-[] {xs = []} _ = refl
map-[] {xs = x ∷ xs} p = contradiction p λ ()
