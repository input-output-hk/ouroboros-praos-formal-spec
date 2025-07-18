module Data.List.Membership.Propositional.Properties.Ext where

open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Bool using (Bool; false; true)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; findᵇ; find; filter; deduplicate; _∷ʳ_; [_])
open import Data.List.Ext using (undup)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (++-comm)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Unary using (Pred; Decidable)
open import Function.Base using (case_of_)
open import Class.DecEq using (DecEq)
open DecEq ⦃...⦄

x∈x∷xs : ∀ {a} {A : Set a} (xs : List A) {x} → x ∈ x ∷ xs
x∈x∷xs xs = here refl

-- NOTE: This seems to be an instance of ++-∈⇔ .from
∈-∷⁻ : ∀ {a} {A : Set a} {xs : List A} {x y} → y ∈ x ∷ xs → (y ≡ x) ⊎ (y ∈ xs)
∈-∷⁻ (here px) = inj₁ px
∈-∷⁻ (there p) = inj₂ p

open import Data.List.Relation.Unary.All.Properties.Core using (¬Any⇒All¬; All¬⇒¬Any)
open import Data.List.Relation.Unary.All using (All; uncons)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality using (≢-sym)

∉-∷⁻ : ∀ {a} {A : Set a} {xs : List A} {x y} → y ∉ x ∷ xs → (y ≢ x) × (y ∉ xs)
∉-∷⁻ {_} {_} {xs} {x} {y} y∉x∷xs with uncons (¬Any⇒All¬ _ y∉x∷xs)
... | y≢x , [≢y]xs = y≢x , All¬⇒¬Any [≢y]xs

∈×∉⇒≢ : ∀ {a} {A : Set a} {xs : List A} {x x′} → x ∈ xs → x′ ∉ xs → x ≢ x′
∈×∉⇒≢ {xs = x″ ∷ xs″} x∈x″∷xs″ x′∉x″∷xs″ with ∈-∷⁻ x∈x″∷xs″ | ∉-∷⁻ x′∉x″∷xs″
... | inj₁ x≡x″  | x′≢x″ , _      rewrite x≡x″ = ≢-sym x′≢x″
... | inj₂ x∈xs″ | _     , x′∉xs″              = ∈×∉⇒≢ x∈xs″ x′∉xs″

∈-findᵇ⁻ : ∀ {a} {A : Set a} ⦃ _ : DecEq A ⦄ {P : A → Bool} {xs : List A} {x : A} → findᵇ P xs ≡ just x → x ∈ xs
∈-findᵇ⁻ {P = P} {xs = x′ ∷ xs′} eqf with P x′
... | false = there (∈-findᵇ⁻ {xs = xs′} eqf)
... | true  = here (sym (just-injective eqf))

module _ {a p} {A : Set a} ⦃ _ : DecEq A ⦄ {P : Pred A p} (P? : Decidable P) where

  ∈-find⁻ : ∀ {xs : List A} {x : A} → find P? xs ≡ just x → x ∈ xs
  ∈-find⁻ {xs = []} eqf = contradiction eqf λ ()
  ∈-find⁻ {xs = x′ ∷ xs′} eqf with P? x′
  ... | no  _ = there (∈-find⁻ {xs = xs′} eqf)
  ... | yes _ = here (sym (just-injective eqf))

∈-∷-≢⁻ : ∀ {a} {A : Set a} {xs : List A} {x y : A} → y ∈ x ∷ xs → y ≢ x → y ∈ xs
∈-∷-≢⁻ y∈x∷xs y≢x with ∈-∷⁻ y∈x∷xs
... | inj₁ y≡x  = contradiction y≡x y≢x
... | inj₂ y∈xs = y∈xs

∈-∷ʳ-≢⁻ : ∀ {a} {A : Set a} {xs : List A} {x y : A} → y ∈ xs ∷ʳ x → y ≢ x → y ∈ xs
∈-∷ʳ-≢⁻ {xs = xs} {x = x} = ∈-∷-≢⁻ ∘ ++-comm xs [ x ]

∉-filter⁺ : ∀ {a p} {A : Set a} {P : Pred A p} {P? : Decidable P} {x : A} (xs : List A) → ¬ P x → x ∉ filter P? xs
∉-filter⁺ [] _ = λ ()
∉-filter⁺ {P? = P?} (x′ ∷ xs) ¬Px with P? x′
... | no ¬Px′ = ∉-filter⁺ xs ¬Px
... | yes Px′ = λ x∈x′∷Pxs → case ∈-∷⁻ x∈x′∷Pxs of λ where
  (inj₁ x≡x′)  → contradiction (subst _ (sym x≡x′) Px′) ¬Px
  (inj₂ x∈Pxs) → contradiction x∈Pxs (∉-filter⁺ xs ¬Px)

module _ {a} {A : Set a} ⦃ _ : DecEq A ⦄ where

  open import Data.List.Membership.DecPropositional (_≟_ {A = A}) using (_∈?_)

  ∈-undup⁺ : ∀ {xs : List A} {x : A} → x ∈ xs → x ∈ undup xs
  ∈-undup⁺ {xs = []} ()
  ∈-undup⁺ {xs = x′ ∷ xs} {x} x∈x′∷xs with x′ ∈? xs | ∈-∷⁻ x∈x′∷xs
  ... | yes x′∈xs | inj₁ x≡x′ rewrite x≡x′ = ∈-undup⁺ x′∈xs
  ... | yes x′∈xs | inj₂ x∈xs = ∈-undup⁺ x∈xs
  ... | no x′∉xs  | inj₁ x≡x′ rewrite x≡x′ = here refl
  ... | no x′∉xs  | inj₂ x∈xs = there (∈-undup⁺ x∈xs)

  ∈-undup⁻ : ∀ (xs : List A) {x} → x ∈ undup xs → x ∈ xs
  ∈-undup⁻ (x′ ∷ xs) {x} p with x′ ∈? xs
  ... | yes x′∈xs = there (∈-undup⁻ xs p)
  ... | no x′∉xs with ∈-∷⁻ p
  ... |   inj₁ x≡x′ rewrite x≡x′ = here refl
  ... |   inj₂ x∈udxs = there (∈-undup⁻ xs x∈udxs)
