module Data.List.Relation.Binary.Subset.Propositional.Properties.Ext where

open import Function.Base using (id; _$_; _∘_; _|>_; const)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; _++_; cartesianProduct; filterᵇ; deduplicate; map; replicate; length)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_; _⊈_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-refl; ⊆-trans; xs⊆x∷xs; filter⁺′; ∷⁺ʳ; xs⊆xs++ys; ∈-∷⁺ʳ; ⊆-respˡ-↭)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-cartesianProduct⁺; ∈-cartesianProduct⁻; ∈-deduplicate⁻; ∈-deduplicate⁺; ∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Membership.Propositional.Properties.Ext using (x∈x∷xs)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (¬Any[])
open import Data.List.Properties.Ext using (replicate-map-const)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; refl; trans; cong)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Class.DecEq using (DecEq; _≟_)

{-- TODO: Prove at a later time...
∷⁻ʳ : ∀ {a} {A : Set a} {xs ys : List A} {x} → x ∉ xs → x ∉ ys → x ∷ xs ⊆ x ∷ ys → xs ⊆ ys
∷⁻ʳ = {!!}
--}

∷-⊆ : ∀ {a} {A : Set a} {xs ys : List A} {x} → x ∷ xs ⊆ ys → xs ⊆ ys
∷-⊆ {a} {_} {xs} {_} {x} p = ⊆-trans (xs⊆x∷xs {a} xs x) p

∷-⊆⁺ : ∀ {a} {A : Set a} {xs ys : List A} {y} → xs ⊆ ys → xs ⊆ y ∷ ys
∷-⊆⁺ {y = y} = ∷-⊆ ∘ ∷⁺ʳ y

∷⊆⇒∈ : ∀ {a} {A : Set a} {xs ys : List A} {x} → x ∷ xs ⊆ ys → x ∈ ys
∷⊆⇒∈ {xs = xs} = (x∈x∷xs xs) |>_

x∷xs⊈[] : ∀ {a} {A : Set a} {xs : List A} {x : A} → x ∷ xs ⊈ []
x∷xs⊈[] p = contradiction (∷⊆⇒∈ p) λ ()

⊆-++-comm : ∀ {a} {A : Set a} (xs ys : List A) → xs ++ ys ⊆ ys ++ xs
⊆-++-comm xs ys p with ∈-++⁻ xs p
... | inj₁ p′ = ∈-++⁺ʳ ys p′
... | inj₂ p′ = ∈-++⁺ˡ p′

++⁻ˡ : ∀ {a} {A : Set a} {xs ys zs : List A} → xs ++ ys ⊆ zs → xs ⊆ zs
++⁻ˡ {xs = xs} {ys = ys} xs++ys⊆zs = ⊆-trans (xs⊆xs++ys xs ys) xs++ys⊆zs

++⁻ʳ : ∀ {a} {A : Set a} {xs ys zs : List A} → xs ++ ys ⊆ zs → ys ⊆ zs
++⁻ʳ {xs = xs} {ys = ys} xs++ys⊆zs = ++⁻ˡ $ ⊆-trans (⊆-++-comm ys xs) xs++ys⊆zs

++⁻ : ∀ {a} {A : Set a} {xs ys zs : List A} → xs ++ ys ⊆ zs → xs ⊆ zs × ys ⊆ zs
++⁻ p = ++⁻ˡ p , ++⁻ʳ p

++-meet : ∀ {a} {A : Set a} {xs ys zs : List A} → xs ⊆ zs → ys ⊆ zs → xs ++ ys ⊆ zs
++-meet {xs = xs} xs⊆zs ys⊆zs {x} x∈xs++ys with ∈-++⁻ xs x∈xs++ys
... | inj₁ x∈xs = xs⊆zs x∈xs
... | inj₂ x∈ys = ys⊆zs x∈ys

++-absorb : ∀ {a} {A : Set a} (xs : List A) → xs ++ xs ⊆ xs
++-absorb _ = ++-meet ⊆-refl ⊆-refl

cartesianProduct-⊆-Mono : ∀ {a b} {A : Set a} {B : Set b} {xs xs′ : List A} {ys ys′ : List B} → xs ⊆ xs′ → ys ⊆ ys′ → cartesianProduct xs ys ⊆ cartesianProduct xs′ ys′
cartesianProduct-⊆-Mono {xs = xs} {xs′ = xs′} {ys = ys} {ys′ = ys′} xs⊆xs′ ys⊆ys′ {x , y} [x,y]∈xs×ys
  with ∈-cartesianProduct⁻ xs ys [x,y]∈xs×ys
... | x∈xs , y∈ys = ∈-cartesianProduct⁺ (xs⊆xs′ x∈xs) (ys⊆ys′ y∈ys)

⊆[]⇒≡[] : ∀ {a} {A : Set a} {xs : List A} → xs ⊆ [] → xs ≡ []
⊆[]⇒≡[] {xs = []} ⊆[] = refl
⊆[]⇒≡[] {xs = x ∷ xs} ⊆[] = contradiction (⊆[] {x} (here refl)) ¬Any[]

filterᵇ-mono : ∀ {A : Set} {P : A → Bool} {xs ys : List A} → xs ⊆ ys → filterᵇ P xs ⊆ filterᵇ P ys
filterᵇ-mono {P = P} xs⊆ys = filter⁺′ (T? ∘ P) (T? ∘ P) id xs⊆ys
  where open import Relation.Nullary.Decidable.Core using (T?)

deduplicate⁺′ : ∀ {a} {A : Set a} ⦃ _ : DecEq A ⦄ {xs ys : List A} → xs ⊆ ys → deduplicate _≟_ xs ⊆ deduplicate _≟_ ys
deduplicate⁺′ {xs = xs} xs⊆ys v∈ddxs with ∈-deduplicate⁻ _≟_ xs v∈ddxs
... | v∈xs = ∈-deduplicate⁺ _≟_ (xs⊆ys v∈xs)

deduplicate-⊆ : ∀ {a} {A : Set a} ⦃ _ : DecEq A ⦄ (xs : List A) → deduplicate _≟_ xs ⊆ xs
deduplicate-⊆ xs {x} x∈ddxs = ∈-deduplicate⁻ _≟_ xs {x} x∈ddxs

replicate[x]⊆x∷xs : ∀ {a} {A : Set a} {xs : List A} {x : A} {n : ℕ} → replicate n x ⊆ x ∷ xs
replicate[x]⊆x∷xs {n = zero}  = λ ()
replicate[x]⊆x∷xs {n = suc n} = ∈-∷⁺ʳ (here refl) (replicate[x]⊆x∷xs {n = n})

map[const-x]xs⊆x∷ys : ∀ {a b} {A : Set a} {B : Set b} {xs : List A} {ys : List B} {x : B} → map (const x) xs ⊆ x ∷ ys
map[const-x]xs⊆x∷ys {xs = xs} {x = x}
  rewrite
    sym $ replicate-map-const {xs = xs} {x = x} {n = length xs}
    = replicate[x]⊆x∷xs
