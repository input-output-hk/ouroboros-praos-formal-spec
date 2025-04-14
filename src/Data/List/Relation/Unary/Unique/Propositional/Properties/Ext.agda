module Data.List.Relation.Unary.Unique.Propositional.Properties.Ext where

open import Level using (Level)
open import Function.Base using (_∘_; _∋_; _$_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≢_; cong)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)
open import Data.Empty using (⊥-elim)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Nat.Base using (suc; _≤_; z≤n; s≤s; _+_)
open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _∷ʳ_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties.Ext using (∈-∷⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs.Core
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.Unique.Propositional.Properties using (Unique[x∷xs]⇒x∉xs)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
import Data.List.Relation.Unary.Unique.Setoid.Properties.Ext as Setoid
open import Data.List.Relation.Binary.Permutation.Propositional using (↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∷↭∷ʳ; ↭-length; ∈-resp-↭)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties.Ext
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties.Ext using (x∷xs⊈[]; ∷-⊆; ∷⊆⇒∈)

private
  variable
    a : Level
    A : Set a
    x : A
    xs ys : List A

module _ {A : Set a} {xs ys} where

  ++⁻ : Unique (xs ++ ys) → Unique xs × Unique ys × Disjoint xs ys
  ++⁻ = Setoid.++⁻ (setoid A)

Unique[xs∷ʳx]⇒x∉xs : Unique (xs ∷ʳ x) → x ∉ xs
Unique[xs∷ʳx]⇒x∉xs {xs = xs} {x = x} = Unique[x∷xs]⇒x∉xs ∘ Unique-resp-↭ (↭-sym (∷↭∷ʳ x xs))

Unique-⊆-#≤ : ∀ {a} {A : Set a} {xs ys : List A} → Unique xs → xs ⊆ ys → length xs ≤ length ys
Unique-⊆-#≤ {xs = []}     {ys = ys} p q = z≤n
Unique-⊆-#≤ {xs = x ∷ xs} {ys = ys} p q with ∈-∃↭ (x ∈ ys ∋ ∷⊆⇒∈ q)
... | zs , ys↭x∷zs rewrite ↭-length ys↭x∷zs = s≤s $ length xs ≤ length zs ∋ Unique-⊆-#≤ Unique[xs] xs⊆zs
  where
    Unique[xs] : Unique xs
    Unique[xs] = (++⁻ p .proj₂ .proj₁)

    x∉xs : x ∉ xs
    x∉xs = Unique[x∷xs]⇒x∉xs p

    xs⊆zs : xs ⊆ zs
    xs⊆zs {x′} x′∈xs with ∈-∷⁻ (x′ ∈ x ∷ zs ∋ ∈-resp-↭ ys↭x∷zs (x′ ∈ ys ∋ (xs ⊆ ys ∋ ∷-⊆ q) x′∈xs))
    ... | inj₁ x′≡x rewrite x′≡x = contradiction x′∈xs x∉xs
    ... | inj₂ x′∈zs = x′∈zs
