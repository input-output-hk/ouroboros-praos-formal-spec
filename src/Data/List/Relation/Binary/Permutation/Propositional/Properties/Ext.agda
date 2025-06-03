module Data.List.Relation.Binary.Permutation.Propositional.Properties.Ext where

open import Function.Base using (_∘_)
open import Relation.Nullary using (yes; no)
open import Relation.Unary using (Decidable; Pred)
open import Relation.Binary.Core using (_Preserves_⟶_)
open import Relation.Binary.Definitions using (_Respects_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; ≢-sym; setoid) renaming (trans to ≡-trans)
open import Data.Product using (_,_; ∃-syntax)
open import Data.Nat.Base using (suc)
open import Data.List using (List; _∷_; _++_; length; filter)
open import Data.List.Ext using (count)
open import Data.List.Properties.Ext using (length0⇒[])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-∃++)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique) renaming (_∷_ to _∷ᵘ_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Binary.Permutation.Setoid.Properties as Permutation
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; refl; prep; swap; trans; ↭-trans; ↭⇒↭ₛ)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (All-resp-↭; shift; ↭-length)

-- TODO: Perhaps add to stdlib (Data.List.Relation.Binary.Permutation.Propositional.Properties)
Unique-resp-↭ : ∀ {a} {A : Set a} → _Respects_ {A = List A} Unique _↭_
Unique-resp-↭ = Permutation.Unique-resp-↭ (setoid _) ∘ ↭⇒↭ₛ

-- TODO: Remove when update stdlib to master (use filter-↭).
filter-↭ : ∀ {a p} {A : Set a} {P : Pred A p} (P? : Decidable P) → (filter {A = A} P?) Preserves _↭_ ⟶ _↭_
filter-↭ P? refl = refl
filter-↭ P? (prep x xs↭ys) with P? x
... | yes _ = prep x (filter-↭ P? xs↭ys)
... | no _  = filter-↭ P? xs↭ys
filter-↭ P? (swap x y xs↭ys) with P? x in eqˣ | P? y in eqʸ
... | yes _ | yes _ rewrite eqˣ rewrite eqʸ = swap x y (filter-↭ P? xs↭ys)
... | yes _ | no  _ rewrite eqˣ rewrite eqʸ = prep x (filter-↭ P? xs↭ys)
... | no _  | yes _ rewrite eqˣ rewrite eqʸ = prep y (filter-↭ P? xs↭ys)
... | no _  | no _  rewrite eqˣ rewrite eqʸ = filter-↭ P? xs↭ys
filter-↭ P? (trans xs↭ys ys↭zs) = ↭-trans (filter-↭ P? xs↭ys) (filter-↭ P? ys↭zs)

opaque
  unfolding count

  count-↭ : ∀ {a p} {A : Set a} {P : Pred A p} (P? : Decidable P) → count P? Preserves _↭_ ⟶ _≡_
  count-↭ P? = ↭-length ∘ filter-↭ P?

∈-∃↭ : ∀ {a} {A : Set a} {xs : List A} {x : A} → x ∈ xs → ∃[ ys ] xs ↭ x ∷ ys
∈-∃↭ {x = x} p with ∈-∃++ p
... | xsₕ , xsₜ , eq rewrite eq =  xsₕ ++ xsₜ , shift x xsₕ xsₜ
