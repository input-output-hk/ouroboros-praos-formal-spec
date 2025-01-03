module Data.List.Properties.Ext where

open import Data.Nat using (suc)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (refl; _≢_)
open import Data.List using (List; []; _∷_; _∷ʳ_; filter; length; updateAt; _[_]%=_; lookup)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable.Core using (does; _×-dec_)
open import Level using (Level)
open import Function.Base using (_∘_; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≗_; sym; cong)
open import Data.Fin using (Fin; cast) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (subst-is-cast)
open import Data.Fin.Properties.Ext using (suc-≢-injective)

private variable
  ℓ : Level
  A : Set
  x : A
  xs : List A
  P Q : Pred A ℓ

[]≢∷ʳ : [] ≢ xs ∷ʳ x
[]≢∷ʳ {xs = []} ()
[]≢∷ʳ {xs = _ ∷ _} ()

filter-∘-comm : (P? : Decidable P) (Q? : Decidable Q) → filter P? ∘ filter Q? ≗ filter Q? ∘ filter P?
filter-∘-comm P? Q? [] = refl
filter-∘-comm P? Q? (x ∷ xs) with ih ← filter-∘-comm P? Q? xs | does (P? x) in eqp | does (Q? x) in eqq
... | true  | true  rewrite eqp | eqq | ih = refl
... | true  | false rewrite eqp | eqq | ih = refl
... | false | true  rewrite eqp | eqq | ih = refl
... | false | false rewrite eqp | eqq | ih = refl

filter-∘-× : (P? : Decidable P) (Q? : Decidable Q) → filter (λ x → P? x ×-dec Q? x) ≗ filter P? ∘ filter Q?
filter-∘-× P? Q? [] = refl
filter-∘-× P? Q? (x ∷ xs) with ih ← filter-∘-× P? Q? xs | does (P? x) in eqp | does (Q? x) in eqq
... | true  | true  rewrite eqp | eqq | ih = refl
... | true  | false rewrite eqp | eqq | ih = refl
... | false | true  rewrite eqp | eqq | ih = refl
... | false | false rewrite eqp | eqq | ih = refl

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
