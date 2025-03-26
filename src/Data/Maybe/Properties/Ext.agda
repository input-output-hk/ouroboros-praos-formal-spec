module Data.Maybe.Properties.Ext where

open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Maybe using (Is-just; to-witness)
open import Data.Maybe.Relation.Unary.Any renaming (just to justᵐ)

Is-just⇒∃ : ∀ {a} {A : Set a} {m : Maybe A} → Is-just m → ∃[ x ] m ≡ just x
Is-just⇒∃ {m = just x} (justᵐ _) = x , refl
Is-just⇒∃ {m = nothing} ()

Is-just⇒to-witness : ∀ {a} {A : Set a} {m : Maybe A} → (p : Is-just m) → m ≡ just (to-witness p)
Is-just⇒to-witness {m = just _} (justᵐ _) = refl
Is-just⇒to-witness {m = nothing} ()

≡just⇒Is-just : ∀ {a} {A : Set a} {m : Maybe A} {x : A} → m ≡ just x → Is-just m
≡just⇒Is-just p rewrite p = Any.just _
