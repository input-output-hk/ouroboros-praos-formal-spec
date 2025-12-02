module Data.Maybe.Properties.Ext where

open import Level using (Level)
open import Function.Base using (const)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Bool using (T)
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Maybe using (maybe′; is-just; Is-just; to-witness)
open import Data.Maybe.Properties using (just-injective)
open import Data.Maybe.Relation.Unary.Any renaming (just to justᵐ)

-- A computable version of `Is-just`:

isJust : {ℓ : Level} {A : Set ℓ} (m : Maybe A) → Set
isJust m = T (is-just m)

Is-just⇒∃ : ∀ {ℓ} {A : Set ℓ} {m : Maybe A} → Is-just m → ∃[ x ] m ≡ just x
Is-just⇒∃ {m = just x} (justᵐ _) = x , refl
Is-just⇒∃ {m = nothing} ()

Is-just⇒to-witness : ∀ {ℓ} {A : Set ℓ} {m : Maybe A} (p : Is-just m) → m ≡ just (to-witness p)
Is-just⇒to-witness {m = just _} (justᵐ _) = refl
Is-just⇒to-witness {m = nothing} ()

≡just⇒Is-just : ∀ {ℓ} {A : Set ℓ} {m : Maybe A} {x : A} → m ≡ just x → Is-just m
≡just⇒Is-just p rewrite p = Any.just _

Is-just⇒isJust : ∀ {ℓ} {A : Set ℓ} {m : Maybe A} → Is-just m → isJust m
Is-just⇒isJust (Any.just _) = _

isJust⇒Is-just : ∀ {ℓ} {A : Set ℓ} {m : Maybe A} → isJust m → Is-just m
isJust⇒Is-just {m = just _} _ = Any.just _

fromJust : ∀ {ℓ} {A : Set ℓ} (m : Maybe A) {pr : maybe′ (const ⊤) ⊥ m} → A
fromJust (just x) = x
fromJust nothing {()}

fromJust⇒just : ∀ {ℓ} {A : Set ℓ} {m : Maybe A} {pr : maybe′ (const ⊤) ⊥ m} {x : A} → x ≡ fromJust m {pr = pr} → just x ≡ m
fromJust⇒just {m = just _} p = cong just p

just⇒fromJust : ∀ {ℓ} {A : Set ℓ} {m : Maybe A} {pr : maybe′ (const ⊤) ⊥ m} {x : A} → just x ≡ m → x ≡ fromJust m {pr = pr}
just⇒fromJust {m = just x} p = just-injective p
