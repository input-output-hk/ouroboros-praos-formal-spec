module Data.List.Relation.Unary.AllPairs.Properties.Ext where

open import Level using (Level)
open import Function.Base using (_$_; _∘_)
open import Relation.Binary.PropositionalEquality.Core using (sym; subst)
open import Relation.Binary.Core using (Rel)
open import Data.Product using (proj₁; proj₂; _×_; _,_)
open import Data.List.Base using ([]; _∷_; _++_; _∷ʳ_)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.All as All using (All; [])
open import Data.List.Relation.Unary.All.Properties hiding (++⁻)
open import Data.List.Relation.Unary.AllPairs as AllPairs using (AllPairs; []; _∷_)

private
  variable
    a ℓ : Level
    A : Set a

module _ {R : Rel A ℓ} where

  ++⁻ : ∀ {xs ys} → AllPairs R (xs ++ ys) → AllPairs R xs × AllPairs R ys × All (λ x → All (R x) ys) xs
  ++⁻ {[]}     {[]}     []       = []             , []     , []
  ++⁻ {[]}     {y ∷ ys} (p ∷ ps) = []             , p ∷ ps , []
  ++⁻ {x ∷ xs} {y ∷ ys} (p ∷ ps)
    with ++⁻ {xs} {_} ps
  ... | p1 , p2 , p3             = ++⁻ˡ xs p ∷ p1 , p2     , ++⁻ʳ xs p All.∷ p3
  ++⁻ {x ∷ xs} {[]}     (p ∷ ps) = p′ ∷ ps′       , []     , ps″
    where
      eq  = ++-identityʳ xs
      p′  = subst (All (R x)) eq p
      ps′ = subst (AllPairs R) eq ps
      ps″ = [] All.∷ proj₂ (proj₂ (++⁻ ps))

  headʳ : ∀ {x xs} → AllPairs R (xs ∷ʳ x) → AllPairs R xs
  headʳ = proj₁ ∘ ++⁻
