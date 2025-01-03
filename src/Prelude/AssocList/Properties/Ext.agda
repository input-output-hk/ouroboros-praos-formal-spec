module Prelude.AssocList.Properties.Ext where

open import Data.Product using (_,′_)
open import Data.Product.Properties using (×-≡,≡→≡)
open import Data.List.Properties.Ext using (updateAt-id-local)
open import Prelude.Init
open import Prelude.Decidable using (¿_¿²)
open import Prelude.Irrelevance using (AnyFirst-irrelevant; ·¬⇒¬)
open import Prelude.DecEq using (DecEq)
open import Prelude.Default using (Default)
open import Prelude.AssocList using (AssocList; _⁉_; _‼_; set; _∈ᵐ_; _∈ᵐ?_; modify; ∈ᵐ-irrelevant)

private variable
  K V : Type

module _ ⦃ _ : DecEq K ⦄ where

  private variable
    m : AssocList K V
    k : K
    v : V

  map-‼ : ∀ {ks : List K} → (k∈ks : k ∈ᵐ map (_, v) ks) → map (_, v) ks ‼ k∈ks ≡ v
  map-‼ {k = .k′} {v = _} {ks = k′ ∷ ks} First.[ refl ] = refl
  map-‼ {k = k} {v = v} {ks = k′ ∷ ks} (k≢k′ ∷ k∈ks) = map-‼ {k = k} {v = v} {ks = ks} k∈ks

  ⁉⇒‼ : m ⁉ k ≡ just v → Σ[ k∈m ∈ k ∈ᵐ m ] m ‼ k∈m ≡ v
  ⁉⇒‼ {m = m} {k = k} eq with k ∈ᵐ? m
  ... | yes First.[ refl ] = First.[ refl ] , M.just-injective eq
  ... | yes (x ∷ p) = x ∷ p , M.just-injective eq

  ‼⇒⁉ : ∀ (k∈m : k ∈ᵐ m) → m ‼ k∈m ≡ v → m ⁉ k ≡ just v
  ‼⇒⁉ {k = k} {m = m} {v = v} k∈m eq with k ∈ᵐ? m | k∈m
  ... | yes First.[ refl ] | First.[ refl ] = cong just eq
  ... | yes (≢k ∷ _) | First.[ refl ] = contradiction refl (·¬⇒¬ ≢k)
  ... | yes First.[ refl ] | ≢k ∷ _ = contradiction refl (·¬⇒¬ ≢k)
  ... | yes (x ∷ p) | x′ ∷ p′ rewrite ∈ᵐ-irrelevant p p′ = cong just eq
  ... | no p | q = contradiction q p

  module _ ⦃ _ : Default V ⦄ {v : V} where

    set-id-local : m ⁉ k ≡ just v → set k v m ≡ m
    set-id-local {m} {k} p with k ∈ᵐ? m
    ... | yes q rewrite dec-yes (k ∈ᵐ? m) q .proj₂ = updateAt-id-local m (L.First.index q) (×-≡,≡→≡ $ L.First.index-satisfied q ,′ (sym $ M.just-injective p))
    ... | no _ = contradiction p λ()

    modify-modifies : ∀ {f : V → V} → m ⁉ k ≡ just v → modify k f m ⁉ k ≡ just (f v)
    modify-modifies = {!!} -- TODO: Prove
