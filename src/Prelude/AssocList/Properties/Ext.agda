module Prelude.AssocList.Properties.Ext where

open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (trans)
open import Relation.Binary.PropositionalEquality using (trans; subst₂)
open import Data.Product using (_,′_)
open import Data.Product.Properties using (×-≡,≡→≡)
open import Data.List.Properties.Ext using (updateAt-id-local; lookup∘updateAt)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Membership.Propositional.Properties.Ext using (∈-∷⁻)
open import Data.Maybe.Properties.Ext using ({- Is-just⇒to-witness;-} Is-just⇒∃; ≡just⇒Is-just)
open import Data.Maybe.Properties.Ext using (Is-just⇒∃; ≡just⇒Is-just)
open import Prelude.Init
open import Class.Decidable using (¿_¿²)
open import Prelude.Irrelevance using (AnyFirst-irrelevant; ·¬⇒¬; ¬⇒·¬)
open import Class.DecEq using (DecEq; _≟_)
open import Class.Default using (Default)
open import Prelude.AssocList using (AssocList; _⁉_; _‼_; set; _∈ᵐ_; _∈ᵐ?_; _∉ᵐ_; _∷=_; modify; ∈ᵐ-irrelevant)

private variable
  K V : Type

module _ ⦃ _ : DecEq K ⦄ where

  private variable
    m : AssocList K V
    k k′ : K
    v : V

  ∈ᵐ-lookup : ∀ (k∈m : k ∈ᵐ m) → L.lookup m (L.First.index k∈m) .proj₁ ≡ k
  ∈ᵐ-lookup First.[ refl ] = refl
  ∈ᵐ-lookup {m = (k′ , v′) ∷ m′} (k≢k′ ∷ k∈m′) = ∈ᵐ-lookup {m = m′} k∈m′

  ∉ᵐ⁻ : k ∉ᵐ ((k′ , v) ∷ m) → k ≢ k′ × k ∉ᵐ m
  ∉ᵐ⁻ {k = k} {k′ = k′} {v = v} {m = m} k∉ᵐ[p∷m] = k≢k′ , k∉ᵐm
    where
      k≢k′ : k ≢ k′
      k≢k′ with k ≟ k′
      ... | yes k≡k′ = contradiction k∈ᵐ[p∷m] (·¬⇒¬ k∉ᵐ[p∷m])
        where
          k∈ᵐ[p∷m] : k ∈ᵐ ((k′ , v) ∷ m)
          k∈ᵐ[p∷m] rewrite k≡k′ = First.[ refl ]
      ... | no k≢k′ = k≢k′

      k∉ᵐm : k ∉ᵐ m
      k∉ᵐm k∈ᵐm = contradiction k∈ᵐ[p∷m] (·¬⇒¬ k∉ᵐ[p∷m])
        where
          k∈ᵐ[p∷m] : k ∈ᵐ ((k′ , v) ∷ m)
          k∈ᵐ[p∷m] = ¬⇒·¬ k≢k′ ∷ k∈ᵐm

  ∉ᵐ⇒⁉≡nothing : ∀ {m : AssocList K V} {k : K} → k ∉ᵐ m → m ⁉ k ≡ nothing
  ∉ᵐ⇒⁉≡nothing {m = m} {k} k∉ᵐm rewrite dec-no (k ∈ᵐ? m) (·¬⇒¬ k∉ᵐm) = refl

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

  -- Looking up a key other than the head's reduces to looking it up in the tail.
  ⁉-∷-≢ : ∀ {k′ : K} (x : K × V) (xs : AssocList K V) → proj₁ x ≢ k′ → (x ∷ xs) ⁉ k′ ≡ xs ⁉ k′
  ⁉-∷-≢ {k′ = k′} x xs x₁≢k′ with k′ ∈ᵐ? (x ∷ xs)
  ... | yes First.[ k′≡x₁ ] = ⊥-elim (x₁≢k′ (sym k′≡x₁))
  ... | yes (_ ∷ p)         = sym (‼⇒⁉ p refl)
  ... | no  ¬p              = sym (∉ᵐ⇒⁉≡nothing k′∉ᵐxs)
    where
      k′∉ᵐxs : k′ ∉ᵐ xs
      k′∉ᵐxs = ¬⇒·¬ λ q → ¬p (¬⇒·¬ (λ e → x₁≢k′ (sym e)) ∷ q)

  -- Looking up the head's key yields the head's value.
  ⁉-∷-≡ : ∀ {k′ : K} (x : K × V) (xs : AssocList K V) → proj₁ x ≡ k′ → (x ∷ xs) ⁉ k′ ≡ just (proj₂ x)
  ⁉-∷-≡ x xs x₁≡k′ = ‼⇒⁉ First.[ sym x₁≡k′ ] refl

  ∈ᵐ⇒∈ : k ∈ᵐ m → k ∈ map proj₁ m
  ∈ᵐ⇒∈ First.[ refl ] = here refl
  ∈ᵐ⇒∈ (_ ∷ p)        = there (∈ᵐ⇒∈ p)

  ∈⇒∈ᵐ : k ∈ map proj₁ m → k ∈ᵐ m
  ∈⇒∈ᵐ {m = []}              = λ ()
  ∈⇒∈ᵐ {m = _ ∷ _} (here px) = First.[ px ]
  ∈⇒∈ᵐ {k = k} {m = (k′ , _) ∷ m} (there p) with k ≟ k′
  ... | yes k≡k′ = First.[ k≡k′ ]
  ... | no  k≢k′ = ¬⇒·¬ k≢k′ ∷ ∈⇒∈ᵐ p

  map-⁉-≡ : ∀ {ks : List K} {k : K} (v : V) → map (_, v) (k ∷ ks) ⁉ k ≡ just v
  map-⁉-≡ _ = let k∈ᵐm = First.[ refl ] in ‼⇒⁉ k∈ᵐm (map-‼ k∈ᵐm)

  map-⁉-≢ : ∀ {ks : List K} {k k′ : K} (v : V) → k ≢ k′ → map (_, v) (k′ ∷ ks) ⁉ k ≡ map (_, v) ks ⁉ k
  map-⁉-≢ {ks = ks} {k} {k′} v k≢k′ = case k ∈ᵐ? map (_, v) ks of λ where
    (yes k∈ᵐm[ks]) → let
        k∈ᵐm[k∷ks] = ¬⇒·¬ k≢k′ ∷ k∈ᵐm[ks]
        p = ‼⇒⁉ k∈ᵐm[k∷ks] (map-‼ k∈ᵐm[k∷ks])
        q = ‼⇒⁉ k∈ᵐm[ks] (map-‼ k∈ᵐm[ks])
      in
        subst₂ _≡_ (sym p) (sym q) refl
    (no ¬k∈ᵐm) → trans (∉ᵐ⇒⁉≡nothing (k∉ᵐm[k′∷ks] ¬k∈ᵐm)) (sym $ ∉ᵐ⇒⁉≡nothing (¬⇒·¬ ¬k∈ᵐm))
      where
        k∉ᵐm[k′∷ks] : ¬ k ∈ᵐ map (_, v) ks → k ∉ᵐ map (_, v) (k′ ∷ ks)
        k∉ᵐm[k′∷ks] ¬k∈ᵐm First.[ k≡k′ ] = contradiction k≡k′ k≢k′
        k∉ᵐm[k′∷ks] ¬k∈ᵐm (k≢k′ ∷ k∈ᵐm[ks]) = contradiction k∈ᵐm[ks] ¬k∈ᵐm

  map-⁉-∈-just : ∀ {ks : List K} {k : K} (v : V) → k ∈ ks → map (_, v) ks ⁉ k ≡ just v
  map-⁉-∈-just v (here refl) = map-⁉-≡ v
  map-⁉-∈-just {ks = k′ ∷ ks′} {k} v (there p) = case k ≟ k′ of λ where
    (yes k≡k′) → trans (cong (λ ◆ → map (_, v) (◆ ∷ ks′) ⁉ k) (sym k≡k′)) (map-⁉-≡ v)
    (no  k≢k′) → trans (map-⁉-≢ v k≢k′) (map-⁉-∈-just v p)

  map-⁉-∈ : ∀ {ks : List K} {k k′ : K} (v : V) → k ∈ ks → map (_, v) (k′ ∷ ks) ⁉ k ≡ map (_, v) ks ⁉ k
  map-⁉-∈ {ks = ks} {k} {k′} v k∈ks = case k ≟ k′ of λ where
   (yes k≡k′) → let open ≡-Reasoning in begin
     map (_, v) (k′ ∷ ks) ⁉ k   ≡⟨ cong (λ ◆ → map (_, v) (◆ ∷ ks) ⁉ k) (sym k≡k′) ⟩
     map (_, v) (k ∷ ks) ⁉ k    ≡⟨ map-⁉-≡ v ⟩
     just v                     ≡⟨ map-⁉-∈-just v k∈ks ⟨
     map (_, v) ks ⁉ k          ∎
   (no k≢k′) → map-⁉-≢ v k≢k′

  map-just⇔∈ : ∀ (ks : List K) (k : K) (v : V) → M.Is-just (map (_, v) ks ⁉ k) ⇔ k ∈ ks
  map-just⇔∈ []        _ _ = mk⇔ (λ ()) λ ()
  map-just⇔∈ (k′ ∷ ks) k v = case k ≟ k′ of λ where
    (yes k≡k′) → subst (λ ◆ → M.Is-just (map (_, v) (◆ ∷ ks) ⁉ k) ⇔ k ∈ ◆ ∷ ks) k≡k′ (mk⇔ (const $ here refl) (const $ ≡just⇒Is-just $ map-⁉-≡ v))
    (no k≢k′) → mk⇔ (from k≢k′) (to k≢k′)
      where
        from : k ≢ k′ → M.Is-just (map (_, v) (k′ ∷ ks) ⁉ k) → k ∈ k′ ∷ ks
        from k≢k′ p with map (_, v) ks ⁉ k in eq
        ... | just _ = there $ map-just⇔∈ ks k v .Equivalence.to (≡just⇒Is-just eq)
        ... | nothing with Is-just⇒∃ p
        ...   | _ , ≡just = contradiction (trans (sym ≡just) (trans (map-⁉-≢ v k≢k′) eq)) λ ()

        to : k ≢ k′ → k ∈ k′ ∷ ks → M.Is-just (map (_, v) (k′ ∷ ks) ⁉ k)
        to k≢k′ p with ∈-∷⁻ p
        ... | inj₁ k≡k′ = contradiction k≡k′ k≢k′
        ... | inj₂ k∈ks = subst M.Is-just (sym (map-⁉-≢ v k≢k′)) (map-just⇔∈ ks k v .Equivalence.from k∈ks)

  module _ ⦃ Default-V : Default V ⦄ where

    set-id-local : m ⁉ k ≡ just v → set ⦃ it ⦄ ⦃ Default-V ⦄ k v m ≡ m
    set-id-local {m} {k} p with k ∈ᵐ? m
    ... | yes q rewrite dec-yes (k ∈ᵐ? m) q .proj₂ = updateAt-id-local m (L.First.index q) (×-≡,≡→≡ $ L.First.index-satisfied q ,′ (sym $ M.just-injective p))
    ... | no _ = contradiction p λ()

    ∷=-witness : ∀ {k} {m : AssocList K V} (p : k ∈ᵐ m) → k ∈ᵐ (p ∷= v)
    ∷=-witness First.[ refl ] = First.[ refl ]
    ∷=-witness (h ∷ p)        = h ∷ ∷=-witness p

    -- Looking up the just-updated key returns the new value.
    ∷=-⁉ : ∀ {k} {m : AssocList K V} (p : k ∈ᵐ m) (w : V) → (p ∷= w) ⁉ k ≡ just w
    ∷=-⁉ First.[ refl ] w = ‼⇒⁉ First.[ refl ] refl
    ∷=-⁉ {k = k} (_∷_ {x = x} h p) w = case k ∈ᵐ? (x ∷ _) of λ where
      (no  k∉) → ⊥-elim (k∉ (h ∷ ∷=-witness {v = w} p))
      (yes _)  →
        let (w′ , eq) = ⁉⇒‼ (∷=-⁉ p w)
        in ‼⇒⁉ (h ∷ ∷=-witness p) (trans (cong (_ ‼_) (∈ᵐ-irrelevant (∷=-witness p) w′)) eq)

    modify-modifies : ∀ {f : V → V} → m ⁉ k ≡ just v → modify k f m ⁉ k ≡ just (f v)
    modify-modifies {m = m} {k = k} {f = f} eq with k ∈ᵐ? m
    ... | no  _ = contradiction eq λ()
    ... | yes p = trans (∷=-⁉ p (f (m ‼ p))) (cong (λ w → just (f w)) (M.just-injective eq))

    set-⁉ : ∀ (m : AssocList K V) (k : K) (v : V) → set k v m ⁉ k ≡ just v
    set-⁉ m k v with k ∈ᵐ? m
    ... | no  ¬p = ‼⇒⁉ First.[ refl ] refl
    ... | yes p  = ∷=-⁉ p v

    set-⁉-¬ : ∀ (m : AssocList K V) (k k′ : K) (v : V) → k ≢ k′ → set k v m ⁉ k′ ≡ m ⁉ k′
    set-⁉-¬ m k k′ v k≢k′ with k ∈ᵐ? m
    ... | no  _ = ⁉-∷-≢ (k , v) m k≢k′
    ... | yes p = go k≢k′ p
      where
        -- Updating the value at `p`'s position leaves lookups at other keys unchanged.
        go : ∀ {k k′ : K} {m : AssocList K V} → k ≢ k′ → (p : k ∈ᵐ m) → (p ∷= v) ⁉ k′ ≡ m ⁉ k′
        go {k′ = k′} {m = x ∷ xs} k≢k′ First.[ refl ] =
          trans (⁉-∷-≢ (proj₁ x , v) xs k≢k′) (sym (⁉-∷-≢ x xs k≢k′))
        go {k′ = k′} {m = x ∷ xs} k≢k′ (_ ∷ p′) with proj₁ x ≟ k′
        ... | yes x₁≡k′ = trans (⁉-∷-≡ x (p′ ∷= v) x₁≡k′) (sym (⁉-∷-≡ x xs x₁≡k′))
        ... | no  x₁≢k′ = trans (⁉-∷-≢ x (p′ ∷= v) x₁≢k′) (trans (go k≢k′ p′) (sym (⁉-∷-≢ x xs x₁≢k′)))
