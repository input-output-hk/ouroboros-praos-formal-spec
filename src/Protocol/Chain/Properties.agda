open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Protocol.Chain.Properties
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.Block ⦃ params ⦄
open import Protocol.Chain ⦃ params ⦄
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open Function.Bundles.Equivalence using (from; to)
open import Data.List.Relation.Unary.Linked
open import Data.List.Relation.Unary.Unique.Propositional.Properties using (map⁻)

opaque
  unfolding _✓

  [b]✓⇔b≡gb : ∀ {b : Block} → [ b ] ✓ ⇔ b ≡ genesisBlock
  [b]✓⇔b≡gb = mk⇔ toπ fromπ
    where
      toπ : ∀ {b : Block} → [ b ] ✓ → b ≡ genesisBlock
      toπ = proj₁ ∘ proj₂

      fromπ : ∀ {b : Block} → b ≡ genesisBlock → [ b ] ✓
      fromπ b≡gb rewrite b≡gb = genesisWinner ∷ [] , refl , [-]

  [gb+c]✓⇔c≡[] : ∀ {c : Chain} → (genesisBlock ∷ c) ✓ ⇔ c ≡ []
  [gb+c]✓⇔c≡[] = mk⇔ toπ fromπ
    where
      toπ : ∀ {c : Chain} → (genesisBlock ∷ c) ✓ → c ≡ []
      toπ {[]} _ = refl
      toπ {b ∷ c} [gb∷b∷c]✓ = contradiction genesisBlockSlot (Nat.n>0⇒n≢0 $ Nat.m<n⇒0<n $ ✓-∷ .from [gb∷b∷c]✓ .proj₂ .proj₂ .proj₁)

      fromπ : ∀ {c : Chain} → c ≡ [] → (genesisBlock ∷ c) ✓
      fromπ c≡[] rewrite c≡[] = [b]✓⇔b≡gb .from refl

✓⇒Unique : ∀ {c : Chain} → c ✓ → Unique c
✓⇒Unique = L.Unique.map⁻ ∘ DecreasingSlots⇒UniqueSlots ∘ ✓⇒ds
