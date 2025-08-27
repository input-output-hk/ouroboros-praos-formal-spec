open import Protocol.Params using (Params)

module Protocol.Assumptions
  ⦃ params : _ ⦄ (open Params params)
  where

open import Protocol.Prelude
open import Protocol.BaseTypes using (Slot; Honesty)
open import Protocol.Block ⦃ params ⦄
open import Protocol.Chain ⦃ params ⦄
open import Protocol.Crypto ⦃ params ⦄ using (Hashable)
open import Protocol.Message ⦃ params ⦄
open import Protocol.Network ⦃ params ⦄
open import Protocol.Tree ⦃ params ⦄
open Hashable ⦃ ... ⦄
open Honesty
open Envelope

record Assumptions : Type₁ where
  field
    TreeImpl          : Type
    AdversarialState  : Type
    honestyOf         : Party → Honesty
    txSelection       : Slot → Party → Txs
    adversarialState₀ : AdversarialState
    parties₀          : List Party

    -- Corrupt behavior
    processMsgsᶜ :
        List Message
      → Slot
      → List Message
      → List Envelope
      → AdversarialState
      → List (Message × DelayMap) × AdversarialState

    makeBlockᶜ :
        Slot
      → List Message
      → List Envelope
      → AdversarialState
      → List (Message × DelayMap) × AdversarialState

    ⦃ Hashable-Block     ⦄ : Hashable Block
    ⦃ Default-Block      ⦄ : Default Block
    ⦃ Tree-TreeImpl      ⦄ : Tree TreeImpl
    ⦃ parties₀Uniqueness ⦄ : Unique parties₀
    ⦃ parties₀HasHonest  ⦄ : L.Any.Any ((_≡ honest) ∘ honestyOf) parties₀
    ⦃ genesisBlockSlot   ⦄ : genesisBlock .slot ≡ 0
    ⦃ genesisHonesty     ⦄ : honestyOf (genesisBlock .pid) ≡ honest
    ⦃ genesisWinner      ⦄ : winner (genesisBlock .pid) (genesisBlock .slot)

  Honest : Pred Party 0ℓ
  Honest p = honestyOf p ≡ honest

  Corrupt : Pred Party 0ℓ
  Corrupt p = honestyOf p ≡ corrupt

  honest⇒¬corrupt : ∀ {p} → Honest p → ¬ Corrupt p
  honest⇒¬corrupt {p} eq eq′ = contradiction (trans (sym eq) eq′) λ()

  ¬corrupt⇒honest : ∀ {p} → ¬ Corrupt p → Honest p
  ¬corrupt⇒honest {p} eq′ with honestyOf p
  ... | honest = refl
  ... | corrupt = contradiction refl eq′

  corrupt⇒¬honest : ∀ {p} → Corrupt p → ¬ Honest p
  corrupt⇒¬honest eq eq′ = contradiction (trans (sym eq) eq′) λ()

  ¬honest⇒corrupt : ∀ {p} → ¬ Honest p → Corrupt p
  ¬honest⇒corrupt {p} eq′ with honestyOf p
  ... | honest = contradiction refl eq′
  ... | corrupt = refl

  HonestBlock : Pred Block 0ℓ
  HonestBlock = Honest ∘ pid

  CorruptBlock : Pred Block 0ℓ
  CorruptBlock = Corrupt ∘ pid

  honestBlocks : List Block → List Block
  honestBlocks = L.filter ¿ HonestBlock ¿¹

  infix 4 _⊆ʰ_
  _⊆ʰ_ : Rel (List Block) 0ℓ
  _⊆ʰ_ = _⊆ˢ_ on honestBlocks

  ∷-⊆ʰ : ∀ {bs bs′ : List Block} {b : Block} → HonestBlock b → b ∷ bs ⊆ʰ bs′ → bs ⊆ʰ bs′
  ∷-⊆ʰ {bs} {_} {b} bh p rewrite bh = L.SubS.⊆-trans (L.SubS.xs⊆x∷xs (honestBlocks bs) b) p

  instance
    Default-TreeImpl : Default TreeImpl
    Default-TreeImpl .def = tree₀
