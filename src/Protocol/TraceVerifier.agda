open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Protocol.TraceVerifier
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open RTC

advanceRoundF : Op₁ GlobalState
advanceRoundF N = record (tick N) { progress = ready }

data Action : Type where
--  DeliverMsgs     : ??? → Action
--  MakeBlock       : ??? → Action
  AdvanceRound    : Action
--  PermuteParties  : ??? → Action
--  PermuteMessages : ??? → Action

Trace = List Action

private variable
  N N′ : GlobalState
  α : Action
  αs : Trace

data ValidAction : Action → GlobalState → Type where
  AdvanceRound : ⦃ _ : N .progress ≡ blockMade ⦄ →
    ValidAction AdvanceRound N

⟦_⟧ : ValidAction α N → GlobalState
⟦_⟧ {α}{N} = λ where
  AdvanceRound →
    advanceRoundF N

private
  ⟦⟧-subst :
    (vα : ValidAction α N) →
    (N≡ : N ≡ N′) →
    ⟦ subst (ValidAction α) N≡ vα ⟧ ≡ ⟦ vα ⟧
  ⟦⟧-subst _ refl = refl

instance
  Dec-ValidAction : ValidAction ⁇²
  Dec-ValidAction {AdvanceRound}{N} .dec
    with N .progress ≟ blockMade
  ... | no ¬NBlockMade
    = no λ where (AdvanceRound ⦃ NBlockMade ⦄) → ¬NBlockMade NBlockMade
  ... | yes NBlockMade
    = yes $ AdvanceRound ⦃ NBlockMade ⦄

mutual
  data ValidTrace : Trace → Type where
    [] :
      ─────────────
      ValidTrace []

    _∷_⊣_ : ∀ α →
      ∀ (tr : ValidTrace αs) →
      ∙ ValidAction α ⟦ tr ⟧∗
        ───────────────────
        ValidTrace (α ∷ αs)

  ⟦_⟧∗ : ValidTrace αs → GlobalState
  ⟦_⟧∗ [] = N₀
  ⟦_⟧∗ (_ ∷ _ ⊣ vα) = ⟦ vα ⟧

Irr-ValidAction : Irrelevant (ValidAction α N)
Irr-ValidAction (AdvanceRound ⦃ NBlockMade ⦄) (AdvanceRound ⦃ NBlockMade′ ⦄)
  rewrite ≡-irrelevant NBlockMade NBlockMade′
  = refl

Irr-ValidTrace : Irrelevant (ValidTrace αs)
Irr-ValidTrace [] [] = refl
Irr-ValidTrace (α ∷ vαs ⊣ vα) (.α ∷ vαs′ ⊣ vα′)
  rewrite Irr-ValidTrace vαs vαs′ | Irr-ValidAction vα vα′
  = refl

instance
  Dec-ValidTrace : ValidTrace ⁇¹
  Dec-ValidTrace {tr} .dec with tr
  ... | []     = yes []
  ... | α ∷ αs
    with ¿ ValidTrace αs ¿
  ... | no ¬vαs = no λ where (_ ∷ vαs ⊣ _) → ¬vαs vαs
  ... | yes vαs
    with ¿ ValidAction α ⟦ vαs ⟧∗ ¿
  ... | no ¬vα = no λ where
    (_ ∷ tr ⊣ vα) → ¬vα
                  $ subst (ValidAction α) (cong ⟦_⟧∗ $ Irr-ValidTrace tr vαs) vα
  ... | yes vα = yes $ _ ∷ vαs ⊣ vα

getLabel : N ↝ N′ → Action
getLabel {N}{N′} = λ where
  (advanceRound _) → AdvanceRound
  _ → {!!}

getLabels : (N ↝⋆ N′) → List Action
getLabels = λ where
  ε → []
  (st ◅ tr) → getLabel st ∷ getLabels tr

ValidAction-sound :
  (va : ValidAction α N) →
  N ↝ ⟦ va ⟧
ValidAction-sound = λ where
  (AdvanceRound ⦃ NBlockMade ⦄) → advanceRound NBlockMade

ValidAction-complete :
  (st : N ↝ N′) →
  ValidAction (getLabel st) N
ValidAction-complete = λ where
  (advanceRound NBlockMade) → AdvanceRound ⦃ NBlockMade ⦄
  _ → {!!}

ValidAction-⟦⟧ : (st : N ↝ N′) → ⟦ ValidAction-complete st ⟧ ≡ N′
ValidAction-⟦⟧ = λ where
  (advanceRound _) → refl
  _ → {!!}

ValidTrace-sound :
  (tr : ValidTrace αs) →
  N₀ ↝⋆ ⟦ tr ⟧∗
ValidTrace-sound [] = ε
ValidTrace-sound (α ∷ tr ⊣ vα) = ValidTrace-sound tr ◅◅ ValidAction-sound vα ◅ ε

ValidTrace-complete :
  (st : N₀ ↝⋆ N) →
  ∃ λ (tr : ValidTrace (getLabels st)) →
    ⟦ tr ⟧∗ ≡ N
ValidTrace-complete = {!!}
