{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled in

{-# OPTIONS --erasure #-}

open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Protocol.TraceVerifier
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Protocol.Network ⦃ params ⦄
open import Irrelevance.Core
open import Irrelevance.List.Permutation
open import Relation.Binary.Core using (_⇒_; _⇔_)
open Envelope
open RTC

advanceRoundF : Op₁ GlobalState
advanceRoundF N = record (tick N) { progress = ready }

permutePartiesF : List Party → Op₁ GlobalState
permutePartiesF parties N = record N { execOrder = parties }

permuteMsgsF : List Envelope → Op₁ GlobalState
permuteMsgsF envelopes N = record N { messages = envelopes }

-- NOTE: Modified `↝` to work with irrelevant permutations
data _—→_ : Rel GlobalState 0ℓ where

  deliverMsgs : ∀ {N N′ : GlobalState}
    → N .progress ≡ ready
    → _ ⊢ N —[ N .execOrder ]↓→∗ N′
    ------------------------------------
    → N —→ record N′ { progress = msgsDelivered }

  makeBlock : ∀ {N N′ : GlobalState}
    → N .progress ≡ msgsDelivered
    → _ ⊢ N —[ N .execOrder ]↑→∗ N′
    ------------------------------------
    → N —→ record N′ { progress = blockMade }

  advanceRound : ∀ {N : GlobalState}
    → N .progress ≡ blockMade
    ------------------------------------
    → N —→ record (tick N) { progress = ready }

  permuteParties : ∀ {N : GlobalState} {parties : List Party}
    → N .execOrder ·↭ parties
    ------------------------------------
    → N —→ record N { execOrder = parties }

  permuteMsgs : ∀ {N : GlobalState} {envelopes : List Envelope}
    → N .messages ·↭ envelopes
    ------------------------------------
    → N —→ record N { messages = envelopes }

↝-⇔-—→ : _↝_ ⇔ _—→_
↝-⇔-—→ = from , to
  where
    from : _↝_ ⇒ _—→_
    from (deliverMsgs    p q) = deliverMsgs    p q
    from (makeBlock      p q) = makeBlock      p q
    from (advanceRound     p) = advanceRound   p
    from (permuteParties   p) = permuteParties (↭⇒·↭ p)
    from (permuteMsgs      p) = permuteMsgs    (↭⇒·↭ p)

    to : _—→_ ⇒ _↝_
    to (deliverMsgs    p q) = deliverMsgs    p q
    to (makeBlock      p q) = makeBlock      p q
    to (advanceRound     p) = advanceRound   p
    to (permuteParties   p) = permuteParties (·↭⇒↭ p)
    to (permuteMsgs      p) = permuteMsgs    (·↭⇒↭ p)

open import Prelude.Closures _—→_ hiding (Trace)

data Action : Type where
--  DeliverMsgs     : ??? → Action
--  MakeBlock       : ??? → Action
  AdvanceRound    : Action
  PermuteParties  : List Party → Action
  PermuteMsgs     : List Envelope → Action

Trace = List Action

private variable
  N N′ : GlobalState
  α : Action
  αs : Trace

data ValidAction : Action → GlobalState → Type where
  AdvanceRound : ⦃ _ : N .progress ≡ blockMade ⦄ →
    ValidAction AdvanceRound N
  PermuteParties : ∀ {parties} ⦃ _ : N .execOrder ·↭ parties ⦄ →
    ValidAction (PermuteParties parties) N
  PermuteMsgs : ∀ {envelopes} ⦃ _ : N .messages ·↭ envelopes ⦄ →
    ValidAction (PermuteMsgs envelopes) N

⟦_⟧ : ValidAction α N → GlobalState
⟦_⟧ {α}{N} = λ where
  AdvanceRound →
    advanceRoundF N
  (PermuteParties {parties = ps}) →
    permutePartiesF ps N
  (PermuteMsgs {envelopes = es}) →
    permuteMsgsF es N

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
  ... | no ¬bm
    = no λ where (AdvanceRound ⦃ bm ⦄) → ¬bm bm
  ... | yes bm
    = yes $ AdvanceRound ⦃ bm ⦄
  Dec-ValidAction {PermuteParties ps}{N} .dec
    with ¿ N .execOrder ·↭ ps ¿
  ... | no ¬eo↭
    = no λ where (PermuteParties ⦃ eo↭ ⦄) → ¬eo↭ eo↭
  ... | yes eo↭
    = yes $ PermuteParties ⦃ eo↭ ⦄
  Dec-ValidAction {PermuteMsgs es}{N} .dec
    with ¿ N .messages ·↭ es ¿
  ... | no ¬ms↭
    = no λ where (PermuteMsgs ⦃ ms↭ ⦄) → ¬ms↭ ms↭
  ... | yes ms↭
    = yes $ PermuteMsgs ⦃ ms↭ ⦄

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
Irr-ValidAction (AdvanceRound ⦃ bm ⦄) (AdvanceRound ⦃ bm′ ⦄)
  rewrite ≡-irrelevant bm bm′
  = refl
Irr-ValidAction (PermuteParties ⦃ eo↭ ⦄) (PermuteParties ⦃ eo↭′ ⦄)
  rewrite ∀≡ eo↭ eo↭′
  = refl
Irr-ValidAction (PermuteMsgs ⦃ ms↭ ⦄) (PermuteMsgs ⦃ ms↭′ ⦄)
  rewrite ∀≡ ms↭ ms↭′
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

getLabel : N —→ N′ → Action
getLabel {N}{N′} = λ where
  (advanceRound _) → AdvanceRound
  (permuteParties {parties = ps} _) → PermuteParties ps
  (permuteMsgs {envelopes = es} _) → PermuteMsgs es
  (deliverMsgs _ _) → {!!}
  (makeBlock _ _) → {!!}

getLabels : (N′ ↞— N) → List Action
getLabels = λ where
  (_ ∎) → []
  (_ ⟨ st ⟩←— tr) → getLabel st ∷ getLabels tr

ValidAction-sound :
  (va : ValidAction α N) →
  N —→ ⟦ va ⟧
ValidAction-sound = λ where
  (AdvanceRound ⦃ bm ⦄) → advanceRound bm
  (PermuteParties ⦃ eo↭ ⦄) → permuteParties eo↭
  (PermuteMsgs ⦃ ms↭ ⦄) → permuteMsgs ms↭

ValidAction-complete :
  (st : N —→ N′) →
  ValidAction (getLabel st) N
ValidAction-complete = λ where
  (advanceRound bm) → AdvanceRound ⦃ bm ⦄
  (permuteParties eo↭) → (PermuteParties ⦃ eo↭ ⦄)
  (permuteMsgs ms↭) → (PermuteMsgs ⦃ ms↭ ⦄)
  (deliverMsgs _ _) → {!!}
  (makeBlock _ _) → {!!}

ValidAction-⟦⟧ : (st : N —→ N′) → ⟦ ValidAction-complete st ⟧ ≡ N′
ValidAction-⟦⟧ = λ where
  (advanceRound _) → refl
  (permuteParties eo↭) → refl
  (permuteMsgs ms↭) → refl
  (deliverMsgs _ _) → {!!}
  (makeBlock _ _) → {!!}

ValidTrace-sound :
  (tr : ValidTrace αs) →
  ⟦ tr ⟧∗ ↞— N₀
ValidTrace-sound [] = _ ∎
ValidTrace-sound (α ∷ tr ⊣ vα) = _ ⟨ ValidAction-sound vα ⟩←— ValidTrace-sound tr

ValidTrace-complete :
  (st : N ↞— N₀) →
  ∃ λ (tr : ValidTrace (getLabels st)) →
    ⟦ tr ⟧∗ ≡ N
ValidTrace-complete (_ ∎) = [] , refl
ValidTrace-complete {N} (_ ⟨ st ⟩←— tr)
  =
  let
    vtr , ≡s = ValidTrace-complete tr

    α  = getLabel st
    vα = ValidAction-complete st

    open ≡-Reasoning
  in
    (_ ∷ vtr ⊣ subst (ValidAction _) (sym ≡s) (ValidAction-complete st)) ,
    (≡-Reasoning.begin
      ⟦ subst (ValidAction α) (sym ≡s) vα ⟧
    ≡⟨  ⟦⟧-subst vα (sym ≡s) ⟩
      ⟦ vα ⟧
    ≡⟨ ValidAction-⟦⟧ st ⟩
      N
    ≡-Reasoning.∎)
