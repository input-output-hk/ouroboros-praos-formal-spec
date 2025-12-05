{-# OPTIONS --erasure #-}

open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Protocol.TraceVerifier
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Properties.Base.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Protocol.Prelude
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Protocol.Network ⦃ params ⦄
open import Protocol.BaseTypes using (Honesty)
open import Irrelevance.Core
open import Irrelevance.List.Permutation
open import Data.Maybe.Properties.Ext using (fromJust; just⇒fromJust; Is-just⇒to-witness; isJust⇒Is-just)
open import Relation.Binary.Core using (_⇒_; _⇔_)
open Honesty
open Envelope
open RTC

compute-↝↓-maybe′ : ∀ N p → M.maybe′ (const ⊤) ⊥ (compute-↝↓ N p)
compute-↝↓-maybe′ N p = _

compute-↝↓∗-maybe′ : ∀ N ps → M.maybe′ (const ⊤) ⊥ (compute-↝↓∗ N ps)
compute-↝↓∗-maybe′ N ps rewrite Is-just⇒to-witness $ isJust⇒Is-just (compute-↝↓∗-total N ps) = _

deliverMsgsToF : Party → Op₁ GlobalState
deliverMsgsToF p N = fromJust (compute-↝↓ N p) {pr = compute-↝↓-maybe′ N p}

deliverMsgsTo∗F : List Party → Op₁ GlobalState
deliverMsgsTo∗F ps N = fromJust (compute-↝↓∗ N ps) {pr = compute-↝↓∗-maybe′ N ps}

deliverMsgsF : Op₁ GlobalState
deliverMsgsF N = record (deliverMsgsTo∗F (N .execOrder) N) { progress = msgsDelivered }

↓→-deliverMsgsToF : ∀ N p → _ ⊢ N —[ p ]↓→ deliverMsgsToF p N
↓→-deliverMsgsToF N p = case Computational.decidable Computational-↝↓ N p of λ where
  (no q)         → contradiction (↝↓-total N p) q
  (yes (N′ , q)) → subst (λ ◆ → N ↝[ p ]↓ ◆) (just⇒fromJust {pr = compute-↝↓-maybe′ N p} (sym $ Computational.completeness Computational-↝↓ _ _ _ q)) q

deliverMsgsTo∗F-∷ : ∀ N p ps → deliverMsgsTo∗F (p ∷ ps) N ≡ deliverMsgsTo∗F ps (deliverMsgsToF p N)
deliverMsgsTo∗F-∷ N p ps = case Computational.decidable Computational-↝↓ N p of λ where
  (no q) → contradiction (↝↓-total N p) q
  (yes (N′ , q)) → (case Computational.decidable Computational-↝↓∗ N′ ps of λ where
    (yes (N″ , r)) →
      let
        N″≡  = just⇒fromJust {pr = compute-↝↓∗-maybe′ N (p ∷ ps)} (sym $ Computational.completeness Computational-↝↓∗ _ _ _ (q ∷ r))
        N′≡  = just⇒fromJust {pr = compute-↝↓-maybe′  N  p      } (sym $ Computational.completeness Computational-↝↓  _ _ _   q)
        N″≡′ = just⇒fromJust {pr = compute-↝↓∗-maybe′ N′     ps } (sym $ Computational.completeness Computational-↝↓∗ _ _ _      r)
      in
        subst₂ (λ ◆ ◇ → ◆ ≡ deliverMsgsTo∗F ps ◇) (subst (_≡ deliverMsgsTo∗F (p ∷ ps) N) N″≡′ N″≡) N′≡ refl
    (no r) → contradiction (↝↓∗-total N′ ps) r)

↓→∗-deliverMsgsTo∗F : ∀ N ps → _ ⊢ N —[ ps ]↓→∗ deliverMsgsTo∗F ps N
↓→∗-deliverMsgsTo∗F N [] = []
↓→∗-deliverMsgsTo∗F N (p ∷ ps) rewrite deliverMsgsTo∗F-∷ N p ps = ↓→-deliverMsgsToF N p ∷ ↓→∗-deliverMsgsTo∗F (deliverMsgsToF p N) ps

compute-↝↑-maybe′ : ∀ N p → M.maybe′ (const ⊤) ⊥ (compute-↝↑ N p)
compute-↝↑-maybe′ N p = _

compute-↝↑∗-maybe′ : ∀ N ps → M.maybe′ (const ⊤) ⊥ (compute-↝↑∗ N ps)
compute-↝↑∗-maybe′ N ps rewrite Is-just⇒to-witness $ isJust⇒Is-just (compute-↝↑∗-total N ps) = _

makeBlockForF : Party → Op₁ GlobalState
makeBlockForF p N = fromJust (compute-↝↑ N p) {pr = compute-↝↑-maybe′ N p}

makeBlockFor∗F : List Party → Op₁ GlobalState
makeBlockFor∗F ps N = fromJust (compute-↝↑∗ N ps) {pr = compute-↝↑∗-maybe′ N ps}

makeBlockF : Op₁ GlobalState
makeBlockF N = record (makeBlockFor∗F (N .execOrder) N) { progress = blockMade }

↑→-makeBlockForF : ∀ N p → _ ⊢ N —[ p ]↑→ makeBlockForF p N
↑→-makeBlockForF N p = case Computational.decidable Computational-↝↑ N p of λ where
  (no q)         → contradiction (↝↑-total N p) q
  (yes (N′ , q)) → subst (λ ◆ → N ↝[ p ]↑ ◆) (just⇒fromJust {pr = compute-↝↑-maybe′ N p} (sym $ Computational.completeness Computational-↝↑ _ _ _ q)) q

makeBlockFor∗F-∷ : ∀ N p ps → makeBlockFor∗F (p ∷ ps) N ≡ makeBlockFor∗F ps (makeBlockForF p N)
makeBlockFor∗F-∷ N p ps = case Computational.decidable Computational-↝↑ N p of λ where
  (no q) → contradiction (↝↑-total N p) q
  (yes (N′ , q)) → (case Computational.decidable Computational-↝↑∗ N′ ps of λ where
    (yes (N″ , r)) →
      let
        N″≡  = just⇒fromJust {pr = compute-↝↑∗-maybe′ N (p ∷ ps)} (sym $ Computational.completeness Computational-↝↑∗ _ _ _ (q ∷ r))
        N′≡  = just⇒fromJust {pr = compute-↝↑-maybe′  N  p      } (sym $ Computational.completeness Computational-↝↑  _ _ _   q)
        N″≡′ = just⇒fromJust {pr = compute-↝↑∗-maybe′ N′     ps } (sym $ Computational.completeness Computational-↝↑∗ _ _ _      r)
      in
        subst₂ (λ ◆ ◇ → ◆ ≡ makeBlockFor∗F ps ◇) (subst (_≡ makeBlockFor∗F (p ∷ ps) N) N″≡′ N″≡) N′≡ refl
    (no r) → contradiction (↝↑∗-total N′ ps) r)

↑→∗-makeBlockFor∗F : ∀ N ps → _ ⊢ N —[ ps ]↑→∗ makeBlockFor∗F ps N
↑→∗-makeBlockFor∗F N [] = []
↑→∗-makeBlockFor∗F N (p ∷ ps) rewrite makeBlockFor∗F-∷ N p ps = ↑→-makeBlockForF N p ∷ ↑→∗-makeBlockFor∗F (makeBlockForF p N) ps

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
  DeliverMsgs     : Action
  MakeBlock       : Action
  AdvanceRound    : Action
  PermuteParties  : List Party → Action
  PermuteMsgs     : List Envelope → Action

Trace = List Action

private variable
  N N′ : GlobalState
  α : Action
  αs : Trace

data ValidAction : Action → GlobalState → Type where
  DeliverMsgs : ⦃ _ : N .progress ≡ ready ⦄ →
    ValidAction DeliverMsgs N
  MakeBlock : ⦃ _ : N .progress ≡ msgsDelivered ⦄ →
    ValidAction MakeBlock N
  AdvanceRound : ⦃ _ : N .progress ≡ blockMade ⦄ →
    ValidAction AdvanceRound N
  PermuteParties : ∀ {parties} ⦃ _ : N .execOrder ·↭ parties ⦄ →
    ValidAction (PermuteParties parties) N
  PermuteMsgs : ∀ {envelopes} ⦃ _ : N .messages ·↭ envelopes ⦄ →
    ValidAction (PermuteMsgs envelopes) N

⟦_⟧ : ValidAction α N → GlobalState
⟦_⟧ {α}{N} = λ where
  DeliverMsgs →
    deliverMsgsF N
  MakeBlock →
    makeBlockF N
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
  Dec-ValidAction {DeliverMsgs}{N} .dec
    with N .progress ≟ ready
  ... | no ¬r
    = no λ where (DeliverMsgs ⦃ r ⦄) → ¬r r
  ... | yes r
    = yes $ DeliverMsgs ⦃ r ⦄
  Dec-ValidAction {MakeBlock}{N} .dec
    with N .progress ≟ msgsDelivered
  ... | no ¬m
    = no λ where (MakeBlock ⦃ m ⦄) → ¬m m
  ... | yes m
    = yes $ MakeBlock ⦃ m ⦄
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
Irr-ValidAction (DeliverMsgs ⦃ r ⦄) (DeliverMsgs ⦃ r′ ⦄)
  rewrite ≡-irrelevant r r′
  = refl
Irr-ValidAction (MakeBlock ⦃ m ⦄) (MakeBlock ⦃ m′ ⦄)
  rewrite ≡-irrelevant m m′
  = refl
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
getLabel {N} {N′} = λ where
  (deliverMsgs                     _ _) → DeliverMsgs
  (makeBlock                       _ _) → MakeBlock
  (advanceRound                    _  ) → AdvanceRound
  (permuteParties {parties   = ps} _  ) → PermuteParties ps
  (permuteMsgs    {envelopes = es} _  ) → PermuteMsgs es

getLabels : (N′ ↞— N) → List Action
getLabels = λ where
  (_ ∎) → []
  (_ ⟨ st ⟩←— tr) → getLabel st ∷ getLabels tr

ValidAction-sound :
  (va : ValidAction α N) →
  N —→ ⟦ va ⟧
ValidAction-sound = λ where
  (DeliverMsgs    {N} ⦃ r   ⦄) → deliverMsgs    r  (↓→∗-deliverMsgsTo∗F N (N .execOrder))
  (MakeBlock      {N} ⦃ m   ⦄) → makeBlock      m  (↑→∗-makeBlockFor∗F  N (N .execOrder))
  (AdvanceRound       ⦃ bm  ⦄) → advanceRound   bm
  (PermuteParties     ⦃ eo↭ ⦄) → permuteParties eo↭
  (PermuteMsgs        ⦃ ms↭ ⦄) → permuteMsgs    ms↭

ValidAction-complete :
  (st : N —→ N′) →
  ValidAction (getLabel st) N
ValidAction-complete = λ where
  (deliverMsgs    r  _) → DeliverMsgs    ⦃ r   ⦄
  (makeBlock      m  _) → MakeBlock      ⦃ m   ⦄
  (advanceRound   bm  ) → AdvanceRound   ⦃ bm  ⦄
  (permuteParties eo↭ ) → PermuteParties ⦃ eo↭ ⦄
  (permuteMsgs    ms↭ ) → PermuteMsgs    ⦃ ms↭ ⦄

ValidAction-⟦⟧ : (st : N —→ N′) → ⟦ ValidAction-complete st ⟧ ≡ N′
ValidAction-⟦⟧ {N} (deliverMsgs {N′ = N″} _ ts) =
  let open ≡-Reasoning renaming (begin_ to ≡-begin_; _∎ to _≡-∎) in
    ≡-begin
      record (deliverMsgsTo∗F (N .execOrder) N) { progress = msgsDelivered }
    ≡⟨ cong (λ ◆ → record ◆ { progress = msgsDelivered }) (Computational.functional Computational-↝↓∗ (↓→∗-deliverMsgsTo∗F N (N .execOrder)) ts) ⟩
      record N″ { progress = msgsDelivered }
    ≡-∎
ValidAction-⟦⟧ {N} (makeBlock {N′ = N″} _ ts) =
  let open ≡-Reasoning renaming (begin_ to ≡-begin_; _∎ to _≡-∎) in
    ≡-begin
      record (makeBlockFor∗F (N .execOrder) N) { progress = blockMade }
    ≡⟨ cong (λ ◆ → record ◆ { progress = blockMade }) (Computational.functional Computational-↝↑∗ (↑→∗-makeBlockFor∗F N (N .execOrder)) ts) ⟩
      record N″ { progress = blockMade }
    ≡-∎
ValidAction-⟦⟧ (advanceRound   _) = refl
ValidAction-⟦⟧ (permuteParties _) = refl
ValidAction-⟦⟧ (permuteMsgs    _) = refl

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
