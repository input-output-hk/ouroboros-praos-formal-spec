open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Base.Semantics
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Protocol.BaseTypes using (Honesty)
open import Data.Maybe.Properties.Ext using (isJust)
open Honesty

↝↓-injective : ∀ {N N′ N″ : GlobalState} {p : Party} → _ ⊢ N —[ p ]↓→ N′ → _ ⊢ N —[ p ]↓→ N″ → N″ ≡ N′
↝↓-injective (unknownParty↓ _  ) (unknownParty↓ _   ) = refl
↝↓-injective (unknownParty↓ π  ) (honestParty↓  π′ _) = contradiction π (subst (_≢ nothing) (sym π′) λ ())
↝↓-injective (unknownParty↓ π  ) (corruptParty↓ π′ _) = contradiction π (subst (_≢ nothing) (sym π′) λ ())
↝↓-injective (honestParty↓  π _) (unknownParty↓ π′  ) = contradiction π′ (subst (_≢ nothing) (sym π) λ ())
↝↓-injective (honestParty↓  π _) (honestParty↓  π′ _) rewrite M.just-injective (trans (sym π′) π) = refl
↝↓-injective (honestParty↓  _ π) (corruptParty↓ _ π′) = contradiction π $ corrupt⇒¬honest π′
↝↓-injective (corruptParty↓ π _) (unknownParty↓ π′  ) = contradiction π′ (subst (_≢ nothing) (sym π) λ ())
↝↓-injective (corruptParty↓ _ π) (honestParty↓  _ π′) = contradiction π′ $ corrupt⇒¬honest π
↝↓-injective (corruptParty↓ _ _) (corruptParty↓ _ _ ) = refl

↝↓-total : ∀ N p → ∃[ N′ ] _ ⊢ N —[ p ]↓→ N′
↝↓-total N p with N .states ⁉ p in eq
... | nothing   = N , unknownParty↓ eq
... | just ls with honestyOf p in honesty
...   | honest  = honestMsgsDelivery  p ls N , honestParty↓  eq honesty
...   | corrupt = corruptMsgsDelivery p    N , corruptParty↓ eq honesty

instance
  Computational-↝↓ : Computational _⊢_—[_]↓→_
  Computational-↝↓ = record {go} where module go where

    functional : ∀ {N p} → Functional (_ ⊢ N —[ p ]↓→_)
    functional {N} {p} {s} {s′} = sym ∘₂ ↝↓-injective {N} {N′ = s} {N″ = s′} {p = p}

    decidable : ∀ N p → Dec $ ∃ (_ ⊢ N —[ p ]↓→_)
    decidable = yes ∘₂ ↝↓-total

compute-↝↓ = Computational.compute Computational-↝↓

compute-↝↓-total : ∀ N p → isJust $ compute-↝↓ N p
compute-↝↓-total N p = _

↝↓∗-total : ∀ N ps → ∃[ N′ ] _ ⊢ N —[ ps ]↓→∗ N′
↝↓∗-total N [] = N , []
↝↓∗-total N (p ∷ ps) =
  let
    (N′ , q) = ↝↓-total N p
    (N″ , r) = ↝↓∗-total N′ ps
  in
    N″ , q ∷ r

instance
  Computational-↝↓∗ : Computational _⊢_—[_]↓→∗_
  Computational-↝↓∗ = Computational∗

compute-↝↓∗ = Computational.compute Computational-↝↓∗

compute-↝↓∗-total : ∀ N ps → isJust $ compute-↝↓∗ N ps
compute-↝↓∗-total N ps rewrite Computational.completeness Computational-↝↓∗ _ _ _ (↝↓∗-total N ps .proj₂) = _

↝↑-injective : ∀ {N N′ N″ : GlobalState} {p : Party} → _ ⊢ N —[ p ]↑→ N′ → _ ⊢ N —[ p ]↑→ N″ → N″ ≡ N′
↝↑-injective (unknownParty↑ _  ) (unknownParty↑ _   ) = refl
↝↑-injective (unknownParty↑ π  ) (honestParty↑  π′ _) = contradiction π (subst (_≢ nothing) (sym π′) λ ())
↝↑-injective (unknownParty↑ π  ) (corruptParty↑ π′ _) = contradiction π (subst (_≢ nothing) (sym π′) λ ())
↝↑-injective (honestParty↑  π _) (unknownParty↑ π′  ) = contradiction π′ (subst (_≢ nothing) (sym π) λ ())
↝↑-injective (honestParty↑  π _) (honestParty↑  π′ _) rewrite M.just-injective (trans (sym π′) π) = refl
↝↑-injective (honestParty↑  _ π) (corruptParty↑ _ π′) = contradiction π $ corrupt⇒¬honest π′
↝↑-injective (corruptParty↑ π _) (unknownParty↑ π′  ) = contradiction π′ (subst (_≢ nothing) (sym π) λ ())
↝↑-injective (corruptParty↑ _ π) (honestParty↑  _ π′) = contradiction π′ $ corrupt⇒¬honest π
↝↑-injective (corruptParty↑ _ _) (corruptParty↑ _ _ ) = refl

↝↑-total : ∀ N p → ∃[ N′ ] _ ⊢ N —[ p ]↑→ N′
↝↑-total N p with N .states ⁉ p in eq
... | nothing   = N , unknownParty↑ eq
... | just ls with honestyOf p in honesty
...   | honest  = honestBlockMaking  p ls N , honestParty↑  eq honesty
...   | corrupt = corruptBlockMaking p    N , corruptParty↑ eq honesty

instance
  Computational-↝↑ : Computational _⊢_—[_]↑→_
  Computational-↝↑ = record {go} where module go where

    functional : ∀ {N p} → Functional (_ ⊢ N —[ p ]↑→_)
    functional {N} {p} {s} {s′} = sym ∘₂ ↝↑-injective {N} {N′ = s} {N″ = s′} {p = p}

    decidable : ∀ N p → Dec $ ∃ (_ ⊢ N —[ p ]↑→_)
    decidable = yes ∘₂ ↝↑-total

compute-↝↑ = Computational.compute Computational-↝↑

compute-↝↑-total : ∀ N p → isJust $ compute-↝↑ N p
compute-↝↑-total N p = _

↝↑∗-total : ∀ N ps → ∃[ N′ ] _ ⊢ N —[ ps ]↑→∗ N′
↝↑∗-total N [] = N , []
↝↑∗-total N (p ∷ ps) =
  let
    (N′ , q) = ↝↑-total N p
    (N″ , r) = ↝↑∗-total N′ ps
  in
    N″ , q ∷ r

instance
  Computational-↝↑∗ : Computational _⊢_—[_]↑→∗_
  Computational-↝↑∗ = Computational∗

compute-↝↑∗ = Computational.compute Computational-↝↑∗

compute-↝↑∗-total : ∀ N ps → isJust $ compute-↝↑∗ N ps
compute-↝↑∗-total N ps rewrite Computational.completeness Computational-↝↑∗ _ _ _ (↝↑∗-total N ps .proj₂) = _
