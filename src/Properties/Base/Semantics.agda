open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Base.Semantics
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄

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
