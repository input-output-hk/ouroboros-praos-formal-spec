module Prelude.DecEq.Ext where

open import Function.Base using (_∋_)
open import Data.Maybe using (Maybe)
open import Prelude.DecEq using (DecEq)
open DecEq ⦃...⦄

instance
  DecEq-Bool = DecEq _ ∋ record {DB} where import Data.Bool as DB

  DecEq-Maybe : ∀ {A : Set} ⦃ _ : DecEq A ⦄ → DecEq (Maybe A)
  DecEq-Maybe ._≟_ = M.≡-dec _≟_
    where import Data.Maybe.Properties as M
