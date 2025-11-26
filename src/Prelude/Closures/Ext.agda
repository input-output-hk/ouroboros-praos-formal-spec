-- FIXME: Remove this module when `https://github.com/input-output-hk/iog-agda-prelude/pull/20` is merged
open import Prelude.Init

module Prelude.Closures.Ext {A : Type ℓ} (_—→_ : Rel A ℓ) where

private variable x y z : A

-- right-biased view
_←—_ = flip _—→_

infixr 2 _⟨_⟩←—_
infix -1 _←—_ _↞—_ _⁺↞—_
data _↞—_ : Rel A ℓ where
  _∎ : ∀ x → x ↞— x
  _⟨_⟩←—_ : ∀ z → z ←— y → y ↞— x → z ↞— x
data _⁺↞—_ : Rel A ℓ where
  _⟨_⟩←—_ : ∀ z → z ←— y → y ↞— x → z ⁺↞— x
