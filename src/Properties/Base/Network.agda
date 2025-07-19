{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove when holes are filled

open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Base.Network
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.Network ⦃ params ⦄; open Envelope
open import Protocol.Message ⦃ params ⦄
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_ ; ≡ˢ-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (map⁺)
open import Data.List.Relation.Binary.BagAndSetEquality using (↭⇒∼bag; bag-=⇒)

messagesAfterTickPreservation : ∀ (N : GlobalState) →
  L.map msg (tick N .messages) ≡ L.map msg (N .messages)
messagesAfterTickPreservation N
  rewrite
    sym $ L.map-∘ {g = msg} {f = decreaseDelay} (N .messages)
    = refl

messagesAfterPermutationPreservation : ∀ {N : GlobalState} {envelopes : List Envelope} →
    N .messages ↭ envelopes
  → L.map msg envelopes ≡ˢ L.map msg (N .messages)
messagesAfterPermutationPreservation π = ≡ˢ-sym $ bag-=⇒ $ ↭⇒∼bag $ map⁺ msg π

immediateMessagesPreservation-∉-↓∗ : ∀ {N N′ : GlobalState} {ps : List Party} {p : Party} →
    p ∉ ps
  → _ ⊢ N —[ ps ]↓→∗ N′
  → immediateMsgs p N′ ≡ immediateMsgs p N
immediateMessagesPreservation-∉-↓∗ = {!!}
