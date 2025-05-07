open import Protocol.Assumptions using (Assumptions)
open import Protocol.Params using (Params)

module Properties.Base.CollisionFree
  ⦃ params : _ ⦄ (open Params params)
  ⦃ assumptions : Assumptions ⦃ params ⦄ ⦄ (open Assumptions assumptions)
  where

open import Protocol.Prelude
open import Protocol.Crypto ⦃ params ⦄ using (Hashable)
open import Protocol.Block ⦃ params ⦄
open import Protocol.Chain ⦃ params ⦄
open import Protocol.Semantics ⦃ params ⦄ ⦃ assumptions ⦄
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (xs⊆x∷xs)
open import Data.List.Relation.Binary.Subset.Propositional.Properties.Ext using (cartesianProduct-⊆-Mono)
open L.All using (All; anti-mono)
open Hashable ⦃ ... ⦄
open import Properties.Base.BlockHistory ⦃ params ⦄ ⦃ assumptions ⦄

BlockListCollisionFree : Pred (List Block) 0ℓ
BlockListCollisionFree bs =
  All
    (λ where (b , b′) → hash b ≡ hash b′ → b ≡ b′)
    (L.cartesianProduct bs bs)

BlockListCollisionFree-∷ : ∀ {bs : List Block} {b : Block} → BlockListCollisionFree (b ∷ bs) → BlockListCollisionFree bs
BlockListCollisionFree-∷ {bs} {b} = anti-mono (cartesianProduct-⊆-Mono (xs⊆x∷xs bs b) (xs⊆x∷xs bs b))

BlockListCollisionFree-⊆ : ∀ {bs bs′ : List Block} → bs ⊆ˢ bs′ → BlockListCollisionFree bs′ → BlockListCollisionFree bs
BlockListCollisionFree-⊆ bs⊆ˢbs′ cfbs = anti-mono (cartesianProduct-⊆-Mono bs⊆ˢbs′ bs⊆ˢbs′) cfbs

CollisionFree : Pred GlobalState 0ℓ
CollisionFree N = BlockListCollisionFree gsBlockHistory
  where
    gsBlockHistory = genesisBlock ∷ blockHistory N

progressCollisionFreePreservation : ∀ {N : GlobalState} {s : Progress} → CollisionFree N → CollisionFree (record N {progress = s})
progressCollisionFreePreservation = id

CollisionFreePrev-↓ : ∀ {p : Party} {N₁ N₂ : GlobalState} → _ ⊢ N₁ —[ p ]↓→ N₂ → CollisionFree N₂ → CollisionFree N₁
CollisionFreePrev-↓ {p} {N₁} {N₂} ts cfN₂ = BlockListCollisionFree-⊆ subs cfN₂
  where
    subs : genesisBlock ∷ blockHistory N₁ ⊆ˢ genesisBlock ∷ blockHistory N₂
    subs = L.SubS.∷⁺ʳ genesisBlock (blockHistoryPreservation-↓ ts)

CollisionFreePrev-↑ : ∀ {p : Party} {N₁ N₂ : GlobalState} → _ ⊢ N₁ —[ p ]↑→ N₂ → CollisionFree N₂ → CollisionFree N₁
CollisionFreePrev-↑ {p} {N₁} {N₂} ts cfN₂ = BlockListCollisionFree-⊆ subs cfN₂
  where
    subs : genesisBlock ∷ blockHistory N₁ ⊆ˢ genesisBlock ∷ blockHistory N₂
    subs = L.SubS.∷⁺ʳ genesisBlock (blockHistoryPreservation-↑ ts)

CollisionFreePrev : ∀ {N₁ N₂ : GlobalState} → N₁ ↝⋆ N₂ → CollisionFree N₂ → CollisionFree N₁
CollisionFreePrev {N₁} {N₂} N₁↝⋆N₂ cfN₂ = BlockListCollisionFree-⊆ subs cfN₂
  where
    subs : genesisBlock ∷ blockHistory N₁ ⊆ˢ genesisBlock ∷ blockHistory N₂
    subs = L.SubS.∷⁺ʳ genesisBlock (blockHistoryPreservation-↝⋆ N₁↝⋆N₂)
