module Praos.Crypto where

-- Cryptographic primitives types

open import Prelude.Init

postulate
  ByteString : Type
  emptyBS : ByteString

{-# FOREIGN GHC import qualified Data.ByteString as BS #-}
{-# COMPILE GHC ByteString = type BS.ByteString #-}
{-# COMPILE GHC emptyBS = BS.empty #-}

record Hash (a : Type) : Type where
  constructor MkHash
  field hashBytes : ByteString

open Hash public

record Hashable (a : Type) : Type where
  field hash : a → Hash a

record MembershipProof : Type where
  field proofM : ByteString

open MembershipProof public

record LeadershipProof : Type where
  field proof : ByteString

open LeadershipProof public

record Signature : Type where
  field bytes : ByteString

open Signature public

record VerificationKey : Type where
  field verificationKey : ByteString

open VerificationKey public
