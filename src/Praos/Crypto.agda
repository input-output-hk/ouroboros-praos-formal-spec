module Praos.Crypto where

-- Cryptographic primitives types

postulate
  ByteString : Set
  emptyBS : ByteString

{-# FOREIGN GHC import qualified Data.ByteString as BS #-}
{-# COMPILE GHC ByteString = type BS.ByteString #-}
{-# COMPILE GHC emptyBS = BS.empty #-}

record Hash (a : Set) : Set where
  constructor MkHash
  field hashBytes : ByteString

open Hash public

record Hashable (a : Set) : Set where
  field hash : a → Hash a

record MembershipProof : Set where
  field proofM : ByteString

open MembershipProof public

record LeadershipProof : Set where
  field proof : ByteString

open LeadershipProof public

record Signature : Set where
  field bytes : ByteString

open Signature public

record VerificationKey : Set where
  field verificationKey : ByteString

open VerificationKey public
