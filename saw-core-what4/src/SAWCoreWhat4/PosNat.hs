------------------------------------------------------------------------
-- |
-- Module      : SAWCoreWhat4.PosNat
-- Copyright   : Galois, Inc. 2018
-- License     : BSD3
-- Maintainer  : sweirich@galois.com
-- Stability   : experimental
-- Portability : non-portable (language extensions)
--
-- A runtime representation of positive nats
------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}

-- This module makes use of 'KnownNat' constraints in its interface as
-- opposed to arguments of type 'NatRepr' or 'PosNatRepr'
-- (cf. 'addPosNat'). As a result, we need two

-- to allow implicitly provided nats
{-# LANGUAGE AllowAmbiguousTypes #-}

-- to allow 'WithKnownNat'
{-# OPTIONS_GHC -Wno-warnings-deprecations #-}

module SAWCoreWhat4.PosNat where
-- TODO: find the right place for this code

import GHC.TypeNats (KnownNat, Nat)
import Data.Parameterized.NatRepr
import Data.Parameterized.Some(Some(..))


-- We include the KnownNat constraint here so that we can avoid using
-- withKnownNat outside this module.  The downside is that we have two
-- different runtime representations of these positive nats --- the
-- one stored in the KnownNat, and the one stored in the NatRepr.

-- | Runtime representation of a non-zero natural number
data PosNat (n :: Nat) where
  PosNat :: (1 <= n, KnownNat n) => NatRepr n -> PosNat n

-- | Check whether an integer is a positive nat
somePosNat :: Integral a => a -> Maybe (Some PosNat)
somePosNat n
  | Just (Some nr) <- someNat n,
    Just LeqProof  <- testLeq (knownNat @1) nr
  = withKnownNat nr $ Just (Some (PosNat nr))
  | otherwise
  = Nothing

-- The above definition should be added to
-- 'Data.Parameterized.NatRepr' so that the redundant check for
-- positivity can be removed. Annoyingly, we cannot do 'testLeq'
-- without already knowing that w >= 0)


-- | Add two numbers together and return a proof that their
-- result is positive.
addPosNat :: forall w1 w2.
  (1 <= w1, 1 <= w2, KnownNat w1, KnownNat w2) => PosNat (w1 + w2)
addPosNat =
  let w1  = knownNat @w1
      w2  = knownNat @w2
      sm  = addNat w1 w2 in
  case leqAddPos w1 w2 of
    LeqProof -> withKnownNat sm $ PosNat sm

-- I would hope that the 'leqAddPos' call can be compiled away...


--- Not needed but included for completeness

-- | Compare for equality, returning witness if true
instance TestEquality PosNat where
  testEquality (PosNat n1) (PosNat n2) =
    case testEquality n1 n2 of
      Just Refl -> Just Refl
      Nothing   -> Nothing
