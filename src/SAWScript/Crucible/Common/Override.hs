{- |
Module      : SAWScript.Crucible.Common.Override
Description : Override pre- and post-condition matching
License     : BSD3
Maintainer  : langston
Stability   : provisional
-}

module SAWScript.Crucible.Common.Override
  (
  -- * "SAWScript.Crucible.Common.Override.Monad"
    Pointer
  , OverrideMatcherRW(..)
  , omAsserts
  , omArgAsserts
  , omAssumes
  , omFree
  , omLocation
  , omGlobals
  , omSymInterface
  , setupValueSub
  , termSub
  --
  , OverrideFailureReason(..)
  , ppOverrideFailureReason
  , OverrideFailure(..)
  , ppOverrideFailure
  --
  , OverrideMatcher(..)
  , runOverrideMatcher
  , RO
  , RW
  , addAssert
  , addAssume
  , readGlobal
  , writeGlobal
  , failure
  , getSymInterface
  --
  , assignmentToList

  -- * "SAWScript.Crucible.Common.Override.Operations"
  , stateCond
  , resolveSAWPred
  , assignTerm
  , matchTerm
  , instantiateSetupValue
  ) where

import SAWScript.Crucible.Common.Override.Monad
import SAWScript.Crucible.Common.Override.Operations
