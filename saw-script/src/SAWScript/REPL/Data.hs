{- |
Module      : SAWScript.REPL.Data
Description :
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional
-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

module SAWScript.REPL.Data (
    getCryptolExprNames,
    getCryptolTypeNames,
    getSAWScriptValueNames,
    getSAWScriptTypeNames
 ) where

import qualified Data.Set as Set
--import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text as Text

import qualified Cryptol.ModuleSystem.NamingEnv as MN
import Cryptol.Utils.Ident (Namespace(..))
import Cryptol.Utils.PP

import qualified SAWSupport.ScopedMap as ScopedMap
import CryptolSAWCore.CryptolEnv

import SAWCentral.TopLevel (TopLevelRW(..))
import SAWCentral.Value (Environ(..))

import SAWScript.REPL.Monad


-- | Get visible Cryptol variable names.
getCryptolExprNames :: REPL [String]
getCryptolExprNames =
  do fNames <- fmap getNamingEnv getCryptolEnv
     return (map (show . pp) (Map.keys (MN.namespaceMap NSValue fNames)))

-- | Get visible Cryptol type names.
getCryptolTypeNames :: REPL [String]
getCryptolTypeNames =
  do fNames <- fmap getNamingEnv getCryptolEnv
     return (map (show . pp) (Map.keys (MN.namespaceMap NSType fNames)))

-- | Get visible variable names for Haskeline completion.
getSAWScriptValueNames :: REPL [String]
getSAWScriptValueNames = do
  rw <- getTopLevelRW
  let avail = rwPrimsAvail rw
      visible (_, lc, _, _, _) = Set.member lc avail
      Environ valenv _tyenv _cryenv = rwEnviron rw
      rbenv = rwRebindables rw
  let rnames1 = ScopedMap.allKeys $ ScopedMap.filter visible valenv
      rnames2 = Map.keys rbenv
  return (map Text.unpack (rnames1 ++ rnames2))

-- | Get visible type names for Haskeline completion.
getSAWScriptTypeNames :: REPL [String]
getSAWScriptTypeNames = do
  rw <- getTopLevelRW
  let avail = rwPrimsAvail rw
      visible (lc, _) = Set.member lc avail
      Environ _valenv tyenv _cryenv = rwEnviron rw
  let rnames = ScopedMap.allKeys $ ScopedMap.filter visible tyenv
  return (map Text.unpack rnames)
