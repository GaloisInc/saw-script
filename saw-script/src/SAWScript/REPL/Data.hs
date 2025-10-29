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
    getSAWScriptTypeNames,
    getSAWScriptVarEnv,
    getSAWScriptTypeEnv,
 ) where

import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import qualified Data.Map as Map
--import Data.Map (Map)
import qualified Data.Text as Text
import Data.Text (Text)

import qualified Cryptol.ModuleSystem.NamingEnv as MN
import Cryptol.Utils.Ident (Namespace(..))
import Cryptol.Utils.PP

import qualified SAWSupport.ScopedMap as ScopedMap
import CryptolSAWCore.CryptolEnv

import qualified SAWCentral.AST as AST
import SAWCentral.Value (TopLevelRW(..), Environ(..))

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

-- Type shorthand for list of pairs of names and types.
type VarEnvList = [(Text, AST.Schema)]

-- | Get names and printed types from the SAWScript variable
--   environment.
--
--   Returns the rebindable environment and a list of scopes, with the
--   innermost scope last. (That's the normal print order.)
--
getSAWScriptVarEnv :: REPL (VarEnvList, [VarEnvList])
getSAWScriptVarEnv = do
  rw <- getTopLevelRW
  let Environ varenv _tyenv _cryenv = rwEnviron rw
      rbenv = rwRebindables rw
      avail = rwPrimsAvail rw

  -- Get the rebindable globals. These are always visible.
  let extractRB (x, (_pos, ty, _v)) = (x, ty)
      rebindables = map extractRB $ Map.assocs rbenv

  -- Get the scopes.
  --
  -- Reverse the list so the innermost is last, because that's what
  -- people will expect to see when it's printed.
  --
  let extractVar (x, (_pos, lc, ty, _v, _doc)) =
        if Set.member lc avail then Just (x, ty)
        else Nothing
      extractScope entries = mapMaybe extractVar entries
      scopes = map extractScope $ reverse $ ScopedMap.scopedAssocs varenv

  return (rebindables, scopes)

-- Type shorthand for list of pairs of names and type expansions.
type TypeEnvList = [(Text, AST.NamedType)]

-- | Get names and printed types from the SAWScript type environment.
--
--   Returns a list of scopes, with the innermost scope last. (That's
--   the normal print order.)
--
getSAWScriptTypeEnv :: REPL [TypeEnvList]
getSAWScriptTypeEnv = do
  rw <- getTopLevelRW
  let Environ _varenv tyenv _cryenv = rwEnviron rw
      avail = rwPrimsAvail rw

  -- Get the scopes.
  --
  -- Reverse the list so the innermost is last, because that's what
  -- people will expect to see when it's printed.
  --
  let extractTyVar (x, (lc, ty)) =
        if Set.member lc avail then Just (x, ty)
        else Nothing
      extractScope entries = mapMaybe extractTyVar entries
      scopes = map extractScope $ reverse $ ScopedMap.scopedAssocs tyenv

  return scopes
