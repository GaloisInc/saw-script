{- |
Module      : SAWCore.Name
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

Various kinds of names.
-}

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module SAWCore.Name
  ( -- * Module names
    ModuleName, mkModuleName
  , preludeName
  , moduleNameText
  , moduleNamePieces
  , qualNameModule
   -- * Qualified Names
  , QualName
  , mkQualName
  , identText
  , toShortName
  , toAbsoluteName
  , nameAliases
  , scFreshQualName
    -- * Name
  , VarIndex
  , Name(..)
    -- * VarName
  , VarName(..)
  , wildcardVarName
  , VarCtx(..)
  , emptyVarCtx
  , consVarCtx
  , lookupVarCtx
    -- * Display Name Environments
  , DisplayNameEnv(..)
  , emptyDisplayNameEnv
  , extendDisplayNameEnv
  , filterDisplayNameEnv
  , mergeDisplayNameEnv
  , resolveDisplayName
  , bestDisplayName
  , allDisplayNames
  , deleteDisplayNameEnv
  ) where

import           Data.Hashable
import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import           Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Text (Text)
import qualified Data.Text as Text
-- import           GHC.Generics (Generic)
import qualified Language.Haskell.TH.Syntax as TH

import SAWCore.Panic (panic)
import SAWCore.QualName (QualName)
import qualified SAWCore.QualName as QN

-- Module Names ----------------------------------------------------------------

newtype ModuleName = ModuleName QN.QualName
  deriving (Eq, Ord, Hashable, TH.Lift)

instance Show ModuleName where
  show mn = Text.unpack (moduleNameText mn)

moduleNameText :: ModuleName -> Text
moduleNameText (ModuleName qn) = QN.ppQualName (qn{ QN.namespace = Nothing })

moduleNamePieces :: ModuleName -> [Text]
moduleNamePieces (ModuleName qn) = QN.fullPath qn

-- | Create a module name given a list of strings with the top-most
-- module name given first.
mkModuleName :: [Text] -> ModuleName
mkModuleName [] = panic "mkModuleName" ["empty list"]
mkModuleName (nm:nms) = ModuleName $ QN.fromPath QN.NamespaceCore (nm :| nms)

preludeName :: ModuleName
preludeName = mkModuleName ["Prelude"]

qualNameModule :: QN.QualName -> Maybe ModuleName
qualNameModule qn =
  case QN.split qn of
    Just (q, _, _) -> Just (ModuleName q)
    Nothing -> Nothing


-- Qualified Names -------------------------------------------------------------

identText :: QualName -> Text
identText qn = QN.ppQualName (qn{ QN.namespace = Nothing })

mkQualName :: ModuleName -> Text -> QualName
mkQualName (ModuleName m) s = QN.qualify m s

nameAliases :: QualName -> [Text]
nameAliases = QN.aliases

toShortName :: QualName -> Text
toShortName = QN.baseName

toAbsoluteName :: QualName -> Text
toAbsoluteName = QN.ppQualName

scFreshQualName :: Text -> VarIndex -> QualName
scFreshQualName nm i = QN.fromNameIndex QN.NamespaceFresh (if Text.null nm then "_" else nm) i

-- Global Names ----------------------------------------------------------------

type VarIndex = Int

-- | A global name with a unique ID. We maintain a global invariant
-- that the 'VarIndex' and the 'QualName' must be in a strict
-- one-to-one correspondence: Each 'VarIndex' is paired with a unique
-- 'QualName', and each 'QualName' is paired with a unique 'VarIndex'.
data Name =
  Name
  { nameIndex :: !VarIndex
  , nameQualName :: !QualName
  }
  deriving (Show)

-- | Because of the global uniqueness invariant, comparing the
-- 'VarIndex' is sufficient to ensure equality of names.
instance Eq Name where
  x == y = nameIndex x == nameIndex y

instance Ord Name where
  compare x y = compare (nameIndex x) (nameIndex y)

-- | For hashing, we consider only the 'QualName' and not the
-- 'VarIndex'; this gives a stable hash value for a particular name,
-- even if the unique IDs are assigned differently from run to run.
instance Hashable Name where
  hashWithSalt x nm = hashWithSalt x (nameQualName nm)


-- Variable Names --------------------------------------------------------------

-- | A variable name with a unique ID.
-- We assume a global uniqueness invariant: The 'VarIndex' determines the name.
data VarName =
  VarName
  { vnIndex :: !VarIndex
  , vnName :: !Text
  }
  deriving (Show)

-- | Because of the global uniqueness invariant, comparing the
-- 'VarIndex' is sufficient to ensure equality of variable names.
instance Eq VarName where
  x == y = vnIndex x == vnIndex y

instance Ord VarName where
  compare x y = compare (vnIndex x) (vnIndex y)

-- | For hashing, we consider only the base name and not the
-- 'VarIndex'; this gives a stable hash value for a particular name,
-- even if the unique IDs are assigned differently from run to run.
instance Hashable VarName where
  hashWithSalt x vn = hashWithSalt x (vnName vn)

-- | A wildcard variable name consisting of an underscore "_".
wildcardVarName :: VarName
wildcardVarName = VarName 0 "_"

-- | A data type representing a context of bound 'VarName's.
-- It maps each 'VarName' to a de Bruijn index.
data VarCtx =
  VarCtx
  !Int -- ^ Context size
  !(IntMap Int) -- ^ Mapping from VarIndex to (size - de Bruijn index)

-- | The empty 'VarName' context.
emptyVarCtx :: VarCtx
emptyVarCtx = VarCtx 0 IntMap.empty

-- | Extend a 'VarCtx' with a new bound 'VarName'.
-- The new name has de Bruijn index 0; the index of each previous name
-- is incremented by one.
consVarCtx :: VarName -> VarCtx -> VarCtx
consVarCtx x (VarCtx size m) =
  let size' = size + 1
  in VarCtx size' (IntMap.insert (vnIndex x) size' m)

-- | Look up the de Bruijn index of the given 'VarName' in a 'VarCtx'.
-- Return 'Nothing' if the name is not present in the context.
lookupVarCtx :: VarName -> VarCtx -> Maybe Int
lookupVarCtx x (VarCtx size m) =
  case IntMap.lookup (vnIndex x) m of
    Just i -> Just (size - i)
    Nothing -> Nothing


-- Display Name Environments --------------------------------------------------------

-- | A 'DisplayNameEnv' encodes the mappings between display names (type
-- 'Text') and internal names (type 'VarIndex'). Multiple display
-- names may be associated with each internal name; these are stored
-- in priority order, with preferred display names first.
data DisplayNameEnv =
  DisplayNameEnv
  { displayNames :: !(IntMap [Text]) -- Keyed by VarIndex; preferred names come first.
  , displayIndexes :: !(Map Text IntSet)
  }
-- Invariants: The 'displayNames' and 'displayIndexes' maps should be
-- inverses of each other. That is, 'displayNames' maps @i@ to a list
-- containing @x@ if and only if 'displayIndexes' maps @x@ to a set
-- containing @i@.

emptyDisplayNameEnv :: DisplayNameEnv
emptyDisplayNameEnv = DisplayNameEnv mempty mempty

-- | Extend a 'DisplayNameEnv' by providing new 'Text' display names
-- for a given 'VarIndex'. Display names should be provided in
-- priority order, with preferred names first. If the 'VarIndex'
-- already exists in the map, then add the new display names with
-- higher priority while keeping the old ones.
extendDisplayNameEnv :: VarIndex -> [Text] -> DisplayNameEnv -> DisplayNameEnv
extendDisplayNameEnv i aliases env =
  DisplayNameEnv
  { displayNames = IntMap.insertWith List.union i aliases (displayNames env)
  , displayIndexes = foldr insertAlias (displayIndexes env) aliases
  }
  where
    insertAlias :: Text -> Map Text IntSet -> Map Text IntSet
    insertAlias x m = Map.insertWith IntSet.union x (IntSet.singleton i) m

-- | Filter display names in a 'DisplayNameEnv' that satisfy a predicate.
filterDisplayNameEnv :: (Text -> Bool) -> DisplayNameEnv -> DisplayNameEnv
filterDisplayNameEnv p env =
  DisplayNameEnv
  { displayNames = IntMap.filter (not . null) $ fmap (filter p) $ displayNames env
  , displayIndexes = Map.filterWithKey (\k _ -> p k) $ displayIndexes env
  }

-- | Delete a 'VarIndex' from the display environment, returning
--   any aliases to it. Has no effect if the index is not present.
deleteDisplayNameEnv :: VarIndex -> DisplayNameEnv -> ([Text], DisplayNameEnv)
deleteDisplayNameEnv i env =
  case IntMap.updateLookupWithKey (\_ _ -> Nothing) i (displayNames env) of
  (Nothing, _) -> ([], env)
  (Just names, displayNames') ->
    (names, DisplayNameEnv
      { displayNames = displayNames'
      , displayIndexes = foldr (Map.update filter_idxs) (displayIndexes env) names
      })
  where
    filter_idxs is =
      let is' = IntSet.delete i is
      in case IntSet.null is' of
        True -> Nothing
        False -> Just is'

-- | Merge two 'DisplayNameEnv's, giving higher priority to display
-- names from the first argument.
mergeDisplayNameEnv :: DisplayNameEnv -> DisplayNameEnv -> DisplayNameEnv
mergeDisplayNameEnv env1 env2 =
  DisplayNameEnv
  { displayNames = IntMap.unionWith List.union (displayNames env1) (displayNames env2)
  , displayIndexes = Map.unionWith IntSet.union (displayIndexes env1) (displayIndexes env2)
  }

-- | Look up a 'Text' display name in an environment, returning the
-- list of indexes it could resolve to.
resolveDisplayName :: DisplayNameEnv -> Text -> [VarIndex]
resolveDisplayName env x =
  case Map.lookup x (displayIndexes env) of
    Nothing -> []
    Just s -> IntSet.elems s

-- | Return the first display name for the given 'VarIndex' that is
-- unambiguous in the naming environment. If there is no unambiguous
-- alias, then return 'Nothing'.
bestDisplayName :: DisplayNameEnv -> VarIndex -> Maybe Text
bestDisplayName env i =
  do aliases <- IntMap.lookup i (displayNames env)
     go aliases
  where
    go [] = Nothing
    go (x : xs) =
      case Map.lookup x (displayIndexes env) of
        Nothing -> panic "bestDisplayName" ["Invariant violated: Missing key " <> x]
        Just vs
          | IntSet.size vs == 1 -> Just x
          | otherwise -> go xs

allDisplayNames :: DisplayNameEnv -> VarIndex -> [Text]
allDisplayNames env i =
  case IntMap.lookup i (displayNames env) of
    Just nms -> nms
    Nothing -> []
