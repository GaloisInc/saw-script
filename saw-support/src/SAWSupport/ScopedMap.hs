{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : SAWSupport.ScopedMap
-- Description : Scoped-aware finite map library
-- License     : BSD3
-- Maintainer  : saw@galois.com
-- Stability   : provisional
--
-- Scope-aware map for use as an interpreter or typechecker
-- environment.
--
-- The `ScopedMap` type is a stack of maps; each layer corresponds
-- to a scope as the client moves into and out of nested naming
-- environments.
--
-- The current (innermost) scope is at the top of the stack / head of
-- the list.
--
-- Update operations act on the current scope. Lookup operations
-- inspect the whole stack, starting at the innermost layer and
-- working out.
--
-- The `push` and `pop` operations add and drop scopes respectively,
-- and should be used when the client enters and leaves a nested
-- naming environment.
--
-- The `flatten` operation produces a single-layer Data.Map that
-- contains all the visible mappings. (That is, duplicate keys in
-- outer scopes are suppressed.)
--
-- Other operations correspond to the ordinary operations on
-- Data.Map. Operations that generate collections (e.g. @keys@) come
-- in two versions: one that preserves the scope structure
-- (generally called @scoped@), and one that flattens it (generally
-- called @all@).
--
-- In principle we should provide all the operations on Data.Map.
-- However, the implementation has been lazily evaluated and the
-- operations present are the ones that have been needed so far.
-- Add more as desired.

module SAWSupport.ScopedMap (
    ScopedMap, -- opaque
    push,
    pop,
    empty,
    seed,
    insert,
    lookup,
    filter,
    scopedAssocs,
    flatten,
    allKeys,
    allKeysSet
  ) where

import Prelude hiding (lookup, filter)

import qualified Data.List.NonEmpty as N
import Data.List.NonEmpty (NonEmpty( (:|) ))
import Data.Foldable (toList)
--import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)

import SAWSupport.Panic (panic)


-- | The type of scoped maps.
--
--   The list of scopes is a `NonEmpty` to avoid unnecessary
--   degenerate cases.
newtype ScopedMap k v = ScopedMap (NonEmpty (Map k v))

-- | Push a new scope.
push :: Ord k => ScopedMap k v -> ScopedMap k v
push (ScopedMap scopes) =
    ScopedMap $ N.cons Map.empty scopes

-- | Pop and discard the most recent scope.
--
--   Popping the last scope is an error and will panic.
pop :: Ord k => ScopedMap k v -> ScopedMap k v
pop (ScopedMap (_ :| more)) = case more of
    [] ->
        panic "pop" ["Popping topmost scope"]
    s : more' ->
        ScopedMap (s :| more')

-- | An empty ScopedMap, with a single empty scope.
empty :: Ord k => ScopedMap k v
empty =
    ScopedMap (Map.empty :| [])

-- | Initialize a ScopedMap from a Map, which becomes the current (and
--   only) scope.
seed :: Ord k => Map k v -> ScopedMap k v
seed m =
    ScopedMap (m :| [])

-- | Insert into a ScopedMap. Always inserts in the innermost (most
--   recent) scope.
insert :: Ord k => k -> v -> ScopedMap k v -> ScopedMap k v
insert k v (ScopedMap (s :| more)) =
    let s' = Map.insert k v s in
    ScopedMap (s' :| more)

-- | Look up a key in a ScopedMap. Checks all the scopes with the most
--   recent first.
lookup :: Ord k => k -> ScopedMap k v -> Maybe v
lookup k (ScopedMap (s0 :| more0)) =
    let visit s more = case Map.lookup k s of
          Just result -> Just result
          Nothing -> case more of
              [] -> Nothing
              s' : more' -> visit s' more'
    in
    visit s0 more0

-- | Drop entries that don't match a predicate.
filter :: Ord k => (v -> Bool) -> ScopedMap k v -> ScopedMap k v
filter keep (ScopedMap (s :| more)) =
    ScopedMap (Map.filter keep s :| map (Map.filter keep) more)

-- | Return Map.assocs for each scope, preserving the scope boundaries.
--   The head of the returned list is the most recent scope.
scopedAssocs :: Ord k => ScopedMap k v -> [[(k, v)]]
scopedAssocs (ScopedMap scopes) =
    map Map.assocs $ toList scopes

-- FUTURE: add scopedKeys, scopedKeysSet

-- | Convert to a plain map by folding the scopes together. Duplicate
--   bindings in more recent scopes take priority.
flatten :: Ord k => ScopedMap k v -> Map k v
flatten (ScopedMap (s0 :| more0)) =
    let visit s more =
          let result = case more of
                [] -> Map.empty
                s' : more' -> visit s' more'
          in
          -- Map.union gives its left argument priority given a
          -- duplicate key.
          Map.union s result
    in
    visit s0 more0

--FUTURE: add allAssocs

-- | Return all keys, ignoring scope.
allKeys :: Ord k => ScopedMap k v -> [k]
allKeys m =
    Map.keys $ flatten m

-- | Return all keys as a set, ignoring scope.
allKeysSet :: Ord k => ScopedMap k v -> Set k
allKeysSet m =
    Map.keysSet $ flatten m
