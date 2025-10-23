{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : SAWScript.REPL.Trie
Description :
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}

module SAWScript.REPL.Trie (
    Trie,
    empty,
    insert,
    lookup,
    lookupWithExact,
    leaves
 ) where

import Prelude hiding (lookup)

import qualified Data.Text as Text
import           Data.Text (Text)
import qualified Data.Map as Map
import           Data.Map (Map)
import           Data.Maybe (fromMaybe,maybeToList)

import           SAWScript.Panic (panic)


-- | Maps string names to values, allowing for partial key matches and querying.
data Trie a = Node (Map Char (Trie a)) (Maybe a)
    deriving (Show)

empty :: Trie a
empty  = Node Map.empty Nothing

-- | Insert a value into the Trie.  Will call `panic` if a value already exists
-- with that key.
insert :: Text -> a -> Trie a -> Trie a
insert k a = loop k
  where
  loop key (Node m mb) = case Text.uncons key of
    Just (c, key') -> Node (Map.alter (Just . loop key' . fromMaybe empty) c m) mb
    Nothing -> case mb of
      Nothing -> Node m (Just a)
      Just _  -> panic "insert" ["Key already exists: " <> k]

-- | Return all matches with the given prefix.
lookup :: Text -> Trie a -> [a]
lookup key t@(Node mp _) = case Text.uncons key of

  Just (c, key') -> case Map.lookup c mp of
    Just m' -> lookup key' m'
    Nothing -> []

  Nothing -> leaves t

-- | Return all matches with the given prefix. However, if an exact match
-- exists, return just that match.
lookupWithExact :: Text -> Trie a -> [a]
lookupWithExact key t@(Node mp mb) = case Text.uncons key of

  Just (c, key') -> case Map.lookup c mp of
    Just m' -> lookupWithExact key' m'
    Nothing -> []

  Nothing -> case mb of
    Just b -> [b]
    Nothing -> leaves t

-- | Return all of the values from a Trie.
leaves :: Trie a -> [a]
leaves (Node mp mb) = maybeToList mb ++ concatMap leaves (Map.elems mp)
