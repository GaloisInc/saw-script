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

import           Cryptol.Utils.Panic (panic)
import qualified Data.Map as Map
import           Data.Map (Map)
import           Data.Maybe (fromMaybe,maybeToList)


-- | Maps string names to values, allowing for partial key matches and querying.
data Trie a = Node (Map Char (Trie a)) (Maybe a)
    deriving (Show)

empty :: Trie a
empty  = Node Map.empty Nothing

-- | Insert a value into the Trie.  Will call `panic` if a value already exists
-- with that key.
insert :: String -> a -> Trie a -> Trie a
insert k a = loop k
  where
  loop key (Node m mb) = case key of
    c:cs -> Node (Map.alter (Just . loop cs . fromMaybe empty) c m) mb
    []   -> case mb of
      Nothing -> Node m (Just a)
      Just _  -> panic "[REPL] Trie" ["key already exists:", "\t" ++ k]

-- | Return all matches with the given prefix.
lookup :: String -> Trie a -> [a]
lookup key t@(Node mp _) = case key of

  c:cs -> case Map.lookup c mp of
    Just m' -> lookup cs m'
    Nothing -> []

  [] -> leaves t

-- | Return all matches with the given prefix. However, if an exact match
-- exists, return just that match.
lookupWithExact :: String -> Trie a -> [a]
lookupWithExact key t@(Node mp mb) = case key of

  c:cs -> case Map.lookup c mp of
    Just m' -> lookupWithExact cs m'
    Nothing -> []

  [] -> case mb of
    Just b -> [b]
    Nothing -> leaves t

-- | Return all of the values from a Trie.
leaves :: Trie a -> [a]
leaves (Node mp mb) = maybeToList mb ++ concatMap leaves (Map.elems mp)
