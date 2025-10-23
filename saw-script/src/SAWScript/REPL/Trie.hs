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
import           Data.Maybe (maybeToList)

import           SAWScript.Panic (panic)


-- | Maps string names to values, allowing for partial key matches and
--   querying.
--
--   Each node contains a map from characters to subnodes, and
--   possibly also a value corresponding to the characters seen so
--   far.
data Trie a = Node (Map Char (Trie a)) (Maybe a)
    deriving (Show)

-- | The empty `Trie`.
empty :: Trie a
empty  = Node Map.empty Nothing

-- | Insert a value into a `Trie`. Will panic if a value already exists
--   with the same key.
insert :: Text -> a -> Trie a -> Trie a
insert k v node0 = insert' k node0
  where
  -- the insertion value is invariant so recurse without it
  insert' key (Node tbl mbValue) = case Text.uncons key of
      Nothing -> case mbValue of
          Nothing ->
              -- Reached the end of the key and there's nothing here yet;
              -- insert the value.
              Node tbl (Just v)
              -- There's already something here; croak
          Just _  ->
              panic "insert" ["Key already exists: " <> k]
      Just (c, key') ->
          let subnode = case Map.lookup c tbl of
                Nothing -> empty
                Just n -> n
              subnode' = insert' key' subnode
          in
          Node (Map.insert c subnode' tbl) mbValue

-- | Return all values in the `Trie` whose keys match the given
--   prefix.
lookup :: Text -> Trie a -> [a]
lookup key node@(Node tbl _) = case Text.uncons key of
    Nothing ->
        leaves node
    Just (c, key') -> case Map.lookup c tbl of
        Nothing -> []
        Just node' -> lookup key' node'

-- | Return all values in the `Trie` whose keys match the given
--   prefix. However, if an exact match to the key exists, return just
--   that match.
lookupWithExact :: Text -> Trie a -> [a]
lookupWithExact key node@(Node tbl mbValue) = case Text.uncons key of
    Nothing -> case mbValue of
        Nothing -> leaves node
        Just val -> [val]
    Just (c, key') -> case Map.lookup c tbl of
        Nothing -> []
        Just node' -> lookupWithExact key' node'

-- | Return all of the values from a Trie.
leaves :: Trie a -> [a]
leaves (Node tbl mbValue) =
    maybeToList mbValue ++ concatMap leaves (Map.elems tbl)
