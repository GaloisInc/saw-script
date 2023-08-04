module Util.FList where

import Control.Applicative (Applicative (liftA2))
import Data.Hashable (Hashable)
import Util.Stack (Stack, emptyStack, pop, push)
import Util.Stack qualified as Stack

data FList a = FList
  { prefix :: Stack a,
    suffix :: Stack a
  }
  deriving (Show)

fromList :: Hashable a => [a] -> FList a
fromList xs = FList {prefix = emptyStack, suffix = Stack.fromList xs}

fromLists :: Hashable a => [a] -> [a] -> FList a
fromLists pre post =
  FList {prefix = Stack.fromList (Prelude.reverse pre), suffix = Stack.fromList post}

toLists :: FList a -> ([a], [a])
toLists = liftA2 (,) before after

toRight :: Hashable a => FList a -> Maybe a
toRight FList {..} = fst <$> pop suffix

toLeft :: Hashable a => FList a -> Maybe a
toLeft FList {..} = fst <$> pop prefix

forward :: Hashable a => FList a -> Maybe (FList a)
forward FList {..} =
  case pop suffix of
    Nothing -> Nothing
    Just (x, xs) -> Just (FList {prefix = push x prefix, suffix = xs})

backward :: Hashable a => FList a -> Maybe (FList a)
backward FList {..} =
  case pop prefix of
    Nothing -> Nothing
    Just (x, xs) -> Just (FList {prefix = xs, suffix = push x suffix})

before :: FList a -> [a]
before FList {..} = Prelude.reverse (Stack.toList prefix)

after :: FList a -> [a]
after FList {..} = Stack.toList suffix

reverse :: FList a -> FList a
reverse FList {..} = FList {prefix = suffix, suffix = prefix}

-- | All possible positions of the finger
fingers :: Hashable a => [a] -> [FList a]
fingers xs = go (fromList xs)
  where
    go flist =
      case forward flist of
        Nothing -> [flist]
        Just flist' -> flist : go flist'

-- fingers xs =
--   case xs of
--     [] -> []
--     (z : zs) -> go zs (FList {prefix = push z emptyStack, suffix = zs} :| [])
--   where
--     go source (flist@FList {..} :| flists) =
--       case source of
--         [] -> NE.toList (flist :| flists)
--         (s : ss) ->
--           go ss (FList {prefix = push s prefix, suffix = ss} :| flist : flists)
