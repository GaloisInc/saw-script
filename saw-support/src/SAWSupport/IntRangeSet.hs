{- |
Module      : SAWSupport.IntRangeSet
Description : A type representing sets of ranges of integers
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional

An 'IntRangeSet' represents a set of 'Int's, much like an @IntSet@,
but it also supports insertion and deletion of whole contiguous ranges
of 'Int's at once.

Ranges are merged so that every set of 'Int's has a canonical
representation as an 'IntRangeSet'.

The complexity of operations scales not with the number of 'Int's in a
set, but rather the number of separate contiguous ranges of 'Int's.
-}

module SAWSupport.IntRangeSet where

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap

-- | An 'IntRangeSet' represents a set of disjoint contiguous
-- intervals of type 'Int'.
-- Each interval @(i, j)@ with @i <= j@ represents the set of values
-- @[i..j]@.
newtype IntRangeSet = IntRangeSet (IntMap Int)
  deriving Eq

instance Show IntRangeSet where
  show (IntRangeSet m) = show m

-- | The empty set.
empty :: IntRangeSet
empty = IntRangeSet IntMap.empty

-- | A set containing a single interval @[i..j]@.
singleton :: (Int, Int) -> IntRangeSet
singleton (i, j)
  | i <= j = IntRangeSet (IntMap.singleton i j)
  | otherwise = empty

-- | Add an interval @[i..j]@ to the set.
insert :: (Int, Int) -> IntRangeSet -> IntRangeSet
insert (i, j) (IntRangeSet m)
  | i > j = IntRangeSet m
  | otherwise =
    let -- m1 contains all intervals strictly below i
        -- also possibly one interval starting at i'
        m1 = IntMap.takeWhileAntitone (< i) m
        -- m2 contains all intervals strictly above j
        m2 = IntMap.dropWhileAntitone (<= j+1) m
        i' = case IntMap.lookupLE i m of
               Nothing -> i
               Just (u, v) -> if i <= v+1 then u else i
        j' = case IntMap.lookupLE (j+1) m of
               Nothing -> j
               Just (_, v) -> max v j
    in IntRangeSet (IntMap.insert i' j' (IntMap.union m1 m2))
    -- Any interval [u..v] with v+1 < i stays unchanged.
    -- Any interval [u..v] with u <= i <= v+1 is overwritten.
    -- Any interval [u..v] with i < u <= j is removed.
    -- Any interval [u..v] with j < u stays unchanged.
    -- If i falls inside (or is adjacent to the upper bound of) an
    -- interval [u..v], set i' = u; else i' = i.
    -- If j falls inside (or is adjacent to the lower bound of) an
    -- interval [u..v], let j' = v; else j' = j.
    -- Always insert a new interval [i'..j'].

-- | Remove an interval @[i..j]@ from the set.
delete :: (Int, Int) -> IntRangeSet -> IntRangeSet
delete (i, j) (IntRangeSet m)
  | i > j = IntRangeSet m
  | otherwise =
    let m1 = IntMap.takeWhileAntitone (< i) m
        m2 = IntMap.dropWhileAntitone (<= j) m
        m1' = case IntMap.lookupLT i m1 of
                Nothing -> m1
                Just (u, v) -> if i <= v then IntMap.insert u (i-1) m1 else m1
        m2' = case IntMap.lookupLE j m of
                Nothing -> m2
                Just (_, v) -> if j < v then IntMap.insert (j+1) v m2 else m2
    in IntRangeSet (IntMap.union m1' m2')
    -- Any interval [u..v] with v < i stays unchanged.
    -- Any interval [u..v] with u < i <= v is overwritten.
    -- Any interval [u..v] with i <= u <= j is removed.
    -- Any interval [u..v] with j < u stays unchanged.
    -- If i falls inside an interval [u..v], replace it with interval [u..i-1].
    -- If j falls inside an interval [u..v], insert a new interval [j+1..v].

-- | Is a specific value in the set?
member :: Int -> IntRangeSet -> Bool
member x (IntRangeSet m) =
  case IntMap.lookupLE x m of
    Nothing -> False
    Just (_, j) -> x <= j

-- | The union of two sets.
union :: IntRangeSet -> IntRangeSet -> IntRangeSet
union s1 s2 = foldr insert s1 (toList s2)

-- | The difference of two sets: Remove all members of the second set
-- from the first set.
difference :: IntRangeSet -> IntRangeSet -> IntRangeSet
difference s1 s2 = foldr delete s1 (toList s2)

-- | Create a set from a list of intervals.
fromList :: [(Int, Int)] -> IntRangeSet
fromList = foldr insert empty

-- | Convert the set to a list of disjoint intervals in ascending
-- order.
toList :: IntRangeSet -> [(Int, Int)]
toList (IntRangeSet m) = IntMap.toList m
