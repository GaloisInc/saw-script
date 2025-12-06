module SAWSupport.IntervalSet where

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap

-- | An 'IntervalSet' represents a set of disjoint contiguous
-- intervals of type 'Int'.
-- Each interval @(i, j)@ with @i <= j@ represents the set of values
-- @[i..j]@.
newtype IntervalSet = IntervalSet (IntMap Int)
  deriving Eq

instance Show IntervalSet where
  show (IntervalSet m) = show m

-- | The empty set.
empty :: IntervalSet
empty = IntervalSet IntMap.empty

-- | A set containing a single interval @[i..j]@.
singleton :: (Int, Int) -> IntervalSet
singleton (i, j)
  | i <= j = IntervalSet (IntMap.singleton i j)
  | otherwise = empty

-- | Add an interval @[i..j]@ to the set.
insert :: (Int, Int) -> IntervalSet -> IntervalSet
insert (i, j) (IntervalSet m)
  | i > j = IntervalSet m
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
    in IntervalSet (IntMap.insert i' j' (IntMap.union m1 m2))
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
delete :: (Int, Int) -> IntervalSet -> IntervalSet
delete (i, j) (IntervalSet m)
  | i > j = IntervalSet m
  | otherwise =
    let m1 = IntMap.takeWhileAntitone (< i) m
        m2 = IntMap.dropWhileAntitone (<= j) m
        m1' = case IntMap.lookupLT i m1 of
                Nothing -> m1
                Just (u, v) -> if i <= v then IntMap.insert u (i-1) m1 else m1
        m2' = case IntMap.lookupLE j m of
                Nothing -> m2
                Just (_, v) -> if j < v then IntMap.insert (j+1) v m2 else m2
    in IntervalSet (IntMap.union m1' m2')
    -- Any interval [u..v] with v < i stays unchanged.
    -- Any interval [u..v] with u < i <= v is overwritten.
    -- Any interval [u..v] with i <= u <= j is removed.
    -- Any interval [u..v] with j < u stays unchanged.
    -- If i falls inside an interval [u..v], replace it with interval [u..i-1].
    -- If j falls inside an interval [u..v], insert a new interval [j+1..v].

-- | Is a specific value in the set?
member :: Int -> IntervalSet -> Bool
member x (IntervalSet m) =
  case IntMap.lookupLE x m of
    Nothing -> False
    Just (_, j) -> x <= j

-- | The union of two sets.
union :: IntervalSet -> IntervalSet -> IntervalSet
union s1 s2 = foldr insert s1 (toList s2)

-- | The difference of two sets: Remove all members of the second set
-- from the first set.
difference :: IntervalSet -> IntervalSet -> IntervalSet
difference s1 s2 = foldr delete s1 (toList s2)

-- | Create a set from a list of intervals.
fromList :: [(Int, Int)] -> IntervalSet
fromList = foldr insert empty

-- | Convert the set to a list of disjoint intervals in ascending
-- order.
toList :: IntervalSet -> [(Int, Int)]
toList (IntervalSet m) = IntMap.toList m
