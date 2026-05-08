-- |
-- Module      : SAWSupport.EqRel
-- Description : Equivalence relation that is defined pointwise
-- License     : BSD3
-- Maintainer  : saw@galois.com
-- Stability   : provisional
--
-- An 'EqRel' is a collection of sets representing equivalence classes.
-- Two values are considered equivalent with respect to this relation if
-- they are both in the same equivalence class.
--
-- The relation is defined pointwise: pairs of values are declared
-- equivalent via 'insert', which implicitly extends the data structure
-- such that the result is a still a valid equivalence relation
-- (symmetric, transitive, reflexive).

module SAWSupport.EqRel
  ( EqRel
  , empty
  , eq
  , insert
  ) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Hashable (Hashable)
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet

-- | Represents an equivalence relation that is defined pointwise.
--   Values marked as equivalent via 'insert' are considered to
--   belong to the same equivalence class.
--   The relation is implicitly transitive, symmetric and reflexive.
--   Specifically, for any @r@:
--     * if @eq r x y@ is @True@
--       then @eq (insert a b r) x y@ is @True@
--     * if @x == y@ is @True@ then @eq r x y@ is @True@
--     * @eq (insert x y r) x y @ is @True@
--     * if @eq r x y@ is @True@,
--       then @eq r y x@ is @True@
--     * if @eq r x y@ and @eq r y z@ are @True@,
--       then @eq r x z@ is @True@
--     * in all other cases, @eq r x y@ is @False@
--
--   Invariant: for each @s@ in the codomain of the map @m@ and each
--   @x@ in @s@: @HashMap.lookup x m == Just s@
newtype EqRel a = EqRel (HashMap a (HashSet a))

-- | An empty 'EqRel', where values are equivalent iff they
--   are exactly equal.
empty :: EqRel a
empty = EqRel HashMap.empty

-- | Test if two values are equivalent up to the given equivalence
--   relation 'EqRel'.
eq :: Hashable a => EqRel a -> a -> a -> Bool
eq (EqRel m) x y =
  case HashMap.lookup y m of
    Just ys -> HashSet.member x ys
    Nothing -> x == y

-- | Extend an equivalence relation 'EqRel' to combine the equivalence
--   classes of the two given values (i.e. consider the
--   two values to be equivalent).
insert :: Hashable a => a -> a -> EqRel a -> EqRel a
insert x y (EqRel m) = EqRel (HashMap.union (const s <$> HashSet.toMap s) m)
  where
    s = case (HashMap.lookup x m, HashMap.lookup y m) of
      (Just xs, Just ys) -> HashSet.union xs ys
      (Nothing, Just ys) -> HashSet.insert x ys
      (Just xs, Nothing) -> HashSet.insert y xs
      (Nothing, Nothing) -> HashSet.insert x $ HashSet.singleton y
