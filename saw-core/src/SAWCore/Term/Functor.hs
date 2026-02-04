{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DeriveTraversable #-}

{- |
Module      : SAWCore.Term.Functor
Copyright   : Galois, Inc. 2012-2025
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Term.Functor
  ( -- * Data types and definitions
    FieldName
  , LocalName
  , VarIndex
    -- * Terms and associated operations
  , TermF(..)
  , FlatTermF(..)
  , CompiledRecursor(..)
  , zipWithFlatTermF
  , alistAllFields
    -- * Sorts
  , Sort(..), mkSort, propSort, sortOf, maxSort
  , SortFlags(..), noFlags, sortFlagsLift2, sortFlagsToList, sortFlagsFromList
    -- * Sets of free variables
  , freesTermF
  ) where

import qualified Data.Foldable as Foldable (foldl')
import Data.Hashable
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Text (Text)
import Data.Vector (Vector)
import qualified Data.Vector as V
import GHC.Generics (Generic)
import Numeric.Natural

import qualified Language.Haskell.TH.Syntax as TH
import Instances.TH.Lift () -- for instance TH.Lift Text

import SAWCore.Name

type FieldName = Text
type LocalName = Text

instance Hashable a => Hashable (Vector a) where
    hashWithSalt x v = hashWithSalt x (V.toList v)


-- Sorts -----------------------------------------------------------------------

-- | The sorts, also known as universes, which can either be a predicative
-- universe with level i or the impredicative universe Prop.
data Sort
  = TypeSort Natural
  | PropSort
  deriving (Eq, Generic, TH.Lift)

-- Prop is the lowest sort
instance Ord Sort where
  PropSort <= _ = True
  (TypeSort _) <= PropSort = False
  (TypeSort i) <= (TypeSort j) = i <= j

instance Hashable Sort -- automatically derived

instance Show Sort where
  showsPrec p (TypeSort i) = showParen (p >= 10) (showString "sort " . shows i)
  showsPrec _ PropSort = showString "Prop"

-- | Create sort @Type i@ for the given natural number @i@.
mkSort :: Natural -> Sort
mkSort i = TypeSort i

-- | Wrapper around 'PropSort', for export
propSort :: Sort
propSort = PropSort

-- | Returns sort of the given sort.
sortOf :: Sort -> Sort
sortOf (TypeSort i) = TypeSort (i + 1)
sortOf PropSort = TypeSort 0

-- | Get the maximum sort in a list, returning Prop for the empty list
maxSort :: [Sort] -> Sort
maxSort [] = propSort
maxSort ss = maximum ss

-- | This type represents a set of advisory flags for 'Sort's that are mostly
-- ignored, but are used in the Rocq export process to indicate where various
-- typeclass instances are necessary in function definitions. In the concrete
-- syntax "isort", "qsort", etc. is used to indicate cases where these flags
-- are set. Note in particular that these flags do not affect typechecking,
-- so missing or overeager "isort"/"qsort" annotations will only be detected
-- via the Rocq export.
--
-- * If 'flagInhabited' is 'True', an implicit @Inhabited@ typeclass argument
--   will be added during Rocq translation. In the concrete syntax, an "i" is
--   prepended to the sort (e.g. "isort").
-- * If 'flagQuantType' is 'True', an implicit @QuantType@ typeclass argument
--   will be added during Rocq translation. In the concrete syntax, an "q" is
--   prepended to the sort (e.g. "qsort", "qisort").
data SortFlags = SortFlags { flagInhabited :: Bool
                           , flagQuantType :: Bool }
    deriving (Eq, Ord, Generic, TH.Lift)

instance Hashable SortFlags -- automatically derived

instance Show SortFlags where
  showsPrec _ (SortFlags i q) = showString $
    concatMap (\(b,s) -> if b then s else "")
              [(q,"q"), (i,"i")]

-- | The 'SortFlags' object with no flags set
noFlags :: SortFlags
noFlags = SortFlags False False

-- | Apply a binary operation to corresponding flags of two 'SortFlags'
sortFlagsLift2 :: (Bool -> Bool -> Bool) -> SortFlags -> SortFlags -> SortFlags
sortFlagsLift2 f (SortFlags i1 q1) (SortFlags i2 q2) = SortFlags (f i1 i2) (f q1 q2)

-- | Convert a 'SortFlags' to a list of 'Bool's, indicating which flags are set
sortFlagsToList :: SortFlags -> [Bool]
sortFlagsToList (SortFlags i q) = [i, q]

-- | Build a 'SortFlags' from a list of 'Bool's indicating which flags are set
sortFlagsFromList :: [Bool] -> SortFlags
sortFlagsFromList bs = SortFlags (isSet 0) (isSet 1)
  where isSet i = i < length bs && bs !! i


-- Flat Terms ------------------------------------------------------------------

-- | The "flat terms", which are the built-in atomic constructs of SAW core.
--
-- NB: If you add constructors to FlatTermF, make sure you update
--     zipWithFlatTermF!
data FlatTermF e
    -- Tuples are represented as nested pairs, grouped to the right,
    -- terminated with unit at the end.
  = UnitValue
  | UnitType
  | PairValue e e
  | PairType e e
  | PairLeft e
  | PairRight e

    -- | A recursor, which is specified by a 'CompiledRecursor'
    -- comprising the datatype name, elimination sort, and other data
    -- about the recursor.
  | Recursor CompiledRecursor

    -- | Sorts, aka universes, are the types of types; i.e., an object is a
    -- "type" iff it has type @Sort s@ for some s. See 'SortFlags' for an
    -- explanation of the extra argument.
  | Sort !Sort !SortFlags

    -- Primitive builtin values
    -- | Array value includes type of elements followed by elements.
  | ArrayValue e (Vector e)
    -- | String literal
  | StringLit !Text
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Hashable e => Hashable (FlatTermF e) -- automatically derived

-- | A 'CompiledRecursor' comprises the datatype name and elimination
-- sort of a recursor, along with some other data derived from details
-- of the datatype definition.
data CompiledRecursor =
  CompiledRecursor
  { recursorDataType  :: Name
  , recursorSort      :: Sort
  , recursorNumParams :: Int
  , recursorNumIxs    :: Int
  , recursorCtorOrder :: [Name]
  }
 deriving (Eq, Ord, Show, Generic)

instance Hashable CompiledRecursor -- automatically derived

-- | Test if an association list uses precisely the given field names
-- and no more.
-- If so, return the values associated with those field names, in the
-- order given in the input, and otherwise return 'Nothing'.
alistAllFields :: Eq k => [k] -> [(k, a)] -> Maybe [a]
alistAllFields [] [] = Just []
alistAllFields (fld:flds) alist
  | Just val <- lookup fld alist =
    (val :) <$> alistAllFields flds (deleteField fld alist)
  where
    deleteField _ [] = error "deleteField"
    deleteField f ((f',_):rest) | f == f' = rest
    deleteField f (x:rest) = x : deleteField f rest
alistAllFields _ _ = Nothing

zipName :: Name -> Name -> Maybe Name
zipName x y
  | x == y = Just x
  | otherwise = Nothing

zipRec :: CompiledRecursor -> CompiledRecursor -> Maybe CompiledRecursor
zipRec (CompiledRecursor d1 s1 ps1 n1 ord1) (CompiledRecursor d2 s2 _ n2 ord2)
  | n1 == n2 && s1 == s2
  = do d <- zipName d1 d2
       ord <- sequence (zipWith zipName ord1 ord2)
       pure $ CompiledRecursor
              d
              s1
              ps1
              n1
              ord
  | otherwise = Nothing

-- | Zip a binary function @f@ over a pair of 'FlatTermF's by applying @f@
-- pointwise to immediate subterms, if the two 'FlatTermF's are the same
-- constructor; otherwise, return 'Nothing' if they use different constructors
zipWithFlatTermF :: (x -> y -> z) -> FlatTermF x -> FlatTermF y ->
                    Maybe (FlatTermF z)
zipWithFlatTermF f = go
  where
    go UnitValue UnitValue = Just UnitValue
    go UnitType UnitType = Just UnitType
    go (PairValue x1 x2) (PairValue y1 y2) = Just (PairValue (f x1 y1) (f x2 y2))
    go (PairType x1 x2) (PairType y1 y2) = Just (PairType (f x1 y1) (f x2 y2))
    go (PairLeft x) (PairLeft y) = Just (PairLeft (f x y))
    go (PairRight x) (PairRight y) = Just (PairLeft (f x y))

    go (Recursor rec1) (Recursor rec2) =
      Recursor <$> zipRec rec1 rec2

    go (Sort sx hx) (Sort sy hy) | sx == sy = Just (Sort sx (sortFlagsLift2 (&&) hx hy))
         -- /\ NB, it's not entirely clear how the flags should be propagated
    go (StringLit s) (StringLit t) | s == t = Just (StringLit s)
    go (ArrayValue tx vx) (ArrayValue ty vy)
      | V.length vx == V.length vy
      = Just $ ArrayValue (f tx ty) (V.zipWith f vx vy)

    go UnitValue      _ = Nothing
    go UnitType       _ = Nothing
    go PairValue{}    _ = Nothing
    go PairType{}     _ = Nothing
    go PairLeft{}     _ = Nothing
    go PairRight{}    _ = Nothing
    go Recursor{}     _ = Nothing
    go Sort{}         _ = Nothing
    go ArrayValue{}   _ = Nothing
    go StringLit{}    _ = Nothing


-- Term Functor ----------------------------------------------------------------

-- | A \"knot-tying\" structure for representing terms and term-like things.
-- Often, this appears in context as the type \"'TermF' 'Term'\", in which case
-- it represents a full 'Term' AST. The \"F\" stands for 'Functor', or
-- occasionally for \"Former\".
data TermF e
    = FTermF !(FlatTermF e)
      -- ^ The atomic, or builtin, term constructs
    | App !e !e
      -- ^ Applications of functions
    | Lambda !VarName !e !e
      -- ^ Function abstractions
    | Pi !VarName !e !e
      -- ^ The type of a (possibly) dependent function
    | Constant !Name
      -- ^ A global constant identified by its name.
    | Variable !VarName !e
      -- ^ A named variable with a type.
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Hashable e => Hashable (TermF e) -- automatically derived


-- Free Named Variables --------------------------------------------------------

-- | Compute an 'IntSet' containing the 'VarIndex' of the free
-- variables of a term, given the free variables for its immediate
-- subterms.
freesTermF :: TermF IntSet -> IntSet
freesTermF tf =
  case tf of
    FTermF ftf -> Foldable.foldl' IntSet.union IntSet.empty ftf
    App l r -> IntSet.union l r
    Lambda nm tp rhs -> IntSet.union tp (IntSet.delete (vnIndex nm) rhs)
    Pi nm lhs rhs -> IntSet.union lhs (IntSet.delete (vnIndex nm) rhs)
    Constant {} -> IntSet.empty
    Variable nm tp -> IntSet.insert (vnIndex nm) tp
