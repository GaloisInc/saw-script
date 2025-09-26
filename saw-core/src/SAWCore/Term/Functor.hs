{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeOperators #-}

{- |
Module      : SAWCore.Term.Functor
Copyright   : Galois, Inc. 2012-2025
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Term.Functor
  ( -- * Module Names
    ModuleName, mkModuleName
  , preludeName
  , moduleNameText
  , moduleNamePieces
    -- * Identifiers
  , Ident(identModule, identBaseName), identName, mkIdent
  , parseIdent
  , isIdent
  , identText
  , identPieces
    -- * Data types and definitions
  , DeBruijnIndex
  , FieldName
  , LocalName
  , ExtCns(..)
  , VarIndex
  , NameInfo(..)
  , toShortName
  , toAbsoluteName
  , CompiledRecursor(..)
    -- * Terms and associated operations
  , TermIndex
  , Term(..)
  , TermF(..)
  , FlatTermF(..)
  , zipWithFlatTermF
  , looseTermF
  , unwrapTermF
  , termToPat
  , alphaEquiv
  , alistAllFields
    -- * Sorts
  , Sort, mkSort, propSort, sortOf, maxSort
  , SortFlags(..), noFlags, sortFlagsLift2, sortFlagsToList, sortFlagsFromList
    -- * Sets of free variables
  , BitSet, emptyBitSet, inBitSet, unionBitSets, intersectBitSets
  , decrBitSet, multiDecrBitSet, completeBitSet, singletonBitSet, bitSetElems
  , smallestBitSetElem
  , bitSetBound
  , looseVars, smallestLooseVar, termIsClosed
  , freesTermF, freeVars
  ) where

import Data.Bits
import qualified Data.Foldable as Foldable (and, foldl')
import Data.Hashable
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Typeable (Typeable)
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Word
import GHC.Generics (Generic)
import Numeric.Natural

import qualified Language.Haskell.TH.Syntax as TH
import Instances.TH.Lift () -- for instance TH.Lift Text

import SAWCore.Name
import qualified SAWCore.TermNet as Net

type DeBruijnIndex = Int
type FieldName = Text
type LocalName = Text
  -- ^ 'LocalName' is used for pretty printing purposes, but does not affect the semantics of SAWCore terms,
  -- rather, the 'DeBruijnIndex'-s are what is used to reference variables.
  -- FIXME: Verify the above statement
  -- FIXME: Possibly, change to a name that suggests this use.

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
-- ignored, but are used in the Coq export process to indicate where various
-- typeclass instances are necessary in function definitions. In the concrete
-- syntax "isort", "qsort", etc. is used to indicate cases where these flags
-- are set. Note in particular that these flags do not affect typechecking,
-- so missing or overeager "isort"/"qsort" annotations will only be detected
-- via the Coq export.
--
-- * If 'flagInhabited' is 'True', an implicit @Inhabited@ typeclass argument
--   will be added during Coq translation. In the concrete syntax, an "i" is
--   prepended to the sort (e.g. "isort").
-- * If 'flagQuantType' is 'True', an implicit @QuantType@ typeclass argument
--   will be added during Coq translation. In the concrete syntax, an "q" is
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

    -- | A recursor, which is specified by giving the datatype name,
    --   the parameters to the datatype, a motive and elimination functions
    --   for each constructor. A recursor can be used with the special
    --   @RecursorApp@ term, which provides the datatype indices and
    --   actual argument to the eliminator.
  | Recursor (CompiledRecursor e)

    -- | Non-dependent record types, i.e., N-ary tuple types with named
    -- fields. These are considered equal up to reordering of fields. Actual
    -- tuple types are represented with field names @"1"@, @"2"@, etc.
  | RecordType ![(FieldName, e)]
    -- | Non-dependent records, i.e., N-ary tuples with named fields. These are
    -- considered equal up to reordering of fields. Actual tuples are
    -- represented with field names @"1"@, @"2"@, etc.
  | RecordValue ![(FieldName, e)]
    -- | Non-dependent record projection
  | RecordProj e !FieldName

    -- | Sorts, aka universes, are the types of types; i.e., an object is a
    -- "type" iff it has type @Sort s@ for some s. See 'SortFlags' for an
    -- explanation of the extra argument.
  | Sort !Sort !SortFlags

    -- Primitive builtin values
    -- | Natural number with given value.
  | NatLit !Natural
    -- | Array value includes type of elements followed by elements.
  | ArrayValue e (Vector e)
    -- | String literal
  | StringLit !Text
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Hashable e => Hashable (FlatTermF e) -- automatically derived

-- Capture more type information here so we can
--  use it during evaluation time to remember the
--  types of the parameters, motive and eliminator functions.
data CompiledRecursor e =
  CompiledRecursor
  { recursorDataType  :: Name
  , recursorParams    :: [e]
  , recursorNumIxs    :: Int
  , recursorMotive    :: e
  , recursorElims     :: Map VarIndex e -- eliminator functions
  , recursorCtorOrder :: [Name]
  , recursorType      :: e
  }
 deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Hashable e => Hashable (CompiledRecursor e) -- automatically derived

-- | Test if the association list used in a 'RecordType' or 'RecordValue' uses
-- precisely the given field names and no more. If so, return the values
-- associated with those field names, in the order given in the input, and
-- otherwise return 'Nothing'
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

zipRec :: (x -> y -> z) -> CompiledRecursor x -> CompiledRecursor y -> Maybe (CompiledRecursor z)
zipRec f (CompiledRecursor d1 ps1 n1 m1 es1 ord1 ty1) (CompiledRecursor d2 ps2 n2 m2 es2 ord2 ty2)
  | Map.keysSet es1 == Map.keysSet es2 && n1 == n2
  = do d <- zipName d1 d2
       ord <- sequence (zipWith zipName ord1 ord2)
       pure $ CompiledRecursor
              d
              (zipWith f ps1 ps2)
              n1
              (f m1 m2)
              (Map.intersectionWith f es1 es2)
              ord
              (f ty1 ty2)

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
      Recursor <$> zipRec f rec1 rec2

    go (RecordType elems1) (RecordType elems2)
      | Just vals2 <- alistAllFields (map fst elems1) elems2 =
        Just $ RecordType $ zipWith (\(fld,x) y -> (fld, f x y)) elems1 vals2
    go (RecordValue elems1) (RecordValue elems2)
      | Just vals2 <- alistAllFields (map fst elems1) elems2 =
        Just $ RecordValue $ zipWith (\(fld,x) y -> (fld, f x y)) elems1 vals2
    go (RecordProj e1 fld1) (RecordProj e2 fld2)
      | fld1 == fld2 = Just $ RecordProj (f e1 e2) fld1

    go (Sort sx hx) (Sort sy hy) | sx == sy = Just (Sort sx (sortFlagsLift2 (&&) hx hy))
         -- /\ NB, it's not entirely clear how the flags should be propagated
    go (NatLit i) (NatLit j) | i == j = Just (NatLit i)
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
    go RecordType{}   _ = Nothing
    go RecordValue{}  _ = Nothing
    go RecordProj{}   _ = Nothing
    go Sort{}         _ = Nothing
    go NatLit{}       _ = Nothing
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
    | Lambda !LocalName !e !e
      -- ^ Function abstractions
    | Pi !LocalName !e !e
      -- ^ The type of a (possibly) dependent function
    | LocalVar !DeBruijnIndex
      -- ^ Local variables are referenced by deBruijn index.
    | Constant !Name
      -- ^ A global constant identified by its name.
    | Variable !(ExtCns e)
      -- ^ A named variable with a type.
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Hashable e => Hashable (TermF e) -- automatically derived


-- Term Datatype ---------------------------------------------------------------

type TermIndex = Int -- Word64

-- | For more information on the semantics of 'Term's, see the
-- [manual](https://saw.galois.com/manual.html). 'Term' and 'TermF' are split
-- into two structures to facilitate mutual structural recursion (sometimes
-- referred to as the ["knot-tying"](https://wiki.haskell.org/Tying_the_Knot)
-- pattern, sometimes referred to in terms of ["recursion
-- schemes"](https://blog.sumtypeofway.com/posts/introduction-to-recursion-schemes.html))
-- and term object reuse via hash-consing.
data Term
  = STApp
    -- ^ This constructor \"wraps\" a 'TermF' 'Term', assigning it a
    -- guaranteed-unique integer identifier and caching its likely-unique hash.
    -- Most 'Term's are constructed via 'STApp'. When a fresh 'TermF' is evinced
    -- in the course of a SAW invocation and needs to be lifted into a 'Term',
    -- we can see if we've already created a 'Term' wrapper for an identical
    -- 'TermF', and reuse it if so. The implementation of hash-consed 'Term'
    -- construction exists in 'SAWCore.SharedTerm', in particular in the
    -- 'SAWCore.SharedTerm.scTermF' field of the
    -- t'SAWCore.SharedTerm.SharedContext' object.
     { stAppIndex    :: {-# UNPACK #-} !TermIndex
       -- ^ The UID associated with a 'Term'. It is guaranteed unique across a
       -- universe of properly-constructed 'Term's within a single SAW
       -- invocation.
     , stAppHash     :: {-# UNPACK #-} !Int
       -- ^ The hash, according to 'hash', of the 'stAppTermF' field associated
       -- with this 'Term'. This should be as unique as a hash can be, but is
       -- not guaranteed unique as 'stAppIndex' is.
     , stAppLooseVars :: !BitSet
       -- ^ A set containing the 'DeBruijnIndex' of each of the loose
       -- de Bruijn indices from 'LocalVar' constructors in the term.
     , stAppFreeVars :: !IntSet
       -- ^ A set containing the 'VarIndex' of each of the free named
       -- variables from 'Variable' constructors in the term.
     , stAppTermF    :: !(TermF Term)
       -- ^ The underlying 'TermF' that this 'Term' wraps. This field "ties the
       -- knot" of the 'Term'/'TermF' recursion scheme.
     }
  | Unshared !(TermF Term)
    -- ^ Used for constructing 'Term's that don't need to be shared/reused.
  deriving (Show, Typeable)

instance Hashable Term where
  -- The hash of an 'STApp' depends on its not-necessarily-unique
  -- 'stAppHash' instead of its necessarily-unique 'stAppIndex'.
  -- The reason is that per #1830 (PR) and #1831 (issue), we want to
  -- to derive references to terms based solely on their shape.
  -- Indices have nothing to do with a term's shape - they're assigned
  -- sequentially when building terms, according to the (arbitrary)
  -- order in which a term is built.
  -- As for uniqueness, though hashing a term based on its subterms'
  -- hashes introduces less randomness/freshness, it maintains plenty,
  -- and provides benefits as described above.
  -- No code should ever rely on total uniqueness of hashes, and terms
  -- are no exception.
  --
  -- Note: Nevertheless, we do take some minor liberties with the
  -- contract of 'hashWithSalt'. The contract states that if two
  -- values are equal according to '(==)', then they must have the
  -- same hash.
  -- For terms constructed by/within SAW, this will hold, because
  -- SAW's handling of index generation and assignment ensures that
  -- equality of indices implies equality of terms and term hashes
  -- (see 'SAWCore.SharedTerm.getTerm').
  -- However, if terms are constructed outside this standard procedure
  -- or in a way that does not respect index uniqueness rules,
  -- 'hashWithSalt''s contract could be violated.
  hash STApp{ stAppHash = h } = h
  hash (Unshared t) = hash t
  hashWithSalt salt = hashWithSalt salt . hash

instance Eq Term where
  (==) = equalTerm

equalTerm :: Term -> Term -> Bool
equalTerm (Unshared tf1) (Unshared tf2) = tf1 == tf2
equalTerm Unshared{} STApp{} = False
equalTerm STApp{} Unshared{} = False
equalTerm (STApp{stAppIndex = i1, stAppHash = h1, stAppTermF = tf1})
          (STApp{stAppIndex = i2, stAppHash = h2, stAppTermF = tf2}) =
  i1 == i2 || (h1 == h2 && tf1 == tf2)
  -- The hash check (^) is merely an optimization that enables us to
  -- quickly return 'False' in most cases. Since we're assuming the
  -- contract of 'hashWithSalt' holds, then we know @tf1 == tf2@
  -- implies @h1 == h2@. Thus we could safely remove @h1 == h2@ without
  -- changing the behavior of this function, but keeping it in enables
  -- us to utilize the fact that we save 'STApp' hashes to get away
  -- with not traversing the 'stAppTermF' fields in most cases of
  -- inequality.

-- | Return 'True' iff the given terms are equal modulo alpha equivalence (i.e.
-- 'LocalNames' in 'Lambda' and 'Pi' expressions) and sharing (i.e. 'STApp' vs.
-- 'Unshared' expressions).
alphaEquiv :: Term -> Term -> Bool
alphaEquiv = term
  where
    term :: Term -> Term -> Bool
    term (Unshared tf1) (Unshared tf2) = termf tf1 tf2
    term (Unshared tf1) (STApp{stAppTermF = tf2}) = termf tf1 tf2
    term (STApp{stAppTermF = tf1}) (Unshared tf2) = termf tf1 tf2
    term (STApp{stAppIndex = i1, stAppTermF = tf1})
         (STApp{stAppIndex = i2, stAppTermF = tf2}) =
         i1 == i2 || termf tf1 tf2

    termf :: TermF Term -> TermF Term -> Bool
    termf (FTermF ftf1) (FTermF ftf2) = ftermf ftf1 ftf2
    termf (App t1 u1) (App t2 u2) = term t1 t2 && term u1 u2
    termf (Lambda _ t1 u1) (Lambda _ t2 u2) = term t1 t2 && term u1 u2
    termf (Pi _ t1 u1) (Pi _ t2 u2) = term t1 t2 && term u1 u2
    termf (LocalVar i1) (LocalVar i2) = i1 == i2
    termf (Constant x1) (Constant x2) = x1 == x2
    termf (Variable x1) (Variable x2) = x1 == x2
    termf FTermF{}   _ = False
    termf App{}      _ = False
    termf Lambda{}   _ = False
    termf Pi{}       _ = False
    termf LocalVar{} _ = False
    termf Constant{} _ = False
    termf Variable{} _ = False

    ftermf :: FlatTermF Term -> FlatTermF Term -> Bool
    ftermf ftf1 ftf2 = case zipWithFlatTermF term ftf1 ftf2 of
                         Nothing -> False
                         Just ftf3 -> Foldable.and ftf3

instance Ord Term where
  compare (STApp{stAppIndex = i}) (STApp{stAppIndex = j}) | i == j = EQ
  compare STApp{} Unshared{} = LT -- matches what we'd get from derived Ord instance
  compare Unshared{} STApp{} = GT
  compare x y = compare (unwrapTermF x) (unwrapTermF y)

instance Net.Pattern Term where
  toPat = termToPat

termToPat :: Term -> Net.Pat
termToPat t =
    case unwrapTermF t of
      Constant nm               -> Net.Atom (toShortName (nameInfo nm))
      App t1 t2                 -> Net.App (termToPat t1) (termToPat t2)
      FTermF (Sort s _)         -> Net.Atom (Text.pack ('*' : show s))
      FTermF (NatLit _)         -> Net.Var
      _                         -> Net.Var

unwrapTermF :: Term -> TermF Term
unwrapTermF STApp{stAppTermF = tf} = tf
unwrapTermF (Unshared tf) = tf


-- Free de Bruijn Variables ----------------------------------------------------

-- | A @BitSet@ represents a set of natural numbers.
-- Bit n is a 1 iff n is in the set.
newtype BitSet = BitSet Integer deriving (Eq, Ord, Show)

-- | The empty 'BitSet'
emptyBitSet :: BitSet
emptyBitSet = BitSet 0

-- | The singleton 'BitSet'
singletonBitSet :: Int -> BitSet
singletonBitSet = BitSet . bit

-- | Test if a number is in a 'BitSet'
inBitSet :: Int -> BitSet -> Bool
inBitSet i (BitSet j) = testBit j i

-- | Union two 'BitSet's
unionBitSets :: BitSet -> BitSet -> BitSet
unionBitSets (BitSet i1) (BitSet i2) = BitSet (i1 .|. i2)

-- | Intersect two 'BitSet's
intersectBitSets :: BitSet -> BitSet -> BitSet
intersectBitSets (BitSet i1) (BitSet i2) = BitSet (i1 .&. i2)

-- | Decrement all elements of a 'BitSet' by 1, removing 0 if it is in the
-- set. This is useful for moving a 'BitSet' out of the scope of a variable.
decrBitSet :: BitSet -> BitSet
decrBitSet (BitSet i) = BitSet (shiftR i 1)

-- | Decrement all elements of a 'BitSet' by some non-negative amount @N@,
-- removing any value less than @N@. This is the same as calling 'decrBitSet'
-- @N@ times.
multiDecrBitSet :: Int -> BitSet -> BitSet
multiDecrBitSet n (BitSet i) = BitSet (shiftR i n)

-- | The 'BitSet' containing all elements less than a given index @i@
completeBitSet :: Int -> BitSet
completeBitSet i = BitSet (bit i - 1)

-- | Compute the smallest element of a 'BitSet', if any
smallestBitSetElem :: BitSet -> Maybe Int
smallestBitSetElem (BitSet 0) = Nothing
smallestBitSetElem (BitSet i) | i < 0 = error "smallestBitSetElem"
smallestBitSetElem (BitSet i) = Just $ go 0 i where
  go :: Int -> Integer -> Int
  go !shft !x
    | xw == 0   = go (shft+64) (shiftR x 64)
    | otherwise = shft + countTrailingZeros xw
    where xw :: Word64
          xw = fromInteger x

-- | Compute the list of all elements of a 'BitSet'
bitSetElems :: BitSet -> [Int]
bitSetElems = go 0 where
  -- Return the addition of shft to all elements of a BitSet
  go :: Int -> BitSet -> [Int]
  go shft bs = case smallestBitSetElem bs of
    Nothing -> []
    Just i ->
      shft + i : go (shft + i + 1) (multiDecrBitSet (i + 1) bs)

-- | Return the smallest non-negative integer greater than every
-- element of the 'BitSet'.
bitSetBound :: BitSet -> Int
bitSetBound b = length $ takeWhile (/= emptyBitSet) $ iterate decrBitSet b

-- | Compute the loose de Bruijn indices of a term given the loose
-- indices for its immediate subterms.
looseTermF :: TermF BitSet -> BitSet
looseTermF tf =
    case tf of
      FTermF ftf -> Foldable.foldl' unionBitSets emptyBitSet ftf
      App l r -> unionBitSets l r
      Lambda _name tp rhs -> unionBitSets tp (decrBitSet rhs)
      Pi _name lhs rhs -> unionBitSets lhs (decrBitSet rhs)
      LocalVar i -> singletonBitSet i
      Constant {} -> emptyBitSet -- assume type is a closed term
      Variable ec -> ecType ec

-- | Return a bitset containing indices of all loose de Bruijn indices.
looseVars :: Term -> BitSet
looseVars STApp{ stAppLooseVars = x } = x
looseVars (Unshared f) = looseTermF (fmap looseVars f)

-- | Compute the value of the smallest variable in the term, if any.
smallestLooseVar :: Term -> Maybe Int
smallestLooseVar = smallestBitSetElem . looseVars

-- | Test whether a 'Term' is closed, i.e., has no loose de Bruijn indices.
termIsClosed :: Term -> Bool
termIsClosed t = looseVars t == emptyBitSet

-- Free Named Variables --------------------------------------------------------

-- | Compute an 'IntSet' containing the 'VarIndex' of the free
-- variables of a term, given the free variables for its immediate
-- subterms.
freesTermF :: TermF IntSet -> IntSet
freesTermF tf =
  case tf of
    FTermF ftf -> Foldable.foldl' IntSet.union IntSet.empty ftf
    App l r -> IntSet.union l r
    Lambda _name tp rhs -> IntSet.union tp rhs
    Pi _name lhs rhs -> IntSet.union lhs rhs
    LocalVar _ -> IntSet.empty
    Constant {} -> IntSet.empty
    Variable ec -> IntSet.singleton (ecVarIndex ec)

-- | Return an 'IntSet' containing the 'VarIndex' of all free
-- variables in the 'Term'.
freeVars :: Term -> IntSet
freeVars STApp{ stAppFreeVars = s } = s
freeVars (Unshared tf) = freesTermF (fmap freeVars tf)
