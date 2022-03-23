{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE BangPatterns #-}

{- |
Module      : Verifier.SAW.Term.Functor
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Term.Functor
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
  , PrimName(..)
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
  , freesTermF
  , unwrapTermF
  , termToPat
  , alphaEquiv
  , alistAllFields
    -- * Sorts
  , Sort, mkSort, propSort, sortOf, maxSort
    -- * Sets of free variables
  , BitSet, emptyBitSet, inBitSet, unionBitSets, intersectBitSets
  , decrBitSet, multiDecrBitSet, completeBitSet, singletonBitSet, bitSetElems
  , smallestBitSetElem
  , looseVars, smallestFreeVar
  ) where

import Data.Bits
#if !MIN_VERSION_base(4,8,0)
import Data.Foldable (Foldable)
#endif
import qualified Data.Foldable as Foldable (and, foldl')
import Data.Hashable
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

import Verifier.SAW.Name
import qualified Verifier.SAW.TermNet as Net

type DeBruijnIndex = Int
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


-- Flat Terms ------------------------------------------------------------------

-- | The "flat terms", which are the built-in atomic constructs of SAW core.
--
-- NB: If you add constructors to FlatTermF, make sure you update
--     zipWithFlatTermF!
data FlatTermF e
    -- | A primitive or axiom without a definition.
  = Primitive !(PrimName e)

  | TupleValue (Vector e)
    -- | A zero-indexed tuple field selection.
  | TupleSelector e Int

    -- | An inductively-defined type, applied to parameters and type indices
  | DataTypeApp !(PrimName e) ![e] ![e]

    -- | An application of a constructor to its arguments, i.e., an element of
    -- an inductively-defined type; the parameters (of the inductive type to
    -- which this constructor belongs) and indices are kept separate
  | CtorApp !(PrimName e) ![e] ![e]

    -- | The type of a recursor, which is specified by the datatype name,
    --   the parameters to the data type, the motive function, and the
    --   type of the motive function.
  | RecursorType !(PrimName e) ![e] !e !e

    -- | A recursor, which is specified by giving the datatype name,
    --   the parameters to the datatype, a motive and elimination functions
    --   for each constructor. A recursor can be used with the special
    --   @RecursorApp@ term, which provides the datatype indices and
    --   actual argument to the eliminator.
  | Recursor (CompiledRecursor e)

    -- | An eliminator / pattern-matching function for an inductively-defined
    -- type, given by:
    -- * The recursor value;
    -- * The indices for the inductive type; AND
    -- * The argument that is being eliminated / pattern-matched
  | RecursorApp e [e] e

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
    -- "type" iff it has type @Sort s@ for some s.
    --
    -- The extra boolean argument is an advisory flag that is used to
    -- indicate that types in this sort are expected to be inhabited.
    -- In the concrete syntax "isort" is used to indicate cases where
    -- this flag is set.  This flag is mostly ignored, but is used in
    -- the Coq export process to indicate where "Inhabited" class
    -- instances are necessary in function definitions. Note in particular
    -- that this flag does not affect typechecking, so missing or overeager
    -- "isort" annotations will only be detected via the Coq export.
  | Sort !Sort !Bool

    -- Primitive builtin values
    -- | Natural number with given value.
  | NatLit !Natural
    -- | Array value includes type of elements followed by elements.
  | ArrayValue e (Vector e)
    -- | String literal
  | StringLit !Text

    -- | An external constant with a name.
  | ExtCns !(ExtCns e)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Hashable e => Hashable (FlatTermF e) -- automatically derived

-- Capture more type information here so we can
--  use it during evaluation time to remember the
--  types of the parameters, motive and eliminator functions.
data CompiledRecursor e =
  CompiledRecursor
  { recursorDataType  :: PrimName e
  , recursorParams    :: [e]
  , recursorMotive    :: e
  , recursorMotiveTy  :: e
  , recursorElims     :: Map VarIndex (e, e) -- eliminator functions and their types
  , recursorCtorOrder :: [PrimName e]
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

zipPair :: (x -> y -> z) -> (x,x) -> (y,y) -> (z,z)
zipPair f (x1,x2) (y1,y2) = (f x1 y1, f x2 y2)

zipPrimName :: (x -> y -> z) -> PrimName x -> PrimName y -> Maybe (PrimName z)
zipPrimName f (PrimName v1 ident x) (PrimName v2 _ y)
  | v1 == v2 = Just (PrimName v1 ident (f x y))
  | otherwise = Nothing

zipRec :: (x -> y -> z) -> CompiledRecursor x -> CompiledRecursor y -> Maybe (CompiledRecursor z)
zipRec f (CompiledRecursor d1 ps1 m1 mty1 es1 ord1) (CompiledRecursor d2 ps2 m2 mty2 es2 ord2)
  | Map.keysSet es1 == Map.keysSet es2
  = do d <- zipPrimName f d1 d2
       ord <- sequence (zipWith (zipPrimName f) ord1 ord2)
       pure $ CompiledRecursor
              d
              (zipWith f ps1 ps2)
              (f m1 m2)
              (f mty1 mty2)
              (Map.intersectionWith (zipPair f) es1 es2)
              ord

  | otherwise = Nothing

-- | Zip a binary function @f@ over a pair of 'FlatTermF's by applying @f@
-- pointwise to immediate subterms, if the two 'FlatTermF's are the same
-- constructor; otherwise, return 'Nothing' if they use different constructors.
zipWithFlatTermF :: (x -> y -> z) -> FlatTermF x -> FlatTermF y ->
                    Maybe (FlatTermF z)
zipWithFlatTermF f = go
  where
    go (Primitive pn1) (Primitive pn2) = Primitive <$> zipPrimName f pn1 pn2
    go (TupleValue xs) (TupleValue ys)
      | V.length xs == V.length ys = Just $ TupleValue (V.zipWith f xs ys)
    go (TupleSelector x i) (TupleSelector y j)
      | i == j = Just (TupleSelector (f x y) i)
    go (CtorApp cx psx lx) (CtorApp cy psy ly) =
      do c <- zipPrimName f cx cy
         Just $ CtorApp c (zipWith f psx psy) (zipWith f lx ly)
    go (DataTypeApp dx psx lx) (DataTypeApp dy psy ly) =
      do d <- zipPrimName f dx dy
         Just $ DataTypeApp d (zipWith f psx psy) (zipWith f lx ly)

    go (RecursorType d1 ps1 m1 mty1) (RecursorType d2 ps2 m2 mty2) =
      do d <- zipPrimName f d1 d2
         Just $ RecursorType d (zipWith f ps1 ps2) (f m1 m2) (f mty1 mty2)

    go (Recursor rec1) (Recursor rec2) =
      Recursor <$> zipRec f rec1 rec2

    go (RecursorApp rec1 ixs1 x1) (RecursorApp rec2 ixs2 x2) =
        Just $ RecursorApp
          (f rec1 rec2)
          (zipWith f ixs1 ixs2)
          (f x1 x2)

    go (RecordType elems1) (RecordType elems2)
      | Just vals2 <- alistAllFields (map fst elems1) elems2 =
        Just $ RecordType $ zipWith (\(fld,x) y -> (fld, f x y)) elems1 vals2
    go (RecordValue elems1) (RecordValue elems2)
      | Just vals2 <- alistAllFields (map fst elems1) elems2 =
        Just $ RecordValue $ zipWith (\(fld,x) y -> (fld, f x y)) elems1 vals2
    go (RecordProj e1 fld1) (RecordProj e2 fld2)
      | fld1 == fld2 = Just $ RecordProj (f e1 e2) fld1

    go (Sort sx hx) (Sort sy hy) | sx == sy = Just (Sort sx (hx && hy))
         -- /\ NB, it's not entirely clear how the inhabited flag should be propagated
    go (NatLit i) (NatLit j) | i == j = Just (NatLit i)
    go (StringLit s) (StringLit t) | s == t = Just (StringLit s)
    go (ArrayValue tx vx) (ArrayValue ty vy)
      | V.length vx == V.length vy
      = Just $ ArrayValue (f tx ty) (V.zipWith f vx vy)
    go (ExtCns (EC xi xn xt)) (ExtCns (EC yi _ yt))
      | xi == yi = Just (ExtCns (EC xi xn (f xt yt)))

    go _ _ = Nothing


-- Term Functor ----------------------------------------------------------------

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
    | Constant !(ExtCns e) !(Maybe e)
      -- ^ An abstract constant packaged with its type and definition.
      -- The body and type should be closed terms.
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Hashable e => Hashable (TermF e) -- automatically derived.


-- Term Datatype ---------------------------------------------------------------

type TermIndex = Int -- Word64

data Term
  = STApp
     { stAppIndex    :: {-# UNPACK #-} !TermIndex
     , stAppFreeVars :: !BitSet -- Free variables
     , stAppTermF    :: !(TermF Term)
     }
  | Unshared !(TermF Term)
  deriving (Show, Typeable)

instance Hashable Term where
  hashWithSalt salt STApp{ stAppIndex = i } = salt `combine` 0x00000000 `hashWithSalt` hash i
  hashWithSalt salt (Unshared t) = salt `combine` 0x55555555 `hashWithSalt` hash t


-- | Combine two given hash values.  'combine' has zero as a left
-- identity. (FNV hash, copied from Data.Hashable 1.2.1.0.)
combine :: Int -> Int -> Int
combine h1 h2 = (h1 * 0x01000193) `xor` h2

instance Eq Term where
  (==) = alphaEquiv

alphaEquiv :: Term -> Term -> Bool
alphaEquiv = term
  where
    term :: Term -> Term -> Bool
    term (Unshared tf1) (Unshared tf2) = termf tf1 tf2
    term (Unshared tf1) (STApp{stAppTermF = tf2}) = termf tf1 tf2
    term (STApp{stAppTermF = tf1}) (Unshared tf2) = termf tf1 tf2
    term (STApp{stAppIndex = i1, stAppTermF = tf1})
         (STApp{stAppIndex = i2, stAppTermF = tf2}) = i1 == i2 || termf tf1 tf2

    termf :: TermF Term -> TermF Term -> Bool
    termf (FTermF ftf1) (FTermF ftf2) = ftermf ftf1 ftf2
    termf (App t1 u1) (App t2 u2) = term t1 t2 && term u1 u2
    termf (Lambda _ t1 u1) (Lambda _ t2 u2) = term t1 t2 && term u1 u2
    termf (Pi _ t1 u1) (Pi _ t2 u2) = term t1 t2 && term u1 u2
    termf (LocalVar i1) (LocalVar i2) = i1 == i2
    termf (Constant x1 _) (Constant x2 _) = ecVarIndex x1 == ecVarIndex x2
    termf _ _ = False

    ftermf :: FlatTermF Term -> FlatTermF Term -> Bool
    ftermf ftf1 ftf2 = case zipWithFlatTermF term ftf1 ftf2 of
                         Nothing -> False
                         Just ftf3 -> Foldable.and ftf3

instance Ord Term where
  compare (STApp{stAppIndex = i}) (STApp{stAppIndex = j}) | i == j = EQ
  compare x y = compare (unwrapTermF x) (unwrapTermF y)

instance Net.Pattern Term where
  toPat = termToPat

termToPat :: Term -> Net.Pat
termToPat t =
    case unwrapTermF t of
      Constant ec _             -> Net.Atom (toShortName (ecName ec))
      App t1 t2                 -> Net.App (termToPat t1) (termToPat t2)
      FTermF (Primitive pn)     -> Net.Atom (identBaseName (primName pn))
      FTermF (Sort s _)         -> Net.Atom (Text.pack ('*' : show s))
      FTermF (NatLit _)         -> Net.Var
      FTermF (DataTypeApp c ps ts) ->
        foldl Net.App (Net.Atom (identBaseName (primName c))) (map termToPat (ps ++ ts))
      FTermF (CtorApp c ps ts)   ->
        foldl Net.App (Net.Atom (identBaseName (primName c))) (map termToPat (ps ++ ts))
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

-- | Compute the free variables of a term given free variables for its immediate
-- subterms
freesTermF :: TermF BitSet -> BitSet
freesTermF tf =
    case tf of
      FTermF ftf -> Foldable.foldl' unionBitSets emptyBitSet ftf
      App l r -> unionBitSets l r
      Lambda _name tp rhs -> unionBitSets tp (decrBitSet rhs)
      Pi _name lhs rhs -> unionBitSets lhs (decrBitSet rhs)
      LocalVar i -> singletonBitSet i
      Constant {} -> emptyBitSet -- assume rhs is a closed term

-- | Return a bitset containing indices of all free local variables
looseVars :: Term -> BitSet
looseVars STApp{ stAppFreeVars = x } = x
looseVars (Unshared f) = freesTermF (fmap looseVars f)

-- | Compute the value of the smallest variable in the term, if any.
smallestFreeVar :: Term -> Maybe Int
smallestFreeVar = smallestBitSetElem . looseVars
