{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes #-}

{- |
Module      : Verifier.SAW.Term.Functor
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Term.Functor
 ( -- * Names.
   ModuleName, mkModuleName
 , preludeName
   -- * Data types and definitions.
 , DeBruijnIndex
 , FieldName
 , DataType(..)
 , Ctor(..)
 , GenericDef(..)
 , Def
 , DefQualifier(..)
 , LocalDef
 , ExtCns(..)
 , VarIndex
 , DefEqn(..)
 , localVarNames
   -- * Patterns.
 , Pat(..)
 , patBoundVars
 , patBoundVarCount
 , patUnusedVarCount
   -- * Terms and associated operations.
 , TermF(..)
 , FlatTermF(..)
 , zipWithFlatTermF
 , BitSet
 , freesTermF
 , Termlike(..)
 , termToPat
   -- * Primitive types.
 , Sort, mkSort, sortOf, maxSort
 , Ident(identModule, identName), mkIdent
 , parseIdent
 , isIdent
 ) where

import Control.Exception (assert)
import Control.Lens
import Data.Bits
import qualified Data.ByteString.UTF8 as BS
import Data.Char
#if !MIN_VERSION_base(4,8,0)
import Data.Foldable (Foldable)
#endif
import Data.Foldable (all)
import Data.Hashable
import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Word
import GHC.Generics (Generic)
import GHC.Exts (IsString(..))

import Prelude hiding (all, foldr, sum)

import qualified Verifier.SAW.TermNet as Net
import Verifier.SAW.Utils (internalError, sumBy)

type DeBruijnIndex = Int
type FieldName = String

instance (Hashable k, Hashable a) => Hashable (Map k a) where
    hashWithSalt x m = hashWithSalt x (Map.assocs m)

instance Hashable a => Hashable (Vector a) where
    hashWithSalt x v = hashWithSalt x (V.toList v)


-- Module Names ----------------------------------------------------------------

newtype ModuleName = ModuleName BS.ByteString -- [String]
  deriving (Eq, Ord, Generic)

instance Hashable ModuleName -- automatically derived

instance Show ModuleName where
  show (ModuleName s) = BS.toString s

-- | Create a module name given a list of strings with the top-most
-- module name given first.
mkModuleName :: [String] -> ModuleName
mkModuleName [] = error "internal: mkModuleName given empty module name"
mkModuleName nms = assert (all isCtor nms) $ ModuleName (BS.fromString s)
  where s = intercalate "." (reverse nms)

preludeName :: ModuleName
preludeName = mkModuleName ["Prelude"]


-- Identifiers -----------------------------------------------------------------

data Ident =
  Ident
  { identModule :: ModuleName
  , identName :: String
  }
  deriving (Eq, Ord, Generic)

instance Hashable Ident -- automatically derived

instance Show Ident where
  show (Ident m s) = shows m ('.' : s)

mkIdent :: ModuleName -> String -> Ident
mkIdent = Ident

-- | Parse a fully qualified identifier.
parseIdent :: String -> Ident
parseIdent s0 =
    case reverse (breakEach s0) of
      (_:[]) -> internalError $ "parseIdent given empty module name."
      (nm:rMod) -> mkIdent (mkModuleName (reverse rMod)) nm
      _ -> internalError $ "parseIdent given bad identifier " ++ show s0
  where breakEach s =
          case break (=='.') s of
            (h,[]) -> [h]
            (h,'.':r) -> h : breakEach r
            _ -> internalError "parseIdent.breakEach failed"

instance IsString Ident where
  fromString = parseIdent

isIdent :: String -> Bool
isIdent (c:l) = isAlpha c && all isIdChar l
isIdent [] = False

isCtor :: String -> Bool
isCtor (c:l) = isUpper c && all isIdChar l
isCtor [] = False

-- | Returns true if character can appear in identifier.
isIdChar :: Char -> Bool
isIdChar c = isAlphaNum c || (c == '_') || (c == '\'')


-- Sorts -----------------------------------------------------------------------

newtype Sort = SortCtor { _sortIndex :: Integer }
  deriving (Eq, Ord, Generic)

instance Hashable Sort -- automatically derived

instance Show Sort where
  showsPrec p (SortCtor i) = showParen (p >= 10) (showString "sort " . shows i)

-- | Create sort for given integer.
mkSort :: Integer -> Sort
mkSort i | 0 <= i = SortCtor i
         | otherwise = error "Negative index given to sort."

-- | Returns sort of the given sort.
sortOf :: Sort -> Sort
sortOf (SortCtor i) = SortCtor (i + 1)

-- | Returns the larger of the two sorts.
maxSort :: Sort -> Sort -> Sort
maxSort (SortCtor x) (SortCtor y) = SortCtor (max x y)


-- Patterns --------------------------------------------------------------------

-- Patterns are used to match equations.
data Pat e = -- | Variable bound by pattern.
             -- Variables may be bound in context in a different order than
             -- a left-to-right traversal.  The DeBruijnIndex indicates the order.
             PVar String DeBruijnIndex e
             -- | The
           | PUnused DeBruijnIndex e
           | PUnit
           | PPair (Pat e) (Pat e)
           | PEmpty
           | PField (Pat e) (Pat e) (Pat e) -- ^ Field name, field value, rest of record
           | PString String
           | PCtor Ident [Pat e]
  deriving (Eq,Ord, Show, Functor, Foldable, Traversable, Generic)

instance Hashable e => Hashable (Pat e) -- automatically derived

patBoundVarCount :: Pat e -> DeBruijnIndex
patBoundVarCount p =
  case p of
    PVar{} -> 1
    PUnused{} -> 0
    PCtor _ l -> sumBy patBoundVarCount l
    PUnit     -> 0
    PPair x y -> patBoundVarCount x + patBoundVarCount y
    PEmpty    -> 0
    PField f x y -> patBoundVarCount f + patBoundVarCount x + patBoundVarCount y
    PString _ -> 0

patUnusedVarCount :: Pat e -> DeBruijnIndex
patUnusedVarCount p =
  case p of
    PVar{}       -> 0
    PUnused{}    -> 1
    PCtor _ l    -> sumBy patUnusedVarCount l
    PUnit        -> 0
    PPair x y    -> patUnusedVarCount x + patUnusedVarCount y
    PEmpty       -> 0
    PField _ x y -> patUnusedVarCount x + patUnusedVarCount y
    PString _    -> 0

patBoundVars :: Pat e -> [String]
patBoundVars p =
  case p of
    PVar s _ _   -> [s]
    PCtor _ l    -> concatMap patBoundVars l
    PUnit        -> []
    PPair x y    -> patBoundVars x ++ patBoundVars y
    PEmpty       -> []
    PField _ x y -> patBoundVars x ++ patBoundVars y
    PString _    -> []
    PUnused{}    -> []


-- Definitions -----------------------------------------------------------------

data DefQualifier
  = NoQualifier
  | PrimQualifier
  | AxiomQualifier
 deriving (Eq, Ord, Show, Generic)

instance Hashable DefQualifier -- automatically derived

-- | A Definition contains an identifier, the type of the definition, and a list of equations.
data GenericDef n e =
  Def
  { defIdent :: n
  , defQualifier :: DefQualifier
  , defType :: e
  , defEqs :: [DefEqn e]
  }
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

type Def = GenericDef Ident
type LocalDef = GenericDef String

instance (Hashable n, Hashable e) => Hashable (GenericDef n e) -- automatically derived

localVarNames :: LocalDef e -> [String]
localVarNames (Def nm _ _ _) = [nm]

data DefEqn e
  = DefEqn [Pat e] e -- ^ List of patterns and a right hand side
  deriving (Functor, Foldable, Traversable, Generic, Show)

instance Hashable e => Hashable (DefEqn e) -- automatically derived

instance (Eq e) => Eq (DefEqn e) where
  DefEqn xp xr == DefEqn yp yr = xp == yp && xr == yr

instance (Ord e) => Ord (DefEqn e) where
  compare (DefEqn xp xr) (DefEqn yp yr) = compare (xp,xr) (yp,yr)


-- Constructors ----------------------------------------------------------------

data Ctor n tp =
  Ctor
  { ctorName :: !n
  , ctorType :: tp -- ^ The type of the constructor (should contain no free variables).
  }
  deriving (Functor, Foldable, Traversable)

lift2 :: (a -> b) -> (b -> b -> c) -> a -> a -> c
lift2 f h x y = h (f x) (f y)

instance Eq n => Eq (Ctor n tp) where
  (==) = lift2 ctorName (==)

instance Ord n => Ord (Ctor n tp) where
  compare = lift2 ctorName compare

instance Show n => Show (Ctor n tp) where
  show = show . ctorName


-- Datatypes -------------------------------------------------------------------

data DataType n t =
  DataType
  { dtName :: n
  , dtType :: t
  , dtCtors :: [Ctor n t]
  , dtIsPrimitive :: Bool
  }
  deriving (Functor, Foldable, Traversable)

instance Eq n => Eq (DataType n t) where
  (==) = lift2 dtName (==)

instance Ord n => Ord (DataType n t) where
  compare = lift2 dtName compare

instance Show n => Show (DataType n t) where
  show = show . dtName


-- External Constants ----------------------------------------------------------

type VarIndex = Word64

-- | An external constant with a name.
-- Names are not necessarily unique, but the var index should be.
data ExtCns e =
  EC
  { ecVarIndex :: !VarIndex
  , ecName :: !String
  , ecType :: !e
  }
  deriving (Functor, Foldable, Traversable)

instance Eq (ExtCns e) where
  x == y = ecVarIndex x == ecVarIndex y

instance Ord (ExtCns e) where
  compare x y = compare (ecVarIndex x) (ecVarIndex y)

instance Hashable (ExtCns e) where
  hashWithSalt x ec = hashWithSalt x (ecVarIndex ec)


-- Flat Terms ------------------------------------------------------------------

-- NB: If you add constructors to FlatTermF, make sure you update
--     zipWithFlatTermF!
data FlatTermF e
  = GlobalDef !Ident  -- ^ Global variables are referenced by label.

    -- Tuples are represented as nested pairs, grouped to the right,
    -- terminated with unit at the end.
  | UnitValue
  | UnitType
  | PairValue e e
  | PairType e e
  | PairLeft e
  | PairRight e
  | EmptyValue
  | EmptyType
  | FieldValue e e e -- Field name, field value, remainder of record
  | FieldType e e e
  | RecordSelector e e -- Record value, field name

  | CtorApp !Ident ![e]
  | DataTypeApp !Ident ![e]

  | Sort !Sort

    -- Primitive builtin values
    -- | Natural number with given value (negative numbers are not allowed).
  | NatLit !Integer
    -- | Array value includes type of elements followed by elements.
  | ArrayValue e (Vector e)
    -- | Floating point literal
  | FloatLit !Float
    -- | Double precision floating point literal.
  | DoubleLit !Double
    -- | String literal.
  | StringLit !String

    -- | An external constant with a name.
  | ExtCns !(ExtCns e)
  deriving (Eq, Ord, Functor, Foldable, Traversable, Generic)

instance Hashable e => Hashable (FlatTermF e) -- automatically derived

zipWithFlatTermF :: (x -> y -> z) -> FlatTermF x -> FlatTermF y -> Maybe (FlatTermF z)
zipWithFlatTermF f = go
  where
    go (GlobalDef x) (GlobalDef y) | x == y = Just $ GlobalDef x

    go UnitValue UnitValue = Just UnitValue
    go UnitType UnitType = Just UnitType
    go (PairValue x1 x2) (PairValue y1 y2) = Just (PairValue (f x1 y1) (f x2 y2))
    go (PairType x1 x2) (PairType y1 y2) = Just (PairType (f x1 y1) (f x2 y2))
    go (PairLeft x) (PairLeft y) = Just (PairLeft (f x y))
    go (PairRight x) (PairRight y) = Just (PairLeft (f x y))

    go EmptyValue EmptyValue = Just EmptyValue
    go EmptyType EmptyType = Just EmptyType
    go (FieldValue x1 x2 x3) (FieldValue y1 y2 y3) =
      Just $ FieldValue (f x1 y1) (f x2 y2) (f x3 y3)
    go (FieldType x1 x2 x3) (FieldType y1 y2 y3) =
      Just $ FieldType (f x1 y1) (f x2 y2) (f x3 y3)
    go (RecordSelector x1 x2) (RecordSelector y1 y2) =
      Just $ RecordSelector (f x1 y1) (f x2 y2)

    go (CtorApp cx lx) (CtorApp cy ly)
      | cx == cy = Just $ CtorApp cx (zipWith f lx ly)
    go (DataTypeApp dx lx) (DataTypeApp dy ly)
      | dx == dy = Just $ DataTypeApp dx (zipWith f lx ly)
    go (Sort sx) (Sort sy) | sx == sy = Just (Sort sx)
    go (NatLit i) (NatLit j) | i == j = Just (NatLit i)
    go (FloatLit fx) (FloatLit fy)
      | fx == fy = Just $ FloatLit fx
    go (DoubleLit fx) (DoubleLit fy)
      | fx == fy = Just $ DoubleLit fx
    go (StringLit s) (StringLit t) | s == t = Just (StringLit s)
    go (ArrayValue tx vx) (ArrayValue ty vy)
      | V.length vx == V.length vy = Just $ ArrayValue (f tx ty) (V.zipWith f vx vy)
    go (ExtCns (EC xi xn xt)) (ExtCns (EC yi _ yt))
      | xi == yi = Just (ExtCns (EC xi xn (f xt yt)))

    go _ _ = Nothing


-- Term Functor ----------------------------------------------------------------

data TermF e
    = FTermF !(FlatTermF e)  -- ^ Global variables are referenced by label.
    | App !e !e
    | Lambda !String !e !e
    | Pi !String !e !e
    | LocalVar !DeBruijnIndex
      -- ^ Local variables are referenced by deBruijn index.
    | Constant String !e !e
      -- ^ An abstract constant packaged with its definition and type.
      -- The body and type should be closed terms.
  deriving (Eq, Ord, Functor, Foldable, Traversable, Generic)

instance Hashable e => Hashable (TermF e) -- automatically derived.


-- Free de Bruijn Variables ----------------------------------------------------

bitwiseOrOf :: (Bits a, Num a) => Fold s a -> s -> a
bitwiseOrOf fld = foldlOf' fld (.|.) 0

-- | A @BitSet@ represents a set of natural numbers.
-- Bit n is a 1 iff n is in the set.
type BitSet = Integer

freesTermF :: TermF BitSet -> BitSet
freesTermF tf =
    case tf of
      FTermF ftf -> bitwiseOrOf folded ftf
      App l r -> l .|. r
      Lambda _name tp rhs -> tp .|. rhs `shiftR` 1
      Pi _name lhs rhs -> lhs .|. rhs `shiftR` 1
      LocalVar i -> bit i
      Constant _ _ _ -> 0 -- assume rhs is a closed term


-- Termlike Class --------------------------------------------------------------

class Termlike t where
  unwrapTermF :: t -> TermF t

termToPat :: Termlike t => t -> Net.Pat
termToPat t =
    case unwrapTermF t of
      Constant d _ _            -> Net.Atom d
      App t1 t2                 -> Net.App (termToPat t1) (termToPat t2)
      FTermF (GlobalDef d)      -> Net.Atom (identName d)
      FTermF (Sort s)           -> Net.Atom ('*' : show s)
      FTermF (NatLit _)         -> Net.Var --Net.Atom (show n)
      FTermF (DataTypeApp c ts) -> foldl Net.App (Net.Atom (identName c)) (map termToPat ts)
      FTermF (CtorApp c ts)     -> foldl Net.App (Net.Atom (identName c)) (map termToPat ts)
      _                         -> Net.Var

