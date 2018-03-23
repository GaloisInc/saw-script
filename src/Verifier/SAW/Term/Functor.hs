{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE UndecidableInstances #-}

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
    -- * Identifiers
  , Ident(identModule, identName), mkIdent
  , parseIdent
  , isIdent
    -- * Data types and definitions
  , DeBruijnIndex
  , FieldName
  , ExtCns(..)
  , VarIndex
    -- * Terms and associated operations
  , TermIndex
  , Term(..)
  , TermF(..)
  , FlatTermF(..)
  , zipWithFlatTermF
  , BitSet
  , freesTermF
  , unwrapTermF
  , termToPat
  , alphaEquiv
  , looseVars, smallestFreeVar
  , alistAllFields, recordAListAsTuple, tupleAsRecordAList
    -- * Sorts
  , Sort, mkSort, propSort, sortOf
    -- * Terms in Context
  , Ctx(..), CtxBind, (:++:), Arrows, CtxExtends(..)
  , ctxTermsForBindings, invAppendBindings, invertBindings
    -- , appendBinding, appendBindings
  , CtxTerm(..), CtxTerms(..), Typ, mkClosedTerm, elimClosedTerm
  , CtxPair(..), Bindings(..), InvBindings(..), InBindings(..)
  ) where

import Control.Exception (assert)
import Control.Lens
import Data.Bits
import qualified Data.ByteString.UTF8 as BS
import Data.Char
#if !MIN_VERSION_base(4,8,0)
import Data.Foldable (Foldable)
#endif
import qualified Data.Foldable as Foldable (all, and)
import Data.Hashable
import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Typeable (Typeable)
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Word
import GHC.Generics (Generic)
import GHC.Exts (IsString(..))

import qualified Verifier.SAW.TermNet as Net
import Verifier.SAW.Utils (internalError)

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
mkModuleName nms = assert (Foldable.all isCtor nms) $ ModuleName (BS.fromString s)
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
isIdent (c:l) = isAlpha c && Foldable.all isIdChar l
isIdent [] = False

isCtor :: String -> Bool
isCtor (c:l) = isUpper c && Foldable.all isIdChar l
isCtor [] = False

-- | Returns true if character can appear in identifier.
isIdChar :: Char -> Bool
isIdChar c = isAlphaNum c || (c == '_') || (c == '\'')


-- Sorts -----------------------------------------------------------------------

-- | The sorts, also known as universes, which can either be a predicative
-- universe with level i or the impredicative universe Prop.
data Sort
  = TypeSort Integer
  | PropSort
  deriving (Eq, Generic)

-- Prop is the lowest sort
instance Ord Sort where
  PropSort <= _ = True
  (TypeSort _) <= PropSort = False
  (TypeSort i) <= (TypeSort j) = i <= j

instance Hashable Sort -- automatically derived

instance Show Sort where
  showsPrec p (TypeSort i) = showParen (p >= 10) (showString "sort " . shows i)
  showsPrec _ PropSort = showString "Prop"

-- | Create sort @Type i@ for the given integer @i@
mkSort :: Integer -> Sort
mkSort i | 0 <= i = TypeSort i
         | otherwise = error "Negative index given to sort."

-- | Wrapper around 'PropSort', for export
propSort :: Sort
propSort = PropSort

-- | Returns sort of the given sort.
sortOf :: Sort -> Sort
sortOf (TypeSort i) = TypeSort (i + 1)
sortOf PropSort = TypeSort 0


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
  deriving (Show, Functor, Foldable, Traversable)

instance Eq (ExtCns e) where
  x == y = ecVarIndex x == ecVarIndex y

instance Ord (ExtCns e) where
  compare x y = compare (ecVarIndex x) (ecVarIndex y)

instance Hashable (ExtCns e) where
  hashWithSalt x ec = hashWithSalt x (ecVarIndex ec)


-- Flat Terms ------------------------------------------------------------------

-- | The "flat terms", which are the built-in atomic constructs of SAW core.
--
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

    -- | An inductively-defined type, applied to parameters and type indices
  | DataTypeApp !Ident ![e] ![e]
    -- | An application of a constructor to its arguments, i.e., an element of
    -- an inductively-defined type; the parameters (of the inductive type to
    -- which this constructor belongs) and indices are kept separate
  | CtorApp !Ident ![e] ![e]
    -- | An eliminator / pattern-matching function for an inductively-defined
    -- type, given by:
    -- * The (identifier of the) inductive type it eliminates;
    -- * The parameters of that inductive type;
    -- * The return type, also called the "intent", given by a function from
    --   type indices of the inductive type to a type;
    -- * The elimination function for each constructor of that inductive type;
    -- * The indices for that inductive type; AND
    -- * The argument that is being eliminated / pattern-matched
  | RecursorApp !Ident [e] e [(Ident,e)] [e] e

    -- | Non-dependent record types, i.e., N-ary tuple types with named
    -- fields. These are considered equal up to reordering of fields. Actual
    -- tuple types are represented with field names @"1"@, @"2"@, etc.
  | RecordType ![(String, e)]
    -- | Non-dependent records, i.e., N-ary tuples with named fields. These are
    -- considered equal up to reordering of fields. Actual tuples are
    -- represented with field names @"1"@, @"2"@, etc.
  | RecordValue ![(String, e)]
    -- | Non-dependent record projection
  | RecordProj e !String

    -- | Sorts, aka universes, are the types of types; i.e., an object is a
    -- "type" iff it has type @Sort s@ for some s
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
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Hashable e => Hashable (FlatTermF e) -- automatically derived

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

-- | Test if the association list used in a 'RecordType' or 'RecordValue' uses
-- field names that are the strings @"1", "2", ...@ indicating that the record
-- type or value is to be printed as a tuple. If so, return a list of the
-- values, and otherwise return 'Nothing'.
recordAListAsTuple :: [(String, e)] -> Maybe [e]
recordAListAsTuple alist =
  alistAllFields (map show [1 .. length alist]) alist

-- | Convert a tuple of expression to an association list used in a 'RecordType'
-- or 'RecordValue' to denote a tuple
tupleAsRecordAList :: [e] -> [(String, e)]
tupleAsRecordAList es = zip (map (show :: Integer -> String) [1 ..]) es

-- | Zip a binary function @f@ over a pair of 'FlatTermF's by applying @f@
-- pointwise to immediate subterms, if the two 'FlatTermF's are the same
-- constructor; otherwise, return 'Nothing' if they use different constructors
zipWithFlatTermF :: (x -> y -> z) -> FlatTermF x -> FlatTermF y ->
                    Maybe (FlatTermF z)
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

    go (CtorApp cx psx lx) (CtorApp cy psy ly)
      | cx == cy = Just $ CtorApp cx (zipWith f psx psy) (zipWith f lx ly)
    go (DataTypeApp dx psx lx) (DataTypeApp dy psy ly)
      | dx == dy = Just $ DataTypeApp dx (zipWith f psx psy) (zipWith f lx ly)
    go (RecursorApp d1 ps1 p1 cs_fs1 ixs1 x1) (RecursorApp d2 ps2 p2 cs_fs2 ixs2 x2)
      | d1 == d2
      , Just fs2 <- alistAllFields (map fst cs_fs1) cs_fs2
      = Just $
        RecursorApp d1 (zipWith f ps1 ps2) (f p1 p2)
        (zipWith (\(c,f1) f2 -> (c, f f1 f2)) cs_fs1 fs2)
        (zipWith f ixs1 ixs2) (f x1 x2)

    go (RecordType elems1) (RecordType elems2)
      | Just vals2 <- alistAllFields (map fst elems1) elems2 =
        Just $ RecordType $ zipWith (\(fld,x) y -> (fld, f x y)) elems1 vals2
    go (RecordValue elems1) (RecordValue elems2)
      | Just vals2 <- alistAllFields (map fst elems1) elems2 =
        Just $ RecordValue $ zipWith (\(fld,x) y -> (fld, f x y)) elems1 vals2
    go (RecordProj e1 fld1) (RecordProj e2 fld2)
      | fld1 == fld2 = Just $ RecordProj (f e1 e2) fld1

    go (Sort sx) (Sort sy) | sx == sy = Just (Sort sx)
    go (NatLit i) (NatLit j) | i == j = Just (NatLit i)
    go (FloatLit fx) (FloatLit fy)
      | fx == fy = Just $ FloatLit fx
    go (DoubleLit fx) (DoubleLit fy)
      | fx == fy = Just $ DoubleLit fx
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
    | Lambda !String !e !e
      -- ^ Function abstractions
    | Pi !String !e !e
      -- ^ The type of a (possibly) dependent function
    | LocalVar !DeBruijnIndex
      -- ^ Local variables are referenced by deBruijn index.
    | Constant String !e !e
      -- ^ An abstract constant packaged with its definition and type.
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
    termf (Constant x1 t1 _) (Constant x2 t2 _) = x1 == x2 && term t1 t2
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
      Constant d _ _            -> Net.Atom d
      App t1 t2                 -> Net.App (termToPat t1) (termToPat t2)
      FTermF (GlobalDef d)      -> Net.Atom (identName d)
      FTermF (Sort s)           -> Net.Atom ('*' : show s)
      FTermF (NatLit _)         -> Net.Var --Net.Atom (show n)
      FTermF (DataTypeApp c ps ts) ->
        foldl Net.App (Net.Atom (identName c)) (map termToPat (ps ++ ts))
      FTermF (CtorApp c ps ts)   ->
        foldl Net.App (Net.Atom (identName c)) (map termToPat (ps ++ ts))
      _                         -> Net.Var

unwrapTermF :: Term -> TermF Term
unwrapTermF STApp{stAppTermF = tf} = tf
unwrapTermF (Unshared tf) = tf


-- Free de Bruijn Variables ----------------------------------------------------

-- | A @BitSet@ represents a set of natural numbers.
-- Bit n is a 1 iff n is in the set.
type BitSet = Integer

bitwiseOrOf :: (Bits a, Num a) => Fold s a -> s -> a
bitwiseOrOf fld = foldlOf' fld (.|.) 0

-- | Compute the free variables of a term given free variables for its immediate
-- subterms
freesTermF :: TermF BitSet -> BitSet
freesTermF tf =
    case tf of
      FTermF ftf -> bitwiseOrOf folded ftf
      App l r -> l .|. r
      Lambda _name tp rhs -> tp .|. rhs `shiftR` 1
      Pi _name lhs rhs -> lhs .|. rhs `shiftR` 1
      LocalVar i -> bit i
      Constant _ _ _ -> 0 -- assume rhs is a closed term

-- | Return a bitset containing indices of all free local variables
looseVars :: Term -> BitSet
looseVars STApp{ stAppFreeVars = x } = x
looseVars (Unshared f) = freesTermF (fmap looseVars f)

-- | Compute the value of the smallest variable in the term, if any.
smallestFreeVar :: Term -> Maybe Int
smallestFreeVar t
   | fv == 0 = Nothing
   | fv > 0  = Just $! go 0 fv
   | otherwise = error "impossible: negative free variable bitset!"
 where fv = looseVars t
       go :: Int -> Integer -> Int
       go !shft !x
          | xw == 0   = go (shft+64) (shiftR x 64)
          | otherwise = shft + countTrailingZeros xw
        where xw :: Word64
              xw = fromInteger x


-- Terms In Context ------------------------------------------------------------

-- | We use DataKinds to represent contexts at the type level. These are
-- basically natural numbers, but we redefine them here in the usual inductive
-- presentation, both because that is how we are using them and also to keep it
-- clear that these are different from the usual type-level nats.
--
-- Note that contexts are "inside-out", meaning that the most recently-bound
-- variable is listed on the outside. We reflect this by having that most
-- recently-bound variable to the right in 'CCons'.
data Ctx a = CNil | CCons (Ctx a) a

-- | Append two lists of types
type family as :++: bs where
  '[] :++: bs = bs
  (a ': as) :++: bs = a ': as :++: bs

-- | Append a list of types to a context, i.e., bind the types in the list
-- inside the context
type family CtxBind ctx as where
  CtxBind ctx '[] = ctx
  CtxBind ctx (a ': as) = CtxBind ('CCons ctx a) as

type family CtxApp ctx1 ctx2 where
  CtxApp ctx1 'CNil = ctx1
  CtxApp ctx1 ('CCons ctx2 a) = 'CCons (CtxApp ctx1 ctx2) a

-- | Abstract a type list using Haskell arrows. This is done "outside-in", since
-- type-level lists represent bindings from the outside in.
type family Arrows as b where
  Arrows '[] b = b
  Arrows (a ': as) b = a -> Arrows as b

-- | Proof that one context is an extension of another
data CtxExtends ctx1 ctx2 where
  CtxExtendsRefl :: CtxExtends ctx ctx
  CtxExtendsCons :: CtxExtends ctx1 ctx2 -> CtxExtends ctx1 ('CCons ctx2 a)

-- | A dummy type of types
data Typ

-- | A 'Term' with a given "type" relative to a given context. Since we cannot
-- hope to represent dependent type theory in Haskell types anyway, these
-- "types" are usually instantiated with a dummy, such as the unit type, but the
-- code that consumes them cannot know that and has to be agnostic to what type
-- it is.
newtype CtxTerm ctx a = CtxTerm Term

-- | Build a term in the empty context
mkClosedTerm :: Term -> CtxTerm 'CNil a
mkClosedTerm = CtxTerm

-- | Take a term out of the empty context
elimClosedTerm :: CtxTerm 'CNil a -> Term
elimClosedTerm (CtxTerm t) = t

-- | A pair of things in a given context
data CtxPair f1 f2 ctx ab where
  CtxPair :: f1 ctx a -> f2 ctx b -> CtxPair f1 f2 ctx (a,b)

-- | A list of terms in a given context
data CtxTerms ctx as where
  CtxTermsNil :: CtxTerms ctx '[]
  CtxTermsCons :: CtxTerm ctx a -> CtxTerms ctx as -> CtxTerms ctx (a ': as)

-- | A list of terms in a given context, stored "inside-out"
{-
data CtxTermsCtx ctx term_ctx where
  CtxTermsCtxNil :: CtxTerms ctx 'CNil
  CtxTermsCtxCons :: CtxTermsCtx ctx term_ctx -> CtxTerm ctx a ->
                     CtxTermsCtx ctx ('CCons as a)
-}

-- | A sequence of bindings of pairs of a variable name and a type of some form
-- for that variable. These bindings are relative to ambient context @ctx@, use
-- @tp@ for the variable types, and bind variables whose types are listed in
-- @as@.
data Bindings (tp :: Ctx * -> * -> *) (ctx :: Ctx *) (as :: [*]) where
  NoBind :: Bindings tp ctx '[]
  Bind :: String -> tp ctx a -> Bindings tp ('CCons ctx a) as ->
          Bindings tp ctx (a ': as)

-- | An inverted list of bindings, seen from the "inside out"
data InvBindings (tp :: Ctx * -> * -> *) (ctx :: Ctx *) (as :: Ctx *) where
  InvNoBind :: InvBindings tp ctx 'CNil
  InvBind :: InvBindings tp ctx as -> String -> tp (CtxApp ctx as) a ->
             InvBindings tp ctx ('CCons as a)


invAppendBindings :: InvBindings tp ctx as ->
                     Bindings tp (CtxApp ctx as) bs ->
                     InvBindings tp ctx (CtxBind as bs)
invAppendBindings as NoBind = as
invAppendBindings as (Bind y y_tp bs) =
  (invAppendBindings (InvBind as y y_tp) bs)

invertBindings :: Bindings tp ctx as -> InvBindings tp ctx (CtxBind 'CNil as)
invertBindings = invAppendBindings InvNoBind

-- | Take a list of terms and match them up with a sequence of bindings,
-- returning a structured 'CtxTermsCtx' list. Note that the bindings themselves
-- can be in an arbitrary context, but the terms passed in are assumed to be
-- closed, i.e., in the empty context.
ctxTermsForBindings :: Bindings tp ctx as -> [Term] ->
                       Maybe (CtxTerms 'CNil as)
ctxTermsForBindings NoBind [] = Just CtxTermsNil
ctxTermsForBindings (Bind _ _ bs) (t : ts) =
  CtxTermsCons (mkClosedTerm t) <$> ctxTermsForBindings bs ts
ctxTermsForBindings _ _ = Nothing

{-
ctxTermsForBindings bs_top ts_top = helper bs_top (reverse ts_top)
  where
    helper :: Bindings tp ctx as -> [Term] -> Maybe (CtxTerms 'CNil as)
    helper NoBind [] = Just CtxTermsNil
    helper (Bind bs _ _) (t : ts) =
      CtxTermsCons <$> helper bs ts <*> Just (mkClosedTerm t)
    helper _ _ = Nothing
-}

-- | Prepend a single binding to a sequence of bindings
{-
prependBinding :: String -> tp ctx a -> Bindings tp ctx as ->
                  Bindings tp ctx ('CCons as a)
prependBinding NoBind x tp = Bind x tp NoBind
prependBinding (Bind bs y y_tp) x tp = Bind (prependBinding bs x tp) y y_tp
-}

-- | Append two sequences of 'Bindings'
{-
appendBindings :: Bindings tp ctx as ->
                  Bindings tp (CtxApp ctx as) bs ->
                  Bindings tp ctx (CtxApp as bs)
appendBindings as NoBind = as
appendBindings as (Bind bs y y_tp) = Bind (appendBindings as bs) y y_tp
-}

-- | A sequence of bindings bundled with something that is relative to those
-- bindings
data InBindings tp (f :: Ctx * -> k -> *) ctx (a::k) where
  InBindings :: Bindings tp ctx as -> f (CtxBind ctx as) a ->
                InBindings tp f ctx a
