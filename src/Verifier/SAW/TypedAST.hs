{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
module Verifier.SAW.TypedAST
 ( -- * Module operations.
   Module
 , emptyModule
 , ModuleName, mkModuleName
 , moduleName
 , preludeName
 , ModuleDecl(..)
 , moduleDecls
 , TypedDataType
 , moduleDataTypes
 , findDataType
 , TypedCtor
 , moduleCtors
 , findCtor
 , TypedDef
 , TypedDefEqn
 , moduleDefs
 , allModuleDefs
 , findDef
 , insImport
 , insDataType
 , insDef
   -- * Data types and defintiions.
 , DataType(..)
 , Ctor(..)
 , GenericDef(..)
 , Def
 , LocalDef
 , localVarNames
 , DefEqn(..)
 , Pat(..)
 , patBoundVarCount
 , patUnusedVarCount
   -- * Terms and associated operations.
 , Term(..)
 , incVars
 , piArgCount
 , TermF(..)
 , FlatTermF(..)
 , Termlike(..)
 , zipWithFlatTermF
 , freesTerm
 , freesTermF

 , LocalVarDoc
 , emptyLocalVarDoc
 , docShowLocalNames
 , docShowLocalTypes

 , TermPrinter
 
 , Prec(..)
 , ppAppParens
 , ppTerm
 , ppTermF
 , ppTermF'
 , ppFlatTermF
 , ppRecordF
   -- * Primitive types.
 , Sort, mkSort, sortOf, maxSort
 , Ident(identModule, identName), mkIdent
 , parseIdent
 , isIdent
 , ppIdent
 , ppDefEqn
 , DeBruijnIndex
 , FieldName
 , instantiateVarList
 , ExtCns(..)
 , VarIndex
   -- * Utility functions
 , BitSet
 , commaSepList
 , semiTermList
 , ppParens
 ) where

import Control.Applicative hiding (empty)
import Control.Exception (assert)
import Control.Lens
import Control.Monad.Identity (runIdentity)
import Data.Bits
import qualified Data.ByteString.UTF8 as BS
import Data.Char
import Data.Foldable (Foldable, foldl', sum, all)
import Data.Hashable
import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Word
import GHC.Generics (Generic)
import GHC.Exts (IsString(..))
import Text.PrettyPrint.Leijen hiding ((<$>))

import Prelude hiding (all, foldr, sum)

import Verifier.SAW.Utils (internalError, sumBy)


instance (Hashable k, Hashable a) => Hashable (Map k a) where
    hashWithSalt x m = hashWithSalt x (Map.assocs m)

instance Hashable a => Hashable (Vector a) where
    hashWithSalt x v = hashWithSalt x (V.toList v)

doublecolon :: Doc
doublecolon = colon <> colon

-- | Print a list of items separated by semicolons
semiTermList :: [Doc] -> Doc
semiTermList = hsep . fmap (<> semi)

commaSepList :: [Doc] -> Doc
commaSepList [] = empty
commaSepList [d] = d
commaSepList (d:l) = d <> comma <+> commaSepList l

-- | Add parenthesis around a document if condition is true.
ppParens :: Bool -> Doc -> Doc
ppParens b = if b then parens else id

newtype ModuleName = ModuleName BS.ByteString -- [String]
  deriving (Eq, Ord, Generic)

instance Hashable ModuleName -- automatically derived

instance Show ModuleName where
  show (ModuleName s) = BS.toString s

-- | Crete a module name given a list of strings with the top-most
-- module name given first.
mkModuleName :: [String] -> ModuleName
mkModuleName [] = error "internal: mkModuleName given empty module name"
mkModuleName nms = assert (all isCtor nms) $ ModuleName (BS.fromString s)
  where s = intercalate "." (reverse nms)

isIdent :: String -> Bool
isIdent (c:l) = isAlpha c && all isIdChar l
isIdent [] = False

isCtor :: String -> Bool
isCtor (c:l) = isUpper c && all isIdChar l
isCtor [] = False

-- | Returns true if character can appear in identifier.
isIdChar :: Char -> Bool
isIdChar c = isAlphaNum c || (c == '_') || (c == '\'')


preludeName :: ModuleName
preludeName = mkModuleName ["Prelude"]

data Ident = Ident { identModule :: ModuleName
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

type DeBruijnIndex = Int

type FieldName = String

-- Patterns are used to match equations.
data Pat e = -- | Variable bound by pattern.
             -- Variables may be bound in context in a different order than
             -- a left-to-right traversal.  The DeBruijnIndex indicates the order.
             PVar String DeBruijnIndex e
             -- | The
           | PUnused DeBruijnIndex e
           | PTuple [Pat e]
           | PRecord (Map FieldName (Pat e))
             -- An arbitrary term that matches anything, but needs to be later
             -- verified to be equivalent.
           | PCtor Ident [Pat e]
  deriving (Eq,Ord, Show, Functor, Foldable, Traversable, Generic)

instance Hashable e => Hashable (Pat e) -- automatically derived

patBoundVarCount :: Pat e -> DeBruijnIndex
patBoundVarCount p =
  case p of
    PVar{} -> 1
    PUnused{} -> 0
    PCtor _ l -> sumBy patBoundVarCount l
    PTuple l  -> sumBy patBoundVarCount l
    PRecord m -> sumBy patBoundVarCount m

patUnusedVarCount :: Pat e -> DeBruijnIndex
patUnusedVarCount p =
  case p of
    PVar{} -> 0
    PUnused{} -> 1
    PCtor _ l -> sumBy patUnusedVarCount l
    PTuple l  -> sumBy patUnusedVarCount l
    PRecord m -> sumBy patUnusedVarCount m

patBoundVars :: Pat e -> [String]
patBoundVars p =
  case p of
    PVar s _ _ -> [s]
    PCtor _ l -> concatMap patBoundVars l
    PTuple l -> concatMap patBoundVars l
    PRecord m -> concatMapOf folded patBoundVars m
    _ -> []

lift2 :: (a -> b) -> (b -> b -> c) -> a -> a -> c
lift2 f h x y = h (f x) (f y)

-- | A Definition contains an identifier, the type of the definition, and a list of equations.
data GenericDef n e =
    Def { defIdent :: n
        , defType :: e
        , defEqs :: [DefEqn e]
        }
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

type Def = GenericDef Ident
type LocalDef = GenericDef String

instance (Hashable n, Hashable e) => Hashable (GenericDef n e) -- automatically derived

localVarNames :: LocalDef e -> [String]
localVarNames (Def nm _ _) = [nm]


data LocalVarDoc = LVD { docModuleName :: Map ModuleName String
                       , _docShowLocalNames :: Bool
                       , _docShowLocalTypes :: Bool
                       , docMap :: !(Map DeBruijnIndex Doc)
                       , docLvl :: !DeBruijnIndex
                       , docUsedMap :: Map String DeBruijnIndex
                       }

-- | Flag indicates doc should use local names (default True)
docShowLocalNames :: Simple Lens LocalVarDoc Bool
docShowLocalNames = lens _docShowLocalNames (\s v -> s { _docShowLocalNames = v })

-- | Flag indicates doc should print type for locals (default false)
docShowLocalTypes :: Simple Lens LocalVarDoc Bool
docShowLocalTypes = lens _docShowLocalTypes (\s v -> s { _docShowLocalTypes = v })

emptyLocalVarDoc :: LocalVarDoc
emptyLocalVarDoc = LVD { docModuleName = Map.empty
                       , _docShowLocalNames = True
                       , _docShowLocalTypes = False
                       , docMap = Map.empty
                       , docLvl = 0
                       , docUsedMap = Map.empty
                       }

consBinding :: LocalVarDoc -> String -> LocalVarDoc
consBinding lvd i = lvd { docMap = Map.insert lvl (text i) m
                        , docLvl = lvl + 1
                        , docUsedMap = Map.insert i lvl (docUsedMap lvd)
                        }
 where lvl = docLvl lvd
       m = case Map.lookup i (docUsedMap lvd) of
             Just pl -> Map.delete pl (docMap lvd)
             Nothing -> docMap lvd

lookupDoc :: LocalVarDoc -> DeBruijnIndex -> Doc
lookupDoc lvd i
    | lvd^.docShowLocalNames =
        case Map.lookup lvl (docMap lvd) of
          Just d -> d
          Nothing -> text ('!' : show (i - docLvl lvd))
    | otherwise = text ('!' : show i)
  where lvl = docLvl lvd - i - 1

data DefEqn e
  = DefEqn [Pat e]  -- ^ List of patterns
           e -- ^ Right hand side.
  deriving (Functor, Foldable, Traversable, Generic, Show)

instance Hashable e => Hashable (DefEqn e) -- automatically derived

instance (Eq e) => Eq (DefEqn e) where
  DefEqn xp xr == DefEqn yp yr = xp == yp && xr == yr

instance (Ord e) => Ord (DefEqn e) where
  compare (DefEqn xp xr) (DefEqn yp yr) = compare (xp,xr) (yp,yr)

data Ctor n tp = Ctor { ctorName :: !n
                        -- | The type of the constructor (should contain no free variables).
                      , ctorType :: tp
                      }
  deriving (Functor, Foldable, Traversable)

instance Eq n => Eq (Ctor n tp) where
  (==) = lift2 ctorName (==)

instance Ord n => Ord (Ctor n tp) where
  compare = lift2 ctorName compare

instance Show n => Show (Ctor n tp) where
  show = show . ctorName

ppCtor :: TermPrinter e -> Ctor Ident e -> Doc
ppCtor f c = ppIdent (ctorName c) <+> doublecolon <+> tp
  where lcls = emptyLocalVarDoc
        tp = f lcls PrecLambda (ctorType c)

data DataType n t = DataType { dtName :: n
                             , dtType :: t
                             , dtCtors :: [Ctor n t]
                             }
  deriving (Functor, Foldable, Traversable)

instance Eq n => Eq (DataType n t) where
  (==) = lift2 dtName (==)

instance Ord n => Ord (DataType n t) where
  compare = lift2 dtName compare

instance Show n => Show (DataType n t) where
  show = show . dtName

ppDataType :: TermPrinter e -> DataType Ident e -> Doc
ppDataType f dt = text "data" <+> tc <+> text "where" <+> lbrace <$$>
                    nest 4 (vcat (ppc <$> dtCtors dt)) <$$>
                    nest 2 rbrace
  where lcls = emptyLocalVarDoc
        sym = ppIdent (dtName dt)
        tc = ppTypeConstraint f lcls sym (dtType dt)
        ppc c = ppCtor f c <> semi

type VarIndex = Word64

data FlatTermF e
  = GlobalDef !Ident  -- ^ Global variables are referenced by label.

    -- Tuples may be 0 or 2+ elements.
    -- A tuple of a single element is not allowed in well-formed expressions.
  | TupleValue [e]
  | TupleType [e]
  | TupleSelector !e !Int

  | RecordValue (Map FieldName e)
  | RecordType (Map FieldName e)
  | RecordSelector e FieldName

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

-- | An external constant with a name.
-- Names are necessarily unique, but the var index should be.
data ExtCns e = EC { ecVarIndex :: !VarIndex
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

instance Hashable e => Hashable (FlatTermF e) -- automatically derived

zipWithFlatTermF :: (x -> y -> z) -> FlatTermF x -> FlatTermF y -> Maybe (FlatTermF z)
zipWithFlatTermF f = go
  where go (GlobalDef x) (GlobalDef y) | x == y = Just $ GlobalDef x

        go (TupleValue lx) (TupleValue ly)
          | length lx == length ly = Just $ TupleValue (zipWith f lx ly)
        go (TupleType lx) (TupleType ly)
          | length lx == length ly = Just $ TupleType (zipWith f lx ly)

        go (RecordValue mx) (RecordValue my)
          | Map.keys mx == Map.keys my =
              Just $ RecordValue $ Map.intersectionWith f mx my
        go (RecordSelector x fx) (RecordSelector y fy)
          | fx == fy = Just $ RecordSelector (f x y) fx
        go (RecordType mx) (RecordType my)
          | Map.keys mx == Map.keys my =
              Just $ RecordType (Map.intersectionWith f mx my)

        go (CtorApp cx lx) (CtorApp cy ly)
          | cx == cy = Just $ CtorApp cx (zipWith f lx ly)
        go (DataTypeApp dx lx) (DataTypeApp dy ly)
          | dx == dy = Just $ DataTypeApp dx (zipWith f lx ly)
        go (Sort sx) (Sort sy) | sx == sy = Just (Sort sx)
        go (NatLit i) (NatLit j) | i == j = Just (NatLit i)
        go (StringLit s) (StringLit t) | s == t = Just (StringLit s)
        go (ArrayValue tx vx) (ArrayValue ty vy)
          | V.length vx == V.length vy = Just $ ArrayValue (f tx ty) (V.zipWith f vx vy)
        go (ExtCns (EC xi xn xt)) (ExtCns (EC yi _ yt))
          | xi == yi = Just (ExtCns (EC xi xn (f xt yt)))

        go _ _ = Nothing

data TermF e
    = FTermF !(FlatTermF e)  -- ^ Global variables are referenced by label.
    | App !e !e
    | Lambda !String !e !e
    | Pi !String !e !e
       -- | List of bindings and the let expression itself.
      -- Let expressions introduce variables for each identifier.
      -- Let definitions are bound in the order they appear, e.g., the first symbol
      -- is referred to by the largest deBruijnIndex within the let, and the last
      -- symbol has index 0 within the let.
    | Let [LocalDef e] !e
      -- | Local variables are referenced by deBruijn index.
      -- The type of the var is in the context of when the variable was bound.
    | LocalVar !DeBruijnIndex
    | Constant !Ident !e  -- ^ An abstract constant packaged with its definition.
  deriving (Eq, Ord, Functor, Foldable, Traversable, Generic)

instance Hashable e => Hashable (TermF e) -- automatically derived.

class Termlike t where
  unwrapTermF :: t -> TermF t

ppIdent :: Ident -> Doc
ppIdent i = text (show i)

ppTypeConstraint :: TermPrinter e -> LocalVarDoc -> Doc -> e -> Doc
ppTypeConstraint f lcls sym tp = sym <+> doublecolon <+> f lcls PrecLambda tp

ppDef :: LocalVarDoc -> Def Term -> Doc
ppDef lcls d = vcat (tpd : (ppDefEqn ppTerm lcls sym <$> defEqs d))
  where sym = ppIdent (defIdent d)
        tpd = ppTypeConstraint ppTerm lcls sym (defType d)

ppLocalDef :: Applicative f 
           => (LocalVarDoc -> Prec -> e -> f Doc)
           -> LocalVarDoc -- ^ Context outside let
           -> LocalVarDoc -- ^ Context inside let
           -> LocalDef e
           -> f Doc
ppLocalDef pp lcls lcls' (Def nm tp eqs) =
    ppd <$> (pptc <$> pp lcls PrecLambda tp)
        <*> traverse (ppDefEqnF pp lcls' sym) eqs
  where sym = text nm
        pptc tpd = sym <+> doublecolon <+> tpd
        ppd tpd eqds = vcat (tpd : eqds)

ppDefEqn :: TermPrinter e -> LocalVarDoc -> Doc -> DefEqn e -> Doc
ppDefEqn pp lcls sym eq = runIdentity (ppDefEqnF pp' lcls sym eq)
  where pp' l' p' e' = pure (pp l' p' e')

ppDefEqnF :: Applicative f
          => (LocalVarDoc -> Prec -> e -> f Doc)
          -> LocalVarDoc -> Doc -> DefEqn e -> f Doc
ppDefEqnF f lcls sym (DefEqn pats rhs) = 
    ppEq <$> traverse ppPat' pats
         <*> f lcls' PrecLambda rhs
  where ppEq pd rhs' = sym <+> hsep pd <+> equals <+> rhs'
        lcls' = foldl' consBinding lcls (concatMap patBoundVars pats)
        ppPat' = ppPat (f lcls') PrecArg

data Prec
  = PrecNone   -- ^ Nonterminal 'Term'
  | PrecLambda -- ^ Nonterminal 'LTerm'
  | PrecApp    -- ^ Nonterminal 'AppTerm'
  | PrecArg    -- ^ Nonterminal 'AppArg'
  deriving (Eq, Ord)

ppAppParens :: Prec -> Doc -> Doc
ppAppParens p d = ppParens (p > PrecApp) d 

ppAppList :: Prec -> Doc -> [Doc] -> Doc
ppAppList _ sym [] = sym
ppAppList p sym l = ppAppParens p $ hsep (sym : l)

ppTuple :: [Doc] -> Doc
ppTuple = parens . commaSepList

ppPat :: Applicative f
      => (Prec -> e -> f Doc)
      -> Prec -> Pat e -> f Doc
ppPat f p pat =
  case pat of
    PVar i _ _ -> pure (text i)
    PUnused{}  -> pure (char '_')
    PCtor c pl -> ppAppList p (ppIdent c) <$> traverse (ppPat f PrecArg) pl
    PTuple pl  -> ppTuple <$> traverse (ppPat f PrecNone) pl
    PRecord m  -> ppRecordF (ppPat f PrecNone) m

type TermPrinter e = LocalVarDoc -> Prec -> e -> Doc

ppRecordF :: Applicative f => (t -> f Doc) -> Map String t -> f Doc
ppRecordF pp m = braces . semiTermList <$> traverse ppFld (Map.toList m)
  where ppFld (fld,v) = eqCat (text fld) <$> pp v
        eqCat x y = x <+> equals <+> y

ppFlatTermF :: Applicative f => (Prec -> t -> f Doc) -> Prec -> FlatTermF t -> f Doc
ppFlatTermF pp prec tf =
  case tf of
    GlobalDef i -> pure $ ppIdent i
    TupleValue l ->                 ppTuple <$> traverse (pp PrecNone) l
    TupleType l  -> (char '#' <>) . ppTuple <$> traverse (pp PrecNone) l
    TupleSelector t i -> ppParens (prec > PrecArg)
                           . (<> (char '.' <> int i)) <$> pp PrecArg t

    RecordValue m      -> ppRecordF (pp PrecNone) m
    RecordType m       -> (char '#' <>) <$> ppRecordF (pp PrecNone) m
    RecordSelector t f -> ppParens (prec > PrecArg)
                          . (<> (char '.' <> text f)) <$> pp PrecArg t

    CtorApp c l      -> ppAppList prec (ppIdent c) <$> traverse (pp PrecArg) l
    DataTypeApp dt l -> ppAppList prec (ppIdent dt) <$> traverse (pp PrecArg) l

    Sort s -> pure $ text (show s)
    NatLit i -> pure $ integer i
    ArrayValue _ vl -> brackets . commaSepList <$> traverse (pp PrecNone) (V.toList vl)
    FloatLit v  -> pure $ text (show v)
    DoubleLit v -> pure $ text (show v)
    StringLit s -> pure $ text (show s)
    ExtCns (EC _ v _) -> pure $ text v

newtype Term = Term (TermF Term)
  deriving (Eq)

instance Termlike Term where
  unwrapTermF (Term tf) = tf

{-
asApp :: Term -> (Term, [Term])
asApp = go []
  where go l (Term (FTermF (App t u))) = go (u:l) t
        go l t = (t,l)
-}

-- | Returns the number of nested pi expressions.
piArgCount :: Term -> Int
piArgCount = go 0
  where go i (Term (Pi _ _ rhs)) = go (i+1) rhs
        go i _ = i

bitwiseOrOf :: (Bits a, Num a) => Fold s a -> s -> a
bitwiseOrOf fld = foldlOf' fld (.|.) 0

-- | A @BitSet@ represents a set of natural numbers.
-- Bit n is a 1 iff n is in the set.
type BitSet = Integer

freesPat :: Pat BitSet -> BitSet
freesPat p0 =
  case p0 of
    PVar  _ i tp -> tp `shiftR` i
    PUnused i tp -> tp `shiftR` i
    PTuple  pl -> bitwiseOrOf folded (freesPat <$> pl)
    PRecord pm -> bitwiseOrOf folded (freesPat <$> pm)
    PCtor _ pl -> bitwiseOrOf folded (freesPat <$> pl)
                  
freesDefEqn :: DefEqn BitSet -> BitSet
freesDefEqn (DefEqn pl rhs) = 
    bitwiseOrOf folded (freesPat <$> pl) .|. rhs `shiftR` pc
  where pc = sum (patBoundVarCount <$> pl) 

freesTermF :: TermF BitSet -> BitSet
freesTermF tf =
    case tf of
      FTermF ftf -> bitwiseOrOf folded ftf
      App l r -> l .|. r
      Lambda _name tp rhs -> tp .|. rhs `shiftR` 1
      Pi _name lhs rhs -> lhs .|. rhs `shiftR` 1
      Let lcls rhs ->
          bitwiseOrOf (folded . folded) lcls' .|. rhs `shiftR` n
        where n = length lcls
              freesLocalDef :: LocalDef BitSet -> [BitSet]
              freesLocalDef (Def _ tp eqs) = 
                tp : fmap ((`shiftR` n) . freesDefEqn) eqs
              lcls' = freesLocalDef <$> lcls
      LocalVar i -> bit i
      Constant _ _ -> 0 -- assume rhs is a closed term

freesTerm :: Term -> BitSet
freesTerm (Term t) = freesTermF (fmap freesTerm t)

-- | @instantiateVars f l t@ substitutes each dangling bound variable
-- @LocalVar j t@ with the term @f i j t@, where @i@ is the number of
-- binders surrounding @LocalVar j t@.
instantiateVars :: (DeBruijnIndex -> DeBruijnIndex -> Term)
                -> DeBruijnIndex -> Term -> Term
instantiateVars f initialLevel = go initialLevel
  where goList :: DeBruijnIndex -> [Term] -> [Term]
        goList _ []  = []
        goList l (e:r) = go l e : goList (l+1) r

        gof l ftf =
          case ftf of
            TupleValue ll -> TupleValue $ go l <$> ll
            TupleType ll  -> TupleType $ go l <$> ll
            RecordValue m -> RecordValue $ go l <$> m
            RecordSelector x fld -> RecordSelector (go l x) fld
            RecordType m      -> RecordType $ go l <$> m
            CtorApp c ll      -> CtorApp c (goList l ll)
            DataTypeApp dt ll -> DataTypeApp dt (goList l ll)
            _ -> ftf
        go :: DeBruijnIndex -> Term -> Term
        go l (Term tf) =
          case tf of
            FTermF ftf ->  Term $ FTermF $ gof l ftf
            App x y         -> Term $ App (go l x) (go l y)
            Constant _ _rhs -> Term tf -- assume rhs is a closed term, so leave it unchanged
            Lambda i tp rhs -> Term $ Lambda i (go l tp) (go (l+1) rhs)
            Pi i lhs rhs    -> Term $ Pi i (go l lhs) (go (l+1) rhs)
            Let defs r      -> Term $ Let (procDef <$> defs) (go l' r)
              where l' = l + length defs
                    procDef (Def sym tp eqs) = Def sym tp' eqs'
                      where tp' = go l tp
                            eqs' = procEq <$> eqs
                    procEq (DefEqn pats rhs) = DefEqn pats (go eql rhs)
                      where eql = l' + sum (patBoundVarCount <$> pats)
            LocalVar i
              | i < l -> Term $ LocalVar i
              | otherwise -> f l i

-- | @incVars j k t@ increments free variables at least @j@ by @k@.
-- e.g., incVars 1 2 (C ?0 ?1) = C ?0 ?3
incVars :: DeBruijnIndex -> DeBruijnIndex -> Term -> Term
incVars _ 0 = id
incVars initialLevel j = assert (j > 0) $ instantiateVars fn initialLevel
  where fn _ i = Term $ LocalVar (i+j)

-- | Substitute @ts@ for variables @[k .. k + length ts - 1]@ and
-- decrement all higher loose variables by @length ts@.
instantiateVarList :: DeBruijnIndex -> [Term] -> Term -> Term
instantiateVarList _ [] = id
instantiateVarList k ts = instantiateVars fn 0
  where
    l = length ts
    -- Use terms to memoize instantiated versions of ts.
    terms = [ [ incVars 0 i t | i <- [0..] ] | t <- ts ]
    -- Instantiate variables [k .. k+l-1].
    fn i j | j >= i + k + l = Term $ LocalVar (j - l)
           | j >= i + k     = (terms !! (j - i - k)) !! i
           | otherwise      = Term $ LocalVar j
-- ^ Specification in terms of @instantiateVar@ (by example):
-- @instantiateVarList 0 [x,y,z] t@ is the beta-reduced form of @Lam
-- (Lam (Lam t)) `App` z `App` y `App` x@, i.e. @instantiateVarList 0
-- [x,y,z] t == instantiateVar 0 x (instantiateVar 1 (incVars 0 1 y)
-- (instantiateVar 2 (incVars 0 2 z) t))@.

{-
-- | Substitute @t@ for variable 0 in @s@ and decrement all remaining
-- variables.
betaReduce :: Term -> Term -> Term
betaReduce s t = instantiateVar 0 t s
-}

-- | Pretty print a term with the given outer precedence.
ppTerm :: TermPrinter Term
ppTerm lcls p0 (Term t) = ppTermF ppTerm lcls p0 t

ppTermF :: TermPrinter t
        -> TermPrinter (TermF t)
ppTermF pp lcls p tf = runIdentity (ppTermF' pp' lcls p tf)
  where pp' l' p' t' = pure (pp l' p' t')

ppTermF' :: Applicative f
         => (LocalVarDoc -> Prec -> e -> f Doc)
         -> LocalVarDoc
         -> Prec
         -> TermF e
         -> f Doc
ppTermF' pp lcls p (FTermF tf) = ppFlatTermF (pp lcls) p tf
ppTermF' pp lcls p (App l r) =
    ppAppParens p <$> liftA2 (<+>) (pp lcls PrecApp l) (pp lcls PrecArg r)
ppTermF' pp lcls p (Lambda name tp rhs) =
    ppLam
      <$> pp lcls  PrecLambda tp
      <*> pp lcls' PrecLambda rhs
  where ppLam tp' rhs' =
          ppParens (p > PrecLambda) $
            text "\\" <> parens (text name <> doublecolon <> tp')
               <+> text "->"
               <+> rhs'
        lcls' = consBinding lcls name

ppTermF' pp lcls p (Pi i tp rhs) = ppPi <$> lhs <*> pp lcls' PrecLambda rhs
  where ppPi lhs' rhs' = ppParens (p > PrecLambda) $ lhs' <+> text "->" <+> rhs'
        lhs | i == "_" = pp lcls PrecApp tp
            | otherwise = (\tp' -> parens (text i <> doublecolon <> tp'))
                            <$> pp lcls PrecLambda tp
        lcls' = consBinding lcls i

ppTermF' pp lcls p (Let dl u) = 
    ppLet <$> traverse (ppLocalDef pp lcls lcls') dl
          <*> pp lcls' PrecNone u
  where ppLet dl' u' = 
          ppParens (p > PrecNone) $
            text "let" <+> vcat dl' <$$>
            text " in" <+> u'
        nms = concatMap localVarNames dl
        lcls' = foldl' consBinding lcls nms
ppTermF' _pp lcls _p (LocalVar i)
--    | lcls^.docShowLocalTypes = pptc <$> pp lcls PrecLambda tp
    | otherwise = pure d
  where d = lookupDoc lcls i
--        pptc tpd = ppParens (p > PrecNone)
--                            (d <> doublecolon <> tpd)
ppTermF' _ _ _ (Constant i _) = pure $ ppIdent i

instance Show Term where
  showsPrec _ t = shows $ ppTerm emptyLocalVarDoc PrecNone t

type TypedDataType = DataType Ident Term
type TypedCtor = Ctor Ident Term
type TypedDef = Def Term
type TypedDefEqn = DefEqn Term

data ModuleDecl = TypeDecl TypedDataType
                | DefDecl TypedDef

data Module = Module {
          moduleName    :: !ModuleName
        , _moduleImports :: !(Map ModuleName Module)
        , moduleTypeMap :: !(Map String TypedDataType)
        , moduleCtorMap :: !(Map String TypedCtor)
        , moduleDefMap  :: !(Map String TypedDef)
        , moduleRDecls   :: [ModuleDecl] -- ^ All declarations in reverse order they were added.
        }

moduleImports :: Simple Lens Module (Map ModuleName Module)
moduleImports = lens _moduleImports (\m v -> m { _moduleImports = v })

instance Show Module where
  show m = show $ vcat $ fmap ppImport (Map.keys (m^.moduleImports))
                        ++ fmap ppdecl   (moduleDecls m)
    where ppImport nm = text $ "import " ++ show nm 
          ppdecl (TypeDecl d) = ppDataType ppTerm d
          ppdecl (DefDecl d) = ppDef emptyLocalVarDoc d <> char '\n'

emptyModule :: ModuleName -> Module
emptyModule nm =
  Module { moduleName = nm
         , _moduleImports = Map.empty
         , moduleTypeMap = Map.empty
         , moduleCtorMap = Map.empty
         , moduleDefMap  = Map.empty
         , moduleRDecls = []
         }

findDataType :: Module -> Ident -> Maybe TypedDataType
findDataType m i = do
  m' <- findDeclaringModule m (identModule i)
  Map.lookup (identName i) (moduleTypeMap m')

-- | @insImport i m@ returns module obtained by importing @i@ into @m@.
insImport :: Module -> Module -> Module
insImport i = moduleImports . at (moduleName i) ?~ i

insDataType :: Module -> TypedDataType -> Module
insDataType m dt 
    | identModule (dtName dt) == moduleName m =
        m { moduleTypeMap = Map.insert (identName (dtName dt)) dt (moduleTypeMap m)
          , moduleCtorMap = foldl' insCtor (moduleCtorMap m) (dtCtors dt)
          , moduleRDecls = TypeDecl dt : moduleRDecls m
          }
    | otherwise = internalError "insDataType given datatype from another module."
  where insCtor m' c = Map.insert (identName (ctorName c)) c m' 

-- | Data types defined in module.
moduleDataTypes :: Module -> [TypedDataType]
moduleDataTypes = Map.elems . moduleTypeMap

-- | Ctors defined in module.
moduleCtors :: Module -> [TypedCtor]
moduleCtors = Map.elems . moduleCtorMap

findDeclaringModule :: Module -> ModuleName -> Maybe Module
findDeclaringModule m nm
  | moduleName m == nm = Just m
  | otherwise = m^.moduleImports^.at nm

findCtor :: Module -> Ident -> Maybe TypedCtor
findCtor m i = do
  m' <- findDeclaringModule m (identModule i)
  Map.lookup (identName i) (moduleCtorMap m')

moduleDefs :: Module -> [TypedDef]
moduleDefs = Map.elems . moduleDefMap

allModuleDefs :: Module -> [TypedDef]
allModuleDefs m = concatMap moduleDefs (m : Map.elems (m^.moduleImports))

findDef :: Module -> Ident -> Maybe TypedDef
findDef m i = do
  m' <- findDeclaringModule m (identModule i)
  Map.lookup (identName i) (moduleDefMap m')

insDef :: Module -> Def Term -> Module
insDef m d 
  | identModule (defIdent d) == moduleName m =
      m { moduleDefMap = Map.insert (identName (defIdent d)) d (moduleDefMap m)
        , moduleRDecls = DefDecl d : moduleRDecls m
        }
  | otherwise = internalError "insDef given def from another module."

moduleDecls :: Module -> [ModuleDecl]
moduleDecls = reverse . moduleRDecls
