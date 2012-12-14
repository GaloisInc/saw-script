{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
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
 , ModuleDecl(..)
 , moduleDecls
 , findDataType
 , findCtor
 , findDef
 , insDataType
 , insDef
   -- * Data types and defintiions.
 , DataType(..)
 , Ctor(..)
 , CtorType(..)
 , Def(..)
 , LocalDef(..)
 , localVarNames
 , DefEqn(..)
 , Pat(..)
 , patBoundVarCount
   -- * Terms and associated operations.
 , Term(..)
 , incVars
 , TermF(..)
   -- * Primitive types.
 , Sort, mkSort, sortOf
 , Ident(identModule, identName), mkIdent
 , isIdent
 , DeBruijnIndex
 , FieldName
 , instantiateVarList
 ) where

import Control.Applicative ((<$>))
import Control.Exception (assert)
import Data.Char
import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable (Traversable)
import Data.Vector (Vector)
import qualified Data.Vector as V
import Text.PrettyPrint.HughesPJ

import Prelude hiding (all, concatMap, foldr, sum)

import Verifier.SAW.Utils

data ModuleName = ModuleName [String]
  deriving (Eq, Ord)

instance Show ModuleName where
   show (ModuleName s) = intercalate "." (reverse s)

isIdent :: String -> Bool
isIdent (c:l) = isAlpha c && all isIdChar l
isIdent [] = False

isCtor :: String -> Bool
isCtor (c:l) = isUpper c && all isIdChar l
isCtor [] = False

-- | Returns true if character can appear in identifier.
isIdChar :: Char -> Bool
isIdChar c = isAlphaNum c || (c == '_') || (c == '\'')

-- | Crete a module name given a list of strings with the top-most
-- module name given first.
mkModuleName :: [String] -> ModuleName
mkModuleName [] = error "internal: Unexpected empty module name"
mkModuleName nms = assert (all isCtor nms) $ ModuleName nms

data Ident = Ident { identModule :: ModuleName
                   , identName :: String
                   }
  deriving (Eq, Ord)

instance Show Ident where
  show (Ident m s) = shows m ('.' : s)

mkIdent :: ModuleName -> String -> Ident
mkIdent = Ident


newtype Sort = SortCtor { _sortIndex :: Integer }
  deriving (Eq, Ord)

instance Show Sort where
  showsPrec p (SortCtor i) = showParen (p >= 10) (showString "sort " . shows i)

-- | Create sort for given integer.
mkSort :: Integer -> Sort
mkSort i | 0 <= i = SortCtor i
         | otherwise = error "Negative index given to sort."

-- | Returns sort of the given sort.
sortOf :: Sort -> Sort
sortOf (SortCtor i) = SortCtor (i + 1)

type DeBruijnIndex = Int

type FieldName = String

-- Patterns are used to match equations.
data Pat e = -- | Variable bound by pattern.
             -- Variables may be bound in context in a different order than
             -- a left-to-right traversal.  The DeBruijnIndex indicates the order.
             PVar String DeBruijnIndex e
           | PUnused
           | PTuple [Pat e]
           | PRecord (Map FieldName (Pat e))
             -- An arbitrary term that matches anything, but needs to be later
             -- verified to be equivalent.
           | PCtor (Ctor Ident (Pat Term) Term) [Pat e]
--           | PIntLit Integer
  deriving (Eq,Ord, Show, Functor, Foldable, Traversable)

patBoundVarCount :: Pat e -> DeBruijnIndex
patBoundVarCount p =
  case p of
    PVar{} -> 1
    PCtor _ l -> sumBy patBoundVarCount l
    PTuple l  -> sumBy patBoundVarCount l
    PRecord m -> sumBy patBoundVarCount m
    _ -> 0

patBoundVars :: Pat e -> [String]
patBoundVars p =
  case p of
    PVar s _ _ -> [s]
    PCtor _ l -> concatMap patBoundVars l
    PTuple l -> concatMap patBoundVars l
    PRecord m -> concatMap patBoundVars m
    _ -> []

lift2 :: (a -> b) -> (b -> b -> c) -> a -> a -> c
lift2 f h x y = h (f x) (f y) 

data LocalDef n p e
   = LocalFnDef n e [DefEqn p e]
  deriving (Eq, Ord, Show)
  

localVarNames :: LocalDef n p e -> [n]
localVarNames (LocalFnDef nm _ _) = [nm]

-- A Definition contains an identifier, the type of the definition, and a list of equations.
data Def e = Def { defIdent :: Ident
                 , defType :: e
                 , defEqs :: [DefEqn (Pat e) e]
                 }

instance Eq (Def e) where
  (==) = lift2 defIdent (==)

instance Ord (Def e) where
  compare = lift2 defIdent compare  

instance Show (Def e) where
  show = show . defIdent

data DefEqn p e
  = DefEqn [p]  -- ^ List of patterns
           e -- ^ Right hand side.
  deriving (Functor, Foldable, Traversable)

instance (Eq e, Eq p) => Eq (DefEqn p e) where
  DefEqn xp xr == DefEqn yp yr = xp == yp && xr == yr

instance (Ord e, Ord p) => Ord (DefEqn p e) where
  compare (DefEqn xp xr) (DefEqn yp yr) = compare (xp,xr) (yp,yr)

instance (Show e, Show p) => Show (DefEqn p e) where
  showsPrec p t = showParen (p >= 10) $ ("DefEqn "++) . showsPrec 10 p . showsPrec 10 t

data Ctor n p e = Ctor { ctorName :: !n
                         -- | The type of the constructor (should contain no free variables).
                       , ctorType :: CtorType p e
                       }

instance Eq n => Eq (Ctor n p e) where
  (==) = lift2 ctorName (==)

instance Ord n => Ord (Ctor n p e) where
  compare = lift2 ctorName compare

instance Show n => Show (Ctor n p e) where
  show = show . ctorName

data CtorType p e
  = CtorResult e
  | CtorArg p e (CtorType p e)
  deriving (Show)
  

ppCtorType :: TermPrinter e -> TermPrinter (CtorType (Pat e) e)
ppCtorType ppe = go
  where go lcls p (CtorResult tp) = ppe lcls p tp
        go lcls p (CtorArg pat tp rhs) =
          ppPi ppe go lcls p (pat,tp,rhs)

ppCtor :: TermPrinter e -> Ctor Ident (Pat e) e -> Doc
ppCtor f c = ppIdent (ctorName c) <+> doublecolon <+> tp
  where lcls = emptyLocalVarDoc
        tp = ppCtorType f lcls 1 (ctorType c)

data DataType n p t = DataType { dtName :: n
                               , dtType :: t
                               , dtCtors :: [Ctor n p t]
                               }

instance Eq n => Eq (DataType n p t) where
  (==) = lift2 dtName (==)

instance Ord n => Ord (DataType n p t) where
  compare = lift2 dtName compare

instance Show n => Show (DataType n p t) where
  show = show . dtName

ppDataType :: TermPrinter e -> DataType Ident (Pat e) e -> Doc
ppDataType f dt = text "data" <+> tc <+> text "where" <+> lbrace $$
                    nest 4 (vcat (ppc <$> dtCtors dt)) $$
                    nest 2 rbrace
  where lcls = emptyLocalVarDoc
        sym = ppIdent (dtName dt)
        tc = ppTypeConstraint f lcls sym (dtType dt)
        ppc c = ppCtor f c <> semi

data TermF e
    -- ^ Local variables are referenced by deBrujin index.
    -- The type of the var is in the context of when the variable was bound.
  = LocalVar !DeBruijnIndex !e
  | GlobalDef (Def e)  -- ^ Global variables are referenced by label.

  | Lambda !(Pat e) !e !e
  | App !e !e
  | Pi !(Pat e) !e !e

    -- Tuples may be 0 or 2+ elements. 
    -- A tuple of a single element is not allowed in well-formed expressions.
  | TupleValue [e]
  | TupleType [e]

  | RecordValue (Map FieldName e)
  | RecordSelector e FieldName
  | RecordType (Map FieldName e)

  | CtorValue !(Ctor Ident (Pat e) Term) [e]
  | CtorType !(DataType Ident (Pat e) Term) [e]

  | Sort Sort

    -- ^ List of bindings and the let expression itself.
    -- Let expressions introduce variables for each identifier.
  | Let [LocalDef String (Pat e) e] e

    -- Primitive builtin values
  | IntLit Integer
    -- | Array value includes type of elements followed by elements.
  | ArrayValue e (Vector e)
    -- | @EqType x y@ is a type representing the equality proposition @x = y@
  | EqType e e
    -- | @Oracle s t@ represents a proof of proposition @t@ (typically
    -- of the form @EqType x y@, but possibly with extra @Pi@
    -- quantifiers), which came from the trusted proof tool @s@.
  | Oracle String e
 deriving (Eq, Ord, Functor, Foldable, Traversable)

ppIdent :: Ident -> Doc
ppIdent i = text (show i)

doublecolon :: Doc
doublecolon = colon <> colon

ppTypeConstraint :: TermPrinter e -> LocalVarDoc -> Doc -> e -> Doc
ppTypeConstraint f lcls sym tp = sym <+> doublecolon <+> f lcls 1 tp

ppDef :: LocalVarDoc -> Def Term -> Doc
ppDef lcls d = vcat (tpd : (ppDefEqn ppTerm lcls sym <$> defEqs d))
  where sym = ppIdent (defIdent d)
        tpd = ppTypeConstraint ppTerm lcls sym (defType d)

ppLocalDef :: TermPrinter e -> LocalVarDoc -> LocalDef String (Pat e) e -> Doc
ppLocalDef f lcls (LocalFnDef nm tp eqs) = tpd $$ vcat (ppDefEqn f lcls sym <$> eqs)
  where sym = text nm
        tpd = sym <+> doublecolon <+> f lcls 1 tp

ppDefEqn :: TermPrinter e -> LocalVarDoc -> Doc -> DefEqn (Pat e) e -> Doc
ppDefEqn f lcls sym (DefEqn pats rhs) = lhs <+> equals <+> f lcls' 1 rhs
  where lcls' = foldl' consBinding lcls (concatMap patBoundVars pats) 
        lhs = sym <+> hsep (ppPat f lcls' 10 <$> pats)

-- | Print a list of items separated by semicolons
semiTermList :: [Doc] -> Doc
semiTermList = hsep . fmap (<> semi)

type Prec = Int

ppPat :: TermPrinter e -> TermPrinter (Pat e)
ppPat f lcls p pat = 
  case pat of
    PVar i _ _ -> text i
    PUnused{} -> char '_'
    PCtor c pl -> sp 10 $ ppIdent (ctorName c) <+> hsep (ppPat f lcls 10 <$> pl)
    PTuple pl -> parens $ commaSepList $ ppPat f lcls 1 <$> pl
    PRecord m -> 
      let ppFld (fld,v) = text fld <+> equals <+> ppPat f lcls 1 v
       in braces $ semiTermList $ ppFld <$> Map.toList m
--    PIntLit i -> integer i
 where sp l d = if p >= l then parens d else d

commaSepList :: [Doc] -> Doc
commaSepList [] = empty
commaSepList [d] = d
commaSepList (d:l) = d <> comma <+> commaSepList l

maybeParens :: Bool -> Doc -> Doc
maybeParens True  d = parens d
maybeParens False d = d

data LocalVarDoc = LVD { docMap :: !(Map DeBruijnIndex Doc)
                       , docLvl :: !DeBruijnIndex
                       , docUsedMap :: Map String DeBruijnIndex
                       }

emptyLocalVarDoc :: LocalVarDoc
emptyLocalVarDoc = LVD { docMap = Map.empty
                       , docLvl = 0
                       , docUsedMap = Map.empty
                       }

consBinding :: LocalVarDoc -> String -> LocalVarDoc
consBinding lvd i = LVD { docMap = Map.insert lvl (text i) m          
                        , docLvl = lvl + 1
                        , docUsedMap = Map.insert i lvl (docUsedMap lvd)
                        }
 where lvl = docLvl lvd
       m = case Map.lookup i (docUsedMap lvd) of
             Just pl -> Map.delete pl (docMap lvd)
             Nothing -> docMap lvd

lookupDoc :: LocalVarDoc -> DeBruijnIndex -> Doc
lookupDoc lvd i =
  let lvl = docLvl lvd - i - 1
   in case Map.lookup lvl (docMap lvd) of
        Just d -> d
        Nothing -> char '!' <> integer (toInteger (i - docLvl lvd))

type TermPrinter e = LocalVarDoc -> Prec -> e -> Doc

ppPi :: TermPrinter e -> TermPrinter r -> TermPrinter (Pat e, e, r)
ppPi ftp frhs lcls p (pat,tp,rhs) = 
    maybeParens (p >= 2) $ lhs <+> text "->" <+> frhs lcls' 1 rhs
  where lcls' = foldl' consBinding lcls (patBoundVars pat)
        lhs = case pat of
                PUnused -> ftp lcls 2 tp
                _ -> parens (ppPat ftp lcls' 1 pat <> doublecolon <> ftp lcls 1 tp)

-- | @ppTermF@ pretty prints term functros.
ppTermF :: TermPrinter e -- ^ Pretty printer for elements.
        -> TermPrinter (TermF e)
ppTermF f lcls p tf = do
  let sp l d = maybeParens (p >= l) d
  case tf of
    LocalVar i _ -> lookupDoc lcls i
    GlobalDef d -> ppIdent $ defIdent d
    Lambda pat tp rhs -> sp 1 $ text "\\" <> lhs <+> text "->" <+> f lcls' 2 rhs
      where lcls' = foldl' consBinding lcls (patBoundVars pat)
            lhs = parens (ppPat f lcls' 1 pat <> doublecolon <> f lcls 1 tp)
    App t u -> sp 10 (f lcls 10 t <+> f lcls 10 u)
    Pi pat tp rhs -> ppPi f f lcls p (pat,tp,rhs)
    TupleValue tl -> parens (commaSepList $ f lcls 1 <$> tl)
    TupleType tl -> char '#' <> parens (commaSepList $ f lcls 1 <$> tl)
    RecordValue m        ->
      let ppFld (fld,v) = text fld <+> equals <+> f lcls 1 v 
       in braces (semiTermList (ppFld <$> Map.toList m))
    RecordSelector t fld -> f lcls 11 t <> text ('.':fld)
    RecordType m         ->
      let ppFld (fld,v) = text fld <> doublecolon <+> f lcls 1 v
       in char '#' <> braces (semiTermList (ppFld <$> Map.toList m))
    CtorValue c tl
      | null tl -> ppIdent (ctorName c)
      | otherwise -> sp 10 $ hsep $ ppIdent (ctorName c) : fmap (f lcls 10) tl
    CtorType dt tl
      | null tl -> ppIdent (dtName dt)
      | otherwise -> sp 10 $ hsep $ ppIdent (dtName dt) : fmap (f lcls 10) tl
    Sort s -> text (show s)
    Let dl t -> text "let" <+> vcat (ppLocalDef f lcls' <$> dl) $$
                text " in" <+> f lcls' 0 t
      where nms = concatMap localVarNames dl
            lcls' = foldl' consBinding lcls nms
    IntLit i -> integer i
    ArrayValue _ vl -> brackets (commaSepList (f lcls 1 <$> V.toList vl))
    EqType lhs rhs -> f lcls 1 lhs <+> equals <+> f lcls 1 rhs
    Oracle s prop -> quotes (text s) <> parens (f lcls 0 prop)

newtype Term = Term (TermF Term)
  deriving (Eq)

asApp :: Term -> (Term, [Term])
asApp = go []
  where go l (Term (App t u)) = go (u:l) t
        go l t = (t,l)

-- | @instantiateVars f l t@ substitutes each dangling bound variable
-- @LocalVar j t@ with the term @f i j t@, where @i@ is the number of
-- binders surrounding @LocalVar j t@.
instantiateVars :: (DeBruijnIndex -> DeBruijnIndex -> Term -> Term)
                -> DeBruijnIndex -> Term -> Term
instantiateVars f initialLevel = go initialLevel 
  where goList :: DeBruijnIndex -> [Term] -> [Term]
        goList _ []  = []
        goList l (e:r) = go l e : goList (l+1) r

        go :: DeBruijnIndex -> Term -> Term
        go l t@(Term tf) =
          case tf of
            LocalVar i tp 
              | i < l -> Term $ LocalVar i (go l tp)
              | otherwise -> f l i (go l tp)
            Lambda i tp rhs -> Term $ Lambda i (go l tp) (go (l+1) rhs)
            App x y -> Term $ App (go l x) (go l y) 
            Pi i lhs rhs -> Term $ Pi i (go l lhs) (go (l+1) rhs)
            TupleValue ll -> Term $ TupleValue $ go l <$> ll
            TupleType ll  -> Term $ TupleType $ go l <$> ll
            RecordValue m -> Term $ RecordValue $ go l <$> m
            RecordSelector x fld -> Term $ RecordSelector (go l x) fld
            RecordType m -> Term $ RecordType $ go l <$> m
            CtorValue c ll -> Term $ CtorValue c (goList l ll)
            CtorType dt ll -> Term $ CtorType dt (goList l ll)
            Let defs r -> Term $ Let (procDef <$> defs) (go l' r)
              where l' = l + length defs
                    procDef (LocalFnDef sym tp eqs) = LocalFnDef sym tp' eqs'
                      where tp' = go l tp
                            eqs' = procEq <$> eqs
                    procEq (DefEqn pats rhs) = DefEqn pats (go eql rhs)
                      where eql = l' + sum (patBoundVarCount <$> pats)
            EqType lhs rhs -> Term $ EqType (go l lhs) (go l rhs)
            Oracle s prop -> Term $ Oracle s (go l prop)
            _ -> t

-- | @incVars j k t@ increments free variables at least @j@ by @k@.
-- e.g., incVars 1 2 (C ?0 ?1) = C ?0 ?3
incVars :: DeBruijnIndex -> DeBruijnIndex -> Term -> Term
incVars _ 0 = id
incVars initialLevel j = assert (j > 0) $ instantiateVars fn initialLevel
  where fn _ i t = Term $ LocalVar (i+j) t

-- | Substitute @t@ for variable @k@ and decrement all higher dangling
-- variables.
instantiateVar :: DeBruijnIndex -> Term -> Term -> Term
instantiateVar k u = instantiateVars fn 0
  where -- Use terms to memoize instantiated versions of t.
        terms = [ incVars 0 i u | i <- [0..] ] 
        -- Instantiate variable 0.
        fn i j t | j - k == i = terms !! i
                 | j - i > k = Term $ LocalVar (j - 1) t                 
                 | otherwise  = Term $ LocalVar j t

-- | Substitute @ts@ for variables @[k .. k + length ts - 1]@ and
-- decrement all higher loose variables by @length ts@.
instantiateVarList :: DeBruijnIndex -> [Term] -> Term -> Term
instantiateVarList k [] = id
instantiateVarList k ts = instantiateVars fn 0
  where
    l = length ts
    -- Use terms to memoize instantiated versions of ts.
    terms = [ [ incVars 0 i t | i <- [0..] ] | t <- ts ]
    -- Instantiate variables [k .. k+l-1].
    fn i j t | j >= i + k + l = Term $ LocalVar (j - l) t
             | j >= i + k     = (terms !! (j - i - k)) !! i
             | otherwise      = Term $ LocalVar j t
-- ^ Specification in terms of @instantiateVar@ (by example):
-- @instantiateVarList 0 [x,y,z] t@ is the beta-reduced form of @Lam
-- (Lam (Lam t)) `App` z `App` y `App` x@, i.e. @instantiateVarList 0
-- [x,y,z] t == instantiateVar 0 x (instantiateVar 1 (incVars 0 1 y)
-- (instantiateVar 2 (incVars 0 2 z) t))@.


-- | Substitute @t@ for variable 0 in @s@ and decrement all remaining
-- variables.
betaReduce :: Term -> Term -> Term
betaReduce s t = instantiateVar 0 t s

-- | Pretty print a term with the given outer precedence.
ppTerm :: TermPrinter Term
ppTerm lcls p t =
  case asApp t of
    (Term u,[]) -> pptf p u
    (Term u,l) -> maybeParens (p >= 10) $ hsep $ pptf 10 u : fmap (ppTerm lcls 10) l 
 where pptf = ppTermF ppTerm lcls

instance Show Term where
  showsPrec p t = shows $ ppTerm emptyLocalVarDoc p t

data ModuleDecl = TypeDecl (DataType Ident (Pat Term) Term) 
                | DefDecl (Def Term)
 
data Module = Module {
          moduleName    :: ModuleName
        , moduleTypeMap :: !(Map Ident (DataType Ident (Pat Term) Term))
        , moduleCtorMap :: !(Map Ident (Ctor Ident (Pat Term) Term))
        , moduleDefMap  :: !(Map Ident (Def Term))
        , moduleRDecls   :: [ModuleDecl] -- ^ All declarations in reverse order they were added. 
        }

moduleDecls :: Module -> [ModuleDecl]
moduleDecls = reverse . moduleRDecls

instance Show Module where
  show m = render $ vcat $ ppdecl <$> moduleDecls m
    where ppdecl (TypeDecl d) = ppDataType ppTerm d
          ppdecl (DefDecl d) = ppDef emptyLocalVarDoc d <> char '\n'

findDataType :: Module -> Ident -> Maybe (DataType Ident (Pat Term) Term)
findDataType m i = Map.lookup i (moduleTypeMap m)

findCtor :: Module -> Ident -> Maybe (Ctor Ident (Pat Term) Term)
findCtor m i = Map.lookup i (moduleCtorMap m)

findDef :: Module -> Ident -> Maybe (Def Term)
findDef m i = Map.lookup i (moduleDefMap m)

emptyModule :: ModuleName -> Module
emptyModule nm =
  Module { moduleName = nm
         , moduleTypeMap = Map.empty
         , moduleCtorMap = Map.empty
         , moduleDefMap  = Map.empty
         , moduleRDecls = []
         }

insDataType :: Module -> DataType Ident (Pat Term) Term -> Module
insDataType m dt = m { moduleTypeMap = Map.insert (dtName dt) dt (moduleTypeMap m)
                     , moduleCtorMap = foldl' insCtor (moduleCtorMap m) (dtCtors dt)
                     , moduleRDecls = TypeDecl dt : moduleRDecls m
                     }
  where insCtor m' c = Map.insert (ctorName c) c m' 

insDef :: Module -> Def Term -> Module
insDef m d = m { moduleDefMap = Map.insert (defIdent d) d (moduleDefMap m)
               , moduleRDecls = DefDecl d : moduleRDecls m
               }
