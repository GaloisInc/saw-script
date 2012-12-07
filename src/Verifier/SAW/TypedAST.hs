
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}

{-# LANGUAGE ViewPatterns #-}
module Verifier.SAW.TypedAST
 ( -- * Module operations.
   Module
 , emptyModule
 , ModuleName
 , moduleName
 , ModuleDecl(..)
 , moduleDecls
 , findDataType
 , findCtor
 , findDef
 , insDef
 , insDataType
   -- * Data types and defintiions.
 , DataType(..)
 , Ctor(..)
 , Def(..)
 , DefEqn(..)
 , Pat(..)
 , patBoundVarCount
   -- * Terms and associated operations.
 , Term(..)
 , incVars
 , TermF(..)
   -- * Primitive types.
 , Sort, sortOf
 , Ident(identModule, identName), mkIdent
 , DeBruijnIndex
 , FieldName
 ) where

import Control.Applicative ((<$>))
import Control.Exception (assert)
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Vector (Vector)
import qualified Data.Vector as V
import Text.PrettyPrint.HughesPJ
import Data.Traversable (Traversable)

import Prelude hiding (concatMap, foldr, sum)

import Verifier.SAW.UntypedAST ( ModuleName
                               , FieldName
                               , Sort, sortOf
                               )

data Ident = Ident { identModule :: ModuleName
                   , identName :: String
                   }
  deriving (Eq, Ord)

instance Show Ident where
  show (Ident m s) = shows m ('.' : s)

mkIdent :: ModuleName -> String -> Ident
mkIdent = Ident

--type EitherIdent = Either UnusedIdent Ident

-- The TermF representation requires that record and field expressions contain
-- the arguments to the record and a term for applying the field to.  Both of
-- these decisions were made so that terms have a well-specified type, and we do
-- not need to be concerned about record subtyping.

type DeBruijnIndex = Int

-- Patterns are used to match equations.
data Pat e = -- | Variable and associated identifier. 
             -- Variables are indexed in order they appear.
             PVar String DeBruijnIndex e
           | PUnused
           | PTuple [Pat e]
           | PRecord (Map FieldName (Pat e))
             -- An arbitrary term that matches anything, but needs to be later
             -- verified to be equivalent.
           | PCtor (Ctor Term) [Pat e]
           | PIntLit Integer
  deriving (Eq,Ord, Show, Functor, Foldable, Traversable)

sumBy :: (Foldable t, Num b) => (a -> b) -> t a -> b
sumBy f = foldl' fn 0
  where fn e v = e + f v

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

-- A Definition contains an identifier, the type of the definition, and a list of equations.
data Def e = Def { defIdent :: Ident
                 , defType :: e
                 , defEqs :: [DefEqn Pat e]
                 }
  deriving (Functor, Foldable, Traversable)

instance Eq (Def e) where
  (==) = lift2 defIdent (==)

instance Ord (Def e) where
  compare = lift2 defIdent compare  

instance Show (Def e) where
  show = show . defIdent

data DefEqn p e
  = DefEqn [p e]  -- ^ List of patterns
           e -- ^ Right hand side.
  deriving (Functor, Foldable, Traversable)

data Ctor e = Ctor { ctorIdent :: !Ident
                     -- | The type of the constructor (should contain no free variables).
                   , ctorType :: e
                   }

instance Eq (Ctor e) where
  (==) = lift2 ctorIdent (==)

instance Ord (Ctor e) where
  compare = lift2 ctorIdent compare

instance Show (Ctor e) where
  show = show . ctorIdent

ppCtor :: Ctor Term -> Doc
ppCtor c = ppIdent (ctorIdent c) <+> doublecolon <+> ppTerm lcls 1 (ctorType c)
  where lcls = emptyLocalVarDoc

data DataType t = DataType { dtIdent :: Ident
                           , dtType :: t
                           , dtCtors :: [Ctor t]
                           }

instance Eq (DataType t) where
  (==) = lift2 dtIdent (==)

instance Ord (DataType t) where
  compare = lift2 dtIdent compare

instance Show (DataType t) where
  show = show . dtIdent

ppTypeConstraint :: LocalVarDoc -> Ident -> Term -> Doc
ppTypeConstraint lcls sym tp = ppIdent sym <+> doublecolon <+> ppTerm lcls 1 tp

ppDataType :: DataType Term -> Doc
ppDataType dt = text "data" <+> tc <+> text "where" <+> lbrace $$
                  nest 4 (vcat (ppc <$> dtCtors dt)) $$
                  nest 2 rbrace
  where lcls = emptyLocalVarDoc
        tc = ppTypeConstraint lcls (dtIdent dt) (dtType dt)
        ppc c = ppCtor c <> semi

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

  | CtorValue (Ctor Term) [e]
  | CtorType (DataType Term) [e]

  | Sort Sort

    -- ^ List of bindings and the let expression itself.
    -- Let expressions introduce variables for each identifier.
  | Let [Def Term] e

    -- Primitive builtin values
  | IntLit Integer
    -- | Array value includes type of elements followed by elements.
  | ArrayValue e (Vector e)
 deriving (Eq, Ord, Functor, Foldable, Traversable)

ppIdent :: Ident -> Doc
ppIdent i = text (show i)

doublecolon :: Doc
doublecolon = colon <> colon

ppDef :: LocalVarDoc -> Def Term -> Doc
ppDef lcls d = vcat (typeDoc : (ppDefEqn lcls sym <$> defEqs d))
  where sym = ppIdent (defIdent d)
        typeDoc = sym <+> doublecolon <+> ppTerm lcls 1 (defType d)

ppDefEqn :: LocalVarDoc -> Doc -> DefEqn Pat Term -> Doc
ppDefEqn lcls sym (DefEqn pats rhs) = lhs <+> equals <+> ppTerm lcls' 1 rhs
  where lcls' = foldl' consBinding lcls (concatMap patBoundVars pats) 
        lhs = sym <+> hsep (ppPat ppTerm lcls' 10 <$> pats)

-- | Print a list of items separated by semicolons
semiTermList :: [Doc] -> Doc
semiTermList = hsep . fmap (<> semi)

type TermPrinter e = LocalVarDoc -> Int -> e -> Doc

ppPat :: TermPrinter e -> TermPrinter (Pat e)
ppPat f lcls p pat = 
  case pat of
    PVar i _ _ -> text i
    PUnused{} -> char '_'
    PCtor c pl -> sp 10 $ ppIdent (ctorIdent c) <+> hsep (ppPat f lcls 10 <$> pl)
    PTuple pl -> parens $ commaSepList $ ppPat f lcls 1 <$> pl
    PRecord m -> 
      let ppFld (fld,v) = text fld <+> equals <+> ppPat f lcls 1 v
       in braces $ semiTermList $ ppFld <$> Map.toList m
    PIntLit i -> integer i
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
        Nothing -> char '!' <> integer (toInteger i)

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
    Pi pat tp rhs -> lhs <+> text "->" <+> f lcls' 2 rhs
      where lcls' = foldl' consBinding lcls (patBoundVars pat)
            lhs = case pat of
                    PUnused -> f lcls 2 tp
                    _ -> parens (ppPat f lcls' 1 pat <> doublecolon <> f lcls 1 tp)

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
      | null tl -> ppIdent (ctorIdent c)
      | otherwise -> sp 10 $ hsep $ ppIdent (ctorIdent c) : fmap (f lcls 10) tl
    CtorType dt tl
      | null tl -> ppIdent (dtIdent dt)
      | otherwise -> sp 10 $ hsep $ ppIdent (dtIdent dt) : fmap (f lcls 10) tl
    Sort s -> text (show s)
    Let dl t -> text "let" <+> vcat (ppDef lcls' <$> dl) $$
                text " in" <+> f lcls' 0 t
      where lcls' = foldl' consBinding lcls (fmap (identName . defIdent) dl)
    IntLit i -> integer i
    ArrayValue _ vl -> brackets (commaSepList (f lcls 1 <$> V.toList vl))

newtype Term = Term (TermF Term)
  deriving (Eq,Ord)

asApp :: Term -> (Term, [Term])
asApp = go []
  where go l (Term (App t u)) = go (u:l) t
        go l t = (t,l)

-- | @incVars j k t@ increments free variables at least @j@ by @k@.
-- e.g., incVars 1 2 (C ?0 ?1) = C ?0 ?3
incVars :: DeBruijnIndex -> DeBruijnIndex -> Term -> Term
incVars _ 0 = id
incVars initialLevel j = assert (j > 0) $ go initialLevel 
  where goList :: DeBruijnIndex -> [Term] -> [Term]
        goList _ []  = []
        goList l (e:r) = go l e : goList (l+1) r
        go :: DeBruijnIndex -> Term -> Term
        go l t@(Term tf) =
          case tf of
            LocalVar i tp
              | i < l     -> Term $ LocalVar i (go (l-(i+1)) tp)
              | otherwise -> Term $ LocalVar (i+j) tp
            Lambda i tp rhs -> Term $ Lambda i (go l tp) (go (l+1) rhs)
            App x y -> Term $ App (go l x) (go l y) 
            Pi i lhs rhs -> Term $ Pi i (go l lhs) (go (l+1) rhs)
            TupleValue ll -> Term $ TupleValue $ go l <$> ll
            TupleType ll  -> Term $ TupleType $ go l <$> ll
            RecordValue m -> Term $ RecordValue $ go l <$> m
            RecordSelector x f -> Term $ RecordSelector (go l x) f
            RecordType m -> Term $ RecordType $ go l <$> m
            CtorValue c ll -> Term $ CtorValue c (goList l ll)
            CtorType dt ll -> Term $ CtorType dt (goList l ll)
            Let defs r -> Term $ Let (procDef <$> defs) (go l' r)
              where l' = l + length defs
                    procDef d = Def { defIdent = defIdent d
                                    , defType = go l (defType d)
                                    , defEqs = procEq <$> defEqs d
                                    }
                    procEq (DefEqn pats rhs) = DefEqn pats (go eql rhs)
                      where eql = l' + sum (patBoundVarCount <$> pats)
            _ -> t

-- | Pretty print a term with the given outer precedence.
ppTerm :: TermPrinter Term
ppTerm lcls p t =
  case asApp t of
    (Term u,[]) -> pptf p u
    (Term u,l) -> maybeParens (p >= 10) $ hsep $ pptf 10 u : fmap (ppTerm lcls 10) l 
 where pptf = ppTermF ppTerm lcls

instance Show Term where
  showsPrec p t = shows $ ppTerm emptyLocalVarDoc p t

data ModuleDecl = TypeDecl (DataType Term) 
                | DefDecl (Def Term)
 
data Module = Module {
          moduleName    :: ModuleName
        , moduleTypeMap :: !(Map Ident (DataType Term))
        , moduleCtorMap :: !(Map Ident (Ctor Term))
        , moduleDefMap  :: !(Map Ident (Def Term))
        , moduleRDecls   :: [ModuleDecl] -- ^ All declarations in reverse order they were added. 
        }

moduleDecls :: Module -> [ModuleDecl]
moduleDecls = reverse . moduleRDecls

instance Show Module where
  show m = render $ vcat $ ppdecl <$> moduleDecls m
    where ppdecl (TypeDecl d) = ppDataType d
          ppdecl (DefDecl d) = ppDef emptyLocalVarDoc d <> char '\n'

findDataType :: Module -> Ident -> Maybe (DataType Term)
findDataType m i = Map.lookup i (moduleTypeMap m)

findCtor :: Module -> Ident -> Maybe (Ctor Term)
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

insDataType :: Module -> DataType Term -> Module
insDataType m dt = m { moduleTypeMap = Map.insert (dtIdent dt) dt (moduleTypeMap m)
                     , moduleCtorMap = foldl' insCtor (moduleCtorMap m) (dtCtors dt)
                     , moduleRDecls = TypeDecl dt : moduleRDecls m
                     }
  where insCtor m' c = Map.insert (ctorIdent c) c m' 

insDef :: Module -> Def Term -> Module
insDef m d = m { moduleDefMap = Map.insert (defIdent d) d (moduleDefMap m)
               , moduleRDecls = DefDecl d : moduleRDecls m
               }