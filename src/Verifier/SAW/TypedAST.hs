{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
module Verifier.SAW.TypedAST
 ( Un.Ident, Un.mkIdent
 , Un.ParamType(..)
 , DeBruijnIndex
 , LambdaVar
 , FieldName
 , Sort, Un.sortOf
 , Def
 , TermF(..)
 , Term(..)
 , Module
 , emptyModule
 , unsafeMkModule
 , findDataType
 , findCtor
 , findDef
 ) where

import Control.Applicative ((<$>))
import Control.Exception (assert)
import Data.Foldable
import Data.List (mapAccumL)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Vector (Vector)
import qualified Data.Vector as V
import Text.PrettyPrint.HughesPJ
import Data.Traversable (Traversable)

import Debug.Trace
import Prelude hiding (concatMap, foldr, sum)

import Verifier.SAW.UntypedAST ( Ident
                               , EitherIdent
                               , FieldName
                               , Sort
                               , val
                               , PosPair(..)
                               )
import qualified Verifier.SAW.UntypedAST as Un

type LambdaVar e = (Un.ParamType, Ident, e)

-- The TermF representation requires that record and field expressions contain
-- the arguments to the record and a term for applying the field to.  Both of
-- these decisions were made so that terms have a well-specified type, and we do
-- not need to be concerned about record subtyping.

type DeBruijnIndex = Int

-- Patterns are used to match equations.
data Pat e = -- | Variable and associated identifier. 
             -- Variables are indexed in order they appear.
             PVar Ident
           | PTuple [Pat e]
           | PRecord (Map FieldName (Pat e))
             -- An arbitrary term that matches anything, but needs to be later
             -- verified to be equivalent.
           | PCtor Ctor [Pat e]
           | PInaccessible
  deriving (Eq,Ord, Functor, Foldable, Traversable)

patBoundVars :: Pat e -> [Ident]
patBoundVars p =
  case p of
    PVar i -> [i]
    PCtor _ l -> concatMap patBoundVars l
    PTuple l -> concatMap patBoundVars l
    PRecord m -> concatMap patBoundVars (Map.elems m)
    PInaccessible{} -> []

lift2 :: (a -> b) -> (b -> b -> c) -> a -> a -> c
lift2 f h x y = h (f x) (f y) 

-- A Definition contains an identifier, the type of the definition, and a list of equations.
data Def e = Def { defIdent :: Ident
                 , defType :: e
                 , defEqs :: [DefEqn e]
                 }
  deriving (Functor, Foldable, Traversable)

instance Eq (Def e) where
  (==) = lift2 defIdent (==)

instance Ord (Def e) where
  compare = lift2 defIdent compare  

instance Show (Def e) where
  show = show . defIdent

data DefEqn e
  = DefEqn [Pat e]  -- ^ List of patterns
           e -- ^ Right hand side.
  deriving (Functor, Foldable, Traversable)

data Ctor = Ctor { ctorIdent :: !Ident
                   -- | The type of the constructor (should contain no free variables).
                 , ctorType :: Term
                 }

instance Eq Ctor where
  (==) = lift2 ctorIdent (==)

instance Ord Ctor where
  compare = lift2 ctorIdent compare

instance Show Ctor where
  show = show . ctorIdent

ppCtor :: Ctor -> Doc
ppCtor c = ppIdent (ctorIdent c) <+> doublecolon <+> ppTerm lcls 1 (ctorType c)
  where lcls = emptyLocalVarDoc

data DataType = DataType { dtIdent :: Ident
                         , dtType :: Term
                         , dtCtors :: [Ctor]
                         }

instance Eq DataType where
  (==) = lift2 dtIdent (==)

instance Ord DataType where
  compare = lift2 dtIdent compare

instance Show DataType where
  show = show . dtIdent

ppTypeConstraint :: LocalVarDoc -> Ident -> Term -> Doc
ppTypeConstraint lcls sym tp = ppIdent sym <+> doublecolon <+> ppTerm lcls 1 tp

ppDataType :: DataType -> Doc
ppDataType dt = text "data" <+> tc <+> text "where" <+> lbrace $$
                  nest 4 (vcat (ppc <$> dtCtors dt)) $$
                  nest 2 rbrace
  where lcls = emptyLocalVarDoc
        tc = ppTypeConstraint lcls (dtIdent dt) (dtType dt)
        ppc c = ppCtor c <> semi

data TermF e
  = LocalVar !DeBruijnIndex !e -- ^ Local variables are referenced by deBrujin index, and the type.
  | GlobalDef (Def e)  -- ^ Global variables are referenced by label.

  | Lambda EitherIdent e e
  | App !e !e
  | Pi !EitherIdent !e !e

    -- Tuples may be 0 or 2+ elements. 
    -- A tuple of a single element is not allowed in well-formed expressions.
  | TupleValue [e]
  | TupleType [e]

  | RecordValue (Map FieldName e)
  | RecordSelector e FieldName
  | RecordType (Map FieldName e)

  | CtorValue Ctor [e]
  | CtorType DataType [e]

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

ppEitherIdent :: EitherIdent -> Doc
ppEitherIdent er = text $ either show show er

doublecolon :: Doc
doublecolon = colon <> colon

ppDef :: LocalVarDoc -> Def Term -> Doc
ppDef lcls d = vcat (typeDoc : (ppDefEqn lcls sym <$> defEqs d))
  where sym = ppIdent (defIdent d)
        typeDoc = sym <+> doublecolon <+> ppTerm lcls 1 (defType d)

ppDefEqn :: LocalVarDoc -> Doc -> DefEqn Term -> Doc
ppDefEqn lcls sym (DefEqn pats rhs) = lhs <+> equals <+> ppTerm lcls' 1 rhs
  where lcls' = foldl' consBinding lcls (Right <$> concatMap patBoundVars pats) 
        lhs = sym <+> hsep (ppPat ppTerm lcls 10 <$> pats)

-- | Print a list of items separated by semicolons
semiTermList :: [Doc] -> Doc
semiTermList = hsep . fmap (<> semi)

type TermPrinter e = LocalVarDoc -> Int -> e -> Doc

ppPat :: TermPrinter e -> TermPrinter (Pat e)
ppPat f lcls p pat = 
  case pat of
    PVar i -> ppIdent i
    PCtor c pl -> sp 10 $ ppIdent (ctorIdent c) <+> hsep (ppPat f lcls 10 <$> pl)
    PTuple pl -> parens $ commaSepList $ ppPat f lcls 1 <$> pl
    PRecord m -> 
      let ppFld (fld,v) = text fld <+> equals <+> ppPat f lcls 1 v
       in braces $ semiTermList $ ppFld <$> Map.toList m
    PInaccessible{} -> char '_'
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
                       , docUsedMap :: Map Ident DeBruijnIndex
                       }

emptyLocalVarDoc :: LocalVarDoc
emptyLocalVarDoc = LVD { docMap = Map.empty
                       , docLvl = 0
                       , docUsedMap = Map.empty
                       }

consBinding :: LocalVarDoc -> EitherIdent -> LocalVarDoc
consBinding lvd ei = LVD { docMap = Map.insert lvl (ppEitherIdent ei) m          
                         , docLvl = lvl + 1
                         , docUsedMap = um
                         }
 where lvl = docLvl lvd
       (m,um) = case ei of
                  Left _ ->
                    ( docMap lvd
                    , docUsedMap lvd
                    )
                  Right i -> 
                    ( case Map.lookup i (docUsedMap lvd) of
                        Just pl -> Map.delete pl (docMap lvd)
                        Nothing -> docMap lvd
                    , Map.insert i lvl (docUsedMap lvd)
                    )

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
    Lambda ei tp rhs -> sp 1 $ text "\\" <> lhs <+> text "->" <+> f lcls' 2 rhs
      where lhs = parens (ppEitherIdent ei <> doublecolon <> f lcls 1 tp)
            lcls' = consBinding lcls ei
    App t u -> sp 10 (f lcls 10 t <+> f lcls 10 u)
    Pi mi tp rhs -> lhs <+> text "->" <+> f lcls' 2 rhs
      where lhs = case mi of
                   Left _ -> f lcls 2 tp
                   Right i -> parens (ppIdent i <> doublecolon <> f lcls 1 tp)
            lcls' = consBinding lcls mi
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
      where lcls' = foldl' consBinding lcls (fmap (Right . defIdent) dl)
    IntLit i -> integer i
    ArrayValue _ vl -> brackets (commaSepList (f lcls 1 <$> V.toList vl))

newtype Term = Term (TermF Term)
  deriving (Eq,Ord)

asApp :: Term -> (Term, [Term])
asApp = go []
  where go l (Term (App t u)) = go (u:l) t
        go l t = (t,l)

-- | @instantiateVars f l t@ substitutes each dangling bound variable
-- @LocalVar j t@ with the term @f i j t'@, where @i@ is the number of
-- binders surrounding @LocalVar j t@ and @t'@ is the result of
-- recursively instantiating @t@.
instantiateVars :: (DeBruijnIndex -> DeBruijnIndex -> Term -> Term)
                -> DeBruijnIndex -> Term -> Term
instantiateVars f initialLevel = go initialLevel 
  where goList _ []  = []
        goList l (e:r) = go l e : goList (l+1) r
        goPat l p = 
          case p of
            PVar{} -> p
            PCtor c pl -> PCtor c (goPat l <$> pl)
            PTuple pl -> PTuple (goPat l <$> pl)
            PRecord m -> PRecord (goPat l <$> m)
            PInaccessible -> PInaccessible
        go :: DeBruijnIndex -> Term -> Term
        go l t@(Term tf) =
          case tf of
            LocalVar i tp | i >= l -> f l i (go l tp)
                          | otherwise -> Term $ LocalVar i (go l tp)
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
                    procEq (DefEqn pats rhs) = DefEqn pats' (go eql rhs)
                      where eql = l' + sum (patBoundVarCount <$> pats)
                            pats' = goPat eql <$> pats
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
instantiateVar k t = instantiateVars fn 0
  where -- Use terms to memoize instantiated versions of t.
        terms = [ incVars 0 i t | i <- [0..] ] 
        -- Instantiate variable 0.
        fn i j t | j  > i + k = Term $ LocalVar (j - 1) t
                 | j == i + k = terms !! i
                 | otherwise  = Term $ LocalVar j t

-- | Substitute @t@ for variable 0 in @s@ and decrement all remaining
-- variables.
betaReduce :: Term -> Term -> Term
betaReduce s t = instantiateVar 0 t s

{-
-- | @termApp t u@ returns the term obtained by replacing var 0 in @t@
-- with @u@.
termApp :: Term -> Term -> Term
termApp (Term tf) u =
  case tf of
    _ -> undefined 
-}

-- | Pretty print a term with the given outer precedence.
ppTerm :: TermPrinter Term
ppTerm lcls p t =
  case asApp t of
    (Term u,[]) -> pptf p u
    (Term u,l) -> maybeParens (p >= 10) $ hsep $ pptf 10 u : fmap (ppTerm lcls 10) l 
 where pptf = ppTermF ppTerm lcls

instance Show Term where
  showsPrec p t = shows $ ppTerm emptyLocalVarDoc p t

data ModuleDecl = TypeDecl DataType 
                | DefDecl (Def Term)
 
data Module = Module {
          moduleTypeMap :: !(Map Ident DataType)
        , moduleCtorMap :: !(Map Ident Ctor)
        , moduleDefMap  :: !(Map Ident (Def Term))
        , moduleDecls   :: [ModuleDecl] -- ^ All declarations in reverse order they were added. 
        }

instance Show Module where
  show m = render $ vcat $ ppdecl <$> reverse (moduleDecls m)
    where ppdecl (TypeDecl d) = ppDataType d
          ppdecl (DefDecl d) = ppDef emptyLocalVarDoc d <> char '\n'

findDataType :: Module -> Ident -> Maybe DataType
findDataType m i = Map.lookup i (moduleTypeMap m)

findCtor :: Module -> Ident -> Maybe Ctor
findCtor m i = Map.lookup i (moduleCtorMap m)

findDef :: Module -> Ident -> Maybe (Def Term)
findDef m i = Map.lookup i (moduleDefMap m)

emptyModule :: Module
emptyModule = Module { moduleTypeMap = Map.empty
                     , moduleCtorMap = Map.empty
                     , moduleDefMap  = Map.empty
                     , moduleDecls = []
                     }

insDataType :: Module -> DataType -> Module
insDataType m dt = m { moduleTypeMap = Map.insert (dtIdent dt) dt (moduleTypeMap m)
                     , moduleCtorMap = foldl' insCtor (moduleCtorMap m) (dtCtors dt)
                     , moduleDecls = TypeDecl dt : moduleDecls m
                     }
  where insCtor m' c = Map.insert (ctorIdent c) c m' 

insDef :: Module -> Def Term -> Module
insDef m d = m { moduleDefMap = Map.insert (defIdent d) d (moduleDefMap m)
               , moduleDecls = DefDecl d : moduleDecls m
               }

internalError :: String -> a
internalError msg = error $ "internal: " ++ msg

declEqs :: TermContext -> [Un.Decl] -> (Ident -> [DefEqn Term])
declEqs ctx d = \i -> Map.findWithDefault [] i eqMap
  where insertEq m (Un.TermDef i lhs rhs) = Map.insertWith (++) sym v m
          where sym = val i
                tp = case findDefType ctx sym of
                       Just tp' -> tp'
                       Nothing -> internalError $ "Could not find " ++ show sym
                ctx' = consPatVars ctx (snd <$> lhs) tp
                patFn p = convertPat ctx' (snd p)
                v = [DefEqn (patFn <$> lhs) (convertTerm ctx' rhs)]
        insertEq m Un.TypeDecl{} = m
        insertEq m Un.DataDecl{} = m
        eqMap = foldl' insertEq Map.empty d

-- | Creates a module from a list of untyped declarations.
unsafeMkModule :: [Un.Decl] -> Module
unsafeMkModule d = gloMod
  where lookupEq = declEqs gloCtx d
        insertDef m (Un.TypeDecl idl untp) = foldl' insDef m (idDef <$> idl)
          where tp = convertTerm gloCtx untp
                idDef i = Def { defIdent = val i
                              , defType = tp
                              , defEqs = lookupEq (val i)
                              }
        insertDef m (Un.DataDecl psym untp cl) = insDataType m tpd
          where tpd = DataType { dtIdent = val psym
                               , dtType = convertTerm gloCtx untp
                               , dtCtors = ctorDef <$> cl
                          }
                ctorDef (Un.Ctor ctorId ctorTp) =
                      Ctor { ctorIdent = val ctorId 
                           , ctorType = convertTerm gloCtx ctorTp
                           }
        insertDef m Un.TermDef{} = m
        gloMod = foldl' insertDef emptyModule d
        gloCtx = globalContext gloMod

type DeBruijnLevel = DeBruijnIndex

data TermContext = TermContext {
         tcDeBruijnLevel :: !DeBruijnLevel
       , tcMap :: !(Map Ident (Either (DeBruijnLevel,Term) (Def Term)))
       , tcDataDecls :: !(Map Ident (Either Ctor DataType))
       }

instance Show TermContext where
  show tc = "tcDeBruijnLevel: " ++ show (tcDeBruijnLevel tc) ++ "\n"
         ++ "tcMap:\n" ++ ppm ppVar (tcMap tc)
         ++ "tcDataDecls:\n" ++ ppm ppData (tcDataDecls tc)
   where ppe :: (a -> String) -> (Ident,a) -> String
         ppe fn (i,v) = "  " ++ show i ++ " = " ++ fn v ++ "\n"
         ppm :: (a -> String) -> Map Ident a -> String
         ppm fn m = concatMap (ppe fn) (Map.toList m) 
         ppVar (Left (l,_))  = "Local " ++ show l
         ppVar (Right d) = "Global " ++ show (defIdent d) 
         ppData (Left c) = "Ctor " ++ show (ctorIdent c)
         ppData (Right dt) = "ADT " ++ show (dtIdent dt)

globalContext :: Module -> TermContext
globalContext m =
    TermContext { tcDeBruijnLevel = 0
                , tcMap = Map.fromList [ (defIdent d, Right d) 
                                       | DefDecl d <- moduleDecls m ]
                , tcDataDecls = Map.fromList  [ p | TypeDecl dt <- moduleDecls m
                                              , p <- dtFn dt ]
                }
  where cFn c = (ctorIdent c, Left c)
        dtFn dt = (dtIdent dt, Right dt) : (cFn <$> dtCtors dt) 

-- | Add a new local var to the context.
consLocalVar :: TermContext -> EitherIdent -> Term -> TermContext
consLocalVar tc ei tp = tc { tcDeBruijnLevel = lvl + 1, tcMap = m }
  where lvl = tcDeBruijnLevel tc
        m = case ei of
              Left{} -> tcMap tc
              Right sym -> Map.insert sym (Left (lvl,tp)) (tcMap tc)

-- | Insert local definitions the terms belong to the given context.
insertLocalDefs :: TermContext -> [(Ident,Term)] -> TermContext
insertLocalDefs = go 0
  where go _ tc [] = tc
        go i tc ((sym,tp):r) = go (i+1) tc' r
          where tc' = consLocalVar tc (Right sym) (incVars 0 i tp)

-- | Returns constructor or data type associated with given identifier.
-- Calls error if attempt to find constructor failed.
findCon :: TermContext -> Ident -> Maybe (Either Ctor DataType)
findCon tc i = Map.lookup i (tcDataDecls tc)

findDefType :: TermContext -> Ident -> Maybe Term
findDefType tc i = getType <$> Map.lookup i (tcMap tc)
  where getType (Left (_,tp)) = tp
        getType (Right d) = defType d

type InaccessibleIndex = Int

data UnifyTerm
  = URigidVar Ident -- ^ Rigid variable that cannot be instantiated.
  | ULocalVar DeBruijnIndex Term  -- ^ Variable bound by context with type.
  | UGlobal (Def Term)
  
  | ULambda EitherIdent UnifyTerm UnifyTerm
  | UApp UnifyTerm UnifyTerm
  | UPi EitherIdent UnifyTerm UnifyTerm

  | UTupleValue [UnifyTerm]
  | UTupleType [UnifyTerm]

  | URecordValue (Map FieldName UnifyTerm)
  | URecordSelector UnifyTerm FieldName
  | URecordType (Map FieldName UnifyTerm)

  | UCtorApp Ctor [UnifyTerm]
  | UDataType DataType [UnifyTerm]

  | USort Sort
 
  | ULet [Def Term] UnifyTerm
  | UIntLit Integer
  | UArray UnifyTerm (Vector UnifyTerm)

  | UInaccessible InaccessibleIndex
  deriving (Eq, Show)

data UnifyState = US { usTypeMap :: Map Ident UnifyTerm
                     , usVarTermMap :: Map InaccessibleIndex UnifyTerm
                     , termEqs :: [(UnifyTerm,UnifyTerm)]
                     , usVars :: Set UVar
                     }
  deriving (Show)

emptyUnifyState :: Set Ident -- ^ Identifiers bound in patterns.
                -> InaccessibleIndex -- ^ Number of inaccessible vars already bound.
                -> UnifyState
emptyUnifyState vs cnt =
    US { usTypeMap = Map.empty
       , usVarTermMap = Map.empty
       , termEqs = []
       , usVars = foldr (Set.insert . UIVar) (Set.map UPVar vs) [0..cnt-1]
       }

identType :: Ident -> UnifyState -> Maybe UnifyTerm
identType i us = Map.lookup i (usTypeMap us)

inaccessibleBinding :: InaccessibleIndex -> UnifyState -> Maybe UnifyTerm
inaccessibleBinding i us = Map.lookup i (usVarTermMap us)

addTermEq :: UnifyTerm -> UnifyTerm -> UnifyState -> UnifyState
addTermEq x y s  = s { termEqs = (x,y):termEqs s }

addTermEqs :: [(UnifyTerm, UnifyTerm)] -> UnifyState -> UnifyState
addTermEqs eqs s = foldr (uncurry addTermEq) s eqs

popTermEq :: UnifyState -> Maybe (UnifyTerm,UnifyTerm,UnifyState)
popTermEq s =
  case termEqs s of
    (t,u):eqs -> Just (t,u,s { termEqs = eqs })
    [] -> Nothing

bindPatVarType :: Ident -> UnifyTerm -> UnifyState -> UnifyState
bindPatVarType sym tp s = s { usTypeMap = Map.insert sym tp (usTypeMap s) }

bindVar :: InaccessibleIndex -> UnifyTerm -> UnifyState -> UnifyState
bindVar i t s =
  case Map.lookup i m of
    Nothing -> s { usVarTermMap = Map.insert i t m }
    Just u -> assert (t == u) s
 where m = usVarTermMap s

-- Two types of edges:
-- For each pattern variable, there is an edge from the variable
-- to the variables in it's type.
-- For each inaccessible index, there is an edge to the subterms for it.
-- Want to bind identifiers 

mkEdgeMap :: Ord a => [(a,a)] -> Map a [a]
mkEdgeMap = foldl' fn Map.empty
  where fn m (x,y) = Map.insertWith (++) x [y] m

flipPair :: (a,b) -> (b,a)
flipPair (x,y) = (y,x)

topSort :: forall a . Ord a
        => Set a -- List of vertices.
        -> [(a,a)] -- List of edges
        -> Either (Map a Int) [a]
topSort vertices e = go (initNulls, initMap) []
  where vl = Set.toList vertices
        outEdgeMap = mkEdgeMap e
        outEdges v = Map.findWithDefault [] v outEdgeMap
        inEdgeMap = mkEdgeMap (flipPair <$> e)
        -- Nodes that have edge to the given node. 
        inEdges :: a -> [a]
        inEdges v = Map.findWithDefault [] v inEdgeMap
        initNulls = filter (null . inEdges) vl
        initMap = Map.fromList [  (v,l) | v <- vl
                               , let l = length (inEdges v)
                               , l > 0
                               ]
        decInEdgeCount :: ([a], Map a Int) -> a -> ([a], Map a Int)
        decInEdgeCount (l,zm) v = 
            case Map.lookup v zm of
                    Nothing -> error "internal: topSort did not maintain edge count"
                    Just 1 -> (v:l, Map.delete v zm)
                    Just n -> assert (n > 1) $ (l, Map.insert v (n-1) zm)
        go :: ([a], Map a Int) -> [a] -> Either (Map a Int) [a]
        go ([],zm) r | Map.null zm = Right (reverse r)
                     | otherwise = Left zm
        go (h:l,zm) r = go (foldl' decInEdgeCount (l,zm) (outEdges h)) (h:r)

orderedListMap :: Ord a => [a] -> Map a Int
orderedListMap l = Map.fromList (l `zip` [0..])

data UVar = UPVar Ident | UIVar InaccessibleIndex
  deriving (Eq, Ord, Show)

addUnifyTermVars :: Set UVar -> UnifyTerm -> Set UVar
addUnifyTermVars = go
  where go s (URigidVar sym) = Set.insert (UPVar sym) s
        go s (ULambda _ x y) = go (go s x) y
        go s (UApp x y)      = go (go s x) y
        go s (UPi _ x y)     = go (go s x) y
        go s (UTupleValue l) = foldl' go s l
        go s (UTupleType l)  = foldl' go s l
        go s (URecordValue m) = foldl' go s m
        go s (URecordSelector x _) = go s x
        go s (URecordType m) = foldl' go s m
        go s (UCtorApp _ l) = foldl' go s l
        go s (UDataType _ l) = foldl' go s l
        go s (ULet _ x) = go s x
        go s (UArray x v) = foldl' go (go s x) v
        go s (UInaccessible i) = Set.insert (UIVar i) s
        go s _ = s

addVarBindings :: UnifyState -> TermContext -> TermContext
addVarBindings us = \tc -> foldl' addIdent tc (zip ordering [0..])
  where completeTerm :: Int -- Ident of this term in ordering.
                     -> DeBruijnIndex
                     -> UnifyTerm
                     -> Term
        completeTerm idx j ut =
          case ut of
            URigidVar sym -> assert (prevIdx < idx) $
               Term $ LocalVar (j + idx') (varTypes V.! idx')
              where Just prevIdx = Map.lookup sym pIdxMap
                    idx' = idx - prevIdx - 1
            ULocalVar i tp -> Term $ LocalVar i tp
            UGlobal d      -> Term $ GlobalDef d
            ULambda s l r  -> Term $ Lambda s (go j l) (go (j+1) r)
            UApp x y  -> Term $ App (go j x) (go j y)
            UPi s l r -> Term $ Pi s (go j l) (go (j+1) r)
            UTupleValue l -> Term $ TupleValue (go j <$> l)
            UTupleType l  -> Term $ TupleType  (go j <$> l)
            URecordValue m      -> Term $ RecordValue (go j <$> m)
            URecordSelector x f -> Term $ RecordSelector (go j x) f
            URecordType m       -> Term $ RecordType (go j <$> m)
            UCtorApp c l   -> Term $ CtorValue c (go j <$> l)
            UDataType dt l -> Term $ CtorType dt (go j <$> l)
            USort s   -> Term $ Sort s
            ULet dl t -> Term $ Let dl (go (j + length dl) t)
            UIntLit i -> Term $ IntLit i
            UArray tp v -> Term $ ArrayValue (go j tp) (go j <$> v)
            UInaccessible i -> go j t
              where Just t = inaccessibleBinding i us
         where go = completeTerm idx
        varSubterm (UPVar sym) = fromMaybe err $ identType sym us
          where err = error $ "Could not find type for " ++ show sym
        varSubterm (UIVar i) = fromMaybe err $ inaccessibleBinding i us
          where err = error $ "Could not find binding for " ++ show i
        vars = usVars us
        edges = [ (v, u)
                      | u <- Set.toList vars
                      , v <- Set.toList $ addUnifyTermVars Set.empty (varSubterm u)
                      ]
        allOrdering =
          case topSort vars edges of
            Left zm -> error $ "Found cyclic dependencies: " ++ show zm
            Right o -> o
        ordering = [ i | UPVar i <- allOrdering ]
        pIdxMap :: Map Ident Int
        pIdxMap = orderedListMap ordering
        varTypes :: Vector Term
        varTypes = V.fromList (uncurry fn <$> zip ordering [0..])
          where fn sym idx = completeTerm idx 0 tp
                  where Just tp = identType sym us
        addIdent :: TermContext -> (Ident, Int) -> TermContext
        addIdent tc (sym,idx) = assert (0 <= idx && idx < V.length varTypes) $
          consLocalVar tc (Right sym) (varTypes V.! idx)

termUnPat :: (?ctx :: TermContext) => Un.Pat InaccessibleIndex -> UnifyTerm
termUnPat = go
  where go (Un.PVar (PosPair _ (Right sym))) = URigidVar sym
        go (Un.PVar _) = internalError "Unexpected unbound identifier in binding position"
        go (Un.PTuple _ pl) = UTupleValue (go <$> pl)
        go (Un.PRecord _ pm) = URecordValue (Map.fromList (fn <$> pm))
           where fn (pf,p) = (val pf, go p)
        go (Un.PCtor sym pl) = UCtorApp c (go <$> pl)
          where Just (Left c) = findCon ?ctx (val sym)
        go (Un.PInaccessible i) = UInaccessible i

instWithUnPat :: V.Vector UnifyTerm -> Term -> UnifyTerm
instWithUnPat pv = go 0
  where plen = V.length pv
        go bnd (Term tf) = 
          case tf of 
            LocalVar i tp
              | i < bnd    -> ULocalVar i tp
              | i' < plen -> pv V.! i'
              | otherwise -> ULocalVar i' tp
             where i' = i - bnd
            GlobalDef d -> UGlobal d
            Lambda sym lhs rhs -> ULambda sym l (go (bnd+1) rhs)
              where l = go bnd lhs
            App x y -> UApp (go bnd x) (go bnd y)
            Pi sym lhs rhs -> UPi sym l (go (bnd+1) rhs)
              where l = go bnd lhs
            TupleValue l -> UTupleValue (go bnd <$> l)
            TupleType l -> UTupleType (go bnd <$> l)
            RecordValue m -> URecordValue (go bnd <$> m)
            RecordSelector x f -> URecordSelector (go bnd x) f
            RecordType m -> URecordType (go bnd <$> m)
            CtorValue c l -> UCtorApp c (go bnd <$> l)
            CtorType dt l -> UDataType dt (go bnd <$> l)
            Sort s -> USort s
            Let dl t -> ULet dl (go (bnd + length dl) t)
            IntLit i -> UIntLit i
            ArrayValue tp v -> UArray (go bnd tp) (go bnd <$> v)

-- | Create a set of constraints for matching a list of patterns against a given pi type.
instPiType :: (?ctx :: TermContext)
              -- | Continuation to generate final constraints
           => (UnifyTerm -> UnifyState -> UnifyState)
           -> [Un.Pat InaccessibleIndex] -- ^ Patterns to match
           -> Term -- ^ Expected pi type 
           -> UnifyState
           -> UnifyState
instPiType cont = \pl tp s -> go s pl V.empty tp
  where go s [] ctx ltp = cont (instWithUnPat ctx ltp) s
        go s (p:pl) pctx ltp =
          case ltp of
            Term (Pi _ lhs rhs) -> go s' pl (V.cons (termUnPat p) pctx) rhs
                where s' = (hasType s (p, instWithUnPat pctx lhs))
            _ -> error "internal: Too many arguments to pi type"

hasType :: (?ctx :: TermContext)
        => UnifyState
        -> (Un.Pat InaccessibleIndex, UnifyTerm)
        -> UnifyState
hasType _ (Un.PVar (PosPair _ Left{}), _) = internalError "Did not clear unused var"
hasType s (Un.PVar (PosPair _ (Right i)), tp) =
  bindPatVarType i tp s
hasType s (Un.PTuple _ pl, tp) =
  case tp of
    UTupleType tpl -> foldl' hasType s (zip pl tpl)
    _ -> error "internal: Could not match tuple pattern"
hasType s (Un.PRecord _ pm, tp) =
  case tp of
    URecordType tpm -> foldl' hasType s elts
      where elts = Map.elems (Map.fromList pm) `zip` Map.elems tpm
    _ -> error "internal: Could not match record pattern"
hasType s (Un.PCtor sym pl, tp) = instPiType cont pl (ctorType c) s
 where Just (Left c) = findCon ?ctx (val sym)
       cont ltp = addTermEq ltp tp
hasType s (Un.PInaccessible _, _) = s

unifyTerms :: UnifyTerm -> UnifyTerm -> UnifyState -> UnifyState
unifyTerms (ULambda _ lx ly) (ULambda _ rx ry) s =
  addTermEqs [(lx,rx), (ly,ry)] s
unifyTerms (UApp lx ly) (UApp rx ry) s =
  addTermEqs [(lx,rx), (ly,ry)] s
unifyTerms (UPi _ lx ly) (UPi _ rx ry) s =
  addTermEqs [(lx, rx), (ly, ry)] s

unifyTerms (UTupleValue l) (UTupleValue r) s = addTermEqs (zip l r) s
unifyTerms (UTupleType l) (UTupleType r) s = addTermEqs (zip l r) s

unifyTerms (URecordValue l) (URecordValue r) s =
  assert (Map.keys l == Map.keys r) $
    addTermEqs (Map.elems l `zip` Map.elems r) s
unifyTerms (URecordSelector l lf) (URecordSelector r rf) s =
  assert (lf == rf) $ unifyTerms l r s
unifyTerms (URecordType l) (URecordType r) s =
  assert (Map.keys l == Map.keys r) $
    addTermEqs (Map.elems l `zip` Map.elems r) s

unifyTerms (UCtorApp lc l) (UCtorApp rc r) s =
  assert (lc == rc) $
    addTermEqs  (l `zip` r) s
unifyTerms (UDataType ld l) (UDataType rd r) s =
  assert (ld == rd) $
    addTermEqs (l `zip` r) s
unifyTerms (UArray _ltp l) (UArray _rtp r) s =
  addTermEqs (V.toList (l `V.zip` r)) s
unifyTerms (UInaccessible i) y s = bindVar i y s
unifyTerms x (UInaccessible j) s = bindVar j x s

unifyTerms x y s | x == y = s
                 | otherwise = internalError $ "unifyTerms failed " ++ show (x,y)

unifyCns :: UnifyState -> UnifyState
unifyCns initCtx =
  case popTermEq initCtx of
    Nothing -> initCtx
    Just (x,y,s) -> unifyCns (unifyTerms x y s)

mapSnd :: (b -> c) -> (a,b) -> (a,c)
mapSnd f (a,b) = (a,f b) 

addUnPatIdents :: Set Ident -> Un.Pat a -> Set Ident
addUnPatIdents s pat =
  case pat of
    Un.PVar (PosPair _ (Right sym)) -> Set.insert sym s
    Un.PTuple _ pl -> foldl' addUnPatIdents s pl
    Un.PRecord _ fpl -> foldl' addUnPatIdents s (snd <$> fpl)
    Un.PCtor _ pl -> foldl' addUnPatIdents s pl
    _ -> s

indexUnPat :: InaccessibleIndex -> Un.Pat a -> (InaccessibleIndex,Un.Pat InaccessibleIndex)
indexUnPat i pat =
  case pat of
    Un.PVar (PosPair _ (Left _)) -> (i+1, Un.PInaccessible i)
    Un.PVar psym@(PosPair _ Right{}) -> (i,Un.PVar psym)
    Un.PTuple p pl   -> mapSnd (Un.PTuple p)   $ mapAccumL indexUnPat i pl
    Un.PRecord p fpl -> mapSnd (Un.PRecord p . zip fl) $ mapAccumL indexUnPat i pl
      where (fl,pl) = unzip fpl 
    Un.PCtor psym pl -> mapSnd (Un.PCtor psym) $ mapAccumL indexUnPat i pl
    Un.PInaccessible _ -> (i+1, Un.PInaccessible i)
    
-- | Insert vars bound by patterns into context.
consPatVars :: TermContext
            -> [Un.Pat Un.Term]
            -> Term
            -> TermContext
consPatVars tc pl tp = addVarBindings (unifyCns s) tc
 where (cnt,pl') = mapAccumL indexUnPat 0 pl
       s = let ?ctx = tc in instPiType (\_ -> id) pl' tp si
       vs = foldl' addUnPatIdents Set.empty pl'
       si = emptyUnifyState vs cnt

-- | Return the number of bound variables in the pattern.
patBoundVarCount :: Pat Term -> DeBruijnIndex
patBoundVarCount p =
  case p of
    PVar{}    -> 1
    PCtor _ m -> sum (patBoundVarCount <$> m)
    PTuple  l -> sum (patBoundVarCount <$> l)
    PRecord m -> sum (patBoundVarCount <$> m)
    PInaccessible{} -> 0


varIndex :: TermContext -> Ident -> Term
varIndex tc i = 
  case Map.lookup i (tcMap tc) of
    Nothing -> error $ "Failed to find identifier " ++ show i ++ " in context."
    Just (Left (lvl,t)) -> Term $ LocalVar idx (incVars 0 idx t)
      where idx = tcDeBruijnLevel tc - lvl - 1
    Just (Right d) -> Term $ GlobalDef d

convertTerm :: TermContext -> Un.Term -> Term
convertTerm ctx (Un.asApp -> (Un.Con i, uargs)) = Term (fn args)
 where fn = case findCon ctx (val i) of
              Just (Left c)   -> CtorValue c
              Just (Right dt) -> CtorType dt
              Nothing -> error $ "Failed to find constructor for " ++ show i ++ "."
       args = convertTerm ctx <$> uargs
convertTerm ctx uut =
  case uut of
    Un.Var i -> varIndex ctx (val i)
    Un.Con _ -> error "internal: Unexpected constructor"
    Un.Sort _ s -> Term (Sort s)
    Un.Lambda _ args f -> procArgs ctx args
      where procArgs lctx [] = convertTerm lctx f 
            procArgs lctx ((_,i,ut):l) = Term (Lambda i t r)
              where t = convertTerm lctx ut
                    r = procArgs (consLocalVar lctx i t) l
    Un.App f _ t -> Term $ App (convertTerm ctx f) (convertTerm ctx t)
    Un.Pi _ idl ut _ f -> procId ctx idl $! convertTerm ctx ut
      where procId lctx [] _ = convertTerm lctx f
            procId lctx (i:l) !t = Term (Pi (val i) t r)
             where lctx' = consLocalVar lctx (val i) t
                   r = seq lctx' $ procId lctx' l (incVars 0 1 t)
    Un.TupleValue _ tl -> Term $ TupleValue (convertTerm ctx <$> tl)
    Un.TupleType _ tl -> Term $ TupleType (convertTerm ctx <$> tl)
    Un.RecordValue _ fl -> Term $ RecordValue (Map.fromList (fieldFn <$> fl))
      where fieldFn (pf,t) = (val pf, convertTerm ctx t)
    Un.RecordSelector t i -> Term $ RecordSelector (convertTerm ctx t) (val i)
    Un.RecordType _ fl -> Term $ RecordType (Map.fromList (fieldFn <$> fl))
      where fieldFn (pf,t) = (val pf, convertTerm ctx t)
    Un.TypeConstraint t _ _ -> convertTerm ctx t
    Un.Paren _ t -> convertTerm ctx t
    Un.LetTerm _ udl ut -> Term $ Let (mkDef <$> dl) t
      where ctx' = insertLocalDefs ctx dl
            t = convertTerm ctx' ut
            lookupEqs = declEqs ctx' udl
            mkDef (i,tp) = Def { defIdent = i
                               , defType = tp
                               , defEqs = lookupEqs i
                               }
            convertDecl (Un.TypeDecl idl utp) = (\i -> (val i,tp)) <$> idl 
              where tp = convertTerm ctx utp
            convertDecl Un.TermDef{} = []
            convertDecl Un.DataDecl{} = error "Unexpected data declaration in let binding"
            dl = concatMap convertDecl udl
    Un.IntLit _ i -> Term $ IntLit i
    Un.BadTerm p -> error $ "Encountered bad term from position " ++ show p

-- | Convert term with context already extended.
convertPat :: TermContext -> Un.Pat Un.Term -> Pat Term
convertPat ctx p = 
  case p of
    Un.PVar (PosPair _ (Right i)) -> PVar i
    Un.PVar (PosPair _ Left{}) -> PInaccessible
    Un.PCtor i l -> PCtor c (convertPat ctx <$> l)
      where Just (Left c) = findCon ctx (val i)
    Un.PTuple _ l -> PTuple (convertPat ctx <$> l)
    Un.PRecord _ l -> PRecord (Map.fromList (fn <$> l))
      where fn (i,q) = (val i,convertPat ctx q)
    Un.PInaccessible t -> PInaccessible -- (convertTerm ctx t)
