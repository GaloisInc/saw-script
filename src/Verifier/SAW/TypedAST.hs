{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ViewPatterns #-}
module Verifier.SAW.TypedAST
 ( Un.Ident, Un.mkIdent, Un.unusedIdent
 , Un.ParamType(..)
 , LambdaVar
 , FieldName
 , DeBruijnIndex
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
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Vector (Vector)
import qualified Data.Vector as V
import Text.PrettyPrint.HughesPJ


import Prelude hiding (concatMap, sum)

import Verifier.SAW.UntypedAST (Ident, FieldName, Sort, val)
import qualified Verifier.SAW.UntypedAST as Un

type LambdaVar e = (Un.ParamType, Ident, e)

-- The TermF representation requires that record and field expressions contain
-- the arguments to the record and a term for applying the field to.  Both of
-- these decisions were made so that terms have a well-specified type, and we do
-- not need to be concerned about record subtyping.

type DeBruijnIndex = Integer

-- Patterns are used to match equations.
data Pat e = -- | Variable and associated identifier. 
             -- Variables are indexed in order they appear.
             PVar Ident
           | PTuple [Pat e]
           | PRecord (Map FieldName (Pat e))
             -- An arbitrary term that matches anything, but needs to be later
             -- verified to be equivalent.
           | PCtor Ctor [Pat e]
           | PInaccessible e
  deriving (Eq,Ord, Functor)

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
data Def = Def { defIdent :: Ident
               , defType :: Term
               , defEqs :: [DefEqn Term]
               }

instance Eq Def where
  (==) = lift2 defIdent (==)

instance Ord Def where
  compare = lift2 defIdent compare  

data DefEqn e
  = DefEqn [Pat e]  -- ^ List of patterns
           e -- ^ Right hand side.

data Ctor = Ctor { ctorIdent :: !Ident
                   -- | The type of the constructor (should contain no free variables).
                 , ctorType :: Term
                 }

instance Eq Ctor where
  (==) = lift2 ctorIdent (==)

instance Ord Ctor where
  compare = lift2 ctorIdent compare

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
  = LocalVar !DeBruijnIndex e -- ^ Local variables are referenced by deBrujin index, and the type.
  | GlobalDef Def           -- ^ Global variables are referenced by label.

  | Lambda Ident e e
  | App e e
  | Pi Ident e e

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
  | Let [Def] e

    -- Primitive builtin values
  | IntLit Integer
    -- | Array value includes type of elements followed by elements.
  | ArrayValue e (Vector e)
 deriving (Eq,Ord)

ppIdent :: Ident -> Doc
ppIdent i = text (show i)

doublecolon :: Doc
doublecolon = colon <> colon

ppDef :: LocalVarDoc -> Def -> Doc
ppDef lcls d = vcat (typeDoc : (ppEq <$> defEqs d))
  where sym = ppIdent (defIdent d)
        typeDoc = sym <+> doublecolon <+> ppTerm lcls 1 (defType d)
        ppEq (DefEqn pats rhs) = lhs <+> equals <+> ppTerm lcls' 1 rhs
          where lcls' = foldl' consBinding lcls (concatMap patBoundVars pats) 
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
    PInaccessible t -> sp 10 $ char '.' <> f lcls 10 t 
 where sp l d = if p >= l then parens d else d

commaSepList :: [Doc] -> Doc
commaSepList [] = empty
commaSepList [d] = d
commaSepList (d:l) = d <> comma <+> commaSepList l


maybeParens :: Bool -> Doc -> Doc
maybeParens True  d = parens d
maybeParens False d = d

data LocalVarDoc = LVD { docMap :: !(Map Integer Doc)
                       , docLvl :: !Integer
                       , docUsedMap :: Map Ident Integer
                       }

emptyLocalVarDoc :: LocalVarDoc
emptyLocalVarDoc = LVD { docMap = Map.empty
                       , docLvl = 0
                       , docUsedMap = Map.empty
                       }

consBinding :: LocalVarDoc -> Ident -> LocalVarDoc
consBinding lvd i = LVD { docMap = Map.insert lvl (ppIdent i) m          
                        , docLvl = lvl + 1
                        , docUsedMap = Map.insert i lvl (docUsedMap lvd)
                        }
 where lvl = docLvl lvd
       m = case Map.lookup i (docUsedMap lvd) of
             Just pl -> Map.delete pl (docMap lvd)
             Nothing -> docMap lvd

lookupDoc :: LocalVarDoc -> Integer -> Doc
lookupDoc lvd i =
  let lvl = docLvl lvd - i - 1
   in case Map.lookup lvl (docMap lvd) of
        Just d -> d
        Nothing -> char '!' <> integer i

-- | @ppTermF@ pretty prints term functros.
ppTermF :: TermPrinter e -- ^ Pretty printer for elements.
        -> TermPrinter (TermF e)
ppTermF f lcls p tf = do
  let sp l d = maybeParens (p >= l) d
  case tf of
    LocalVar i _ -> lookupDoc lcls i
    GlobalDef d -> ppIdent $ defIdent d
    Lambda i tp rhs -> sp 1 $ text "\\" <> lhs <+> text "->" <+> f lcls' 2 rhs
      where lhs = parens (ppIdent i <> doublecolon <> f lcls 1 tp)
            lcls' = consBinding lcls i
    App t u -> sp 10 (f lcls 10 t <+> f lcls 10 u)
    Pi i tp rhs -> lhs <+> text "->" <+> f lcls' 2 rhs
      where lhs | i == Un.unusedIdent = f lcls 2 tp
                | otherwise = parens (ppIdent i <> doublecolon <> f lcls 1 tp)
            lcls' = consBinding lcls i
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
      where lcls' = foldl' consBinding lcls (defIdent <$> dl)
    IntLit i -> integer i
    ArrayValue _ vl -> brackets (commaSepList (f lcls 1 <$> V.toList vl))

data Term = Term (TermF Term)
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
  where goList _ []  = []
        goList l (e:r) = go l e : goList (l+1) r
        goPat l p = 
          case p of
            PVar{} -> p
            PCtor c pl -> PCtor c (goPat l <$> pl)
            PTuple pl -> PTuple (goPat l <$> pl)
            PRecord m -> PRecord (goPat l <$> m)
            PInaccessible t -> PInaccessible (go l t)
        go :: Integer -> Term -> Term
        go l t@(Term tf) =
          case tf of
            LocalVar i tp
              | i >= l -> Term $ LocalVar (i+j) (go l tp)
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
              where l' = l + toInteger (length defs)
                    procDef d = Def { defIdent = defIdent d
                                    , defType = go l (defType d)
                                    , defEqs = procEq <$> defEqs d
                                    }
                    procEq (DefEqn pats rhs) = DefEqn pats' (go eql rhs)
                      where eql = l' + sum (patBoundVarCount <$> pats)
                            pats' = goPat eql <$> pats
            _ -> t

-- | @termApp t u@ returns the term obtained by replacing var 0 in @t@
-- with @u@.
{-
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
                | DefDecl Def
 
data Module = Module {
          moduleTypeMap :: !(Map Ident DataType)
        , moduleCtorMap :: !(Map Ident Ctor)
        , moduleDefMap  :: !(Map Ident Def)
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

findDef :: Module -> Ident -> Maybe Def
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

insDef :: Module -> Def -> Module
insDef m d = m { moduleDefMap = Map.insert (defIdent d) d (moduleDefMap m)
               , moduleDecls = DefDecl d : moduleDecls m
               }

declEqs :: TermContext -> [Un.Decl] -> (Ident -> [DefEqn Term])
declEqs ctx d = \i -> fromMaybe [] $ Map.lookup i eqMap
  where insertEq m (Un.TermDef i lhs rhs) = Map.insertWith (++) (val i) v m
          where Just (Right dt) = findCon ctx (val i) 
                ctx' = consPatVars ctx (snd <$> lhs) (dtType dt)
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

type DeBruijnLevel = Integer

data TermContext = TermContext {
         tcDeBruijnLevel :: DeBruijnLevel
       , tcMap :: Map Ident (Either (DeBruijnLevel,Term) Def) 
       , tcDataDecls :: Map Ident (Either Ctor DataType)
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
consLocalVar :: TermContext -> Ident -> Term -> TermContext
consLocalVar tc i tp = tc { tcDeBruijnLevel = lvl + 1
                          , tcMap = Map.insert i (Left (lvl,tp)) (tcMap tc)
                          }
  where lvl = tcDeBruijnLevel tc

{-
data UnifyTerm
  = UApp UnifyTerm UnifyTerm
  | URigidVar Ident -- ^ Rigid variable that cannot be instantiated.
  | UFlexVar Ident  -- ^ Flexible variable that can.
  | UTupleValue [UnifyTerm]
  | URecordValue (Map FieldName UnifyTerm)
  | UCtorValue Ctor [UnifyTerm]
  | UPi Ident UnifyTerm UnifyTerm
  | UInaccessible

data UnifyCns = HasType UnifyTerm UnifyTerm

type UnifyContext = TermContext

untermUnifyTerm :: (?uctx :: UnifyContext) => Un.Term -> UnifyTerm
untermUnifyTerm = undefined

patUnifyTerm :: (?uctx :: UnifyContext) => Un.Pat -> UnifyTerm
patUnifyTerm (Un.PVar i)     = URigidVar (val i)
patUnifyTerm (Un.PTuple _ pl)  = UTupleValue (patUnifyTerm <$> pl)
patUnifyTerm (Un.PRecord _ pm) = URecordValue $
  Map.fromList [  (val f, patUnifyTerm t) | (f, t) <-  pm]
patUnifyTerm (Un.PCtor c pl) = UCtorValue (undefined c) (patUnifyTerm <$> pl)
patUnifyTerm (Un.PInaccessible _t) = UInaccessible

instFlexVar :: UnifyTerm -> Ident -> UnifyTerm -> UnifyTerm
instFlexVar root s u = go root
  where go (UFlexVar v) | s == v = u
        go (UApp x y) = UApp (go x) (go y)
        go (UTupleValue l) = UTupleValue (go <$> l)
        go (URecordValue m) = URecordValue (go <$> m)
        go (UCtorValue c l) = UCtorValue c (go <$> l)
        go (UPi v x y) | v /= s = UPi v (go x) (go y)
        go x = x

-- | Build constraints for mapping a set of types.
depPatCns :: (?uctx :: UnifyContext) => [UnifyTerm] -> UnifyTerm -> [UnifyCns]
depPatCns [] _ = []
depPatCns (p:pl) (UPi sym x y) = HasType p x : depPatCns pl (instFlexVar y sym p)

unify :: TermContext [UnifyCns] -> UnifyContext -> [(Un.Pat, Term)] -> UnifyContext
-}


{-

c :: (x1 : T1) -> ... (xn : Tn) -> D u1 .. umX
c t1 ... tn : D v1 .. vm
-}

{-
insertNPatVars :: (TermContext,[Term]) -> [Un.Pat] -> [Term] -> (TermContext,[Term])
insertNPatVars rprev [] [] = rprev
insertNPatVars (ctx,rprev) (p:pl) (tp:tpl) =
  case p of
    Un.PVar i -> insertNPatVars (consVarList (ctx,rprev) i tp) pl (incVars 0 1 <$> tpl)
    Un.PCtor c l -> 

procPat :: TermContext -> Un.Pat -> Term -> (TermContext,Term)
procPat ctx (Un.PVar i) tp = (consLocalVar ctx i tp, Term (LocalVar 0 tp))
procPat ctx (Un.PCtor c l) tp = (ctx', val)
  where (ctx',rprev') = insertPatVars (ctx,[]) l (ctorType c)
        val = Term (CtorValue c (reverse rprev'))
procPat ctx (Un.PTuple _ l) (Term (TupleType ltp)) = (ctx',val)
  where (ctx',rprev') = insertNPatVars (ctx,[]) l ltp
        val = Term (TupleValue (reverse rprev'))
procPat ctx (Un.PRecord _ m) tp = undefined m
procPat ctx (Un.PInaccessible t) tp = (ctx, undefined t)

-- | Insert vars bound by patterns into context.
insertPatVars :: (TermContext, Maybe [Term])
              -> [Un.Pat]
              -> Term
              -> (TermContext, Maybe [Term])
insertPatVars rprev [] _tp = rprev
insertPatVars (ctx,rprev) tp (p:pl) tp = do
  let handleRest = insertPatVars (ctx', rprev'') pl tp'
  case p of
    Un.PVar i -> handleRest
    Un.PCtor c l -> handleRest
    Un.PTuple _ l -> handleRest
    Un.PRecord _ _ -> undefined
    Un.PInaccessible{} -> undefined
 where Term (Pi pisym lhs rhs) = tp
       (ctx', val) = procPat ctx p lhs
       cnt = tcDebruijnLevel ctx' - tcDebruijnLevel ctx
       tp' = termApp (incVars 1 cnt rhs) val
       rprev'' = val : fmap (incVars 0 cnt) rprev
-}

-- | Insert vars bound by patterns into context.
consPatVars :: TermContext
            -> [Un.Pat]
            -> Term
            -> TermContext
consPatVars = undefined

-- | Return the number of bound variables in the pattern.
patBoundVarCount :: Pat Term -> Integer
patBoundVarCount p =
  case p of
    PVar{}    -> 1
    PCtor _ m -> sum (patBoundVarCount <$> m)
    PTuple  l -> sum (patBoundVarCount <$> l)
    PRecord m -> sum (patBoundVarCount <$> m)
    PInaccessible{} -> 0

-- | Insert local definitions the terms belong to the given context.
insertLocalDefs :: TermContext -> [(Ident,Term)] -> TermContext
insertLocalDefs = go 0
  where go _ tc [] = tc
        go i tc ((sym,tp):r) = go (i+1) tc' r
          where tc' = consLocalVar tc sym (incVars 0 i tp)

-- | Returns constructor or data type associated with given identifier.
-- Calls error if attempt to find constructor failed.
findCon :: TermContext -> Ident -> Maybe (Either Ctor DataType)
findCon tc i = Map.lookup i (tcDataDecls tc)

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
    Un.Pi _ idl ut _ f -> procId ctx idl (convertTerm ctx ut)
      where procId lctx []    _ = convertTerm lctx f
            procId lctx (i:l) t = Term (Pi (val i) t r)
              where r = procId (consLocalVar lctx (val i) t) l (incVars 0 1 t)
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
convertPat :: TermContext -> Un.Pat -> Pat Term
convertPat ctx p = 
  case p of
    Un.PVar i -> PVar (val i)
    Un.PCtor i l -> PCtor c (convertPat ctx <$> l)
      where Just (Left c) = findCon ctx (val i)
    Un.PTuple _ l -> PTuple (convertPat ctx <$> l)
    Un.PRecord _ l -> PRecord (Map.fromList (fn <$> l))
      where fn (i,q) = (val i,convertPat ctx q)
    Un.PInaccessible t -> PInaccessible (convertTerm ctx t)