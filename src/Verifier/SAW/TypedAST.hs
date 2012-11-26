{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ViewPatterns #-}
module Verifier.SAW.TypedAST
 ( Un.Ident, Un.mkIdent, Un.unusedIdent
 , Un.ParamType(..)
 , LambdaVar
 , FieldName
 , TermF(..)
 , Term(..)
-- , PosPair(..)
-- , GroupError(..)
 , Module
 , unsafeMkModule
-- , TCError(..)
-- , tcDefs
 ) where

import Control.Applicative ((<$>))
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Vector (Vector)
import qualified Data.Vector as V
import Text.PrettyPrint.HughesPJ

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
           | PCtor Ident [Pat e]
           | PTuple [Pat e]
           | PRecord (Map FieldName (Pat e))
             -- An arbitrary term that matches anything, but needs to be later
             -- verified to be equivalent.
           | PInaccessible e
  deriving (Eq,Ord, Functor, Show)

patBoundVars :: Pat e -> [Ident]
patBoundVars p =
  case p of
    PVar i -> [i]
    PCtor _ l -> concatMap patBoundVars l
    PTuple l -> concatMap patBoundVars l
    PRecord m -> concatMap patBoundVars (Map.elems m)
    PInaccessible{} -> []

unPatBoundVars :: Un.Pat -> [Ident]
unPatBoundVars p =
  case p of
    Un.PVar i -> [val i]
    Un.PCtor _ l -> concatMap unPatBoundVars l
    Un.PTuple _ l  -> concatMap unPatBoundVars l
    Un.PRecord _ m -> concatMap unPatBoundVars (snd <$> m)
    Un.PInaccessible _ -> []

lift2 :: (a -> b) -> (b -> b -> c) -> a -> a -> c
lift2 f h x y = h (f x) (f y) 


-- A Definition contains an identifier, the type of the definition, and a list of equations.
data Def e = Def { defIdent :: Ident
                 , defType :: e
                 , defEqs :: [DefEqn e]
                 }

instance Eq (Def e) where
  (==) = lift2 defIdent (==)

instance Ord (Def e) where
  compare = lift2 defIdent compare  

data DefEqn e
  = DefEqn [Pat e]  -- ^ List of patterns
           e -- ^ Right hand side.

data Ctor = Ctor { ctorIdent :: Ident
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
  = LocalVar !DeBruijnIndex -- ^ Local variables are referenced by deBrujin index.
  | GlobalDef (Def Term)  -- ^ Global variables are referenced by label.

  | Lambda (Pat e) e e
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
  | Let [Def e] e

    -- Primitive builtin values
  | IntLit Integer
  | ArrayValue (Vector e)
 deriving (Eq,Ord)

ppIdent :: Ident -> Doc
ppIdent i = text (show i)

doublecolon :: Doc
doublecolon = colon <> colon

ppDef :: TermPrinter e -> LocalVarDoc -> Def e -> Doc
ppDef f lcls d = vcat (typeDoc : (ppEq <$> defEqs d))
  where sym = ppIdent (defIdent d)
        typeDoc = sym <+> doublecolon <+> f emptyLocalVarDoc 1 (defType d)
        ppEq (DefEqn pats rhs) = lhs <+> equals <+> f lcls' 1 rhs
          where lcls' = foldl' consBinding lcls (concatMap patBoundVars pats) 
                lhs = sym <+> hsep (ppPat f lcls 10 <$> pats)

-- | Print a list of items separated by semicolons
semiTermList :: [Doc] -> Doc
semiTermList = hsep . fmap (<> semi)

type TermPrinter e = LocalVarDoc -> Int -> e -> Doc

ppPat :: TermPrinter e -> TermPrinter (Pat e)
ppPat f lcls p pat = 
  case pat of
    PVar i -> ppIdent i
    PCtor i pl -> sp 10 $ ppIdent i <+> hsep (ppPat f lcls 10 <$> pl)
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
    LocalVar i -> lookupDoc lcls i
    GlobalDef d -> ppIdent $ defIdent d
    Lambda pat tp rhs -> sp 1 $ text "\\" <> lhs <+> text "->" <+> f lcls' 2 rhs
      where lhs = parens (ppPat f lcls' 2 pat <> doublecolon <> f lcls 1 tp)
            lcls' = foldl' consBinding lcls (patBoundVars pat)
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
    Let dl t -> text "let" <+> vcat (ppDef f lcls' <$> dl) $$
                text " in" <+> f lcls' 0 t
      where lcls' = foldl' consBinding lcls (defIdent <$> dl)
    IntLit i -> integer i
    ArrayValue vl -> brackets (commaSepList (f lcls 1 <$> V.toList vl))

data Term = Term (TermF Term)
  deriving (Eq,Ord)

asApp :: Term -> (Term, [Term])
asApp = go []
  where go l (Term (App t u)) = go (u:l) t
        go l t = (t,l)

-- | Pretty print a term with the given outer precedence.
ppTerm :: TermPrinter Term
ppTerm lcls p t =
  case asApp t of
    (Term u,[]) -> pptf p u
    (Term u,l) -> maybeParens (p >= 10) $ hsep $ pptf 10 u : fmap (ppTerm lcls 10) l 
 where pptf = ppTermF ppTerm lcls
{-

ppTerm p (Term t) = ppTermF ppTerm p t
-}

instance Show Term where
  showsPrec p t = shows $ ppTerm emptyLocalVarDoc p t

data Module = Module {
          moduleTypes :: [DataType]
        , moduleDefs :: [Def Term]
        }

instance Show Module where
  show m = render $
    vcat [ vcat $ ppDataType <$> moduleTypes m
         , vcat $ ppd <$> moduleDefs m
         ]
   where ppd d = ppDef ppTerm emptyLocalVarDoc d <> char '\n'

emptyModule :: Module
emptyModule = Module { moduleTypes = [], moduleDefs = [] }

insDef :: Module -> Def Term -> Module
insDef m d = m { moduleDefs = moduleDefs m ++ [d] }

insDataType :: Module -> DataType -> Module
insDataType m tp = m { moduleTypes = tp:moduleTypes m } 

{-
data GroupError
 = PrevDefined Pos Ident -- ^ Identifier and old p
osition.
 | NoSignature Ident -- ^ Identifier is missing signature.
 | DuplicateDef Ident Pos -- ^ Equation for defintion already appeared.
   -- ^ An internal limitation resulted in an error.
 | Limitation String
 deriving (Show)
-}

declEqs :: TermContext -> [Un.Decl] -> (Ident -> [DefEqn Term])
declEqs ctx d = \i -> fromMaybe [] $ Map.lookup i eqMap
  where insertEq m (Un.TermDef i lhs rhs) = Map.insertWith (++) (val i) v m
          where ctx' = insertLocalVars ctx (concatMap unPatBoundVars (snd <$> lhs))
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

{-
type UnEqn = (Pos, [Un.Pat], Un.Term)

-- Extract equations for identifier an return them along with remaining equations.
gatherEqs :: Ident -> [Un.Decl] -> ([UnEqn], [Un.Decl])
gatherEqs i = go []
  where go eqs (Un.TermDef (PosPair p j) lhs rhs : decls)
          | i == j = go ((p,snd <$> lhs,rhs):eqs) decls
        go eqs decls = (reverse eqs, decls)

-- Extract declarations from list of functions.
gatherManyEqs :: Set Ident -> [Un.Decl] -> (Map Ident [UnEqn], [Un.Decl])
gatherManyEqs s = go Map.empty
  where go m (Un.TermDef (PosPair p i) lhs rhs : decls)
          | Set.member i s = go (Map.insert i ((p,snd <$> lhs,rhs):feqs) m) rest
              where (feqs, rest) = gatherEqs i decls
        go m decls = (m, decls)

data GroupState = GS { gsDefs :: Map Ident (Pos, Def Term)
                     , gsErrors :: [PosPair GroupError]
                     }

type Grouper a = State GroupState a
-}

type DeBruijnLevel = Integer

data TermContext = TermContext {
         tcDeBruijnLevel :: DeBruijnLevel
       , tcMap :: Map Ident (Either DeBruijnLevel (Def Term)) 
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
         ppVar (Left l)  = "Local " ++ show l
         ppVar (Right d) = "Global " ++ show (defIdent d) 
         ppData (Left c) = "Ctor " ++ show (ctorIdent c)
         ppData (Right dt) = "ADT " ++ show (dtIdent dt)

globalContext :: Module -> TermContext
globalContext m =
    TermContext { tcDeBruijnLevel = 0
                , tcMap = Map.fromList [ (defIdent d, Right d) | d <- moduleDefs m ]
                , tcDataDecls = Map.fromList (concatMap dtFn (moduleTypes m))
                }
  where cFn c = (ctorIdent c, Left c)
        dtFn dt = (dtIdent dt, Right dt) : (cFn <$> dtCtors dt) 

insertLocalVar :: TermContext -> Ident -> TermContext
insertLocalVar tc i = tc { tcDeBruijnLevel = lvl + 1
                         , tcMap = Map.insert i (Left lvl) (tcMap tc)
                         }
  where lvl = tcDeBruijnLevel tc

insertLocalVars :: TermContext -> [Ident] -> TermContext
insertLocalVars = foldl' insertLocalVar

findCon :: TermContext -> Ident -> Either Ctor DataType
findCon tc i =
  case Map.lookup i (tcDataDecls tc) of
    Nothing -> error $ "Failed to find constructor " ++ show i
                                     ++ " in context:\n" ++ show tc
    Just v -> v 

varIndex :: TermContext -> Ident -> Either DeBruijnIndex (Def Term)
varIndex tc i = 
  case Map.lookup i (tcMap tc) of
    Nothing -> error $ "Failed to find identifier " ++ show i ++ " in context."
    Just v -> either (Left . lvlToIdx) Right v
      where lvlToIdx lvl = tcDeBruijnLevel tc - lvl - 1

convertTerm :: TermContext -> Un.Term -> Term
convertTerm ctx (Un.asApp -> (Un.Con i, uargs)) = Term (fn args)
 where fn = case findCon ctx (val i) of
              Left c   -> CtorValue c
              Right dt -> CtorType dt
       args = convertTerm ctx <$> uargs
convertTerm ctx uut =
  case uut of
    Un.Var i -> 
      Term $ case varIndex ctx (val i) of
               Left idx -> LocalVar idx
               Right d -> GlobalDef d
    Un.Con _ -> error "internal: Unexpected constructor"
    Un.Sort _ s -> Term (Sort s)
    Un.Lambda _ args f -> procArgs ctx args
      where procArgs lctx [] = convertTerm lctx f 
            procArgs lctx ((_,up,ut):l) = Term (Lambda p t r)
              where p = convertPat lctx up
                    t = convertTerm lctx ut
                    r = procArgs (insertLocalVars lctx (unPatBoundVars up)) l
    Un.App f _ t -> Term $ App (convertTerm ctx f) (convertTerm ctx t)
    Un.Pi _ idl ut _ f -> procId ctx idl
      where t = convertTerm ctx ut
            procId lctx [] = convertTerm lctx f
            procId lctx (i:l) = Term (Pi (val i) t r)
              where r = procId (insertLocalVar lctx (val i)) l
    Un.TupleValue _ tl -> Term $ TupleValue (convertTerm ctx <$> tl)
    Un.TupleType _ tl -> Term $ TupleType (convertTerm ctx <$> tl)
    Un.RecordValue _ fl -> Term $ RecordValue (Map.fromList (fieldFn <$> fl))
      where fieldFn (pf,t) = (val pf, convertTerm ctx t)
    Un.RecordSelector t i -> Term $ RecordSelector (convertTerm ctx t) (val i)
    Un.RecordType _ fl -> Term $ RecordType (Map.fromList (fieldFn <$> fl))
      where fieldFn (pf,t) = (val pf, convertTerm ctx t)
    Un.ArrayValue _ tl -> Term $ ArrayValue (convertTerm ctx <$> V.fromList tl)
    Un.Paren _ t -> convertTerm ctx t
    Un.TypeConstraint t _ _ -> convertTerm ctx t
    Un.LetTerm _ udl ut -> Term $ Let dl t
      where ctx' = insertLocalVars ctx (defIdent <$> dl)
            t = convertTerm ctx' ut
            lookupEqs = declEqs ctx' udl
            convertDecl (Un.TypeDecl idl utp) = go <$> idl 
             where tp = convertTerm ctx' utp
                   go i = Def { defIdent = val i
                              , defType = tp
                              , defEqs = lookupEqs (val i)
                              }
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
    Un.PCtor i l -> PCtor (val i) (convertPat ctx <$> l)
    Un.PTuple _ l -> PTuple (convertPat ctx <$> l)
    Un.PRecord _ l -> PRecord (Map.fromList (fn <$> l))
      where fn (i,q) = (val i,convertPat ctx q)
    Un.PInaccessible t -> PInaccessible (convertTerm ctx t)
--    Un.PTypeConstraint p _ -> convertPat ctx p

{-
-- | Collect individual untyped declarations into symbol definitions.
identifyDefs :: [Un.Decl] -> Grouper ()
identifyDefs (Un.TypeDecl idl tp: decls) = do
  let (meqs,rest) = gatherManyEqs (Set.fromList (val <$> idl)) decls
  forM_ idl $ \psym -> do
    let eqs = fromMaybe [] $ Map.lookup (val psym) meqs
    let mapEqn (_, lhsl, rhs) = DefEqn (convertPat ctx <$> lhsl) (convertTerm ctx rhs)
    addDef (pos psym)
           Def { defIdent = val psym
               , defType = convertTerm ctx tp
               , defEqs = mapEqn <$> eqs
               }
  identifyDefs rest
identifyDefs (Un.DataDecl psym tp ctors: decls) = do
  -- Add type symbol
  addDef (pos psym)
         Def { defIdent = val psym
             , defType = convertTerm ctx tp
             , defEqs = []
             }
  -- Add ctor symbols
  forM_ ctors $ \(Un.Ctor ctorId ctorTp) -> do
    addDef (pos psym)
           Def { defIdent = val ctorId
               , defType = convertTerm ctx ctorTp
               , defEqs = []
               }
  identifyDefs decls
identifyDefs (Un.TermDef psym _ _ : decls) = do
  let (_, rest) = gatherEqs (val psym) decls
  addGroupError (pos psym) (NoSignature (val psym))
  identifyDefs rest
identifyDefs [] = return ()
-}

{-
data TypeCheckerState = TCS {
                            }

type TypeChecker a = State TypeCheckerState a


execTypechecker :: TypeChecker () -> 

unexpectedBadTermession :: Pos -> a
unexpectedBadTermession p =
    error "internal: Bad expression from " ++ show p ++ " appears during typechecking"
-}

