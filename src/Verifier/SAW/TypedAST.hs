{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- |
Module      : Verifier.SAW.TypedAST
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.TypedAST
 ( -- * Module operations.
   Module
 , emptyModule
 , ModuleName, mkModuleName
 , moduleName
 , preludeName
 , ModuleDecl(..)
 , moduleDecls
 , allModuleDecls
 , TypedDataType
 , moduleDataTypes
 , moduleImports
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
 , moduleActualDefs
 , allModuleActualDefs
 , modulePrimitives
 , allModulePrimitives
 , moduleAxioms
 , allModuleAxioms
   -- * Data types and definitions.
 , DataType(..)
 , Ctor(..)
 , GenericDef(..)
 , Def
 , DefQualifier(..)
 , LocalDef
 , localVarNames
 , DefEqn(..)
 , Pat(..)
 , patBoundVarCount
 , patUnusedVarCount
   -- * Terms and associated operations.
 , Term(..)
 , incVarsTerm
 , piArgCount
 , TermF(..)
 , FlatTermF(..)
 , Termlike(..)
 , zipWithFlatTermF
 , freesTerm
 , freesTermF
 , termToPat

 , LocalVarDoc
 , emptyLocalVarDoc
 , docShowLocalNames
 , docShowLocalTypes

 , TermPrinter
 , TermDoc(..)
 , PPOpts(..)
 , defaultPPOpts
 , ppTermDoc
 , Prec(..)
 , ppAppParens
 , ppTerm
 , ppTermF
 , ppTermF'
 , ppFlatTermF
 , ppFlatTermF'
 , ppRecordF
 , ppTermDepth
   -- * Primitive types.
 , Sort, mkSort, sortOf, maxSort
 , Ident(identModule, identName), mkIdent
 , parseIdent
 , isIdent
 , ppIdent
 , ppDef
 , ppDefEqn
 , DeBruijnIndex
 , FieldName
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
#if !MIN_VERSION_base(4,8,0)
import Data.Foldable (Foldable)
#endif
import Data.Foldable (foldl', sum)
import Data.Map (Map)
import qualified Data.Map as Map
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as Leijen ((<$>))

import Prelude hiding (all, foldr, sum)

import Verifier.SAW.Utils (internalError)
import qualified Verifier.SAW.TermNet as Net
import Verifier.SAW.Term.Functor
import Verifier.SAW.Term.Pretty

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

instance Net.Pattern Term where
  toPat = termToPat

ppDef :: PPOpts -> LocalVarDoc -> Def Term -> Doc
ppDef opts lcls d = vcat (tpd : (ppDefEqn (ppTerm opts) lcls sym <$> (reverse $ defEqs d)))
  where sym = ppIdent (defIdent d)
        tpd = ppTypeConstraint (ppTerm opts) lcls sym (defType d) <> semi

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

freesTerm :: Term -> BitSet
freesTerm (Term t) = freesTermF (fmap freesTerm t)

-- | @instantiateVars f l t@ substitutes each dangling bound variable
-- @LocalVar j t@ with the term @f i j t@, where @i@ is the number of
-- binders surrounding @LocalVar j t@.
instantiateVars :: (DeBruijnIndex -> DeBruijnIndex -> Term)
                -> DeBruijnIndex -> Term -> Term
instantiateVars f initialLevel = go initialLevel
  where go :: DeBruijnIndex -> Term -> Term
        go l (Term tf) =
          case tf of
            FTermF ftf      -> Term $ FTermF $ fmap (go l) ftf
            App x y         -> Term $ App (go l x) (go l y)
            Constant _ _rhs _ -> Term tf -- assume rhs is a closed term, so leave it unchanged
            Lambda i tp rhs -> Term $ Lambda i (go l tp) (go (l+1) rhs)
            Pi i lhs rhs    -> Term $ Pi i (go l lhs) (go (l+1) rhs)
            Let defs r      -> Term $ Let (procDef <$> defs) (go l' r)
              where l' = l + length defs
                    procDef (Def sym qual tp eqs) = Def sym qual tp' eqs'
                      where tp' = go l tp
                            eqs' = procEq <$> eqs
                    procEq (DefEqn pats rhs) = DefEqn pats (go eql rhs)
                      where eql = l' + sum (patBoundVarCount <$> pats)
            LocalVar i
              | i < l -> Term $ LocalVar i
              | otherwise -> f l i

-- | @incVars j k t@ increments free variables at least @j@ by @k@.
-- e.g., incVars 1 2 (C ?0 ?1) = C ?0 ?3
incVarsTerm :: DeBruijnIndex -> DeBruijnIndex -> Term -> Term
incVarsTerm _ 0 = id
incVarsTerm initialLevel j = assert (j > 0) $ instantiateVars fn initialLevel
  where fn _ i = Term $ LocalVar (i+j)

-- | Pretty print a term with the given outer precedence.
ppTerm :: PPOpts -> TermPrinter Term
ppTerm opts lcls0 p0 trm = ppTermDoc (pp lcls0 p0 trm)
  where
    pp :: LocalVarDoc -> Prec -> Term -> TermDoc
    pp lcls p (Term t) = ppTermF opts pp lcls p t

ppTermDepth :: forall t. Termlike t => PPOpts -> Int -> t -> Doc
ppTermDepth opts d0 = pp d0 emptyLocalVarDoc PrecNone
  where
    pp :: Int -> TermPrinter t
    pp d lcls p t = ppTermDoc (pp' d lcls p t)

    pp' :: Int -> LocalVarDoc -> Prec -> t -> TermDoc
    pp' 0 _ _ _ = TermDoc $ text "_"
    pp' d lcls p t = case unwrapTermF t of
      App t1 t2 -> TermDoc $
        ppAppParens p $ group $ hang 2 $
        (pp d lcls PrecApp t1) Leijen.<$>
        (pp (d-1) lcls PrecArg t2)
      tf ->
        ppTermF opts (pp' (d-1)) lcls p tf

instance Show Term where
  showsPrec _ t = shows $ ppTerm defaultPPOpts emptyLocalVarDoc PrecNone t

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
  show m = flip displayS "" $ renderPretty 0.8 80 $
             vcat $ concat $ fmap (map (<> line)) $
                   [ fmap ppImport (Map.keys (m^.moduleImports))
                   , fmap ppdecl   (moduleRDecls m)
                   ]
    where ppImport nm = text $ "import " ++ show nm
          ppdecl (TypeDecl d) = ppDataType (ppTerm defaultPPOpts) d
          ppdecl (DefDecl d) = ppDef defaultPPOpts emptyLocalVarDoc d

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

allModuleDecls :: Module -> [ModuleDecl]
allModuleDecls m = concatMap moduleDecls (m : Map.elems (m^.moduleImports))

modulePrimitives :: Module -> [TypedDef]
modulePrimitives m =
    [ def
    | DefDecl def <- moduleDecls m
    , defQualifier def == PrimQualifier
    ]

moduleAxioms :: Module -> [TypedDef]
moduleAxioms m =
    [ def
    | DefDecl def <- moduleDecls m
    , defQualifier def == AxiomQualifier
    ]

moduleActualDefs :: Module -> [TypedDef]
moduleActualDefs m =
    [ def
    | DefDecl def <- moduleDecls m
    , defQualifier def == NoQualifier
    ]

allModulePrimitives :: Module -> [TypedDef]
allModulePrimitives m =
    [ def
    | DefDecl def <- allModuleDecls m
    , defQualifier def == PrimQualifier
    ]

allModuleAxioms :: Module -> [TypedDef]
allModuleAxioms m =
    [ def
    | DefDecl def <- allModuleDecls m
    , defQualifier def == AxiomQualifier
    ]

allModuleActualDefs :: Module -> [TypedDef]
allModuleActualDefs m =
    [ def
    | DefDecl def <- allModuleDecls m
    , defQualifier def == NoQualifier
    ]
