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
 , Def(..)
 , DefQualifier(..)
 , DefEqn(..)
 , Pat(..)
 , patBoundVarCount
 , patUnusedVarCount
   -- * Terms and associated operations.
 , SimpleTerm(..)
 , incVarsSimpleTerm
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
 , ppLetBlock
 ) where

import Control.Applicative hiding (empty)
import Control.Exception (assert)
import Control.Lens
#if !MIN_VERSION_base(4,8,0)
import Data.Foldable (Foldable)
#endif
import Data.Foldable (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Prelude hiding (all, foldr)

import Verifier.SAW.Utils (internalError)
import qualified Verifier.SAW.TermNet as Net
import Verifier.SAW.Term.Functor
import Verifier.SAW.Term.Pretty

newtype SimpleTerm = SimpleTerm (TermF SimpleTerm)
  deriving (Eq)

instance Termlike SimpleTerm where
  unwrapTermF (SimpleTerm tf) = tf

instance Net.Pattern SimpleTerm where
  toPat = termToPat

ppDef :: PPOpts -> LocalVarDoc -> Def SimpleTerm -> Doc
ppDef opts lcls d = vcat (tpd : (ppDefEqn (ppTerm opts) lcls sym <$> (reverse $ defEqs d)))
  where sym = ppIdent (defIdent d)
        tpd = ppTypeConstraint (ppTerm opts) lcls sym (defType d) <> semi

{-
asApp :: Term -> (Term, [Term])
asApp = go []
  where go l (Term (FTermF (App t u))) = go (u:l) t
        go l t = (t,l)
-}

-- | Returns the number of nested pi expressions.
piArgCount :: SimpleTerm -> Int
piArgCount = go 0
  where go i (SimpleTerm (Pi _ _ rhs)) = go (i+1) rhs
        go i _ = i

freesTerm :: SimpleTerm -> BitSet
freesTerm (SimpleTerm t) = freesTermF (fmap freesTerm t)

-- | @instantiateVars f l t@ substitutes each dangling bound variable
-- @LocalVar j t@ with the term @f i j t@, where @i@ is the number of
-- binders surrounding @LocalVar j t@.
instantiateVars :: (DeBruijnIndex -> DeBruijnIndex -> SimpleTerm)
                -> DeBruijnIndex -> SimpleTerm -> SimpleTerm
instantiateVars f initialLevel = go initialLevel
  where go :: DeBruijnIndex -> SimpleTerm -> SimpleTerm
        go l (SimpleTerm tf) =
          case tf of
            FTermF ftf      -> SimpleTerm $ FTermF $ fmap (go l) ftf
            App x y         -> SimpleTerm $ App (go l x) (go l y)
            Constant{}      -> SimpleTerm tf -- assume rhs is a closed term, so leave it unchanged
            Lambda i tp rhs -> SimpleTerm $ Lambda i (go l tp) (go (l+1) rhs)
            Pi i lhs rhs    -> SimpleTerm $ Pi i (go l lhs) (go (l+1) rhs)
            LocalVar i
              | i < l -> SimpleTerm $ LocalVar i
              | otherwise -> f l i

-- | @incVars j k t@ increments free variables at least @j@ by @k@.
-- e.g., incVars 1 2 (C ?0 ?1) = C ?0 ?3
incVarsSimpleTerm :: DeBruijnIndex -> DeBruijnIndex -> SimpleTerm -> SimpleTerm
incVarsSimpleTerm _ 0 = id
incVarsSimpleTerm initialLevel j = assert (j > 0) $ instantiateVars fn initialLevel
  where fn _ i = SimpleTerm $ LocalVar (i+j)

-- | Pretty print a term with the given outer precedence.
ppTerm :: PPOpts -> TermPrinter SimpleTerm
ppTerm = ppTermlike

instance Show SimpleTerm where
  showsPrec _ t = shows $ ppTerm defaultPPOpts emptyLocalVarDoc PrecNone t

type TypedDataType = DataType Ident SimpleTerm
type TypedCtor = Ctor Ident SimpleTerm
type TypedDef = Def SimpleTerm
type TypedDefEqn = DefEqn SimpleTerm

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

insDef :: Module -> Def SimpleTerm -> Module
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
