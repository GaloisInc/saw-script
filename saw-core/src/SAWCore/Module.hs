{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : SAWCore.Module
Copyright   : Galois, Inc. 2012-2017
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Module
  ( -- * Data types and definitions.
    DefQualifier(..)
  , Def(..)
  , CtorArg(..)
  , CtorArgStruct(..)
  , Ctor(..)
  , ctorNumParams
  , ctorNumArgs
  , ctorPrimName
  , DataType(..)
  , dtNumParams
  , dtNumIndices
  , dtPrimName
    -- * Modules
  , Module
  , ModuleDecl(..)
  , ResolvedName(..)
  , resolvedNameIdent
  , resolvedNameType
  , moduleName
  , emptyModule
  , resolveName
  , resolveNameInMap
  , lookupVarIndexInMap
  , findDataType
  , insImport
  , beginDataType
  , completeDataType
  , findCtor
  , moduleDefs
  , findDef
  , moduleDecls
    -- * Module Maps
  , ModuleMap
  , emptyModuleMap
  , moduleIsLoaded
  , loadModule
  , findModule
  , findCtorInMap
  , findDataTypeInMap
  , findDefInMap
  , allModuleDefs
  , allModuleDecls
  , allModulePrimitives
  , allModuleAxioms
  , allModuleActualDefs
  , allModuleDataTypes
  , allModuleCtors
  , insDefInMap
  , insInjectCodeInMap
  , insImportInMap
  ) where

import Control.Monad (foldM)
#if !MIN_VERSION_base(4,8,0)
import Data.Foldable (Foldable)
#endif
import Data.Foldable (foldl', foldr')
import Data.Hashable
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe, fromMaybe)
import Data.Text (Text)
import GHC.Generics (Generic)

import qualified Language.Haskell.TH.Syntax as TH

import Prelude hiding (all, foldr, sum)

import SAWCore.Name hiding (resolveName)
import SAWCore.Panic (panic)
import SAWCore.Term.Functor
import SAWCore.Term.CtxTerm


-- Definitions -----------------------------------------------------------------

data DefQualifier
  = NoQualifier
  | PrimQualifier
  | AxiomQualifier
 deriving (Eq, Show, Generic, TH.Lift)

instance Hashable DefQualifier -- automatically derived

-- | A Definition contains an identifier, the type of the definition, and an
-- optional body (axioms and primitives do not have a body)
data Def =
  Def
  { defIdent :: Ident
  , defVarIndex :: VarIndex
  , defQualifier :: DefQualifier
  , defType :: Term
  , defBody :: Maybe Term
  }
  deriving (Eq, Show, Generic)

instance Hashable Def -- automatically derived


-- Constructors ----------------------------------------------------------------

-- | A specification of a constructor
data Ctor =
  forall d params ixs.
  Ctor
  { ctorName :: !Ident
    -- ^ The name of this constructor
  , ctorVarIndex :: !VarIndex
    -- ^ Unique var index for this constructor
  , ctorArgStruct :: CtorArgStruct d params ixs
    -- ^ Arguments to the constructor
  , ctorDataType :: !(PrimName Term)
    -- ^ The datatype this constructor belongs to
  , ctorType :: Term
    -- ^ Cached type of the constructor, which should always be equal to
    --
    -- > (p1::P1) -> .. -> (pn::Pn) -> (x1::arg1) -> .. -> (xm::argm) ->
    -- >  d p1 .. pn ix1 .. ixk
    --
    -- where the @pi@ are the 'ctorParams', the @argi@ are the types specified
    -- by the 'ctorArgs', and the @ixi@ are the 'ctorDataTypeIndices'. Note that
    -- this type should always be top-level, i.e., have no free variables.
  , ctorElimTypeFun :: [Term] -> Term -> IO Term
    -- ^ Cached function for generating the type of an eliminator for this
    -- constructor by passing it a list of parameters and a @p_ret@ function,
    -- also known as the "motive function", which itself must have type
    --
    -- > (x1::ix1) -> .. -> (xm::ixm) -> d p1 .. pn x1 .. xm -> Type i
    --
    -- where the @ps@ are the parameters and the @ix@s are the indices of
    -- datatype @d@
  , ctorIotaReduction ::
       Term {- ^ recursor term -} ->
       Map VarIndex Term {- ^ constructor eliminators -} ->
       [Term] {- ^ constructor arguments -} ->
       IO Term
    -- ^ Cached function for computing the result of one step of iota
    --   reduction of the term
    --
    -- > RecursorApp rec ixs (c params args)
    --
    --   The arguments to this function are the recusor value, the
    --   the map from the recursor that maps constructors to eliminator
    --   functions, and the arguments to the constructor.

  , ctorIotaTemplate :: Term
    -- ^ Cached term used for computing iota reductions.  It has free variables
    --   @rec@, @elim@ and @args@, in that order so that the last @arg@ is the
    --   most recently-bound variable with deBruijn index 0.  The @rec@ variable
    --   represents the recursor value, @elim@ represents the eliminator function
    --   for the constructor, and @args@ represent the arguments to this constructor.
  }

-- | Return the number of parameters of a constructor
ctorNumParams :: Ctor -> Int
ctorNumParams (Ctor { ctorArgStruct = CtorArgStruct {..}}) =
  bindingsLength ctorParams

-- | Return the number of non-parameter arguments of a constructor
ctorNumArgs :: Ctor -> Int
ctorNumArgs (Ctor { ctorArgStruct = CtorArgStruct {..}}) =
  bindingsLength ctorArgs

-- | Compute the ExtCns that uniquely references a constructor
ctorPrimName :: Ctor -> PrimName Term
ctorPrimName ctor = PrimName (ctorVarIndex ctor) (ctorName ctor) (ctorType ctor)

lift2 :: (a -> b) -> (b -> b -> c) -> a -> a -> c
lift2 f h x y = h (f x) (f y)

instance Eq Ctor where
  (==) = lift2 ctorName (==)

instance Ord Ctor where
  compare = lift2 ctorName compare

instance Show Ctor where
  show = show . ctorName


-- Datatypes -------------------------------------------------------------------

-- | An inductively-defined datatype
data DataType =
  DataType
  { dtName :: Ident
    -- ^ The name of this datatype
  , dtVarIndex :: !VarIndex
    -- ^ Unique var index for this data type
  , dtParams :: [(LocalName, Term)]
    -- ^ The context of parameters of this datatype
  , dtIndices :: [(LocalName, Term)]
    -- ^ The context of indices of this datatype
  , dtSort :: Sort
    -- ^ The universe of this datatype
  , dtCtors :: [Ctor]
    -- ^ The list of constructors of this datatype
  , dtType :: Term
    -- ^ The cached type of this datatype, which should always be equal to
    --
    -- > (p1::P1) -> .. -> (pn::Pn) -> (i1::I1) -> .. -> (im::Im) -> 'dtSort'
    --
    -- where the @pi@ are the 'dtParams' and the @ii@ are the 'dtIndices'. Note
    -- that this type should always be top-level, i.e., have no free variables.
  }

-- | Return the number of parameters of a datatype
dtNumParams :: DataType -> Int
dtNumParams dt = length $ dtParams dt

-- | Return the number of indices of a datatype
dtNumIndices :: DataType -> Int
dtNumIndices dt = length $ dtIndices dt

-- | Compute the ExtCns that uniquely references a datatype
dtPrimName :: DataType -> PrimName Term
dtPrimName dt = PrimName (dtVarIndex dt) (dtName dt) (dtType dt)

instance Eq DataType where
  (==) = lift2 dtName (==)

instance Ord DataType where
  compare = lift2 dtName compare

instance Show DataType where
  show = show . dtName


-- Modules ---------------------------------------------------------------------

-- | Declarations that can occur in a module
data ModuleDecl = TypeDecl DataType
                | DefDecl Def
                    -- | Code to inject directly in-stream when
                    --   doing translations.
                | InjectCodeDecl
                    Text {- ^ Code namespace -}
                    Text {- ^ Code to inject -}

-- | The different sorts of things that a 'Text' name can be resolved to
data ResolvedName
  = ResolvedCtor Ctor
  | ResolvedDataType DataType
  | ResolvedDef Def

-- | Get the 'Ident' for a 'ResolvedName'
resolvedNameIdent :: ResolvedName -> Ident
resolvedNameIdent (ResolvedCtor ctor) = ctorName ctor
resolvedNameIdent (ResolvedDataType dt) = dtName dt
resolvedNameIdent (ResolvedDef d) = defIdent d

-- | Get the type of a 'ResolvedName' as a 'Term'.
resolvedNameType :: ResolvedName -> Term
resolvedNameType r =
  case r of
    ResolvedCtor ctor -> ctorType ctor
    ResolvedDataType dt -> dtType dt
    ResolvedDef def -> defType def

-- | Get the 'VarIndex' for a 'ResolvedName'.
resolvedNameVarIndex :: ResolvedName -> VarIndex
resolvedNameVarIndex r =
  case r of
    ResolvedCtor ctor -> ctorVarIndex ctor
    ResolvedDataType dt -> dtVarIndex dt
    ResolvedDef def -> defVarIndex def

-- | Modules define namespaces of datatypes, constructors, and definitions,
-- i.e., mappings from 'Text' names to these objects. A module is allowed to
-- map a 'Text' name to an object defined in a different module. Modules also
-- keep a record of the top-level declarations and the imports that were used to
-- build them.
data Module = Module {
          moduleName    :: !ModuleName
        , moduleResolveMap :: !(Map Text ResolvedName)
        , moduleRDecls   :: [ModuleDecl] -- ^ All declarations in reverse order they were added.
        }

emptyModule :: ModuleName -> Module
emptyModule nm =
  Module { moduleName = nm
         , moduleResolveMap = Map.empty
         , moduleRDecls = []
         }


-- | Resolve a 'Text' name in the namespace defined by a 'Module', to either a
-- 'Ctor', 'DataType', or 'Def'
resolveName :: Module -> Text -> Maybe ResolvedName
resolveName m str = Map.lookup str (moduleResolveMap m)

asResolvedCtor :: ResolvedName -> Maybe Ctor
asResolvedCtor = \case { ResolvedCtor ctor -> Just ctor; _ -> Nothing }

asResolvedDataType :: ResolvedName -> Maybe DataType
asResolvedDataType = \case { ResolvedDataType d -> Just d; _ -> Nothing }

asResolvedDef :: ResolvedName -> Maybe Def
asResolvedDef = \case { ResolvedDef d -> Just d; _ -> Nothing }

-- | Resolve a 'Text' name to a 'Ctor'
findCtor :: Module -> Text -> Maybe Ctor
findCtor m str = resolveName m str >>= asResolvedCtor

-- | Resolve a 'Text' name to a 'DataType'
findDataType :: Module -> Text -> Maybe DataType
findDataType m str = resolveName m str >>= asResolvedDataType

-- | Resolve a 'Text' name to a 'Def'
findDef :: Module -> Text -> Maybe Def
findDef m str = resolveName m str >>= asResolvedDef


-- | Insert a 'ResolvedName' into a 'Module', adding a mapping from the 'Text'
-- name of that resolved name to it. Signal an error in the case of a name
-- clash, i.e., an existing binding for the same 'Text' name.
insResolvedName :: Module -> ResolvedName -> Module
insResolvedName m nm =
  let str = identBaseName $ resolvedNameIdent nm in
  if Map.member str (moduleResolveMap m) then
    panic "insResolvedName" [
        "inserting duplicate name " <> str <> " into module " <>
            moduleNameText (moduleName m)
    ]
  else
    m { moduleResolveMap = Map.insert str nm (moduleResolveMap m) }

-- | @insImport i m@ returns the module obtained by importing @i@ into @m@,
-- using a predicate to specify which names are imported from @i@ into @m@. In
-- the case of name clashes, an error is signaled.
insImport :: (ResolvedName -> Bool) -> Module -> Module -> Module
insImport name_p i m =
  (foldl' insResolvedName m $ Map.elems $
   Map.filter name_p (moduleResolveMap i))

-- | Insert an \"incomplete\" datatype, used as part of building up a
-- 'DataType' to typecheck its constructors. This incomplete datatype
-- must have no constructors, and it will not be added to the
-- declaration list until it is completed by 'completeDataType'.
-- Return 'Left' in the case of a name clash, i.e., an existing
-- binding for the same 'Ident' name.
beginDataType :: DataType -> ModuleMap -> Either Ident ModuleMap
beginDataType dt =
  insResolvedNameInMap (ResolvedDataType dt')
  where dt' = dt { dtCtors = [] }

-- | Complete a datatype, by adding its constructors. Return 'Left' if
-- there is a name clash with any constructor name.
completeDataType :: Ident -> [Ctor] -> ModuleMap -> Either Ident ModuleMap
completeDataType ident ctors mm0 =
  let str = identBaseName ident in
  case resolveNameInMap mm0 ident of
    Just (ResolvedDataType dt)
      | null (dtCtors dt) ->
        do let dt' = dt {dtCtors = ctors}
           let r = ResolvedDataType dt'
           let mm1 = insDeclInMap (identModule ident) (TypeDecl dt') mm0
           let mm2 = mm1 { mmIndexMap = IntMap.insert (dtVarIndex dt) r (mmIndexMap mm1) }
           foldM (flip insResolvedNameInMap) mm2 (map ResolvedCtor ctors)
    Just (ResolvedDataType _) ->
      panic "completeDataType" ["datatype already completed: " <> str]
    Just _ ->
      panic "completeDataType" ["not a datatype: " <> str]
    Nothing ->
      panic "completeDataType" ["datatype not found: " <> str]


-- | Get the resolved names that are local to a module
localResolvedNames :: Module -> [ResolvedName]
localResolvedNames m =
  filter ((== moduleName m) . identModule . resolvedNameIdent)
  (Map.elems $ moduleResolveMap m)

-- | Get all definitions defined in a module
moduleDefs :: Module -> [Def]
moduleDefs =
  foldr' (\case { ResolvedDef d -> (d :); _ -> id } ) [] .
  localResolvedNames

-- | Get all declarations that are local to a module, i.e., that defined names
-- that were not imported from some other module
moduleDecls :: Module -> [ModuleDecl]
moduleDecls = reverse . moduleRDecls

-- | The type of mappings from module names to modules
data ModuleMap =
  ModuleMap
  { mmNameEnv :: !(Map ModuleName DisplayNameEnv)
  , mmIndexMap :: !(IntMap ResolvedName) -- keyed by VarIndex
  , mmRDecls :: !(Map ModuleName [ModuleDecl])
  }

emptyModuleMap :: ModuleMap
emptyModuleMap =
  ModuleMap
  { mmNameEnv = Map.empty
  , mmIndexMap = IntMap.empty
  , mmRDecls = Map.empty
  }

-- | Test whether a 'ModuleName' is in a 'ModuleMap'.
moduleIsLoaded :: ModuleName -> ModuleMap -> Bool
moduleIsLoaded mn mm = Map.member mn (mmRDecls mm)

loadModule :: Module -> ModuleMap -> ModuleMap
loadModule m mm =
  ModuleMap
  { mmNameEnv = Map.insert (moduleName m) env (mmNameEnv mm)
  , mmIndexMap = IntMap.union indexMap (mmIndexMap mm)
  , mmRDecls = Map.insert (moduleName m) (moduleRDecls m) (mmRDecls mm)
  }
  where
    env =
      foldr' (\(x, r) -> extendDisplayNameEnv (resolvedNameVarIndex r) [x]) emptyDisplayNameEnv $
      Map.assocs (moduleResolveMap m)
    indexMap = IntMap.fromList [ (resolvedNameVarIndex r, r) | r <- Map.elems (moduleResolveMap m) ]

findModule :: ModuleName -> ModuleMap -> Maybe Module
findModule mnm mm =
  do decls <- Map.lookup mnm (mmRDecls mm)
     env <- Map.lookup mnm (mmNameEnv mm)
     -- moduleResolveMap :: !(Map Text ResolvedName)
     -- { displayNames :: !(IntMap [Text]) -- Keyed by VarIndex; preferred names come first.
     -- , displayIndexes :: !(Map Text IntSet)
     let rmap =
           Map.mapMaybe (\vi -> IntMap.lookup vi (mmIndexMap mm)) $
           Map.fromList [ (x, i) | (x, s) <- Map.assocs (displayIndexes env), i <- IntSet.elems s ]
     Just $ Module { moduleName = mnm, moduleResolveMap = rmap, moduleRDecls = decls }

lookupVarIndexInMap :: VarIndex -> ModuleMap -> Maybe ResolvedName
lookupVarIndexInMap vi mm = IntMap.lookup vi (mmIndexMap mm)

resolveNameInMap :: ModuleMap -> Ident -> Maybe ResolvedName
resolveNameInMap mm i =
  do env <- Map.lookup (identModule i) (mmNameEnv mm)
     vi <-
       case resolveDisplayName env (identBaseName i) of
         [vi] -> Just vi
         _ -> Nothing
     IntMap.lookup vi (mmIndexMap mm)

-- | Resolve an 'Ident' to a 'Ctor' in a 'ModuleMap'
findCtorInMap :: Ident -> ModuleMap -> Maybe Ctor
findCtorInMap i mm = resolveNameInMap mm i >>= asResolvedCtor

-- | Resolve an 'Ident' to a 'DataType' in a 'ModuleMap'
findDataTypeInMap :: Ident -> ModuleMap -> Maybe DataType
findDataTypeInMap i mm = resolveNameInMap mm i >>= asResolvedDataType

-- | Resolve an 'Ident' to a 'Def' in a 'ModuleMap'.
findDefInMap :: Ident -> ModuleMap -> Maybe Def
findDefInMap i mm = resolveNameInMap mm i >>= asResolvedDef

-- | Get all definitions defined in any module in an entire module map. Note
-- that the returned list might have redundancies if a definition is visible /
-- imported in multiple modules in the module map.
allModuleDefs :: ModuleMap -> [Def]
allModuleDefs mm = mapMaybe asResolvedDef (IntMap.elems (mmIndexMap mm))

-- | Get all local declarations from all modules in an entire module map
allModuleDecls :: ModuleMap -> [ModuleDecl]
allModuleDecls mm = concat (Map.elems (mmRDecls mm))

-- | Get all local declarations from all modules in an entire module map that
-- are marked as primitives
allModulePrimitives :: ModuleMap -> [Def]
allModulePrimitives modmap =
    [ def
    | DefDecl def <- allModuleDecls modmap
    , defQualifier def == PrimQualifier
    ]

-- | Get all local declarations from all modules in an entire module map that
-- are marked as axioms
allModuleAxioms :: ModuleMap -> [Def]
allModuleAxioms modmap =
    [ def
    | DefDecl def <- allModuleDecls modmap
    , defQualifier def == AxiomQualifier
    ]

-- | Get all local declarations from all modules in an entire module map that
-- are marked as neither primitives nor axioms
allModuleActualDefs :: ModuleMap -> [Def]
allModuleActualDefs modmap =
    [ def
    | DefDecl def <- allModuleDecls modmap
    , defQualifier def == NoQualifier
    ]

-- | Get all datatypes in all modules in a module map
allModuleDataTypes :: ModuleMap -> [DataType]
allModuleDataTypes mm = mapMaybe asResolvedDataType (IntMap.elems (mmIndexMap mm))

-- | Get all constructors in all modules in a module map
allModuleCtors :: ModuleMap -> [Ctor]
allModuleCtors mm = mapMaybe asResolvedCtor (IntMap.elems (mmIndexMap mm))

-- | Insert a 'ResolvedName' into a 'ModuleMap', adding a mapping from
-- the 'Ident' name of that resolved name to it. Return 'Left' in the
-- case of a name clash, i.e., an existing binding for the same
-- 'Ident' name.
insResolvedNameInMap :: ResolvedName -> ModuleMap -> Either Ident ModuleMap
insResolvedNameInMap r mm =
  if Map.member base (displayIndexes env)
  then Left ident
  else Right $ mm { mmNameEnv = Map.insert mname env' (mmNameEnv mm)
                  , mmIndexMap = IntMap.insert vi r (mmIndexMap mm)
                  }
  where
    vi = resolvedNameVarIndex r
    ident = resolvedNameIdent r
    mname = identModule ident
    base = identBaseName ident
    env = fromMaybe emptyDisplayNameEnv $ Map.lookup mname (mmNameEnv mm)
    env' = extendDisplayNameEnv vi [base] env

insDeclInMap :: ModuleName -> ModuleDecl -> ModuleMap -> ModuleMap
insDeclInMap mname decl mm =
  mm { mmRDecls = Map.alter (Just . (decl :) . fromMaybe []) mname (mmRDecls mm) }

-- | Insert a definition into a 'ModuleMap'.
insDefInMap :: Def -> ModuleMap -> Either Ident ModuleMap
insDefInMap d mm =
  insResolvedNameInMap (ResolvedDef d) $
  insDeclInMap (identModule (defIdent d)) (DefDecl d) mm

-- | Insert an injectCode declaration into a 'ModuleMap'.
insInjectCodeInMap :: ModuleName -> Text -> Text -> ModuleMap -> ModuleMap
insInjectCodeInMap mname ns txt = insDeclInMap mname (InjectCodeDecl ns txt)

-- | @insImportInMap p m1 m2@ adds all the names from module @m1@ into
-- module @m2@ in the name table of the 'ModuleMap'. The predicate @p@
-- determines which names to import.
insImportInMap :: (Text -> Bool) -> ModuleName -> ModuleName -> ModuleMap -> ModuleMap
insImportInMap p name1 name2 mm =
  mm { mmNameEnv = Map.insert name2 env2' (mmNameEnv mm) }
  where
    env1 = fromMaybe emptyDisplayNameEnv $ Map.lookup name1 (mmNameEnv mm)
    env2 = fromMaybe emptyDisplayNameEnv $ Map.lookup name2 (mmNameEnv mm)
    env2' = mergeDisplayNameEnv (filterDisplayNameEnv p env1) env2
