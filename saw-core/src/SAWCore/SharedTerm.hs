{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}

{- |
Module      : SAWCore.SharedTerm
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.SharedTerm
  ( TermF(..)
  , Ident, mkIdent
  , VarIndex
  , NameInfo(..)
  , ppName
    -- * Shared terms
  , Term(..)
  , TermIndex
  , scImport
  , alphaEquiv
  , alistAllFields
  , scRegisterName
  , scResolveName
  , scResolveNameByURI
  , scShowTerm
  , DuplicateNameException(..)
    -- * SharedContext interface for building shared terms
  , SharedContext -- abstract type
  , mkSharedContext
  , scGetModuleMap
  , SharedContextCheckpoint -- abstract type
  , checkpointSharedContext
  , restoreSharedContext
  , scGetNamingEnv
    -- ** Low-level generic term constructors
  , scTermF
  , scFlatTermF
    -- ** Implicit versions of functions.
  , scFreshVariable
  , scFreshName
  , scFreshVarName
  , scVariable
  , scVariables
  , scGlobalDef
  , scFreshenGlobalIdent
    -- ** Recursors and datatypes
  , scRecursorType
  , scReduceRecursor
  , allowedElimSort
  , scBuildCtor
    -- ** Modules
  , scLoadModule
  , scImportModule
  , scModuleIsLoaded
  , scFindModule
  , scFindDef
  , scFindDataType
  , scFindCtor
  , scRequireDef
  , scRequireDataType
  , scRequireCtor
  , scInjectCode
    -- ** Declaring global constants
  , scDeclarePrim
  , scFreshConstant
  , scDefineConstant
  , scOpaqueConstant
  , scBeginDataType
  , scCompleteDataType
    -- ** Term construction
    -- *** Sorts
  , scSort
  , scISort
  , scSortWithFlags
    -- *** Variables and constants
  , scConst
  , scConstApply
    -- *** Functions and function application
  , scApply
  , scApplyAll
  , scApplyBeta
  , scApplyAllBeta
  , scGlobalApply
  , scFun
  , scFunAll
  , scLambda
  , scLambdaList
  , scPi
  , scPiList
    -- *** Strings
  , scString
  , scStringType
    -- *** Booleans
  , scEqTrue
  , scBool
  , scBoolType
    -- *** Unit, pairs, and tuples
  , scUnitValue
  , scUnitType
  , scPairValue
  , scPairType
  , scPairLeft
  , scPairRight
  , scPairValueReduced
  , scTuple
  , scTupleType
  , scTupleSelector
  , scTupleReduced
    -- *** Records
  , scRecord
  , scRecordSelect
  , scRecordType
    -- *** Vectors
  , scVector
  , scVecType
  , scVectorReduced
    -- ** Normalization
  , scWhnf
  , scConvertibleEval
  , scConvertible
    -- ** Type checking
  , scTypeOf
  , asSort
  , reducePi
  , scTypeOfIdent
  , scTypeOfName
    -- ** Prelude operations
    -- *** Booleans
  , scNot
  , scAnd
  , scOr
  , scImplies
  , scXor
  , scBoolEq
  , scIte
  , scAndList
  , scOrList
  -- *** Natural numbers
  , scNat
  , scNatType
  , scAddNat
  , scSubNat
  , scMulNat
  , scDivNat
  , scModNat
  , scDivModNat
  , scEqualNat
  , scLtNat
  , scMinNat
  , scMaxNat
  , scUpdNatFun
    -- *** Integers
  , scIntegerType
  , scIntegerConst
  , scIntAdd, scIntSub, scIntMul
  , scIntDiv, scIntMod, scIntNeg
  , scIntAbs, scIntMin, scIntMax
  , scIntEq, scIntLe, scIntLt
  , scIntToNat, scNatToInt
  , scIntToBv, scBvToInt, scSbvToInt
    -- *** IntMod
  , scIntModType
  , scToIntMod
  , scFromIntMod
  , scIntModEq
  , scIntModAdd
  , scIntModSub
  , scIntModMul
  , scIntModNeg
    -- *** Vectors
  , scAppend
  , scJoin
  , scSplit
  , scGet
  , scAtWithDefault
  , scAt
  , scSingle
  , scSlice
    -- *** Bitvectors
  , scBitvector
  , scBvNat
  , scBvToNat
  , scBvAt
  , scBvConst
  , scBvLit
  , scBvForall
  , scUpdBvFun
  , scBvNonzero, scBvBool
  , scBvAdd, scBvSub, scBvMul, scBvNeg
  , scBvURem, scBvUDiv, scBvSRem, scBvSDiv
  , scBvOr, scBvAnd, scBvXor
  , scBvNot
  , scBvEq, scBvUGe, scBvUGt, scBvULe, scBvULt
  , scBvSGt, scBvSGe, scBvSLt, scBvSLe
  , scBvShl, scBvShr, scBvSShr
  , scBvUExt, scBvSExt
  , scBvTrunc
  , scBvLg2
  , scBvPopcount
  , scBvCountLeadingZeros
  , scBvCountTrailingZeros
  , scLsb, scMsb
    -- *** Arrays
  , scArrayType
  , scArrayConstant
  , scArrayLookup
  , scArrayUpdate
  , scArrayEq
  , scArrayCopy
  , scArraySet
  , scArrayRangeEq
    -- ** Variable substitution
  , betaNormalize
  , isConstFoldTerm
  , getAllVars
  , getAllVarsMap
  , getConstantSet
  , scInstantiate
  , scInstantiateBeta
  , scAbstractTerms
  , scLambdaListEtaCollapse
  , scGeneralizeTerms
  , scUnfoldConstants
  , scUnfoldConstantsBeta
  , scUnfoldOnceFixConstantSet
  , scSharedSize
  , scSharedSizeAux
  , scSharedSizeMany
  , scTreeSize
  , scTreeSizeAux
  , scTreeSizeMany
  ) where

import Control.Applicative
-- ((<$>), pure, (<*>))
import Control.Concurrent.MVar
import Control.Exception
import Control.Lens
import Control.Monad (foldM, forM, forM_, join, unless, when)
import Control.Monad.IO.Class (MonadIO(..))
import qualified Control.Monad.State.Strict as State
import Control.Monad.Trans.Class (MonadTrans(..))
import Data.Bits
import Data.List (find)
import Data.Maybe
import qualified Data.Foldable as Fold
import Data.Foldable (foldl', foldlM, foldrM, maximum)
import Data.Hashable (Hashable(hash))
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HMap
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import Data.IORef (IORef,newIORef,readIORef,modifyIORef',atomicModifyIORef',writeIORef)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Ref ( C )
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Vector as V
import Numeric.Natural (Natural)
import Prelude hiding (maximum)
import Text.URI

import qualified SAWSupport.Pretty as PPS (Opts)

import SAWCore.Panic (panic)
import SAWCore.Cache
import SAWCore.Change
import SAWCore.Module
  ( beginDataType
  , completeDataType
  , dtName
  , ctorNumParams
  , ctorName
  , emptyModuleMap
  , moduleIsLoaded
  , moduleName
  , loadModule
  , lookupVarIndexInMap
  , findCtorInMap
  , findDataTypeInMap
  , findDefInMap
  , findModule
  , insDefInMap
  , insInjectCodeInMap
  , insImportInMap
  , resolvedNameType
  , resolveNameInMap
  , requireNameInMap
  , CtorArg(..)
  , CtorArgStruct(..)
  , Ctor(..)
  , DefQualifier(..)
  , DataType(..)
  , Def(..)
  , Module
  , ModuleMap
  , ResolvedName(..)
  )
import SAWCore.Name
import SAWCore.Prelude.Constants
import SAWCore.Recognizer
import SAWCore.Term.Functor
import SAWCore.Term.Pretty
import SAWCore.Term.Raw
import SAWCore.Unique

------------------------------------------------------------
-- TermFMaps

-- | A TermFMap is a data structure used for hash-consing of terms.
data TermFMap a
  = TermFMap
  { appMapTFM :: !(IntMap (IntMap a))
  , hashMapTFM :: !(HashMap (TermF Term) a)
  }

emptyTFM :: TermFMap a
emptyTFM = TermFMap mempty mempty

lookupTFM :: TermF Term -> TermFMap a -> Maybe a
lookupTFM tf tfm =
  case tf of
    App (STApp{ stAppIndex = i }) (STApp{ stAppIndex = j}) ->
      IntMap.lookup i (appMapTFM tfm) >>= IntMap.lookup j
    _ -> HMap.lookup tf (hashMapTFM tfm)

insertTFM :: TermF Term -> a -> TermFMap a -> TermFMap a
insertTFM tf x tfm =
  case tf of
    App (STApp{ stAppIndex = i }) (STApp{ stAppIndex = j}) ->
      let f Nothing = Just (IntMap.singleton j x)
          f (Just m) = Just (IntMap.insert j x m)
      in tfm { appMapTFM = IntMap.alter f i (appMapTFM tfm) }
    _ -> tfm { hashMapTFM = HMap.insert tf x (hashMapTFM tfm) }

type AppCache = TermFMap Term

type AppCacheRef = MVar AppCache

emptyAppCache :: AppCache
emptyAppCache = emptyTFM

----------------------------------------------------------------------
-- SharedContext: a high-level interface for building Terms.

-- | 'SharedContext' is an abstract datatype representing all the
-- information necessary to resolve names and to construct,
-- type-check, normalize, and evaluate SAWCore 'Term's.
-- A 'SharedContext' contains mutable references so that it can be
-- extended at run-time with new names and declarations.

-- Invariant: scGlobalEnv is a cache with one entry for every global
-- declaration in 'scModuleMap' whose name is a 'ModuleIdentifier'.
-- Each map entry points to a 'Constant' term with the same 'Ident'.
-- It exists only to save one map lookup when building terms: Without
-- it we would first have to look up the Ident by URI in scURIEnv, and
-- then do another lookup for hash-consing the Constant term.
data SharedContext = SharedContext
  { scModuleMap      :: IORef ModuleMap
  , scAppCache       :: AppCacheRef
  , scDisplayNameEnv :: IORef DisplayNameEnv
  , scURIEnv         :: IORef (Map URI VarIndex)
  , scGlobalEnv      :: IORef (HashMap Ident Term)
  , scNextVarIndex   :: IORef VarIndex
  }

-- | Internal function to make a 'Term' from a 'TermF' with a given
-- variable typing context.
scMakeTerm :: SharedContext -> IntMap Term -> TermF Term -> IO Term
scMakeTerm sc vt tf =
  modifyMVar (scAppCache sc) $ \s -> do
    case lookupTFM tf s of
      Just term -> return (s, term)
      Nothing -> do
        i <- getUniqueInt
        let term = STApp { stAppIndex = i
                         , stAppHash = hash tf
                         , stAppVarTypes = vt
                         , stAppTermF = tf
                         }
            s' = insertTFM tf term s
        seq s' $ return (s', term)

--------------------------------------------------------------------------------

data SharedContextCheckpoint =
  SCC
  { sccModuleMap :: ModuleMap
  , sccNamingEnv :: DisplayNameEnv
  , sccURIEnv    :: Map URI VarIndex
  , sccGlobalEnv :: HashMap Ident Term
  }

checkpointSharedContext :: SharedContext -> IO SharedContextCheckpoint
checkpointSharedContext sc =
  do mmap <- readIORef (scModuleMap sc)
     nenv <- readIORef (scDisplayNameEnv sc)
     uenv <- readIORef (scURIEnv sc)
     genv <- readIORef (scGlobalEnv sc)
     return SCC
            { sccModuleMap = mmap
            , sccNamingEnv = nenv
            , sccURIEnv = uenv
            , sccGlobalEnv = genv
            }

restoreSharedContext :: SharedContextCheckpoint -> SharedContext -> IO SharedContext
restoreSharedContext scc sc =
  do writeIORef (scModuleMap sc) (sccModuleMap scc)
     writeIORef (scDisplayNameEnv sc) (sccNamingEnv scc)
     writeIORef (scURIEnv sc) (sccURIEnv scc)
     writeIORef (scGlobalEnv sc) (sccGlobalEnv scc)
     return sc

--------------------------------------------------------------------------------
-- Fundamental term builders

-- | Build a new 'Term' value from the given 'TermF'.
-- Reuse a 'Term' from the cache if an identical one already exists.
scTermF :: SharedContext -> TermF Term -> IO Term
scTermF sc tf =
  case tf of
    FTermF ftf -> scFlatTermF sc ftf
    App t1 t2 -> scApply sc t1 t2
    Lambda x t1 t2 -> scLambda sc x t1 t2
    Pi x t1 t2 -> scPi sc x t1 t2
    Constant nm -> scConst sc nm
    Variable x t1 -> scVariable sc x t1

-- | Create a new term from a lower-level 'FlatTermF' term.
scFlatTermF :: SharedContext -> FlatTermF Term -> IO Term
scFlatTermF sc ftf =
  do vt <- foldM (unifyVarTypes "scFlatTermF") IntMap.empty (fmap varTypes ftf)
     scMakeTerm sc vt (FTermF ftf)

-- | Create a function application term.
scApply ::
  SharedContext ->
  Term {- ^ The function to apply -} ->
  Term {- ^ The argument to apply to -} ->
  IO Term
scApply sc t1 t2 =
  do vt <- unifyVarTypes "scApply" (varTypes t1) (varTypes t2)
     scMakeTerm sc vt (App t1 t2)

-- | Create a lambda term from a parameter name (as a 'VarName'),
-- parameter type (as a 'Term'), and a body ('Term').
-- All free variables with the same 'VarName' in the body become
-- bound.
scLambda ::
  SharedContext ->
  VarName {- ^ The parameter name -} ->
  Term {- ^ The parameter type -} ->
  Term {- ^ The body -} ->
  IO Term
scLambda sc x t body =
  do ensureNotFreeInContext x body
     _ <- unifyVarTypes "scLambda" (IntMap.singleton (vnIndex x) t) (varTypes body)
     vt <- unifyVarTypes "scLambda" (varTypes t) (IntMap.delete (vnIndex x) (varTypes body))
     scMakeTerm sc vt (Lambda x t body)

-- | Create a (possibly dependent) function given a parameter name,
-- parameter type (as a 'Term'), and a body ('Term').
-- All free variables with the same 'VarName' in the body become
-- bound.
scPi ::
  SharedContext ->
  VarName {- ^ The parameter name -} ->
  Term {- ^ The parameter type -} ->
  Term {- ^ The body -} ->
  IO Term
scPi sc x t body =
  do ensureNotFreeInContext x body
     _ <- unifyVarTypes "scPi" (IntMap.singleton (vnIndex x) t) (varTypes body)
     vt <- unifyVarTypes "scPi" (varTypes t) (IntMap.delete (vnIndex x) (varTypes body))
     scMakeTerm sc vt (Pi x t body)

-- | Create a constant 'Term' from a 'Name'.
scConst :: SharedContext -> Name -> IO Term
scConst sc nm =
  scMakeTerm sc IntMap.empty (Constant nm)

-- | Create a named variable 'Term' from a 'VarName' and a type.
scVariable :: SharedContext -> VarName -> Term -> IO Term
scVariable sc x t =
  do vt <- unifyVarTypes "scVariable" (IntMap.singleton (vnIndex x) t) (varTypes t)
     scMakeTerm sc vt (Variable x t)

-- | Check whether the given 'VarName' occurs free in the type of
-- another variable in the context of the given 'Term', and fail if it
-- does.
ensureNotFreeInContext :: VarName -> Term -> IO ()
ensureNotFreeInContext x body =
  when (any (IntMap.member (vnIndex x) . varTypes) (varTypes body)) $
    fail $ "Variable occurs free in typing context: " ++ show (vnName x)

-- | Two typing contexts are unifiable if they agree perfectly on all
-- entries where they overlap.
unifyVarTypes :: String -> IntMap Term -> IntMap Term -> IO (IntMap Term)
unifyVarTypes msg ctx1 ctx2 =
  do let check i t1 t2 =
           unless (t1 == t2) $
           fail $ unlines [msg ++ ": variable typing context mismatch",
                           "VarIndex: " ++ show i,
                           "t1: " ++ showTerm t1,
                           "t2: " ++ showTerm t2]
     sequence_ (IntMap.intersectionWithKey check ctx1 ctx2)
     pure (IntMap.union ctx1 ctx2)

--------------------------------------------------------------------------------

-- | Create a function application term from the 'Name' of a global
-- constant and a list of 'Term' arguments.
scConstApply :: SharedContext -> Name -> [Term] -> IO Term
scConstApply sc i ts =
  do c <- scConst sc i
     scApplyAll sc c ts

-- | Create a list of named variables from a list of names and types.
scVariables :: Traversable t => SharedContext -> t (VarName, Term) -> IO (t Term)
scVariables sc = traverse (\(v, t) -> scVariable sc v t)

data DuplicateNameException = DuplicateNameException URI
instance Exception DuplicateNameException
instance Show DuplicateNameException where
  show (DuplicateNameException uri) =
      "Attempted to register the following name twice: " ++ Text.unpack (render uri)

-- | Internal function to get the next available 'VarIndex'. Not exported.
scFreshVarIndex :: SharedContext -> IO VarIndex
scFreshVarIndex sc = atomicModifyIORef' (scNextVarIndex sc) (\i -> (i + 1, i))

-- | Internal function to register a name with a caller-provided
-- 'VarIndex'. Not exported.
scRegisterNameWithIndex :: SharedContext -> VarIndex -> NameInfo -> IO ()
scRegisterNameWithIndex sc i nmi =
  do uris <- readIORef (scURIEnv sc)
     let uri = nameURI nmi
     when (Map.member uri uris) $ throwIO (DuplicateNameException uri)
     writeIORef (scURIEnv sc) (Map.insert uri i uris)
     modifyIORef' (scDisplayNameEnv sc) $ extendDisplayNameEnv i (nameAliases nmi)


-- | Generate a 'Name' with a fresh 'VarIndex' for the given
-- 'NameInfo' and register everything together in the naming
-- environment of the 'SharedContext'.
-- Throws 'DuplicateNameException' if the URI in the 'NameInfo' is
-- already registered.
scRegisterName :: SharedContext -> NameInfo -> IO Name
scRegisterName sc nmi =
  do i <- scFreshVarIndex sc
     scRegisterNameWithIndex sc i nmi
     pure (Name i nmi)

scResolveNameByURI :: SharedContext -> URI -> IO (Maybe VarIndex)
scResolveNameByURI sc uri =
  do env <- readIORef (scURIEnv sc)
     pure $! Map.lookup uri env

scResolveName :: SharedContext -> Text -> IO [VarIndex]
scResolveName sc nm =
  do env <- readIORef (scDisplayNameEnv sc)
     pure (resolveDisplayName env nm)

scShowTerm :: SharedContext -> PPS.Opts -> Term -> IO String
scShowTerm sc opts t =
  do env <- readIORef (scDisplayNameEnv sc)
     pure (showTermWithNames opts env t)

-- | Create a unique global name with the given base name.
scFreshName :: SharedContext -> Text -> IO Name
scFreshName sc x =
  do i <- scFreshVarIndex sc
     let uri = scFreshNameURI x i
     let nmi = ImportedName uri [x, x <> "#" <>  Text.pack (show i)]
     scRegisterNameWithIndex sc i nmi
     pure (Name i nmi)

-- | Create a 'VarName' with the given identifier (which may be "_").
scFreshVarName :: SharedContext -> Text -> IO VarName
scFreshVarName sc x = VarName <$> scFreshVarIndex sc <*> pure x

-- | Create a fresh variable with the given identifier (which may be "_") and type.
scFreshVariable :: SharedContext -> Text -> Term -> IO Term
scFreshVariable sc x tp =
  do nm <- scFreshVarName sc x
     scVariable sc nm tp

-- | Returns shared term associated with ident.
-- Does not check module namespace.
scGlobalDef :: SharedContext -> Ident -> IO Term
scGlobalDef sc ident =
  do m <- readIORef (scGlobalEnv sc)
     case HMap.lookup ident m of
       Nothing -> fail ("Could not find global: " ++ show ident)
       Just t -> pure t

-- | Internal function to register an 'Ident' with a 'Term' (which
-- must be a 'Constant' term with the same 'Ident') in the
-- 'scGlobalEnv' map of the 'SharedContext'. Not exported.
scRegisterGlobal :: SharedContext -> Ident -> Term -> IO ()
scRegisterGlobal sc ident t =
  do dup <- atomicModifyIORef' (scGlobalEnv sc) f
     when dup $ fail ("Global identifier already registered: " ++ show ident)
  where
    f m =
      case HMap.lookup ident m of
        Just _ -> (m, True)
        Nothing -> (HMap.insert ident t m, False)

-- | Find a variant of an identifier that is not already being used as a global,
-- by possibly adding a numeric suffix
scFreshenGlobalIdent :: SharedContext -> Ident -> IO Ident
scFreshenGlobalIdent sc ident =
  readIORef (scGlobalEnv sc) >>= \gmap ->
  return $ fromJust $ find (\i -> not $ HMap.member i gmap) $
  ident : map (mkIdent (identModule ident) .
               Text.append (identBaseName ident) .
               Text.pack . show) [(0::Integer) ..]

-- | Get the current naming environment
scGetNamingEnv :: SharedContext -> IO DisplayNameEnv
scGetNamingEnv sc = readIORef (scDisplayNameEnv sc)

-- | Get the current 'ModuleMap'
scGetModuleMap :: SharedContext -> IO ModuleMap
scGetModuleMap sc = readIORef (scModuleMap sc)

-- | Test if a module is loaded in the current shared context
scModuleIsLoaded :: SharedContext -> ModuleName -> IO Bool
scModuleIsLoaded sc name =
  moduleIsLoaded name <$> scGetModuleMap sc

-- | Load a module into the current shared context, raising an error if a module
-- of the same name is already loaded
scLoadModule :: SharedContext -> Module -> IO ()
scLoadModule sc m =
  do loaded <- scModuleIsLoaded sc (moduleName m)
     when loaded $ fail $ "scLoadModule: module "
                   ++ show (moduleName m) ++ " already loaded!"
     modifyIORef' (scModuleMap sc) (loadModule m)

-- | Bring a subset of names from one module into scope in a second module.
scImportModule ::
  SharedContext ->
  (Text -> Bool) {- ^ which names to import -} ->
  ModuleName {- ^ from this module -} ->
  ModuleName {- ^ into this module -} ->
  IO ()
scImportModule sc p mn1 mn2 =
  modifyIORef' (scModuleMap sc) (insImportInMap p mn1 mn2)

-- | Internal function to insert a definition into the 'ModuleMap' of
-- the 'SharedContext'. Throws 'DuplicateNameException' if the name is
-- already registered.
scInsDefInMap :: SharedContext -> Def -> IO ()
scInsDefInMap sc d =
  do e <- atomicModifyIORef' (scModuleMap sc) $ \mm ->
       case insDefInMap d mm of
         Left i -> (mm, Just (DuplicateNameException (moduleIdentToURI i)))
         Right mm' -> (mm', Nothing)
     maybe (pure ()) throwIO e

-- | Internal function to extend the SAWCore global environment with a
-- new constant, which may or may not have a definition. Not exported.
-- Assumes that the type and body (if present) are closed terms, and
-- that the body has the given type.
scDeclareDef ::
  SharedContext -> Name -> DefQualifier -> Term -> Maybe Term -> IO Term
scDeclareDef sc nm q ty body =
  do scInsDefInMap sc $
       Def
       { defName = nm
       , defQualifier = q
       , defType = ty
       , defBody = body
       }
     t <- scConst sc nm
     -- Register constant in scGlobalEnv if it has an Ident name
     case nameInfo nm of
       ModuleIdentifier ident -> scRegisterGlobal sc ident t
       ImportedName{} -> pure ()
     pure t

-- | Declare a SAW core primitive of the specified type.
scDeclarePrim :: SharedContext -> Ident -> DefQualifier -> Term -> IO ()
scDeclarePrim sc ident q def_tp =
  do let nmi = ModuleIdentifier ident
     nm <- scRegisterName sc nmi
     _ <- scDeclareDef sc nm q def_tp Nothing
     pure ()

-- | Look up a module by name, raising an error if it is not loaded
scFindModule :: SharedContext -> ModuleName -> IO Module
scFindModule sc name =
  do maybe_mod <- findModule name <$> scGetModuleMap sc
     case maybe_mod of
       Just m -> return m
       Nothing ->
         error ("scFindModule: module " ++ show name ++ " not found!")

-- | Look up a definition by its identifier
scFindDef :: SharedContext -> Ident -> IO (Maybe Def)
scFindDef sc i = findDefInMap i <$> scGetModuleMap sc

-- Internal function
scFindDefBody :: SharedContext -> VarIndex -> IO (Maybe Term)
scFindDefBody sc vi =
  do mm <- scGetModuleMap sc
     case lookupVarIndexInMap vi mm of
       Just (ResolvedDef d) -> pure (defBody d)
       _ -> pure Nothing

-- | Look up a 'Def' by its identifier, throwing an error if it is not found
scRequireDef :: SharedContext -> Ident -> IO Def
scRequireDef sc i =
  scFindDef sc i >>= \maybe_d ->
  case maybe_d of
    Just d -> return d
    Nothing -> fail ("Could not find definition: " ++ show i)

-- | Insert an \"incomplete\" datatype, used as part of building up a
-- 'DataType' to typecheck its constructors. The constructors must be
-- registered separately with 'scCompleteDataType'.
scBeginDataType ::
  SharedContext ->
  Ident {- ^ The name of this datatype -} ->
  [(VarName, Term)] {- ^ The context of parameters of this datatype -} ->
  [(VarName, Term)] {- ^ The context of indices of this datatype -} ->
  Sort {- ^ The universe of this datatype -} ->
  IO Name
scBeginDataType sc dtIdent dtParams dtIndices dtSort =
  do dtName <- scRegisterName sc (ModuleIdentifier dtIdent)
     dtType <- scPiList sc (dtParams ++ dtIndices) =<< scSort sc dtSort
     dtMotiveName <- scFreshVarName sc "p"
     dtArgName <- scFreshVarName sc "arg"
     let dt = DataType { dtCtors = [], .. }
     e <- atomicModifyIORef' (scModuleMap sc) $ \mm ->
       case beginDataType dt mm of
         Left i -> (mm, Just (DuplicateNameException (moduleIdentToURI i)))
         Right mm' -> (mm', Nothing)
     maybe (pure ()) throwIO e
     scRegisterGlobal sc dtIdent =<< scConst sc dtName
     pure dtName

-- | Complete a datatype, by adding its constructors. See also 'scBeginDataType'.
scCompleteDataType :: SharedContext -> Ident -> [Ctor] -> IO ()
scCompleteDataType sc dtIdent ctors =
  do e <- atomicModifyIORef' (scModuleMap sc) $ \mm ->
       case completeDataType dtIdent ctors mm of
         Left i -> (mm, Just (DuplicateNameException (moduleIdentToURI i)))
         Right mm' -> (mm', Nothing)
     maybe (pure ()) throwIO e
     forM_ ctors $ \ctor ->
       case nameInfo (ctorName ctor) of
         ModuleIdentifier ident ->
           -- register constructor in scGlobalEnv if it has an Ident name
           scRegisterGlobal sc ident =<< scConst sc (ctorName ctor)
         ImportedName{} ->
           pure ()

-- | Look up a datatype by its identifier
scFindDataType :: SharedContext -> Ident -> IO (Maybe DataType)
scFindDataType sc i = findDataTypeInMap i <$> scGetModuleMap sc

-- | Look up a datatype by its identifier, throwing an error if it is not found
scRequireDataType :: SharedContext -> Ident -> IO DataType
scRequireDataType sc i =
  scFindDataType sc i >>= \maybe_d ->
  case maybe_d of
    Just d -> return d
    Nothing -> fail ("Could not find datatype: " ++ show i)

-- | Look up a constructor by its identifier
scFindCtor :: SharedContext -> Ident -> IO (Maybe Ctor)
scFindCtor sc i = findCtorInMap i <$> scGetModuleMap sc

-- | Look up a constructor by its identifier, throwing an error if not found
scRequireCtor :: SharedContext -> Ident -> IO Ctor
scRequireCtor sc i =
  scFindCtor sc i >>= \maybe_ctor ->
  case maybe_ctor of
    Just ctor -> return ctor
    Nothing -> fail ("Could not find constructor: " ++ show i)

-- | Insert an \"injectCode\" declaration to the given SAWCore module.
-- This declaration has no logical effect within SAW; it is used to
-- add extra code (like class instance declarations, for example) to
-- exported SAWCore modules in certain translation backends.
scInjectCode ::
  SharedContext ->
  ModuleName ->
  Text {- ^ Code namespace -} ->
  Text {- ^ Code to inject -} ->
  IO ()
scInjectCode sc mnm ns txt =
  modifyIORef' (scModuleMap sc) $ insInjectCodeInMap mnm ns txt

--------------------------------------------------------------------------------
-- Recursors

-- | Test whether a 'DataType' can be eliminated to the given sort. The rules
-- are that you can only eliminate propositional datatypes to the proposition
-- sort, unless your propositional data type is the empty type. This differs
-- slightly from the Coq rules, which allow elimination of propositional
-- datatypes with a single constructor that has only propositional arguments,
-- but this Coq behavior can be simulated with the behavior we are using here.
allowedElimSort :: DataType -> Sort -> Bool
allowedElimSort dt s =
  if dtSort dt == propSort && s /= propSort then
    length (dtCtors dt) == 1
  else True

-- | Internal: Convert a 'CtorArg' into the type that it represents,
-- given a context of the parameters and of the previous arguments.
ctxCtorArgType ::
  SharedContext ->
  Term {- ^ datatype applied to parameters -} ->
  CtorArg ->
  IO Term
ctxCtorArgType _ _ (ConstArg tp) = return tp
ctxCtorArgType sc d_params (RecursiveArg zs_ctx ixs) =
  scPiList sc zs_ctx =<< scApplyAll sc d_params ixs

-- | Internal: Convert a bindings list of 'CtorArg's to a binding list
-- of types.
ctxCtorArgBindings ::
  SharedContext ->
  Term {- ^ data type applied to params -} ->
  [(VarName, CtorArg)] ->
  IO [(VarName, Term)]
ctxCtorArgBindings _ _ [] = return []
ctxCtorArgBindings sc d_params ((x, arg) : args) =
  do tp <- ctxCtorArgType sc d_params arg
     rest <- ctxCtorArgBindings sc d_params args
     return ((x, tp) : rest)

-- | Internal: Compute the type of a constructor from the name of its
-- datatype and its 'CtorArgStruct'
ctxCtorType :: SharedContext -> Name -> CtorArgStruct -> IO Term
ctxCtorType sc d (CtorArgStruct{..}) =
  do params <- scVariables sc ctorParams
     d_params <- scConstApply sc d params
     bs <- ctxCtorArgBindings sc d_params ctorArgs
     d_params_ixs <- scApplyAll sc d_params ctorIndices
     body <- scPiList sc bs d_params_ixs
     scPiList sc ctorParams body

-- | Build a 'Ctor' from a 'CtorArgStruct' and a list of the other constructor
-- names of the 'DataType'. Note that we cannot look up the latter information,
-- as 'scBuildCtor' is called during construction of the 'DataType'.
scBuildCtor ::
  SharedContext ->
  Name {- ^ data type -} ->
  Ident {- ^ constructor name -} ->
  CtorArgStruct {- ^ constructor formal arguments -} ->
  IO Ctor
scBuildCtor sc d c arg_struct =
  do
    -- Step 0: allocate a fresh unique variable index for this constructor
    -- and register its name in the naming environment
    cname <- scRegisterName sc (ModuleIdentifier c)

    -- Step 1: build the types for the constructor and the type required
    -- of its eliminator functions
    tp <- ctxCtorType sc d arg_struct

    -- Finally, return the required Ctor record
    return $ Ctor
      { ctorName = cname
      , ctorArgStruct = arg_struct
      , ctorDataType = d
      , ctorType = tp
      }

-- | Compute the type of an eliminator function for a constructor from the name
-- of its datatype, its name, and its 'CtorArgStruct'. This type has, as free
-- variables, both the parameters of the datatype and a "motive" function from
-- indices of the datatype to a return type. It is of the form
--
-- > (x1::arg1) -> maybe (rec1::rec_tp1) -> .. ->
-- > (xn::argn) -> maybe (recn::rec_tpn) ->
-- >   p_ret ix_1 .. ix_k (ctor params x1 .. xn)
--
-- where the ixs are the type indices of the return type for the constructor,
-- the (xi::argi) are the arguments of the constructor, and the @maybe@s
-- indicate additional arguments that are present only for arguments of
-- recursive type, that is, where @argi@ has the form
--
-- > (z1::Z1) -> .. -> (zm::Zm) -> d params t1 .. tk
--
-- In this case, @rec_tpi@ has the form
--
-- > (z1::Z1) -> .. -> (zm::Zm) -> p_ret t1 .. tk (f z1 .. zm)
--
-- Note that the output type cannot be expressed in the type of this function,
-- since it depends on fields of the 'CtorArgStruct', so, instead, the result is
-- just casted to whatever type the caller specifies.
ctxCtorElimType ::
  SharedContext ->
  Name {- ^ data type name -} ->
  Name {- ^ constructor name -} ->
  Term {- ^ motive function -} ->
  CtorArgStruct ->
  IO Term
ctxCtorElimType sc d c p_ret (CtorArgStruct{..}) =
  do params <- scVariables sc ctorParams
     d_params <- scConstApply sc d params
     let helper :: [Term] -> [(VarName, CtorArg)] -> IO Term
         helper prevs ((nm, ConstArg tp) : args) =
           -- For a constant argument type, just abstract it and continue
           do arg <- scVariable sc nm tp
              rest <- helper (prevs ++ [arg]) args
              scGeneralizeTerms sc [arg] rest
         helper prevs ((nm, RecursiveArg zs ts) : args) =
           -- For a recursive argument type of the form
           --
           -- (z1::Z1) -> .. -> (zm::Zm) -> d params t1 .. tk
           --
           -- form the type abstraction
           --
           -- (arg:: (z1::Z1) -> .. -> (zm::Zm) -> d params t1 .. tk) ->
           -- (ih :: (z1::Z1) -> .. -> (zm::Zm) -> p_ret t1 .. tk (arg z1 .. zm)) ->
           -- rest
           --
           -- where rest is the result of a recursive call
           do d_params_ts <- scApplyAll sc d_params ts
              -- Build the type of the argument arg
              arg_tp <- scPiList sc zs d_params_ts
              arg <- scVariable sc nm arg_tp
              -- Build the type of ih
              pret_ts <- scApplyAll sc p_ret ts
              z_vars <- scVariables sc zs
              arg_zs <- scApplyAll sc arg z_vars
              ih_ret <- scApply sc pret_ts arg_zs
              ih_tp <- scPiList sc zs ih_ret
              -- Finally, build the pi-abstraction for arg and ih around the rest
              rest <- helper (prevs ++ [arg]) args
              scGeneralizeTerms sc [arg] =<< scFun sc ih_tp rest
         helper prevs [] =
           -- If we are finished with our arguments, construct the final result type
           -- (p_ret ret_ixs (c params prevs))
           do p_ret_ixs <- scApplyAll sc p_ret ctorIndices
              appliedCtor <- scConstApply sc c (params ++ prevs)
              scApply sc p_ret_ixs appliedCtor
     helper [] ctorArgs

-- | Reduce an application of a recursor to a particular constructor.
-- This is known in the Coq literature as an iota reduction. More specifically,
-- the call
--
-- > ctxReduceRecursor rec f_c [x1, .., xk]
--
-- reduces the term @(RecursorApp rec ixs (CtorApp c ps xs))@ to
--
-- > f_c x1 (maybe rec_tm_1) .. xk (maybe rec_tm_k)
--
-- where @f_c@ is the eliminator function associated to the constructor @c@ by the
-- recursor value @rec@.  Here @maybe rec_tm_i@ indicates an optional recursive call
-- of the recursor on one of the @xi@. These recursive calls only exist for those
-- arguments @xi@ that are recursive arguments, i.e., that are specified with
-- 'RecursiveArg', and are omitted for non-recursive arguments specified by 'ConstArg'.
--
-- Specifically, for a @'RecursiveArg' zs ixs@ argument @xi@, which has type
-- @\(z1::Z1) -> .. -> d p1 .. pn ix1 .. ixp@, we build the recursive call
--
-- > \(z1::[xs/args]Z1) -> .. ->
-- >   RecursorApp rec [xs/args]ixs (xi z1 ... zn)
--
-- where @[xs/args]@ substitutes the concrete values for the earlier
-- constructor arguments @xs@ for the remaining free variables.

ctxReduceRecursor ::
  SharedContext ->
  Term {- ^ recursor applied to params, motive, and eliminator functions -} ->
  Term {- ^ constructor eliminator function -} ->
  [Term] {- ^ constructor arguments -} ->
  CtorArgStruct {- ^ constructor formal argument descriptor -} ->
  IO Term
ctxReduceRecursor sc r elimf c_args CtorArgStruct{..}
  | length c_args /= length ctorArgs = panic "ctxReduceRecursor" ["Wrong number of constructor arguments"]
  | otherwise =
    do args <- mk_args IntMap.empty (zip c_args ctorArgs)
       scWhnf sc =<< scApplyAll sc elimf args
  where
    mk_args :: IntMap Term ->  -- already processed parameters/arguments
               [(Term, (VarName, CtorArg))] ->
                 -- remaining actual arguments to process, with
                 -- telescope for typing the actual arguments
               IO [Term]
    -- no more arguments to process
    mk_args _ [] = return []

    -- process an argument that is not a recursive call
    mk_args pre_xs ((x, (nm, ConstArg _)) : xs_args) =
      do tl <- mk_args (IntMap.insert (vnIndex nm) x pre_xs) xs_args
         pure (x : tl)

    -- process an argument that is a recursive call
    mk_args pre_xs ((x, (nm, RecursiveArg zs ixs)) : xs_args) =
      do zs'  <- traverse (traverse (scInstantiate sc pre_xs)) zs
         ixs' <- traverse (scInstantiate sc pre_xs) ixs
         recx <- mk_rec_arg zs' ixs' x
         tl   <- mk_args (IntMap.insert (vnIndex nm) x pre_xs) xs_args
         pure (x : recx : tl)

    -- Build an individual recursive call, given the parameters, the bindings
    -- for the RecursiveArg, and the argument we are going to recurse on
    -- The resulting term has the form
    -- > \(z1:Z1) .. (zk:Zk) -> r ixs (x z1 .. zk)
    mk_rec_arg ::
      [(VarName, Term)] ->             -- telescope describing the zs
      [Term] ->                        -- actual values for the indices, shifted under zs
      Term ->                         -- actual value in recursive position
      IO Term
    mk_rec_arg zs_ctx ixs x =
      -- eta expand over the zs and apply the Recursor form
      do zs <- scVariables sc zs_ctx
         x_zs <- scApplyAll sc x zs
         r_ixs <- scApplyAll sc r ixs
         body <- scApply sc r_ixs x_zs
         scLambdaList sc zs_ctx body

-- | Build the type of the @p_ret@ function, also known as the "motive"
-- function, of a recursor on datatype @d@. This type has the form
--
-- > (i1::ix1) -> .. -> (im::ixm) -> d p1 .. pn i1 .. im -> s
--
-- where the @pi@ are the parameters of @d@, the @ixj@ are the indices
-- of @d@, and @s@ is any sort supplied as an argument.
-- Parameter variables @p1 .. pn@ will be free in the resulting term.
scRecursorMotiveType :: SharedContext -> DataType -> Sort -> IO Term
scRecursorMotiveType sc dt s =
  do param_vars <- scVariables sc (dtParams dt)
     ix_vars <- scVariables sc (dtIndices dt)
     d <- scConstApply sc (dtName dt) (param_vars ++ ix_vars)
     ret <- scFun sc d =<< scSort sc s
     scPiList sc (dtIndices dt) ret

-- | Build the type of a recursor for datatype @d@ that has been
-- applied to parameters, a motive function, and a full set of
-- eliminator functions. This type has the form
--
-- > (i1:ix1) -> .. -> (im:ixm) ->
-- >   (arg : d p1 .. pn i1 .. im) -> motive i1 .. im arg
--
-- where the @pi@ are the parameters of @d@, and the @ixj@ are the
-- indices of @d@.
-- Parameter variables @p1 .. pn@ will be free in the resulting term.
scRecursorAppType :: SharedContext -> DataType -> Term -> IO Term
scRecursorAppType sc dt motive =
  do param_vars <- scVariables sc (dtParams dt)
     ix_vars <- scVariables sc (dtIndices dt)
     d <- scConstApply sc (dtName dt) (param_vars ++ ix_vars)
     let arg_vn = dtArgName dt
     arg_var <- scVariable sc arg_vn d
     ret <- scApplyAll sc motive (ix_vars ++ [arg_var])
     scPiList sc (dtIndices dt ++ [(arg_vn, d)]) ret

-- | Build the full type of an unapplied recursor for datatype @d@
-- with elimination to sort @s@.
-- This type has the form
--
-- > (p1:pt1) -> .. -> (pn::ptn) ->
-- > (motive : (i1::ix1) -> .. -> (im::ixm) -> d p1 .. pn i1 .. im -> s) ->
-- > (elim1 : ..) -> .. (elimk : ..) ->
-- > (i1:ix1) -> .. -> (im:ixm) ->
-- >   (arg : d p1 .. pn i1 .. im) -> motive i1 .. im arg
scRecursorType :: SharedContext -> DataType -> Sort -> IO Term
scRecursorType sc dt s =
  do let d = dtName dt

     -- Compute the type of the motive function, which has the form
     -- (i1:ix1) -> .. -> (im:ixm) -> d p1 .. pn i1 .. im -> s
     motive_ty <- scRecursorMotiveType sc dt s
     let motive_vn = dtMotiveName dt
     motive_var <- scVariable sc motive_vn motive_ty

     -- Compute the types of the elimination functions
     elims_tps <-
       forM (dtCtors dt) $ \ctor ->
       ctxCtorElimType sc d (ctorName ctor) motive_var (ctorArgStruct ctor)

     scPiList sc (dtParams dt) =<<
       scPi sc motive_vn motive_ty =<<
       scFunAll sc elims_tps =<<
       scRecursorAppType sc dt motive_var

-- | Reduce an application of a recursor. This is known in the Coq literature as
-- an iota reduction. More specifically, the call
--
-- > scReduceRecursor sc rec crec ci [x1, .., xk]
--
-- reduces the term @(Recursor r elims ixs (CtorApp ci ps xs))@ to
--
-- > fi x1 (maybe rec_tm_1) .. xk (maybe rec_tm_k)
--
-- where @maybe rec_tm_i@ indicates an optional recursive call of the recursor
-- on one of the @xi@. These recursive calls only exist for those arguments
-- @xi@. See the documentation for 'ctxReduceRecursor' and the
-- 'ctorIotaReduction' field for more details.
scReduceRecursor ::
  SharedContext ->
  Term {- ^ recursor term -} ->
  CompiledRecursor {- ^ concrete data included in the recursor term -} ->
  [Term] {- ^ datatype parameters -} ->
  Term {- ^ motive function -} ->
  [Term] {- ^ eliminator functions -} ->
  Name {- ^ constructor name -} ->
  [Term] {- ^ constructor arguments -} ->
  IO Term
scReduceRecursor sc r crec params motive elims c args =
  do mres <- lookupVarIndexInMap (nameIndex c) <$> scGetModuleMap sc
     let cs_fs = Map.fromList (zip (map nameIndex (recursorCtorOrder crec)) elims)
     r_applied <- scApplyAll sc r (params ++ motive : elims)
     case mres of
       Just (ResolvedCtor ctor) ->
         -- The ctorIotaReduction field caches the result of iota reduction, which
         -- we just substitute into to perform the reduction
         ctorIotaReduction sc ctor r_applied cs_fs args
       _ ->
         panic "scReduceRecursor" ["Could not find constructor: " <> toAbsoluteName (nameInfo c)]

-- | Function for computing the result of one step of iota reduction
-- of the term
--
-- > dt#rec params elims ixs (c params args)
--
-- The arguments to this function are the recursor value (applied to
-- params and elims), a mapping from constructor name indices to
-- eliminator functions, and the arguments to the constructor.
ctorIotaReduction ::
  SharedContext ->
  Ctor ->
  Term {- ^ recursor term -} ->
  Map VarIndex Term {- ^ constructor eliminators -} ->
  [Term] {- ^ constructor arguments -} ->
  IO Term
ctorIotaReduction sc ctor r cs_fs args =
  ctxReduceRecursor sc r elim args (ctorArgStruct ctor)
  where
    elim =
      case Map.lookup (nameIndex (ctorName ctor)) cs_fs of
        Just e -> e
        Nothing ->
          panic "ctorIotaReduction"
          ["no eliminator for constructor " <> toAbsoluteName (nameInfo (ctorName ctor))]

--------------------------------------------------------------------------------
-- Reduction to head-normal form

-- | An elimination for 'scWhnf'
data WHNFElim
  = ElimApp Term
  | ElimProj FieldName
  | ElimPair Bool
  | ElimRecursor Term CompiledRecursor [Term] Term [Term] [Term]
    -- ^ recursor, compiled recursor, params, motive, eliminators, indices

-- | Reduces beta-redexes, tuple/record selectors, recursor applications, and
-- definitions at the top level of a term.
scWhnf :: SharedContext -> Term -> IO Term
scWhnf sc t0 =
  do cache <- newCacheIntMap
     let ?cache = cache in memo t0
  where
    memo :: (?cache :: Cache IO TermIndex Term) => Term -> IO Term
    memo t =
      case t of
        STApp { stAppIndex = i } -> useCache ?cache i (go [] t)

    go :: (?cache :: Cache IO TermIndex Term) => [WHNFElim] -> Term -> IO Term
    go xs                     (asApp            -> Just (t, x)) = go (ElimApp x : xs) t
    go xs                     (asRecordSelector -> Just (t, n)) = go (ElimProj n : xs) t
    go xs                     (asPairSelector -> Just (t, i))   = go (ElimPair i : xs) t
    go (ElimApp x : xs)       (asLambda -> Just (vn, _, body))  = betaReduce xs [(vn, x)] body
    go (ElimPair i : xs)      (asPairValue -> Just (a, b))      = go xs (if i then b else a)
    go (ElimProj fld : xs)    (asRecordValue -> Just elems)     = case Map.lookup fld elems of
                                                                    Just t -> go xs t
                                                                    Nothing ->
                                                                      error "scWhnf: field missing in record"
    go xs                     (asRecursorApp -> Just (r, crec)) | Just (params, ElimApp motive : xs1) <- splitApps (recursorNumParams crec) xs
                                                                , Just (elims, xs2) <- splitApps (length (recursorCtorOrder crec)) xs1
                                                                , Just (ixs, ElimApp x : xs') <- splitApps (recursorNumIxs crec) xs2
                                                                = go (ElimRecursor r crec params motive elims ixs : xs') x
    go xs                     t@(asConstant -> Just nm)         = do r <- resolveConstant nm
                                                                     case r of
                                                                       ResolvedDef d ->
                                                                         case defBody d of
                                                                           Just body -> go xs body
                                                                           Nothing -> foldM reapply t xs
                                                                       ResolvedCtor ctor ->
                                                                         case asArgsRec xs of
                                                                           Nothing -> foldM reapply t xs
                                                                           Just (rt, crec, params, motive, elims, args, xs') ->
                                                                             do let args' = drop (ctorNumParams ctor) args
                                                                                scReduceRecursor sc rt crec params motive elims nm args' >>= go xs'
                                                                       ResolvedDataType _ ->
                                                                         foldM reapply t xs

    go xs                     t                                 = foldM reapply t xs

    betaReduce :: (?cache :: Cache IO TermIndex Term) =>
      [WHNFElim] -> [(VarName, Term)] -> Term -> IO Term
    betaReduce (ElimApp x : xs) vs (asLambda -> Just (vn,_,body)) =
      betaReduce xs ((vn, x) : vs) body
    betaReduce xs vs body =
      do let subst = IntMap.fromList [ (vnIndex vn, x) | (vn, x) <- vs ]
         body' <- scInstantiate sc subst body
         go xs body'

    reapply :: Term -> WHNFElim -> IO Term
    reapply t (ElimApp x) = scApply sc t x
    reapply t (ElimProj i) = scRecordSelect sc t i
    reapply t (ElimPair i) = scPairSelector sc t i
    reapply t (ElimRecursor r _crec params motive elims ixs) =
      do f <- scApplyAll sc r (params ++ motive : elims ++ ixs)
         scApply sc f t

    resolveConstant :: Name -> IO ResolvedName
    resolveConstant nm = requireNameInMap nm <$> scGetModuleMap sc

    -- look for a prefix of ElimApps followed by an ElimRecursor
    asArgsRec :: [WHNFElim] -> Maybe (Term, CompiledRecursor, [Term], Term, [Term], [Term], [WHNFElim])
    asArgsRec (ElimRecursor r crec params motive elims _ixs : xs) = Just (r, crec, params, motive, elims, [], xs)
    asArgsRec (ElimApp x : xs) =
      case asArgsRec xs of
        Just (r, crec, params, motive, elims, args, xs') -> Just (r, crec, params, motive, elims, x : args, xs')
        Nothing -> Nothing
    asArgsRec _ = Nothing

    -- look for a prefix of n ElimApps
    splitApps :: Int -> [WHNFElim] -> Maybe ([Term], [WHNFElim])
    splitApps 0 xs = Just ([], xs)
    splitApps n (ElimApp t : xs) =
       do (ts, xs') <- splitApps (n-1) xs
          Just (t : ts, xs')
    splitApps _ _ = Nothing


-- | Test if two terms are convertible up to a given evaluation procedure. In
-- practice, this procedure is usually 'scWhnf', possibly combined with some
-- rewriting.
scConvertibleEval :: SharedContext
                  -> (SharedContext -> Term -> IO Term)
                  -> Bool -- ^ Should constants be unfolded during this check?
                  -> Term
                  -> Term
                  -> IO Bool
scConvertibleEval sc eval unfoldConst tm1 tm2 = do
   c <- newCache
   go c IntMap.empty tm1 tm2

 where whnf :: Cache IO TermIndex Term -> Term -> IO (TermF Term)
       whnf c t@(STApp{ stAppIndex = idx}) =
         unwrapTermF <$> useCache c idx (eval sc t)

       go :: Cache IO TermIndex Term -> IntMap VarIndex -> Term -> Term -> IO Bool
       go _c vm (STApp{stAppIndex = idx1, stAppVarTypes = vt1}) (STApp{stAppIndex = idx2})
         | IntMap.disjoint vt1 vm && idx1 == idx2 = pure True   -- succeed early case
       go c vm t1 t2 = join (goF c vm <$> whnf c t1 <*> whnf c t2)

       goF :: Cache IO TermIndex Term -> IntMap VarIndex -> TermF Term -> TermF Term -> IO Bool

       goF _c _vm (Constant nx) (Constant ny) | nameIndex nx == nameIndex ny = pure True
       goF c vm (Constant nx) y
           | unfoldConst =
             do mx <- scFindDefBody sc (nameIndex nx)
                case mx of
                  Just x -> join (goF c vm <$> whnf c x <*> return y)
                  Nothing -> pure False
       goF c vm x (Constant ny)
           | unfoldConst =
             do my <- scFindDefBody sc (nameIndex ny)
                case my of
                  Just y -> join (goF c vm <$> return x <*> whnf c y)
                  Nothing -> pure False

       goF c vm (FTermF ftf1) (FTermF ftf2) =
               case zipWithFlatTermF (go c vm) ftf1 ftf2 of
                 Nothing -> return False
                 Just zipped -> Fold.and <$> traverse id zipped

       goF c vm (App f1 x1) (App f2 x2) =
              pure (&&) <*> go c vm f1 f2 <*> go c vm x1 x2

       goF c vm (Lambda (vnIndex -> i1) ty1 body1) (Lambda (vnIndex -> i2) ty2 body2) =
         pure (&&) <*> go c vm ty1 ty2 <*> go c vm' body1 body2
           where vm' = if i1 == i2 then vm else IntMap.insert i1 i2 vm

       goF c vm (Pi (vnIndex -> i1) ty1 body1) (Pi (vnIndex -> i2) ty2 body2) =
         pure (&&) <*> go c vm ty1 ty2 <*> go c vm' body1 body2
           where vm' = if i1 == i2 then vm else IntMap.insert i1 i2 vm

       goF c vm (Variable x1 t1) (Variable x2 t2)
         | i' == vnIndex x2 = go c vm t1 t2
           where i' = case IntMap.lookup (vnIndex x1) vm of
                        Nothing -> vnIndex x1
                        Just i -> i

       -- final catch-all case
       goF _c _vm _x _y = pure False

-- | Test if two terms are convertible using 'scWhnf' for evaluation
scConvertible :: SharedContext
              -> Bool -- ^ Should constants be unfolded during this check?
              -> Term
              -> Term
              -> IO Bool
scConvertible sc = scConvertibleEval sc scWhnf


--------------------------------------------------------------------------------
-- Type checking

-- | @reducePi sc (Pi x tp body) t@ returns @[t/x]body@, and otherwise fails
reducePi :: SharedContext -> Term -> Term -> IO Term
reducePi sc t arg = do
  t' <- scWhnf sc t
  case asPi t' of
    Just (vn, _, body) ->
      scInstantiateBeta sc (IntMap.singleton (vnIndex vn) arg) body
    _ ->
      fail $ unlines ["reducePi: not a Pi term", showTerm t']


-- | Look up the type of a global constant, primitive, data type, or
-- data constructor, given its name as an 'Ident'.
scTypeOfIdent :: SharedContext -> Ident -> IO Term
scTypeOfIdent sc ident =
  do mm <- scGetModuleMap sc
     case resolveNameInMap mm ident of
       Just r -> pure (resolvedNameType r)
       Nothing -> fail ("scTypeOfIdent: Identifier not found: " ++ show ident)

-- | Look up the type of a global constant, given its 'Name'.
scTypeOfName :: SharedContext -> Name -> IO Term
scTypeOfName sc nm =
  do mm <- scGetModuleMap sc
     case lookupVarIndexInMap (nameIndex nm) mm of
       Just r -> pure (resolvedNameType r)
       Nothing -> fail ("scTypeOfName: Name not found: " ++ show nm)

-- | Computes the type of a term as quickly as possible, assuming that
-- the term is well-typed.
scTypeOf :: SharedContext -> Term -> IO Term
scTypeOf sc t0 = State.evalStateT (memo t0) Map.empty
  where
    memo :: Term -> State.StateT (Map TermIndex Term) IO Term
    memo STApp{ stAppIndex = i, stAppTermF = t} = do
      table <- State.get
      case Map.lookup i table of
        Just x  -> return x
        Nothing -> do
          x <- termf t
          State.modify (Map.insert i x)
          return x
    toSort :: Term -> State.StateT (Map TermIndex Term) IO Sort
    toSort t =
      do t' <- liftIO (scWhnf sc t)
         case asSort t' of
           Just s -> return s
           Nothing -> fail "scTypeOf: type error: expected sort"
    sort :: Term -> State.StateT (Map TermIndex Term) IO Sort
    sort t = toSort =<< memo t
    termf :: TermF Term -> State.StateT (Map TermIndex Term) IO Term
    termf tf =
      case tf of
        FTermF ftf -> ftermf ftf
        App x y -> do
          tx <- memo x
          lift $ reducePi sc tx y
        Lambda x tp rhs ->
          do rtp <- lift $ scTypeOf sc rhs
             lift $ scPi sc x tp rtp
        Pi _x tp rhs ->
          do ltp <- sort tp
             rtp <- toSort =<< lift (scTypeOf sc rhs)
             -- NOTE: the rule for type-checking Pi types is that (Pi x a b) is a Prop
             -- when b is a Prop (this is a forall proposition), otherwise it is a
             -- (Type (max (sortOf a) (sortOf b)))
             let srt = if rtp == propSort then propSort else max ltp rtp
             lift $ scSort sc srt
        Constant nm ->
          do mm <- liftIO $ scGetModuleMap sc
             case lookupVarIndexInMap (nameIndex nm) mm of
               Just r -> pure $ resolvedNameType r
               _ -> panic "scTypeOf" ["Constant not found: " <> toAbsoluteName (nameInfo nm)]
        Variable _x tp ->
          pure tp
    ftermf :: FlatTermF Term
           -> State.StateT (Map TermIndex Term) IO Term
    ftermf tf =
      case tf of
        UnitValue -> lift $ scUnitType sc
        UnitType -> lift $ scSort sc (mkSort 0)
        PairValue x y -> do
          tx <- memo x
          ty <- memo y
          lift $ scPairType sc tx ty
        PairType x y -> do
          sx <- sort x
          sy <- sort y
          lift $ scSort sc (max sx sy)
        PairLeft t -> do
          tp <- (liftIO . scWhnf sc) =<< memo t
          case asPairType tp of
            Just (t1, _) -> return t1
            Nothing -> fail "scTypeOf: type error: expected pair type"
        PairRight t -> do
          tp <- (liftIO . scWhnf sc) =<< memo t
          case asPairType tp of
            Just (_, t2) -> return t2
            Nothing -> fail "scTypeOf: type error: expected pair type"
        Recursor crec ->
          do mm <- liftIO $ scGetModuleMap sc
             let d = recursorDataType crec
             case lookupVarIndexInMap (nameIndex d) mm of
               Just (ResolvedDataType dt) ->
                 liftIO $ scRecursorType sc dt (recursorSort crec)
               _ -> fail $ "scTypeOf: Could not find datatype: " ++ show d
        RecordType elems ->
          do max_s <- maximum <$> mapM (sort . snd) elems
             lift $ scSort sc max_s
        RecordValue elems ->
          do elem_tps <- mapM (\(fld,t) -> (fld,) <$> memo t) elems
             lift $ scRecordType sc elem_tps
        RecordProj t fld ->
          do tp <- (liftIO . scWhnf sc) =<< memo t
             case asRecordType tp of
               Just (Map.lookup fld -> Just f_tp) -> return f_tp
               Just _ -> fail "Record field not in record type"
               Nothing -> fail "Record project of non-record type"
        Sort s _ -> lift $ scSort sc (sortOf s)
        ArrayValue tp vs -> lift $ do
          n <- scNat sc (fromIntegral (V.length vs))
          scVecType sc n tp
        StringLit{} -> lift $ scStringType sc

--------------------------------------------------------------------------------

-- | Imports a term built in a different shared context into the given
-- shared context. The caller must ensure that all the global constants
-- appearing in the term are valid in the new context.
scImport :: SharedContext -> Term -> IO Term
scImport sc t0 =
    do cache <- newCache
       go cache t0
  where
    go :: Cache IO TermIndex Term -> Term -> IO Term
    go cache (STApp{ stAppIndex = idx, stAppTermF = tf}) =
          useCache cache idx (scTermF sc =<< traverse (go cache) tf)

--------------------------------------------------------------------------------
-- Beta Normalization

-- | Instantiate some of the named variables in the term, reducing any
-- new beta redexes created in the process.
-- The substitution 'IntMap' is keyed by 'VarIndex'.
-- If the input term and all terms in the substitution are in
-- beta-normal form, then the result will also be beta-normal.
-- If a substituted term is a lambda, and it is substituted into the
-- left side of an application, creating a new beta redex, then it
-- will trigger further beta reduction.
-- Existing beta redexes in the input term or substitution are
-- not reduced.
scInstantiateBeta :: SharedContext -> IntMap Term -> Term -> IO Term
scInstantiateBeta sc sub t0 =
  do let domainVars = IntMap.keysSet sub
     let rangeVars = foldMap freeVars sub
     cache <- newCacheIntMap
     let memo :: Term -> IO Term
         memo t@STApp{stAppIndex = i} = useCache cache i (go t)
         go :: Term -> IO Term
         go t
           | IntSet.disjoint domainVars (freeVars t) = pure t
           | otherwise = goArgs t []
         goArgs :: Term -> [Term] -> IO Term
         goArgs t args =
           case unwrapTermF t of
             FTermF ftf ->
               do ftf' <- traverse memo ftf
                  t' <- scFlatTermF sc ftf'
                  scApplyAll sc t' args
             App t1 t2 ->
               do t2' <- memo t2
                  goArgs t1 (t2' : args)
             Lambda x t1 t2 ->
               do t1' <- memo t1
                  (x', t2') <- goBinder x t1' t2
                  t' <- scLambda sc x' t1' t2'
                  scApplyAll sc t' args
             Pi x t1 t2 ->
               do t1' <- memo t1
                  (x', t2') <- goBinder x t1' t2
                  t' <- scPi sc x' t1' t2'
                  scApplyAll sc t' args
             Constant {} ->
               scApplyAll sc t args
             Variable x t1 ->
               case IntMap.lookup (vnIndex x) sub of
                 Just t' -> scApplyAllBeta sc t' args
                 Nothing ->
                   do t1' <- memo t1
                      t' <- scVariable sc x t1'
                      scApplyAll sc t' args
         goBinder :: VarName -> Term -> Term -> IO (VarName, Term)
         goBinder x@(vnIndex -> i) t body
           | IntSet.member i rangeVars =
               -- Possibility of capture; rename bound variable.
               do x' <- scFreshVarName sc (vnName x)
                  var <- scVariable sc x' t
                  let sub' = IntMap.insert i var sub
                  body' <- scInstantiateBeta sc sub' body
                  pure (x', body')
           | IntMap.member i sub =
               -- Shadowing; remove entry from substitution.
               do let sub' = IntMap.delete i sub
                  body' <- scInstantiateBeta sc sub' body
                  pure (x, body')
           | otherwise =
               -- No possibility of shadowing or capture.
               do body' <- memo body
                  pure (x, body')
     go t0

-- | Apply a function 'Term' to a list of zero or more arguments.
-- If the function is a lambda term, then beta reduce the arguments
-- into the function body.
-- If all input terms are in beta-normal form, then the result will
-- also be beta-normal.
scApplyAllBeta :: SharedContext -> Term -> [Term] -> IO Term
scApplyAllBeta _ t0 [] = pure t0
scApplyAllBeta sc t0 (arg0 : args0) =
  case asLambda t0 of
    Nothing -> scApplyAll sc t0 (arg0 : args0)
    Just (x, _, body) -> go (IntMap.singleton (vnIndex x) arg0) body args0
  where
    go :: IntMap Term -> Term -> [Term] -> IO Term
    go sub (asLambda -> Just (x, _, body)) (arg : args) =
      go (IntMap.insert (vnIndex x) arg sub) body args
    go sub t args =
      do t' <- scInstantiateBeta sc sub t
         scApplyAllBeta sc t' args

-- | Apply a function to an argument, beta-reducing if the function is
-- a lambda.
-- If both input terms are in beta-normal form, then the result will
-- also be beta-normal.
scApplyBeta :: SharedContext -> Term -> Term -> IO Term
scApplyBeta sc f arg = scApplyAllBeta sc f [arg]

-- | Internal function: Instantiate free variables within a term,
-- apply it to a list of arguments, and beta-normalize the result.
-- Precondition: All terms in the substitution map and the list of
-- arguments are already in beta-normal form.
scBetaNormalizeAux ::
  SharedContext -> IntMap Term -> Term -> [Term] -> IO Term
scBetaNormalizeAux sc sub t0 args0 =
  do let rangeVars = foldMap freeVars sub
     -- The cache memoizes the result of normalizing a given
     -- expression under the current substitution; recursive calls
     -- that change the substitution must start a new memo table.
     cache <- newCacheIntMap
     let memo :: Term -> IO Term
         memo t@STApp{ stAppIndex = i } = useCache cache i (go t [])
         go :: Term -> [Term] -> IO Term
         go t args =
           case unwrapTermF t of
             FTermF ftf ->
               do ftf' <- traverse memo ftf
                  t' <- scFlatTermF sc ftf'
                  scApplyAll sc t' args
             App t1 t2 ->
               do t2' <- memo t2
                  go t1 (t2' : args)
             Lambda x t1 t2 ->
               case args of
                 arg : args' ->
                   -- No possibility of capture here, as the binder is
                   -- going away. If x is already in the map,
                   -- overwriting that entry is what we want.
                   do let sub' = IntMap.insert (vnIndex x) arg sub
                      scBetaNormalizeAux sc sub' t2 args'
                 [] ->
                   do t1' <- memo t1
                      -- Freshen bound variable if it can capture.
                      x' <-
                        if IntSet.member (vnIndex x) rangeVars
                        then scFreshVarName sc (vnName x)
                        else pure x
                      var <- scVariable sc x' t1'
                      let sub' = IntMap.insert (vnIndex x) var sub
                      t2' <- scBetaNormalizeAux sc sub' t2 []
                      scLambda sc x' t1' t2'
             Pi x t1 t2 ->
               -- Pi expressions may never be applied to arguments
               do t1' <- memo t1
                  -- Freshen bound variable if it can capture.
                  x' <-
                    if IntSet.member (vnIndex x) rangeVars
                    then scFreshVarName sc (vnName x)
                    else pure x
                  var <- scVariable sc x' t1'
                  let sub' = IntMap.insert (vnIndex x) var sub
                  t2' <- scBetaNormalizeAux sc sub' t2 []
                  scPi sc x' t1' t2'
             Constant{} ->
               scApplyAll sc t args
             Variable x _ ->
               -- All bound variables will be present in the map.
               -- To preserve term invariants, free variables must
               -- have their type annotations left unmodified.
               case IntMap.lookup (vnIndex x) sub of
                 Nothing ->
                   scApplyAll sc t args
                 Just t' ->
                   scApplyAllBeta sc t' args
     go t0 args0

-- | Beta-reduce a term to normal form.
betaNormalize :: SharedContext -> Term -> IO Term
betaNormalize sc t = scBetaNormalizeAux sc IntMap.empty t []


--------------------------------------------------------------------------------
-- Building shared terms

-- | Apply a function 'Term' to zero or more argument 'Term's.
scApplyAll :: SharedContext -> Term -> [Term] -> IO Term
scApplyAll sc = foldlM (scApply sc)

-- | Create a term from a 'Sort'.
scSort :: SharedContext -> Sort -> IO Term
scSort sc s = scFlatTermF sc (Sort s noFlags)

-- | Create a term from a 'Sort', and set the given advisory flags
scSortWithFlags :: SharedContext -> Sort -> SortFlags -> IO Term
scSortWithFlags sc s h = scFlatTermF sc (Sort s h)

-- | Create a term from a 'Sort', and set the advisory "inhabited" flag
scISort :: SharedContext -> Sort -> IO Term
scISort sc s = scSortWithFlags sc s $ noFlags { flagInhabited = True }

-- | Create a literal term from a 'Natural'.
scNat :: SharedContext -> Natural -> IO Term
scNat sc 0 = scGlobalDef sc "Prelude.Zero"
scNat sc n =
  do p <- scPos sc n
     scGlobalApply sc "Prelude.NatPos" [p]

scPos :: SharedContext -> Natural -> IO Term
scPos sc n
  | n <= 1    = scGlobalDef sc "Prelude.One"
  | otherwise =
    do arg <- scPos sc (div n 2)
       let ident = if even n then "Prelude.Bit0" else "Prelude.Bit1"
       scGlobalApply sc ident [arg]

-- | Create a literal term (of saw-core type @String@) from a 'Text'.
scString :: SharedContext -> Text -> IO Term
scString sc s = scFlatTermF sc (StringLit s)

-- | Create a term representing the primitive saw-core type @String@.
scStringType :: SharedContext -> IO Term
scStringType sc = scGlobalDef sc preludeStringIdent

-- | Create a vector term from a type (as a 'Term') and a list of 'Term's of
-- that type.
scVector :: SharedContext -> Term -> [Term] -> IO Term
scVector sc e xs = scFlatTermF sc (ArrayValue e (V.fromList xs))

-- | Create a record term from a 'Map' from 'FieldName's to 'Term's.
scRecord :: SharedContext -> Map FieldName Term -> IO Term
scRecord sc m = scFlatTermF sc (RecordValue $ Map.assocs m)

-- | Create a record field access term from a 'Term' representing a record and
-- a 'FieldName'.
scRecordSelect :: SharedContext -> Term -> FieldName -> IO Term
scRecordSelect sc t fname = scFlatTermF sc (RecordProj t fname)

-- | Create a term representing the type of a record from a list associating
-- field names (as 'FieldName's) and types (as 'Term's). Note that the order of
-- the given list is irrelevant, as record fields are not ordered.
scRecordType :: SharedContext -> [(FieldName, Term)] -> IO Term
scRecordType sc elem_tps = scFlatTermF sc (RecordType elem_tps)

-- | Create a unit-valued term.
scUnitValue :: SharedContext -> IO Term
scUnitValue sc = scFlatTermF sc UnitValue

-- | Create a term representing the unit type.
scUnitType :: SharedContext -> IO Term
scUnitType sc = scFlatTermF sc UnitType

-- | Create a pair term from two terms.
scPairValue :: SharedContext
            -> Term -- ^ The left projection
            -> Term -- ^ The right projection
            -> IO Term
scPairValue sc x y = scFlatTermF sc (PairValue x y)

-- | Create a term representing a pair type from two other terms, each
-- representing a type.
scPairType :: SharedContext
           -> Term -- ^ Left projection type
           -> Term -- ^ Right projection type
           -> IO Term
scPairType sc x y = scFlatTermF sc (PairType x y)

-- | Create an n-place tuple from a list (of length n) of 'Term's.
-- Note that tuples are nested pairs, associating to the right e.g.
-- @(a, (b, (c, d)))@.
scTuple :: SharedContext -> [Term] -> IO Term
scTuple sc [] = scUnitValue sc
scTuple _ [t] = return t
scTuple sc (t : ts) = scPairValue sc t =<< scTuple sc ts

-- | Create a term representing the type of an n-place tuple, from a list
-- (of length n) of 'Term's, each representing a type.
scTupleType :: SharedContext -> [Term] -> IO Term
scTupleType sc [] = scUnitType sc
scTupleType _ [t] = return t
scTupleType sc (t : ts) = scPairType sc t =<< scTupleType sc ts

-- | Create a term giving the left projection of a 'Term' representing a pair.
scPairLeft :: SharedContext -> Term -> IO Term
scPairLeft sc t = scFlatTermF sc (PairLeft t)

-- | Create a term giving the right projection of a 'Term' representing a pair.
scPairRight :: SharedContext -> Term -> IO Term
scPairRight sc t = scFlatTermF sc (PairRight t)

-- | Create a term representing either the left or right projection of the
-- given 'Term', depending on the given 'Bool': left if @False@, right if @True@.
scPairSelector :: SharedContext -> Term -> Bool -> IO Term
scPairSelector sc t False = scPairLeft sc t
scPairSelector sc t True = scPairRight sc t

-- | @scTupleSelector sc t i n@ returns a term selecting the @i@th component of
-- an @n@-place tuple 'Term', @t@.
scTupleSelector ::
  SharedContext -> Term ->
  Int {- ^ 1-based index -} ->
  Int {- ^ tuple size -} ->
  IO Term
scTupleSelector sc t i n
  | n == 1    = return t
  | i == 1    = scPairLeft sc t
  | i > 1     = do t' <- scPairRight sc t
                   scTupleSelector sc t' (i - 1) (n - 1)
  | otherwise = fail "scTupleSelector: non-positive index"

-- | Create a term representing the type of a non-dependent function, given a
-- parameter and result type (as 'Term's).
scFun :: SharedContext
      -> Term -- ^ The parameter type
      -> Term -- ^ The result type
      -> IO Term
scFun sc a b = scTermF sc (Pi wildcardVarName a b)

-- | Create a term representing the type of a non-dependent n-ary function,
-- given a list of parameter types and a result type (as terms).
scFunAll :: SharedContext
         -> [Term] -- ^ The parameter types
         -> Term   -- ^ The result type
         -> IO Term
scFunAll sc argTypes resultType = foldrM (scFun sc) resultType argTypes

-- | Create a lambda term of multiple arguments (curried) from a list
-- associating parameter names to types (as 'Term's) and a body.
-- The parameters are listed outermost first.
-- Variable names in the parameter list are in scope for all parameter
-- types occurring later in the list.
scLambdaList :: SharedContext
             -> [(VarName, Term)] -- ^ List of parameter / parameter type pairs
             -> Term -- ^ The body
             -> IO Term
scLambdaList _ [] rhs = return rhs
scLambdaList sc ((nm,tp):r) rhs =
  scLambda sc nm tp =<< scLambdaList sc r rhs

-- | Create a (possibly dependent) function of multiple arguments (curried)
-- from a list associating parameter names to types (as 'Term's) and a body.
-- Variable names in the parameter list are in scope for all parameter
-- types occurring later in the list.
scPiList :: SharedContext
         -> [(VarName, Term)] -- ^ List of parameter / parameter type pairs
         -> Term -- ^ The body
         -> IO Term
scPiList _ [] rhs = return rhs
scPiList sc ((nm,tp):r) rhs = scPi sc nm tp =<< scPiList sc r rhs

-- | Define a global constant with the specified base name (as
-- 'Text'), body, and type.
-- The term for the body must not have any free variables.
-- A globally-unique name with the specified base name will be created
-- using 'scFreshName'.
scFreshConstant ::
  SharedContext ->
  Text {- ^ The base name -} ->
  Term {- ^ The body -} ->
  Term {- ^ The type -} ->
  IO Term
scFreshConstant sc name rhs ty =
  do unless (closedTerm rhs) $
       fail $ unlines
       [ "scFreshConstant: term contains free variables"
       , "name: " ++ Text.unpack name
       , "ty: " ++ showTerm ty
       , "rhs: " ++ showTerm rhs
       , "frees: " ++ unwords (map (Text.unpack . vnName . fst) (getAllVars rhs))
       ]
     nm <- scFreshName sc name
     scDeclareDef sc nm NoQualifier ty (Just rhs)

-- | Define a global constant with the specified name (as 'NameInfo'),
-- body, and type.
-- The URI in the given 'NameInfo' must be globally unique.
-- The term for the body must not have any free variables.
scDefineConstant ::
  SharedContext ->
  NameInfo {- ^ The name -} ->
  Term {- ^ The body -} ->
  Term {- ^ The type -} ->
  IO Term
scDefineConstant sc nmi rhs ty =
  do unless (closedTerm rhs) $
       fail $ unlines
       [ "scDefineConstant: term contains free variables"
       , "nmi: " ++ Text.unpack (toAbsoluteName nmi)
       , "ty: " ++ showTerm ty
       , "rhs: " ++ showTerm rhs
       , "frees: " ++ unwords (map (Text.unpack . vnName . fst) (getAllVars rhs))
       ]
     nm <- scRegisterName sc nmi
     scDeclareDef sc nm NoQualifier ty (Just rhs)


-- | Declare a global opaque constant with the specified name (as
-- 'NameInfo') and type.
-- Such a constant has no definition, but unlike a variable it may be
-- used in other constant definitions and is not subject to
-- lambda-binding or substitution.
scOpaqueConstant ::
  SharedContext ->
  NameInfo ->
  Term {- ^ type of the constant -} ->
  IO Term
scOpaqueConstant sc nmi ty =
  do nm <- scRegisterName sc nmi
     scDeclareDef sc nm NoQualifier ty Nothing

-- | Create a function application term from a global identifier and a list of
-- arguments (as 'Term's).
scGlobalApply :: SharedContext -> Ident -> [Term] -> IO Term
scGlobalApply sc i ts =
    do c <- scGlobalDef sc i
       scApplyAll sc c ts

-- | An optimized variant of 'scPairValue' that will reduce pairs of
-- the form @(x.L, x.R)@ to @x@.
scPairValueReduced :: SharedContext -> Term -> Term -> IO Term
scPairValueReduced sc x y =
  case (unwrapTermF x, unwrapTermF y) of
    (FTermF (PairLeft a), FTermF (PairRight b)) | a == b -> return a
    _ -> scPairValue sc x y

-- | An optimized variant of 'scPairTuple' that will reduce tuples of
-- the form @(x.1, x.2, x.3)@ to @x@.
scTupleReduced :: SharedContext -> [Term] -> IO Term
scTupleReduced sc [] = scUnitValue sc
scTupleReduced _ [t] = return t
scTupleReduced sc (t : ts) = scPairValueReduced sc t =<< scTupleReduced sc ts

-- | An optimized variant of 'scVector' that will reduce vectors of
-- the form @[at x 0, at x 1, at x 2, at x 3]@ to just @x@.
scVectorReduced :: SharedContext -> Term {- ^ element type -} -> [Term] {- ^ elements -} -> IO Term
scVectorReduced sc ety xs
  | (hd : _) <- xs
  , Just ((arr_sz :*: arr_tm) :*: 0) <- asAtOrBvAt hd
  , fromIntegral (length xs) == arr_sz
  , iall (\i x -> asAtOrBvAt x == Just ((arr_sz :*: arr_tm) :*: fromIntegral i)) xs =
    return arr_tm
  | otherwise = scVector sc ety xs
  where
    asAny :: Term -> Maybe ()
    asAny _ = Just ()

    asAt :: Term -> Maybe ((Natural :*: Term) :*: Natural)
    asAt = (((isGlobalDef "Prelude.at" @> asNat) <@ asAny) <@> return) <@> asNat

    asBvAt :: Term -> Maybe ((Natural :*: Term) :*: Natural)
    asBvAt = ((((isGlobalDef "Prelude.bvAt" @> asNat) <@ asAny) <@ asAny) <@> return) <@> asUnsignedConcreteBv

    asAtOrBvAt :: Term -> Maybe ((Natural :*: Term) :*: Natural)
    asAtOrBvAt term
      | res@Just{} <- asAt term = res
      | res@Just{} <- asBvAt term = res
      | otherwise = Nothing

------------------------------------------------------------
-- Building terms using prelude functions

-- | Create a term applying @Prelude.EqTrue@ to the given term.
--
-- > EqTrue : Bool -> sort 1;
scEqTrue :: SharedContext -> Term -> IO Term
scEqTrue sc t = scGlobalApply sc "Prelude.EqTrue" [t]

-- | Create a @Prelude.Bool@-typed term from the given Boolean: @Prelude.True@
-- for @True@, @Prelude.False@ for @False@.
scBool :: SharedContext -> Bool -> IO Term
scBool sc True  = scGlobalDef sc "Prelude.True"
scBool sc False = scGlobalDef sc "Prelude.False"

-- | Create a term representing the prelude Boolean type, @Prelude.Bool@.
scBoolType :: SharedContext -> IO Term
scBoolType sc = scGlobalDef sc "Prelude.Bool"

-- | Create a term representing the prelude Natural type.
scNatType :: SharedContext -> IO Term
scNatType sc = scGlobalDef sc preludeNatIdent

-- | Create a term representing a vector type, from a term giving the length
-- and a term giving the element type.
scVecType :: SharedContext
          -> Term -- ^ The length of the vector
          -> Term -- ^ The element type
          -> IO Term
scVecType sc n e = scGlobalApply sc preludeVecIdent [n, e]

-- | Create a term applying @Prelude.not@ to the given term.
--
-- > not : Bool -> Bool;
scNot :: SharedContext -> Term -> IO Term
scNot sc t = scGlobalApply sc "Prelude.not" [t]

-- | Create a term applying @Prelude.and@ to the two given terms.
--
-- > and : Bool -> Bool -> Bool;
scAnd :: SharedContext -> Term -> Term -> IO Term
scAnd sc x y = scGlobalApply sc "Prelude.and" [x,y]

-- | Create a term applying @Prelude.or@ to the two given terms.
--
-- > or : Bool -> Bool -> Bool;
scOr :: SharedContext -> Term -> Term -> IO Term
scOr sc x y = scGlobalApply sc "Prelude.or" [x,y]

-- | Create a term applying @Prelude.implies@ to the two given terms.
--
-- > implies : Bool -> Bool -> Bool;
scImplies :: SharedContext -> Term -> Term
          -> IO Term
scImplies sc x y = scGlobalApply sc "Prelude.implies" [x,y]

-- | Create a term applying @Prelude.xor@ to the two given terms.
--
-- > xor : Bool -> Bool -> Bool;
scXor :: SharedContext -> Term -> Term -> IO Term
scXor sc x y = scGlobalApply sc "Prelude.xor" [x,y]

-- | Create a term applying @Prelude.boolEq@ to the two given terms.
--
-- > boolEq : Bool -> Bool -> Bool;
scBoolEq :: SharedContext -> Term -> Term -> IO Term
scBoolEq sc x y = scGlobalApply sc "Prelude.boolEq" [x,y]

-- | Create a universally quantified bitvector term.
--
-- > bvForall : (n : Nat) -> (Vec n Bool -> Bool) -> Bool;
scBvForall :: SharedContext -> Term -> Term -> IO Term
scBvForall sc w f = scGlobalApply sc "Prelude.bvForall" [w, f]

-- | Create a non-dependent if-then-else term.
--
-- > ite : (a : sort 1) -> Bool -> a -> a -> a;
scIte :: SharedContext -> Term -> Term ->
         Term -> Term -> IO Term
scIte sc t b x y = scGlobalApply sc "Prelude.ite" [t, b, x, y]

-- | Build a conjunction from a list of boolean terms.
scAndList :: SharedContext -> [Term] -> IO Term
scAndList sc = conj . filter nontrivial
  where
    nontrivial x = asBool x /= Just True
    conj [] = scBool sc True
    conj [x] = return x
    conj (x : xs) = foldM (scAnd sc) x xs

-- | Build a conjunction from a list of boolean terms.
scOrList :: SharedContext -> [Term] -> IO Term
scOrList sc = disj . filter nontrivial
  where
    nontrivial x = asBool x /= Just False
    disj [] = scBool sc False
    disj [x] = return x
    disj (x : xs) = foldM (scOr sc) x xs


-- | Create a term applying @Prelude.append@ to two vectors.
--
-- > append : (m n : Nat) -> (e : sort 0) -> Vec m e -> Vec n e -> Vec (addNat m n) e;
scAppend :: SharedContext -> Term -> Term -> Term ->
            Term -> Term -> IO Term
scAppend sc m n t x y = scGlobalApply sc "Prelude.append" [m, n, t, x, y]

-- | Create a term applying @Prelude.join@ to a vector of vectors.
--
-- > join  : (m n : Nat) -> (a : sort 0) -> Vec m (Vec n a) -> Vec (mulNat m n) a;
scJoin :: SharedContext -> Term -> Term -> Term -> Term -> IO Term
scJoin sc m n a v = scGlobalApply sc "Prelude.join" [m, n, a, v]

-- | Create a term splitting a vector with @Prelude.split@.
--
-- > split : (m n : Nat) -> (a : sort 0) -> Vec (mulNat m n) a -> Vec m (Vec n a);
scSplit :: SharedContext -> Term -> Term -> Term -> Term -> IO Term
scSplit sc m n a v = scGlobalApply sc "Prelude.split" [m, n, a, v]

-- | Create a term selecting a range of values from a vector with @Prelude.slice@.
--
-- > slice : (e : sort 1) -> (i n o : Nat) -> Vec (addNat (addNat i n) o) e -> Vec n e;
scSlice :: SharedContext -> Term -> Term ->
           Term -> Term -> Term -> IO Term
scSlice sc e i n o a = scGlobalApply sc "Prelude.slice" [e, i, n, o, a]

-- | Create a term accessing a particular element of a vector with @get@.
--
-- > get : (n : Nat) -> (e : sort 0) -> Vec n e -> Fin n -> e;
scGet :: SharedContext -> Term -> Term ->
         Term -> Term -> IO Term
scGet sc n e v i = scGlobalApply sc (mkIdent preludeName "get") [n, e, v, i]

-- | Create a term accessing a particular element of a vector with @bvAt@,
-- which uses a bitvector for indexing.
--
-- > bvAt : (n : Nat) -> (a : sort 0) -> (w : Nat) -> Vec n a -> Vec w Bool -> a;
scBvAt :: SharedContext -> Term -> Term ->
         Term -> Term -> Term -> IO Term
scBvAt sc n a i xs idx = scGlobalApply sc (mkIdent preludeName "bvAt") [n, a, i, xs, idx]

-- | Create a term accessing a particular element of a vector, with a default
-- to return if the index is out of bounds.
--
-- > atWithDefault : (n : Nat) -> (a : sort 0) -> a -> Vec n a -> Nat -> a;
scAtWithDefault :: SharedContext -> Term -> Term -> Term -> Term -> Term -> IO Term
scAtWithDefault sc n a v xs idx = scGlobalApply sc (mkIdent preludeName "atWithDefault") [n, a, v, xs, idx]

-- | Create a term accessing a particular element of a vector, failing if the
-- index is out of bounds.
--
-- > at : (n : Nat) -> (a : sort 0) -> Vec n a -> Nat -> a;
scAt :: SharedContext -> Term -> Term ->
        Term -> Term -> IO Term
scAt sc n a xs idx = scGlobalApply sc (mkIdent preludeName "at") [n, a, xs, idx]

-- | Create a term evaluating to a vector containing a single element.
--
-- > single : (e : sort 1) -> e -> Vec 1 e;
scSingle :: SharedContext -> Term -> Term -> IO Term
scSingle sc e x = scGlobalApply sc (mkIdent preludeName "single") [e, x]

-- | Create a term computing the least significant bit of a bitvector, given a
-- length and bitvector.
--
-- > lsb : (n : Nat) -> Vec (Succ n) Bool -> Bool;
scLsb :: SharedContext -> Term -> Term -> IO Term
scLsb sc n x = scGlobalApply sc (mkIdent preludeName "lsb") [n, x]

-- | Create a term computing the most significant bit of a bitvector, given a
-- length and bitvector.
--
-- > msb : (n : Nat) -> Vec (Succ n) Bool -> Bool;
scMsb :: SharedContext -> Term -> Term -> IO Term
scMsb sc n x = scGlobalApply sc (mkIdent preludeName "lsb") [n, x]

-- Primitive operations on nats

-- | Create a term computing the sum of the two given (natural number) terms.
--
-- > addNat : Nat -> Nat -> Nat;
scAddNat :: SharedContext -> Term -> Term -> IO Term
scAddNat sc x y = scGlobalApply sc "Prelude.addNat" [x,y]

-- | Create a term computing the difference between the two given
-- (natural number) terms.
--
-- > subNat : Nat -> Nat -> Nat
scSubNat :: SharedContext -> Term -> Term -> IO Term
scSubNat sc x y = scGlobalApply sc "Prelude.subNat" [x,y]

-- | Create a term computing the product of the two given (natural number)
-- terms.
--
-- > mulNat : Nat -> Nat -> Nat;
scMulNat :: SharedContext -> Term -> Term -> IO Term
scMulNat sc x y = scGlobalApply sc "Prelude.mulNat" [x,y]

-- | Create a term computing the quotient of the two given (natural number)
-- terms.
--
-- > divNat : Nat -> Nat -> Nat;
scDivNat :: SharedContext -> Term -> Term -> IO Term
scDivNat sc x y = scGlobalApply sc "Prelude.divNat" [x,y]

-- | Create a term computing the remainder upon division of the two given
-- (natural number) terms.
--
-- > modNat : Nat -> Nat -> Nat;
scModNat :: SharedContext -> Term -> Term -> IO Term
scModNat sc x y = scGlobalApply sc "Prelude.modNat" [x,y]

-- | Create a term computing the quotient and remainder upon division of the
-- two given (natural number) terms, giving the result as a pair.
--
-- > divModNat : Nat -> Nat -> Nat * Nat;
scDivModNat :: SharedContext -> Term -> Term -> IO Term
scDivModNat sc x y = scGlobalApply sc "Prelude.divModNat" [x,y]

-- | Create a term computing whether the two given (natural number) terms are
-- equal.
--
-- > equalNat : Nat -> Nat -> Bool;
scEqualNat :: SharedContext -> Term -> Term -> IO Term
scEqualNat sc x y = scGlobalApply sc "Prelude.equalNat" [x,y]

-- | Create a term computing whether the first term (a natural number) is less
-- than the second term (also a natural number).
--
-- > ltNat : Nat -> Nat -> Bool;
scLtNat :: SharedContext -> Term -> Term -> IO Term
scLtNat sc x y = scGlobalApply sc "Prelude.ltNat" [x,y]

-- | Create a term computing the minimum of the two given (natural number)
-- terms.
--
-- > minNat : Nat -> Nat -> Nat
scMinNat :: SharedContext -> Term -> Term -> IO Term
scMinNat sc x y = scGlobalApply sc "Prelude.minNat" [x,y]

-- | Create a term computing the maximum of the two given (natural number)
-- terms.
--
-- > maxNat : Nat -> Nat -> Nat;
scMaxNat :: SharedContext -> Term -> Term -> IO Term
scMaxNat sc x y = scGlobalApply sc "Prelude.maxNat" [x,y]

-- Primitive operations on Integer

-- | Create a term representing the prelude Integer type.
scIntegerType :: SharedContext -> IO Term
scIntegerType sc = scGlobalDef sc preludeIntegerIdent

-- | Create an integer constant term from an 'Integer'.
scIntegerConst :: SharedContext -> Integer -> IO Term
scIntegerConst sc i
  | i >= 0    = scNatToInt sc =<< scNat sc (fromInteger i)
  | otherwise = scIntNeg sc =<< scNatToInt sc =<< scNat sc (fromInteger (- i))

-- | Create a term applying the integer addition primitive.
--
-- > intAdd : Integer -> Integer -> Integer
scIntAdd :: SharedContext -> Term -> Term -> IO Term
scIntAdd sc x y = scGlobalApply sc "Prelude.intAdd" [x, y]

-- | Create a term applying the integer subtraction primitive.
--
-- > intSub : Integer -> Integer -> Integer
scIntSub :: SharedContext -> Term -> Term -> IO Term
scIntSub sc x y = scGlobalApply sc "Prelude.intSub" [x, y]

-- | Create a term applying the integer multiplication primitive.
--
-- > intMul : Integer -> Integer -> Integer
scIntMul :: SharedContext -> Term -> Term -> IO Term
scIntMul sc x y = scGlobalApply sc "Prelude.intMul" [x, y]

-- | Create a term applying the integer division primitive.
--
-- > intDiv : Integer -> Integer -> Integer
scIntDiv :: SharedContext -> Term -> Term -> IO Term
scIntDiv sc x y = scGlobalApply sc "Prelude.intDiv" [x, y]

-- | Create a term applying the integer modulus primitive.
--
-- > intMod : Integer -> Integer -> Integer
scIntMod :: SharedContext -> Term -> Term -> IO Term
scIntMod sc x y = scGlobalApply sc "Prelude.intMod" [x, y]

-- | Create a term applying the integer min primitive.
--
-- > intMin : Integer -> Integer -> Integer
scIntMin :: SharedContext -> Term -> Term -> IO Term
scIntMin sc x y = scGlobalApply sc "Prelude.intMin" [x, y]

-- | Create a term applying the integer max primitive.
--
-- > intMax : Integer -> Integer -> Integer
scIntMax :: SharedContext -> Term -> Term -> IO Term
scIntMax sc x y = scGlobalApply sc "Prelude.intMax" [x, y]

-- | Create a term applying the negation integer primitive.
--
-- > intNeg : Integer -> Integer;
scIntNeg :: SharedContext -> Term -> IO Term
scIntNeg sc x = scGlobalApply sc "Prelude.intNeg" [x]

-- | Create a term applying the absolute value integer primitive.
--
-- > intAbs : Integer -> Integer;
scIntAbs :: SharedContext -> Term -> IO Term
scIntAbs sc x = scGlobalApply sc "Prelude.intAbs" [x]

-- | Create a term applying the integer equality testing primitive.
--
-- > intEq : Integer -> Integer -> Bool;
scIntEq :: SharedContext -> Term -> Term -> IO Term
scIntEq sc x y = scGlobalApply sc "Prelude.intEq" [x, y]

-- | Create a term applying the integer less-than-or-equal primitive.
--
-- > intLe : Integer -> Integer -> Bool;
scIntLe :: SharedContext -> Term -> Term -> IO Term
scIntLe sc x y = scGlobalApply sc "Prelude.intLe" [x, y]

-- | Create a term applying the integer less-than primitive.
--
-- > intLt : Integer -> Integer -> Bool;
scIntLt :: SharedContext -> Term -> Term -> IO Term
scIntLt sc x y = scGlobalApply sc "Prelude.intLt" [x, y]

-- | Create a term computing a @Nat@ from an @Integer@, if possible.
--
-- > intToNat : Integer -> Nat;
scIntToNat
   :: SharedContext -> Term -> IO Term
scIntToNat sc x = scGlobalApply sc "Prelude.intToNat" [x]

-- | Create a term computing an @Integer@ from a @Nat@.
--
-- > natToInt : Nat -> Integer;
scNatToInt
   :: SharedContext -> Term -> IO Term
scNatToInt sc x = scGlobalApply sc "Prelude.natToInt" [x]

-- | Create a term computing a bitvector of length n from an @Integer@, if
-- possible.
--
-- > intToBv : (n::Nat) -> Integer -> Vec n Bool;
scIntToBv
   :: SharedContext -> Term -> Term -> IO Term
scIntToBv sc n x = scGlobalApply sc "Prelude.intToBv" [n,x]

-- | Create a term computing an @Integer@ from a bitvector of length n.
-- This produces the unsigned value of the bitvector.
--
-- > bvToInt : (n : Nat) -> Vec n Bool -> Integer;
scBvToInt
   :: SharedContext -> Term -> Term -> IO Term
scBvToInt sc n x = scGlobalApply sc "Prelude.bvToInt" [n,x]

-- | Create a term computing an @Integer@ from a bitvector of length n.
-- This produces the 2's complement signed value of the bitvector.
--
-- > sbvToInt : (n : Nat) -> Vec n Bool -> Integer;
scSbvToInt
   :: SharedContext -> Term -> Term -> IO Term
scSbvToInt sc n x = scGlobalApply sc "Prelude.sbvToInt" [n,x]


-- Primitive operations on IntMod

-- | Create a term representing the prelude @IntMod@ type.
--
-- > IntMod : Nat -> sort 0;
scIntModType :: SharedContext -> Term -> IO Term
scIntModType sc n = scGlobalApply sc "Prelude.IntMod" [n]

-- | Convert an integer to an integer mod n.
--
-- > toIntMod : (n : Nat) -> Integer -> IntMod n;
scToIntMod :: SharedContext -> Term -> Term -> IO Term
scToIntMod sc n x = scGlobalApply sc "Prelude.toIntMod" [n, x]

-- | Convert an integer mod n to an integer.
--
-- > fromIntMod : (n : Nat) -> IntMod n -> Integer;
scFromIntMod :: SharedContext -> Term -> Term -> IO Term
scFromIntMod sc n x = scGlobalApply sc "Prelude.fromIntMod" [n, x]

-- | Equality test on the @IntMod@ type
--
-- > intModEq  : (n : Nat) -> IntMod n -> IntMod n -> Bool;
scIntModEq :: SharedContext -> Term -> Term -> Term -> IO Term
scIntModEq sc n x y = scGlobalApply sc "Prelude.intModEq" [n,x,y]

-- | Addition of @IntMod@ values
--
-- > intModAdd : (n : Nat) -> IntMod n -> IntMod n -> IntMod n;
scIntModAdd :: SharedContext -> Term -> Term -> Term -> IO Term
scIntModAdd sc n x y = scGlobalApply sc "Prelude.intModAdd" [n,x,y]

-- | Subtraction of @IntMod@ values
--
-- > intModSub : (n : Nat) -> IntMod n -> IntMod n -> IntMod n;
scIntModSub :: SharedContext -> Term -> Term -> Term -> IO Term
scIntModSub sc n x y = scGlobalApply sc "Prelude.intModSub" [n,x,y]

-- | Multiplication of @IntMod@ values
--
-- > intModMul : (n : Nat) -> IntMod n -> IntMod n -> IntMod n;
scIntModMul :: SharedContext -> Term -> Term -> Term -> IO Term
scIntModMul sc n x y = scGlobalApply sc "Prelude.intModMul" [n,x,y]

-- | Negation (additive inverse) of @IntMod@ values
--
-- > intModNeg : (n : Nat) -> IntMod n -> IntMod n;
scIntModNeg :: SharedContext -> Term -> Term -> IO Term
scIntModNeg sc n x = scGlobalApply sc "Prelude.intModNeg" [n,x]


-- Primitive operations on bitvectors

-- | Create a term computing the type of a length-n bitvector.
--
-- > bitvector : (n : Nat) -> sort 1
scBitvector :: SharedContext -> Natural -> IO Term
scBitvector sc size =
  do s <- scNat sc size
     t <- scBoolType sc
     scVecType sc s t

-- | Create a term computing a bitvector of length x from a @Nat@, if possible.
--
-- > bvNat : (n : Nat) -> Nat -> Vec n Bool;
scBvNat :: SharedContext -> Term -> Term -> IO Term
scBvNat sc x y = scGlobalApply sc "Prelude.bvNat" [x, y]

-- | Create a term computing a @Nat@ from a bitvector of length n.
--
-- > bvToNat : (n : Nat) -> Vec n Bool -> Nat;
scBvToNat :: SharedContext -> Natural -> Term -> IO Term
scBvToNat sc n x = do
    n' <- scNat sc n
    scGlobalApply sc "Prelude.bvToNat" [n',x]

-- | Create a @bvNat@ term computing a bitvector of the given length
-- representing the given 'Integer' value (if possible).
scBvConst :: SharedContext -> Natural -> Integer -> IO Term
scBvConst sc w v = assert (w <= fromIntegral (maxBound :: Int)) $ do
  x <- scNat sc w
  y <- scNat sc $ fromInteger $ v .&. (1 `shiftL` fromIntegral w - 1)
  scGlobalApply sc "Prelude.bvNat" [x, y]

-- | Create a vector literal term computing a bitvector of the given length
-- representing the given 'Integer' value (if possible).
scBvLit :: SharedContext -> Natural -> Integer -> IO Term
scBvLit sc w v = assert (w <= fromIntegral (maxBound :: Int)) $ do
  do bool_tp <- scBoolType sc
     bits <- mapM (scBool sc . testBit v)
                  [(fromIntegral w - 1), (fromIntegral w - 2) .. 0]
     scVector sc bool_tp bits

-- | Create a term computing the bitvector of given length representing 0 if
-- the other given term evaluates to @False@ and representing 1 if the other
-- given term evaluates to @True@.
--
-- > bvBool : (n : Nat) -> Bool -> Vec n Bool;
scBvBool :: SharedContext -> Term -> Term -> IO Term
scBvBool sc n x = scGlobalApply sc "Prelude.bvBool" [n, x]

-- | Create a term returning true if and only if the given bitvector represents
-- a nonzero value.
--
-- > bvNonzero : (n : Nat) -> Vec n Bool -> Bool;
scBvNonzero :: SharedContext -> Term -> Term -> IO Term
scBvNonzero sc n x = scGlobalApply sc "Prelude.bvNonzero" [n, x]

-- | Create a term computing the 2's complement negation of the given
-- bitvector.
-- > bvNeg : (n : Nat) -> Vec n Bool -> Vec n Bool;
scBvNeg :: SharedContext -> Term -> Term -> IO Term
scBvNeg sc n x = scGlobalApply sc "Prelude.bvNeg" [n, x]

-- | Create a term applying the bitvector addition primitive.
--
-- > bvAdd : (n : Nat) -> Vec n Bool -> Vec n Bool -> Vec n Bool;
scBvAdd :: SharedContext -> Term -> Term -> Term -> IO Term
scBvAdd sc n x y = scGlobalApply sc "Prelude.bvAdd" [n, x, y]

-- | Create a term applying the bitvector subtraction primitive.
--
-- > bvSub : (n : Nat) -> Vec n Bool -> Vec n Bool -> Vec n Bool;
scBvSub :: SharedContext -> Term -> Term -> Term -> IO Term
scBvSub sc n x y = scGlobalApply sc "Prelude.bvSub" [n, x, y]

-- | Create a term applying the bitvector multiplication primitive.
--
-- > bvMul : (n : Nat) -> Vec n Bool -> Vec n Bool -> Vec n Bool;
scBvMul :: SharedContext -> Term -> Term -> Term -> IO Term
scBvMul sc n x y = scGlobalApply sc "Prelude.bvMul" [n, x, y]

-- | Create a term applying the bitvector (unsigned) modulus primitive.
--
-- > bvURem : (n : Nat) -> Vec n Bool -> Vec n Bool -> Vec n Bool;
scBvURem :: SharedContext -> Term -> Term -> Term -> IO Term
scBvURem sc n x y = scGlobalApply sc "Prelude.bvURem" [n, x, y]

-- | Create a term applying the bitvector (unsigned) division primitive.
--
-- > bvUDiv : (n : Nat) -> Vec n Bool -> Vec n Bool -> Vec n Bool;
scBvUDiv :: SharedContext -> Term -> Term -> Term -> IO Term
scBvUDiv sc n x y = scGlobalApply sc "Prelude.bvUDiv" [n, x, y]

-- | Create a term applying the bitvector (signed) modulus primitive.
--
-- > bvSRem : (n : Nat) -> Vec n Bool -> Vec n Bool -> Vec n Bool;
scBvSRem :: SharedContext -> Term -> Term -> Term -> IO Term
scBvSRem sc n x y = scGlobalApply sc "Prelude.bvSRem" [n, x, y]

-- | Create a term applying the bitvector (signed) division primitive.
--
-- > bvSDiv : (n : Nat) -> Vec n Bool -> Vec n Bool -> Vec n Bool;
scBvSDiv :: SharedContext -> Term -> Term -> Term -> IO Term
scBvSDiv sc n x y = scGlobalApply sc "Prelude.bvSDiv" [n, x, y]

-- | Create a term applying the lg2 bitvector primitive.
--
-- > bvLg2 : (n : Nat) -> Vec n Bool -> Vec n Bool;
scBvLg2 :: SharedContext -> Term -> Term -> IO Term
scBvLg2 sc n x = scGlobalApply sc "Prelude.bvLg2" [n, x]

-- | Create a term applying the population count bitvector primitive.
--
-- > bvPopcount : (n : Nat) -> Vec n Bool -> Vec n Bool;
scBvPopcount :: SharedContext -> Term -> Term -> IO Term
scBvPopcount sc n x = scGlobalApply sc "Prelude.bvPopcount" [n, x]

-- | Create a term applying the leading zero counting bitvector primitive.
--
-- > bvCountLeadingZeros : (n : Nat) -> Vec n Bool -> Vec n Bool;
scBvCountLeadingZeros :: SharedContext -> Term -> Term -> IO Term
scBvCountLeadingZeros sc n x = scGlobalApply sc "Prelude.bvCountLeadingZeros" [n, x]

-- | Create a term applying the trailing zero counting bitvector primitive.
--
-- > bvCountTrailingZeros : (n : Nat) -> Vec n Bool -> Vec n Bool;
scBvCountTrailingZeros :: SharedContext -> Term -> Term -> IO Term
scBvCountTrailingZeros sc n x = scGlobalApply sc "Prelude.bvCountTrailingZeros" [n, x]

-- | Create a term applying the bit-wise and primitive.
--
-- > bvAnd : (n : Nat) -> Vec n Bool -> Vec n Bool -> Vec n Bool;
scBvAnd :: SharedContext -> Term -> Term -> Term -> IO Term
scBvAnd sc n x y = scGlobalApply sc "Prelude.bvAnd" [n, x, y]

-- | Create a term applying the bit-wise xor primitive.
--
-- > bvXor : (n : Nat) -> Vec n Bool -> Vec n Bool -> Vec n Bool;
scBvXor :: SharedContext -> Term -> Term -> Term -> IO Term
scBvXor sc n x y = scGlobalApply sc "Prelude.bvXor" [n, x, y]

-- | Create a term applying the bit-wise or primitive.
--
-- > bvOr : (n : Nat) -> Vec n Bool -> Vec n Bool -> Vec n Bool;
scBvOr :: SharedContext -> Term -> Term -> Term -> IO Term
scBvOr  sc n x y = scGlobalApply sc "Prelude.bvOr"  [n, x, y]

-- | Create a term applying the bit-wise negation primitive.
--
-- > bvNot : (n : Nat) -> Vec n Bool -> Vec n Bool;
scBvNot :: SharedContext -> Term -> Term -> IO Term
scBvNot sc n x = scGlobalApply sc "Prelude.bvNot" [n, x]

-- | Create a term computing whether the two given bitvectors (of equal length)
-- are equal.
--
-- > bvEq : (n : Nat) -> Vec n Bool -> Vec n Bool -> Bool;
scBvEq :: SharedContext -> Term -> Term -> Term -> IO Term
scBvEq  sc n x y = scGlobalApply sc "Prelude.bvEq"  [n, x, y]

-- | Create a term applying the bitvector (unsigned) greater-than-or-equal
-- primitive.
--
-- > bvuge : (n : Nat) -> Vec n Bool -> Vec n Bool -> Bool;
scBvUGe :: SharedContext -> Term -> Term -> Term -> IO Term
scBvUGe sc n x y = scGlobalApply sc "Prelude.bvuge" [n, x, y]

-- | Create a term applying the bitvector (unsigned) less-than-or-equal
-- primitive.
--
-- > bvule : (n : Nat) -> Vec n Bool -> Vec n Bool -> Bool;
scBvULe :: SharedContext -> Term -> Term -> Term -> IO Term
scBvULe sc n x y = scGlobalApply sc "Prelude.bvule" [n, x, y]

-- | Create a term applying the bitvector (unsigned) greater-than primitive.
--
-- > bvugt : (n : Nat) -> Vec n Bool -> Vec n Bool -> Bool;
scBvUGt :: SharedContext -> Term -> Term -> Term -> IO Term
scBvUGt sc n x y = scGlobalApply sc "Prelude.bvugt" [n, x, y]

-- | Create a term applying the bitvector (unsigned) less-than primitive.
--
-- > bvult : (n : Nat) -> Vec n Bool -> Vec n Bool -> Bool;
scBvULt :: SharedContext -> Term -> Term -> Term -> IO Term
scBvULt sc n x y = scGlobalApply sc "Prelude.bvult" [n, x, y]

-- | Create a term applying the bitvector (signed) greater-than-or-equal
-- primitive.
--
-- > bvsge : (n : Nat) -> Vec n Bool -> Vec n Bool -> Bool;
scBvSGe :: SharedContext -> Term -> Term -> Term -> IO Term
scBvSGe sc n x y = scGlobalApply sc "Prelude.bvsge" [n, x, y]

-- | Create a term applying the bitvector (signed) less-than-or-equal
-- primitive.
--
-- > bvsle : (n : Nat) -> Vec n Bool -> Vec n Bool -> Bool;
scBvSLe :: SharedContext -> Term -> Term -> Term -> IO Term
scBvSLe sc n x y = scGlobalApply sc "Prelude.bvsle" [n, x, y]

-- | Create a term applying the bitvector (signed) greater-than primitive.
--
-- > bvsgt : (n : Nat) -> Vec n Bool -> Vec n Bool -> Bool;
scBvSGt :: SharedContext -> Term -> Term -> Term -> IO Term
scBvSGt sc n x y = scGlobalApply sc "Prelude.bvsgt" [n, x, y]

-- | Create a term applying the bitvector (signed) less-than primitive.
--
-- > bvslt : (n : Nat) -> Vec n Bool -> Vec n Bool -> Bool;
scBvSLt :: SharedContext -> Term -> Term -> Term -> IO Term
scBvSLt sc n x y = scGlobalApply sc "Prelude.bvslt" [n, x, y]

-- | Create a term applying the left-shift primitive.
--
-- > bvShl : (n : Nat) -> Vec n Bool -> Nat -> Vec n Bool;
scBvShl :: SharedContext -> Term -> Term -> Term -> IO Term
scBvShl sc n x y = scGlobalApply sc "Prelude.bvShl" [n, x, y]

-- | Create a term applying the logical right-shift primitive.
--
-- > bvShr : (n : Nat) -> Vec n Bool -> Nat -> Vec n Bool;
scBvShr :: SharedContext -> Term -> Term -> Term -> IO Term
scBvShr sc n x y = scGlobalApply sc "Prelude.bvShr" [n, x, y]

-- | Create a term applying the arithmetic/signed right-shift primitive.
--
-- > bvSShr : (w : Nat) -> Vec (Succ w) Bool -> Nat -> Vec (Succ w) Bool;
scBvSShr :: SharedContext -> Term -> Term -> Term -> IO Term
scBvSShr sc n x y = scGlobalApply sc "Prelude.bvSShr" [n, x, y]

-- | Create a term applying the unsigned bitvector extension primitive.
--
-- > bvUExt : (m n : Nat) -> Vec n Bool -> Vec (addNat m n) Bool;
scBvUExt :: SharedContext -> Term -> Term -> Term -> IO Term
scBvUExt sc n m x = scGlobalApply sc "Prelude.bvUExt" [n,m,x]

-- | Create a term applying the signed bitvector extension primitive.
--
-- > bvSExt : (m n : Nat) -> Vec (Succ n) Bool -> Vec (addNat m (Succ n)) Bool;
scBvSExt :: SharedContext -> Term -> Term -> Term -> IO Term
scBvSExt sc n m x = scGlobalApply sc "Prelude.bvSExt" [n,m,x]

-- | Create a term applying the bitvector truncation primitive. Note that this
-- truncates starting from the most significant bit.
--
-- > bvTrunc : (m n : Nat) -> Vec (addNat m n) Bool -> Vec n Bool;
scBvTrunc :: SharedContext -> Term -> Term -> Term -> IO Term
scBvTrunc sc n m x = scGlobalApply sc "Prelude.bvTrunc" [n,m,x]

-- | Create a term applying the @updNatFun@ primitive, which satisfies the
-- following laws:
--
-- > updNatFun : (a : sort 0) -> (Nat -> a) -> Nat -> a -> (Nat -> a);
-- > updNatFun a _ i v i == v
-- > updNatFun a f i v x == f x, when i != x
scUpdNatFun :: SharedContext -> Term -> Term
            -> Term -> Term -> IO Term
scUpdNatFun sc a f i v = scGlobalApply sc "Prelude.updNatFun" [a, f, i, v]

-- | Create a term applying the @updBvFun@ primitive, which has the same
-- behavior as @updNatFun@ but acts on bitvectors.
--
-- > updBvFun : (n : Nat) -> (a : sort 0) -> (Vec n Bool -> a) -> Vec n Bool -> a -> (Vec n Bool -> a);
scUpdBvFun :: SharedContext -> Term -> Term
           -> Term -> Term -> Term -> IO Term
scUpdBvFun sc n a f i v = scGlobalApply sc "Prelude.updBvFun" [n, a, f, i, v]

-- | Create a term representing the type of arrays, given an index type and
-- element type (as 'Term's).
--
-- > Array : sort 0 -> sort 0 -> sort 0
scArrayType :: SharedContext -> Term -> Term -> IO Term
scArrayType sc a b = scGlobalApply sc "Prelude.Array" [a, b]

-- | Create a term computing a constant array, given an index type, element type,
-- and element (all as 'Term's).
--
-- > arrayConstant : (a b : sort 0) -> b -> (Array a b);
scArrayConstant :: SharedContext -> Term -> Term -> Term -> IO Term
scArrayConstant sc a b e = scGlobalApply sc "Prelude.arrayConstant" [a, b, e]

-- | Create a term computing the value at a particular index of an array.
--
-- > arrayLookup : (a b : sort 0) -> (Array a b) -> a -> b;
scArrayLookup :: SharedContext -> Term -> Term -> Term -> Term -> IO Term
scArrayLookup sc a b f i = scGlobalApply sc "Prelude.arrayLookup" [a, b, f, i]

-- | Create a term computing an array updated at a particular index.
--
-- > arrayUpdate : (a b : sort 0) -> (Array a b) -> a -> b -> (Array a b);
scArrayUpdate :: SharedContext -> Term -> Term -> Term -> Term -> Term -> IO Term
scArrayUpdate sc a b f i e = scGlobalApply sc "Prelude.arrayUpdate" [a, b, f, i, e]

-- | Create a term computing the equality of two arrays.
--
-- > arrayEq : (a b : sort 0) -> (Array a b) -> (Array a b) -> Bool;
scArrayEq :: SharedContext -> Term -> Term -> Term -> Term -> IO Term
scArrayEq sc a b x y = scGlobalApply sc "Prelude.arrayEq" [a, b, x, y]

-- > arrayCopy : (n : Nat) -> (a : sort 0) -> Array (Vec n Bool) a -> Vec n Bool -> Array (Vec n Bool) a -> Vec n Bool -> Vec n Bool -> Array (Vec n Bool) a;
-- > arrayCopy n a dest_arr dest_idx src_arr src_idx len
scArrayCopy :: SharedContext -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> IO Term
scArrayCopy sc n a f i g j l = scGlobalApply sc "Prelude.arrayCopy" [n, a, f, i, g, j, l]

-- > arraySet : (n : Nat) -> (a : sort 0) -> Array (Vec n Bool) a -> Vec n Bool -> a -> Vec n Bool -> Array (Vec n Bool) a;
-- > arraySet n a arr idx val len
scArraySet :: SharedContext -> Term -> Term -> Term -> Term -> Term -> Term -> IO Term
scArraySet sc n a f i e l = scGlobalApply sc "Prelude.arraySet" [n, a, f, i, e, l]

-- > arrayRangeEq : (n : Nat) -> (a : sort 0) -> Array (Vec n Bool) a -> Vec n Bool -> Array (Vec n Bool) a -> Vec n Bool -> Vec n Bool -> Bool;
-- > arrayRangeEq n a lhs_arr lhs_idx rhs_arr rhs_idx len
scArrayRangeEq :: SharedContext -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> IO Term
scArrayRangeEq sc n a f i g j l = scGlobalApply sc "Prelude.arrayRangeEq" [n, a, f, i, g, j, l]

------------------------------------------------------------
-- | The default instance of the SharedContext operations.
mkSharedContext :: IO SharedContext
mkSharedContext = do
  vr <- newIORef (1 :: VarIndex) -- 0 is reserved for wildcardVarName.
  cr <- newMVar emptyAppCache
  gr <- newIORef HMap.empty
  mod_map_ref <- newIORef emptyModuleMap
  dr <- newIORef emptyDisplayNameEnv
  ur <- newIORef Map.empty
  return SharedContext {
             scModuleMap = mod_map_ref
           , scAppCache = cr
           , scNextVarIndex = vr
           , scDisplayNameEnv = dr
           , scURIEnv = ur
           , scGlobalEnv = gr
           }

useChangeCache :: C m => Cache m k (Change v) -> k -> ChangeT m v -> ChangeT m v
useChangeCache c k a = ChangeT $ useCache c k (runChangeT a)

-- | Performs an action when a value has been modified, and otherwise
-- returns a pure value.
whenModified :: (Functor m, Monad m) => b -> (a -> m b) -> ChangeT m a -> ChangeT m b
whenModified b f m = ChangeT $ do
  ca <- runChangeT m
  case ca of
    Original{} -> return (Original b)
    Modified a -> Modified <$> f a

-- | Can this term be evaluated to a constant?
-- The parameter is a set of names which should be considered opaque---if
-- we encounter any of these then the term is not considered to evaluate to
-- a constant.
isConstFoldTerm :: SharedContext -> Set VarIndex -> Term -> IO Bool
isConstFoldTerm sc unint t
  | closedTerm t =
    do
      mm <- scGetModuleMap sc
      let ?mmap = mm
      pure (isJust (go mempty t))
  | otherwise = pure False
    where
    go !vis term =
      case term of
        STApp { stAppIndex = idx, stAppTermF = termF }
          | IntSet.member idx vis -> Just vis
          | otherwise -> goF (IntSet.insert idx vis) termF
    goF vis tf =
      case tf of
        Constant c
          | nameIndex c `Set.member` unint -> Nothing
          | Just (ResolvedDef d) <- lookupVarIndexInMap (nameIndex c) ?mmap
          , Just t1 <- defBody d -> go vis t1
          | otherwise -> Just vis
        _ -> foldM go vis tf

-- | Return a list of all free variables in the given term along with
-- their types, sorted by index.
getAllVars :: Term -> [(VarName, Term)]
getAllVars t = Map.toList (getAllVarsMap t)

-- | Return a map of all free variables in the given term with their
-- types.
getAllVarsMap :: Term -> Map VarName Term
getAllVarsMap t = State.evalState (go t) IntMap.empty
  where
    go :: Term -> State.State (IntMap (Map VarName Term)) (Map VarName Term)
    go STApp{ stAppIndex = i, stAppTermF = tf, stAppVarTypes = vt }
      | IntMap.null vt = pure Map.empty
      | otherwise =
        do memo <- State.get
           case IntMap.lookup i memo of
             Just vars -> pure vars
             Nothing ->
               do vars <- termf tf
                  State.modify' (IntMap.insert i vars)
                  pure vars
    termf :: TermF Term -> State.State (IntMap (Map VarName Term)) (Map VarName Term)
    termf tf =
      case tf of
        Variable x tp -> pure (Map.singleton x tp)
        Lambda x t1 t2 ->
          do vars1 <- go t1
             vars2 <- go t2
             pure (vars1 <> Map.delete x vars2)
        Pi x t1 t2 ->
          do vars1 <- go t1
             vars2 <- go t2
             pure (vars1 <> Map.delete x vars2)
        _ -> Fold.fold <$> traverse go tf

getConstantSet :: Term -> Map VarIndex NameInfo
getConstantSet t = snd $ go (IntSet.empty, Map.empty) t
  where
    go acc@(idxs, names) (STApp{ stAppIndex = i, stAppTermF = tf})
      | IntSet.member i idxs = acc
      | otherwise = termf (IntSet.insert i idxs, names) tf

    termf acc@(idxs, names) tf =
      case tf of
        Constant (Name vidx n) -> (idxs, Map.insert vidx n names)
        _ -> foldl' go acc tf

-- | Instantiate some of the named variables in the term.
-- The 'IntMap' is keyed by 'VarIndex'.
-- Note: The replacement is _not_ applied recursively
-- to the terms in the substitution map.
scInstantiate :: SharedContext -> IntMap Term -> Term -> IO Term
scInstantiate sc vmap t0 =
  do let domainVars = IntMap.keysSet vmap
     let rangeVars = foldMap freeVars vmap
     tcache <- newCacheIntMap
     let memo :: Term -> IO Term
         memo t =
           case t of
             STApp {stAppIndex = i} -> useCache tcache i (go t)
         go :: Term -> IO Term
         go t
           | IntSet.disjoint domainVars (freeVars t) = pure t
           | otherwise =
             case unwrapTermF t of
               FTermF ftf     -> scFlatTermF sc =<< traverse memo ftf
               App t1 t2      -> scTermF sc =<< App <$> memo t1 <*> memo t2
               Lambda x t1 t2 ->
                 do t1' <- memo t1
                    (x', t2') <- goBinder x t1' t2
                    scLambda sc x' t1' t2'
               Pi x t1 t2 ->
                 do t1' <- memo t1
                    (x', t2') <- goBinder x t1' t2
                    scPi sc x' t1' t2'
               Constant {} -> pure t
               Variable nm tp ->
                 case IntMap.lookup (vnIndex nm) vmap of
                   Just t' -> pure t'
                   Nothing -> scVariable sc nm =<< memo tp
         goBinder :: VarName -> Term -> Term -> IO (VarName, Term)
         goBinder x@(vnIndex -> i) t body
           | IntSet.member i rangeVars =
               -- Possibility of capture; rename bound variable.
               do x' <- scFreshVarName sc (vnName x)
                  var <- scVariable sc x' t
                  let vmap' = IntMap.insert i var vmap
                  body' <- scInstantiate sc vmap' body
                  pure (x', body')
           | IntMap.member i vmap =
               -- Shadowing; remove entry from substitution.
               do let vmap' = IntMap.delete i vmap
                  body' <- scInstantiate sc vmap' body
                  pure (x, body')
           | otherwise =
               -- No possibility of shadowing or capture.
               do body' <- memo body
                  pure (x, body')
     go t0

-- | Create a lambda term by abstracting over the list of arguments,
-- which must all be named variables (e.g. terms generated by
-- 'scVariable' or 'scFreshVariable').
scAbstractTerms :: SharedContext -> [Term] -> Term -> IO Term
scAbstractTerms sc args body =
  do vars <- mapM toVar args
     scLambdaList sc vars body
  where
    toVar :: Term -> IO (VarName, Term)
    toVar t =
      case asVariable t of
        Just var -> pure var
        Nothing -> fail "scAbstractTerms: expected Variable"

-- | Abstract over the given list of variables by wrapping the given
-- term with lambdas.
-- However, the term will be eta-collapsed as far as possible, so
-- unnecessary lambdas will simply be omitted.
scLambdaListEtaCollapse :: SharedContext -> [(VarName, Term)] -> Term -> IO Term
scLambdaListEtaCollapse sc = \vars tm -> loop (reverse vars) tm
  where
    -- we eta-collapsed all the variables, nothing more to do
    loop [] tm = pure tm

    -- the final variable to abstract is applied to the
    -- term, and does not appear elsewhere in the term,
    -- so we can eta-collapse.
    loop ((x, _) : vars) (asApp -> Just (f, asVariable -> Just (x', _)))
      | x == x', IntSet.notMember (vnIndex x) (freeVars f)
      = loop vars f

    -- cannot eta-collapse, do abstraction as usual
    loop vars tm = scLambdaList sc (reverse vars) tm


-- | Create a pi term by abstracting over the list of arguments, which
-- must all be named variables (e.g. terms generated by 'scVariable' or
-- 'scFreshVariable').
scGeneralizeTerms :: SharedContext -> [Term] -> Term -> IO Term
scGeneralizeTerms sc args body =
  do vars <- mapM toVar args
     scPiList sc vars body
  where
    toVar :: Term -> IO (VarName, Term)
    toVar t =
      case asVariable t of
        Just var -> pure var
        Nothing -> fail "scGeneralizeTerms: expected Variable"

-- | Unfold some of the defined constants within a 'Term'.
-- The supplied predicate specifies whether or not to unfold each
-- constant, based on its 'Name'.
scUnfoldConstants ::
  SharedContext ->
  (Name -> Bool) {- ^ whether to unfold a constant with this name -} ->
  Term -> IO Term
scUnfoldConstants sc unfold t0 =
  do tcache <- newCacheMap' Map.empty
     mm <- scGetModuleMap sc
     let getRhs nm =
           case lookupVarIndexInMap (nameIndex nm) mm of
             Just (ResolvedDef d) -> defBody d
             _ -> Nothing
     let go :: Term -> ChangeT IO Term
         go t@STApp{stAppIndex = idx, stAppTermF = tf} =
           case tf of
             Constant nm
               | unfold nm
               , Just rhs <- getRhs nm -> taint (go rhs)
               | otherwise             -> pure t
             Variable x _
               | IntMap.member (vnIndex x) (varTypes t0) ->
                 -- Avoid modifying types of free variables to preserve Term invariant
                 pure t
             _ ->
               useChangeCache tcache idx $
               whenModified t (scTermF sc) (traverse go tf)
     commitChangeT (go t0)

-- | Unfold some of the defined constants within a 'Term'.
-- The supplied predicate specifies whether or not to unfold each
-- constant, based on its 'Name'.
-- Reduce any beta redexes created by unfolding a constant definition
-- that is a lambda term.
scUnfoldConstantsBeta ::
  SharedContext ->
  (Name -> Bool) {- ^ whether to unfold a constant with this name -} ->
  Term -> IO Term
scUnfoldConstantsBeta sc unfold t0 =
  do tcache <- newCacheMap' Map.empty
     mm <- scGetModuleMap sc
     let getRhs nm =
           case lookupVarIndexInMap (nameIndex nm) mm of
             Just (ResolvedDef d) -> defBody d
             _ -> Nothing
     let memo :: Term -> ChangeT IO Term
         memo t@STApp{stAppIndex = i} = useChangeCache tcache i (go t)
         go :: Term -> ChangeT IO Term
         go (asApplyAll -> (asConstant -> Just nm, args))
           | unfold nm, Just rhs <- getRhs nm =
               do args' <- traverse memo args
                  taint $ lift $ scApplyAllBeta sc rhs args'
         go t@(asVariable -> Just (x, _))
           | IntMap.member (vnIndex x) (varTypes t0) =
               -- Avoid modifying types of free variables to preserve Term invariant
               pure t
         go t = whenModified t (scTermF sc) (traverse memo (unwrapTermF t))

     commitChangeT (memo t0)

-- | Unfold one time fixpoint constants.
--
-- Specifically, if @c = fix a f@, then replace @c@ with @f c@, that is replace
-- @(fix a f)@ with @f (fix a f)@ while preserving the constant name.  The
-- signature of @fix@ is @primitive fix : (a : sort 1) -> (a -> a) -> a;@.
scUnfoldOnceFixConstantSet :: SharedContext
                           -> Bool  -- ^ True: unfold constants in set. False: unfold constants NOT in set
                           -> Set VarIndex -- ^ Set of constant names
                           -> Term
                           -> IO Term
scUnfoldOnceFixConstantSet sc b names t0 = do
  cache <- newCache
  mm <- scGetModuleMap sc
  let getRhs v =
        case lookupVarIndexInMap v mm of
          Just (ResolvedDef d) -> defBody d
          _ -> Nothing
  let unfold t idx rhs
        | Set.member idx names == b
        , (isGlobalDef "Prelude.fix" -> Just (), [_, f]) <- asApplyAll rhs =
          betaNormalize sc =<< scApply sc f t
        | otherwise =
          return t
  let go :: Term -> IO Term
      go t@(STApp{ stAppIndex = idx, stAppTermF = tf }) = useCache cache idx $
        case tf of
          Constant (Name nmidx _) | Just rhs <- getRhs nmidx -> unfold t nmidx rhs
          _ -> scTermF sc =<< traverse go tf
  go t0

-- | Return the number of DAG nodes used by the given @Term@.
scSharedSize :: Term -> Integer
scSharedSize = fst . scSharedSizeAux (0, Set.empty)

scSharedSizeMany :: [Term] -> Integer
scSharedSizeMany = fst . foldl scSharedSizeAux (0, Set.empty)

scSharedSizeAux :: (Integer, Set TermIndex) -> Term -> (Integer, Set TermIndex)
scSharedSizeAux = go
  where
    go (sz, seen) (STApp{ stAppIndex = idx, stAppTermF = tf })
      | Set.member idx seen = (sz, seen)
      | otherwise = foldl' go (strictPair (sz + 1) (Set.insert idx seen)) tf

strictPair :: a -> b -> (a, b)
strictPair x y = x `seq` y `seq` (x, y)

-- | Return the number of nodes that would be used by the given
-- @Term@ if it were represented as a tree instead of a DAG.
scTreeSize :: Term -> Integer
scTreeSize = fst . scTreeSizeAux (0, Map.empty)

scTreeSizeMany :: [Term] -> Integer
scTreeSizeMany = fst . foldl scTreeSizeAux (0, Map.empty)

scTreeSizeAux :: (Integer, Map TermIndex Integer) -> Term -> (Integer, Map TermIndex Integer)
scTreeSizeAux = go
  where
    go (sz, seen) (STApp{ stAppIndex = idx, stAppTermF = tf }) =
      case Map.lookup idx seen of
        Just sz' -> (sz + sz', seen)
        Nothing -> (sz + sz', Map.insert idx sz' seen')
          where (sz', seen') = foldl' go (1, seen) tf
