{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase #-}

{- |
Module      : Verifier.SAW.SharedTerm
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.SharedTerm
  ( TermF(..)
  , Uninterp(..)
  , Ident, mkIdent
  , VarIndex
  , ExtCns(..)
  , PrimName(..)
  , NameInfo(..)
  , ppName
    -- * Shared terms
  , Term(..)
  , TermIndex
  , looseVars
  , smallestFreeVar
  , scSharedTerm
  , unshare
  , scImport
  , alphaEquiv
  , alistAllFields
  , scRegisterName
  , scResolveName
  , scResolveNameByURI
  , scResolveUnambiguous
  , scFindBestName
  , scShowTerm
  , DuplicateNameException(..)
    -- * Re-exported pretty-printing functions
  , PPOpts(..)
  , defaultPPOpts
  , ppTerm
  , ppTermDepth
  , showTerm
  , scPrettyTerm
  , scPrettyTermInCtx
    -- * SharedContext interface for building shared terms
  , SharedContext
  , mkSharedContext
  , scGetModuleMap
    -- ** Low-level generic term constructors
  , scTermF
  , scFlatTermF
    -- ** Implicit versions of functions.
  , scDefTerm
  , scFreshGlobalVar
  , scFreshGlobal
  , scFreshEC
  , scExtCns
  , scGlobalDef
  , scRegisterGlobal
  , scFreshenGlobalIdent
    -- ** Recursors and datatypes
  , scRecursorElimTypes
  , scRecursorRetTypeType
  , scReduceRecursor
  , scReduceNatRecursor
  , allowedElimSort
  , scBuildCtor
    -- ** Modules
  , scLoadModule
  , scUnloadModule
  , scModifyModule
  , scModuleIsLoaded
  , scFindModule
  , scFindDef
  , scFindDataType
  , scFindCtor
  , scRequireDef
  , scRequireDataType
  , scRequireCtor
    -- ** Term construction
    -- *** Datatypes and constructors
  , scDataTypeAppParams
  , scDataTypeApp
  , scCtorAppParams
  , scCtorApp
  , scApplyCtor
  , scSort
  , scISort
    -- *** Variables and constants
  , scLocalVar
  , scConstant
  , scConstant'
  , scOpaqueConstant
  , scLookupDef
    -- *** Functions and function application
  , scApply
  , scApplyAll
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
  , scTypeOf'
  , asSort
  , reducePi
  , scTypeOfCtor
  , scTypeOfDataType
  , scTypeOfGlobal
    -- ** Prelude operations
    -- *** Booleans
  , scNot
  , scAnd
  , scOr
  , scImplies
  , scXor
  , scBoolEq
  , scIte
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
  , scFinVal
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
    -- ** Utilities
--  , scTrue
--  , scFalse
   , scOpenTerm
   , scCloseTerm
    -- ** Variable substitution
  , instantiateVar
  , instantiateVarList
  , betaNormalize
  , getAllExts
  , getAllExtSet
  , getConstantSet
  , scInstantiateExt
  , scAbstractExts
  , scAbstractExtsEtaCollapse
  , scGeneralizeExts
  , incVars
  , scUnfoldConstants
  , scUnfoldConstants'
  , scUnfoldConstantSet
  , scUnfoldConstantSet'
  , scSharedSize
  , scTreeSize
  ) where

import Control.Applicative
-- ((<$>), pure, (<*>))
import Control.Concurrent.MVar
import Control.Exception
import Control.Lens
import Control.Monad.State.Strict as State
import Control.Monad.Reader
import Data.Bits
import Data.List (inits, find)
import Data.Maybe
import qualified Data.Foldable as Fold
import Data.Foldable (foldl', foldlM, foldrM, maximum)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HMap
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.IORef (IORef,newIORef,readIORef,modifyIORef',atomicModifyIORef')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Ref ( C )
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Vector as V
import Numeric.Natural (Natural)
import Prelude hiding (mapM, maximum)
import Text.URI

import Verifier.SAW.Cache
import Verifier.SAW.Change
import Verifier.SAW.Name
import Verifier.SAW.Utils (panic)
import Verifier.SAW.Prelude.Constants
import Verifier.SAW.Recognizer
import Verifier.SAW.Term.Functor
import Verifier.SAW.Term.CtxTerm
import Verifier.SAW.Term.Pretty
import Verifier.SAW.TypedAST
import Verifier.SAW.Unique


#if !MIN_VERSION_base(4,8,0)
countTrailingZeros :: (FiniteBits b) => b -> Int
countTrailingZeros x = go 0
  where
    go i | i >= w      = i
         | testBit x i = i
         | otherwise   = go (i+1)
    w = finiteBitSize x
#endif

newtype Uninterp = Uninterp { getUninterp :: (String, Term) } deriving Show

------------------------------------------------------------
-- TermFMaps

-- | A TermFMap is a data structure used for hash-consing of terms.
data TermFMap a
  = TermFMap
  { appMapTFM :: !(IntMap (IntMap a))
  , hashMapTFM :: !(HashMap (TermF Term) a)
  }

emptyTFM :: TermFMap a
emptyTFM = TermFMap IntMap.empty HMap.empty

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

----------------------------------------------------------------------
-- SharedContext: a high-level interface for building Terms.

data SharedContext = SharedContext
  { scModuleMap      :: IORef ModuleMap
  , scTermF          :: TermF Term -> IO Term
  , scNamingEnv      :: IORef SAWNamingEnv
  , scGlobalEnv      :: IORef (HashMap Ident Term)
  , scFreshGlobalVar :: IO VarIndex
  }

-- | Create a new term from a lower-level 'FlatTermF' term.
scFlatTermF :: SharedContext -> FlatTermF Term -> IO Term
scFlatTermF sc ftf = scTermF sc (FTermF ftf)

-- | Create a 'Term' from an 'ExtCns'.
scExtCns :: SharedContext -> ExtCns Term -> IO Term
scExtCns sc ec = scFlatTermF sc (ExtCns ec)

data DuplicateNameException = DuplicateNameException URI
instance Exception DuplicateNameException
instance Show DuplicateNameException where
  show (DuplicateNameException uri) =
      "Attempted to register the following name twice: " ++ Text.unpack (render uri)

scRegisterName :: SharedContext -> VarIndex -> NameInfo -> IO ()
scRegisterName sc i nmi = atomicModifyIORef' (scNamingEnv sc) (\env -> (f env, ()))
  where
    f env =
      case registerName i nmi env of
        Left uri -> throw (DuplicateNameException uri)
        Right env' -> env'

scResolveUnambiguous :: SharedContext -> Text -> IO (VarIndex, NameInfo)
scResolveUnambiguous sc nm =
  scResolveName sc nm >>= \case
     []  -> fail ("Could not resolve name: " ++ show nm)
     [x] -> pure x
     xs  ->
       do nms <- mapM (scFindBestName sc . snd) xs
          fail $ unlines (("Ambiguous name " ++ show nm ++ " might refer to any of the following:") : map show nms)

scFindBestName :: SharedContext -> NameInfo -> IO Text
scFindBestName sc nmi =
  do env <- readIORef (scNamingEnv sc)
     case bestAlias env nmi of
       Left uri -> pure (render uri)
       Right nm -> pure nm

scResolveNameByURI :: SharedContext -> URI -> IO (Maybe VarIndex)
scResolveNameByURI sc uri =
  do env <- readIORef (scNamingEnv sc)
     pure $! resolveURI env uri

scResolveName :: SharedContext -> Text -> IO [(VarIndex, NameInfo)]
scResolveName sc nm =
  do env <- readIORef (scNamingEnv sc)
     pure (resolveName env nm)

scShowTerm :: SharedContext -> PPOpts -> Term -> IO String
scShowTerm sc opts t =
  do env <- readIORef (scNamingEnv sc)
     pure (showTermWithNames opts env t)

-- | Create a global variable with the given identifier (which may be "_") and type.
scFreshEC :: SharedContext -> Text -> a -> IO (ExtCns a)
scFreshEC sc x tp =
  do i <- scFreshGlobalVar sc
     let uri = scFreshNameURI x i
     let nmi = ImportedName uri [x, x <> "#" <>  Text.pack (show i)]
     scRegisterName sc i nmi
     pure (EC i nmi tp)

-- | Create a global variable with the given identifier (which may be "_") and type.
scFreshGlobal :: SharedContext -> Text -> Term -> IO Term
scFreshGlobal sc x tp = scExtCns sc =<< scFreshEC sc x tp

-- | Returns shared term associated with ident.
-- Does not check module namespace.
scGlobalDef :: SharedContext -> Ident -> IO Term
scGlobalDef sc ident =
  do m <- readIORef (scGlobalEnv sc)
     case HMap.lookup ident m of
       Nothing -> fail ("Could not find global: " ++ show ident)
       Just t -> pure t

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

-- | Create a function application term.
scApply :: SharedContext
        -> Term -- ^ The function to apply
        -> Term -- ^ The argument to apply to
        -> IO Term
scApply sc f = scTermF sc . App f

-- | Applies the constructor with the given name to the list of parameters and
-- arguments. This version does no checking against the module.
scDataTypeAppParams :: SharedContext
                    -> PrimName Term -- ^ The data type
                    -> [Term] -- ^ The parameters
                    -> [Term] -- ^ The arguments
                    -> IO Term
scDataTypeAppParams sc d params args =
  scFlatTermF sc (DataTypeApp d params args)

-- | Applies the constructor with the given name to the list of
-- arguments. This version does no checking against the module.
scDataTypeApp :: SharedContext -> Ident -> [Term] -> IO Term
scDataTypeApp sc d_id args =
  do d <- scRequireDataType sc d_id
     let (params,args') = splitAt (length (dtParams d)) args
     scDataTypeAppParams sc (dtPrimName d) params args'

-- | Applies the constructor with the given name to the list of parameters and
-- arguments. This version does no checking against the module.
scCtorAppParams :: SharedContext
                -> PrimName Term  -- ^ The constructor name
                -> [Term] -- ^ The parameters
                -> [Term] -- ^ The arguments
                -> IO Term
scCtorAppParams sc c params args =
  scFlatTermF sc (CtorApp c params args)

-- | Applies the constructor with the given name to the list of
-- arguments. This version does no checking against the module.
scCtorApp :: SharedContext -> Ident -> [Term] -> IO Term
scCtorApp sc c_id args =
  do ctor <- scRequireCtor sc c_id
     let (params,args') = splitAt (ctorNumParams ctor) args
     scCtorAppParams sc (ctorPrimName ctor) params args'

-- | Get the current 'ModuleMap'
scGetModuleMap :: SharedContext -> IO ModuleMap
scGetModuleMap sc = readIORef (scModuleMap sc)

-- | Test if a module is loaded in the current shared context
scModuleIsLoaded :: SharedContext -> ModuleName -> IO Bool
scModuleIsLoaded sc name =
  HMap.member name <$> scGetModuleMap sc

-- | Load a module into the current shared context, raising an error if a module
-- of the same name is already loaded
scLoadModule :: SharedContext -> Module -> IO ()
scLoadModule sc m =
  modifyIORef' (scModuleMap sc) $
  HMap.insertWith (error $ "scLoadModule: module "
                   ++ show (moduleName m) ++ " already loaded!")
  (moduleName m) m

-- | Remove a module from the current shared context, or do nothing if it does
-- not exist
scUnloadModule :: SharedContext -> ModuleName -> IO ()
scUnloadModule sc mnm =
  modifyIORef' (scModuleMap sc) $ HMap.delete mnm

-- | Modify an already loaded module, raising an error if it is not loaded
scModifyModule :: SharedContext -> ModuleName -> (Module -> Module) -> IO ()
scModifyModule sc mnm f =
  let err_msg = "scModifyModule: module " ++ show mnm ++ " not found!" in
  modifyIORef' (scModuleMap sc) $
  HMap.alter (\case { Just m -> Just (f m); _ -> error err_msg }) mnm

-- | Look up a module by name, raising an error if it is not loaded
scFindModule :: SharedContext -> ModuleName -> IO Module
scFindModule sc name =
  do maybe_mod <- HMap.lookup name <$> scGetModuleMap sc
     case maybe_mod of
       Just m -> return m
       Nothing ->
         error ("scFindModule: module " ++ show name ++ " not found!")

-- | Look up a definition by its identifier
scFindDef :: SharedContext -> Ident -> IO (Maybe Def)
scFindDef sc i =
  findDef <$> scFindModule sc (identModule i) <*> pure (identBaseName i)

-- | Look up a 'Def' by its identifier, throwing an error if it is not found
scRequireDef :: SharedContext -> Ident -> IO Def
scRequireDef sc i =
  scFindDef sc i >>= \maybe_d ->
  case maybe_d of
    Just d -> return d
    Nothing -> fail ("Could not find definition: " ++ show i)

-- | Look up a datatype by its identifier
scFindDataType :: SharedContext -> Ident -> IO (Maybe DataType)
scFindDataType sc i =
  findDataType <$> scFindModule sc (identModule i) <*> pure (identBaseName i)

-- | Look up a datatype by its identifier, throwing an error if it is not found
scRequireDataType :: SharedContext -> Ident -> IO DataType
scRequireDataType sc i =
  scFindDataType sc i >>= \maybe_d ->
  case maybe_d of
    Just d -> return d
    Nothing -> fail ("Could not find datatype: " ++ show i)

-- | Look up a constructor by its identifier
scFindCtor :: SharedContext -> Ident -> IO (Maybe Ctor)
scFindCtor sc i =
  findCtor <$> scFindModule sc (identModule i) <*> pure (identBaseName i)

-- | Look up a constructor by its identifier, throwing an error if not found
scRequireCtor :: SharedContext -> Ident -> IO Ctor
scRequireCtor sc i =
  scFindCtor sc i >>= \maybe_ctor ->
  case maybe_ctor of
    Just ctor -> return ctor
    Nothing -> fail ("Could not find constructor: " ++ show i)

-- SharedContext implementation.

type AppCache = TermFMap Term

type AppCacheRef = MVar AppCache

emptyAppCache :: AppCache
emptyAppCache = emptyTFM

-- | Return term for application using existing term in cache if it is available.
getTerm :: AppCacheRef -> TermF Term -> IO Term
getTerm r a =
  modifyMVar r $ \s -> do
    case lookupTFM a s of
      Just t -> return (s, t)
      Nothing -> do
        i <- getUniqueInt
        let t = STApp { stAppIndex = i
                      , stAppFreeVars = freesTermF (fmap looseVars a)
                      , stAppTermF = a
                      }
        let s' = insertTFM a t s
        seq s' $ return (s', t)


--------------------------------------------------------------------------------
-- Recursors

-- | Helper monad for building terms relative to a 'SharedContext'
newtype ShCtxM a = ShCtxM (ReaderT SharedContext IO a)
                 deriving (Functor, Applicative, Monad)

scShCtxM :: SharedContext -> ShCtxM a -> IO a
scShCtxM sc (ShCtxM m) = runReaderT m sc

instance MonadReader SharedContext ShCtxM where
  ask = ShCtxM ask
  local f (ShCtxM m) = ShCtxM $ local f m

instance MonadIO ShCtxM where
  liftIO m = ShCtxM $ liftIO m

instance MonadTerm ShCtxM where
  mkTermF tf = ask >>= \sc -> liftIO $ scTermF sc tf
  liftTerm n i t = ask >>= \sc -> liftIO $ incVars sc n i t
  whnfTerm t = ask >>= \sc -> liftIO $ scWhnf sc t
  substTerm n subst t = ask >>= \sc -> liftIO $ instantiateVarList sc n subst t

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


-- | Build a 'Ctor' from a 'CtorArgStruct' and a list of the other constructor
-- names of the 'DataType'. Note that we cannot look up the latter information,
-- as 'scBuildCtor' is called during construction of the 'DataType'.
scBuildCtor ::
  SharedContext ->
  PrimName Term {- ^ data type -} ->
  Ident {- ^ constructor name -} ->
  CtorArgStruct d params ixs {- ^ constructor formal arguments -} ->
  IO Ctor
scBuildCtor sc d c arg_struct =
  do
    -- Step 0: allocate a fresh unique varaible index for this constructor
    -- and register its name in the naming environment
    varidx <- scFreshGlobalVar sc
    scRegisterName sc varidx (ModuleIdentifier c)

    -- Step 1: build the types for the constructor and the type required
    -- of its eliminator functions
    tp <- scShCtxM sc $ ctxCtorType d arg_struct
    let cec = PrimName varidx c tp
    elim_tp_fun <- scShCtxM sc $ mkCtorElimTypeFun d cec arg_struct

    -- Step 2: build free variables for rec, elim and the
    -- constructor argument variables
    let num_args =
          case arg_struct of
            CtorArgStruct {..} -> bindingsLength ctorArgs

    vars <- reverse <$> mapM (scLocalVar sc) (take num_args [0 ..])
    elim_var <- scLocalVar sc num_args
    rec_var  <- scLocalVar sc (num_args+1)

    -- Step 3: pass these variables to ctxReduceRecursor to build the
    -- ctorIotaTemplate field
    iota_red <- scShCtxM sc $
      ctxReduceRecursor rec_var elim_var vars arg_struct

    -- Step 4: build the API function that shuffles the terms around in the
    -- correct way.
    let iota_fun rec cs_fs args =
          do let elim = case Map.lookup varidx cs_fs of
                          Just e -> e
                          Nothing -> panic "ctorIotaReduction"
                                       ["no eliminator for constructor", show c]
             instantiateVarList sc 0 (reverse ([rec,elim]++args)) iota_red

    -- Finally, return the required Ctor record
    return $ Ctor
      { ctorName = c
      , ctorVarIndex = varidx
      , ctorArgStruct = arg_struct
      , ctorDataType = d
      , ctorType = tp
      , ctorElimTypeFun = \ps p_ret -> scShCtxM sc $ elim_tp_fun ps p_ret
      , ctorIotaTemplate  = iota_red
      , ctorIotaReduction = iota_fun
      }

-- | Given a datatype @d@, parameters @p1,..,pn@ for @d@, and a "motive"
-- function @p_ret@ of type
--
-- > (x1::ix1) -> .. -> (xm::ixm) -> d p1 .. pn x1 .. xm -> Type i
--
-- that computes a return type from type indices for @d@ and an element of @d@
-- for those indices, return the requires types of elimination functions for
-- each constructor of @d@. See the documentation of the 'Ctor' type and/or the
-- 'ctxCtorElimType' function for more details.
scRecursorElimTypes ::
  SharedContext ->
  PrimName Term ->
  [Term] ->
  Term ->
  IO [(PrimName Term, Term)]
scRecursorElimTypes sc d params p_ret =
  do dt <- scRequireDataType sc (primName d)
     forM (dtCtors dt) $ \ctor ->
       do elim_type <- ctorElimTypeFun ctor params p_ret >>= scWhnf sc
          return (ctorPrimName ctor, elim_type)


-- | Generate the type @(ix1::Ix1) -> .. -> (ixn::Ixn) -> d params ixs -> s@
-- given @d@, @params@, and the sort @s@
scRecursorRetTypeType :: SharedContext -> DataType -> [Term] -> Sort -> IO Term
scRecursorRetTypeType sc dt params s =
  scShCtxM sc $ mkPRetTp (dtPrimName dt) (dtParams dt) (dtIndices dt) params s


-- | Reduce an application of a recursor. This is known in the Coq literature as
-- an iota reduction. More specifically, the call
--
-- > scReduceRecursor sc rec crec ci [x1, .., xk]
--
-- reduces the term @(RecursorApp r ixs (CtorApp ci ps xs))@ to
--
-- > fi x1 (maybe rec_tm_1) .. xk (maybe rec_tm_k)
--
-- where @maybe rec_tm_i@ indicates an optional recursive call of the recursor
-- on one of the @xi@. These recursive calls only exist for those arguments
-- @xi@. See the documentation for 'ctxReduceRecursor' and the
-- 'ctorIotaReduction' field for more details.
scReduceRecursor ::
  SharedContext ->
  Term {- ^ recusor term -} ->
  CompiledRecursor Term {- ^ concrete data included in the recursor term -} ->
  PrimName Term {- ^ constructor name -} ->
  [Term] {- ^ constructor arguments -} ->
  IO Term
scReduceRecursor sc r crec c args =
   do ctor <- scRequireCtor sc (primName c)
      -- The ctorIotaReduction field caches the result of iota reduction, which
      -- we just substitute into to perform the reduction
      ctorIotaReduction ctor r (fmap fst $ recursorElims crec) args

-- | Reduce an application of a recursor to a concrete nat value.
--   The given recursor value is assumed to be correctly-typed
--   for the @Nat@ datatype.  It will reduce using either the
--   elimiation function for @Zero@ or @Succ@, depending on
--   the concrete value of the @Nat@.
scReduceNatRecursor ::
  SharedContext ->
  Term {- ^ recusor term -} ->
  CompiledRecursor Term {- ^ concrete data included in the recursor term -} ->
  Natural {- ^ Concrete natural value to eliminate -} ->
  IO Term
scReduceNatRecursor sc rec crec n
  | n == 0 =
     do ctor <- scRequireCtor sc preludeZeroIdent
        ctorIotaReduction ctor rec (fmap fst $ recursorElims crec) []

  | otherwise =
     do ctor <- scRequireCtor sc preludeSuccIdent
        ctorIotaReduction ctor rec (fmap fst $ recursorElims crec) [(Unshared (FTermF (NatLit (pred n))))]

--------------------------------------------------------------------------------
-- Reduction to head-normal form

-- | An elimination for 'scWhnf'
data WHNFElim
  = ElimApp Term
  | ElimProj FieldName
  | ElimPair Bool
  | ElimRecursor Term (CompiledRecursor Term) [Term]

-- | Test if a term is a constructor application that should be converted to a
-- natural number literal. Specifically, test if a term is not already a natural
-- number literal, but is 0 or more applications of the @Succ@ constructor to
-- either the @Zero@ constructor or a natural number literal
convertsToNat :: Term -> Maybe Natural
convertsToNat (asFTermF -> Just (NatLit _)) = Nothing
convertsToNat t = helper t where
  helper (asFTermF -> Just (NatLit k)) = return k
  helper (asCtor -> Just (z, []))
    | primName z == preludeZeroIdent = return 0
  helper (asCtor -> Just (s, [t']))
    | primName s == preludeSuccIdent = (1+) <$> helper t'
  helper _ = Nothing


-- | Reduces beta-redexes, tuple/record selectors, recursor applications, and
-- definitions at the top level of a term, and evaluates all arguments to type
-- constructors (including function, record, and tuple types).
--
-- NOTE: this notion of weak head normal form differs from the standard type
-- theory definition, in that it normalizes the arguments of type-forming
-- constructs like pi types, pair types, etc. The idea is that these constructs
-- are being treated as strict constructors in the Haskell sense.
scWhnf :: SharedContext -> Term -> IO Term
scWhnf sc t0 =
  do cache <- newCacheIntMap
     let ?cache = cache in memo t0
  where
    memo :: (?cache :: Cache IO TermIndex Term) => Term -> IO Term
    memo t =
      case t of
        Unshared _ -> go [] t
        STApp { stAppIndex = i } -> useCache ?cache i (go [] t)

    go :: (?cache :: Cache IO TermIndex Term) => [WHNFElim] -> Term -> IO Term
    go xs                     (convertsToNat    -> Just k) = scFlatTermF sc (NatLit k) >>= go xs
    go xs                     (asApp            -> Just (t, x)) = go (ElimApp x : xs) t
    go xs                     (asRecordSelector -> Just (t, n)) = go (ElimProj n : xs) t
    go xs                     (asPairSelector -> Just (t, i))   = go (ElimPair i : xs) t
    go (ElimApp x : xs)       (asLambda -> Just (_, _, body))   = betaReduce xs [x] body
    go (ElimPair i : xs)      (asPairValue -> Just (a, b))      = go xs (if i then b else a)
    go (ElimProj fld : xs)    (asRecordValue -> Just elems)     = case Map.lookup fld elems of
                                                                    Just t -> go xs t
                                                                    Nothing ->
                                                                      error "scWhnf: field missing in record"
    go (ElimRecursor rec crec _ : xs)
                              (asCtorParams ->
                               Just (c, _, args))               = scReduceRecursor sc rec crec c args >>= go xs

    go (ElimRecursor rec crec _ : xs)
                              (asNat -> Just n)                 = scReduceNatRecursor sc rec crec n >>= go xs

    go xs                     (asGlobalDef -> Just c)           = scRequireDef sc c >>= tryDef c xs
    go xs                     (asRecursorApp ->
                                Just (r, crec, ixs, arg))       = go (ElimRecursor r crec ixs : xs) arg
    go xs                     (asPairValue -> Just (a, b))      = do b' <- memo b
                                                                     t' <- scPairValue sc a b'
                                                                     foldM reapply t' xs
    go xs                     (asPairType -> Just (a, b))       = do a' <- memo a
                                                                     b' <- memo b
                                                                     t' <- scPairType sc a' b'
                                                                     foldM reapply t' xs
    go xs                     (asRecordType -> Just elems)      = do elems' <- mapM (\(i,t) -> (i,) <$> memo t)
                                                                                    (Map.assocs elems)
                                                                     t' <- scRecordType sc elems'
                                                                     foldM reapply t' xs
    go xs                     (asPi -> Just (x,aty,rty))        = do aty' <- memo aty
                                                                     rty' <- memo rty
                                                                     t' <- scPi sc x aty' rty'
                                                                     foldM reapply t' xs
    go xs                     (asDataTypeParams ->
                                 Just (d,ps,args))              = do ps' <- mapM memo ps
                                                                     args' <- mapM memo args
                                                                     t' <- scDataTypeAppParams sc d ps' args'
                                                                     foldM reapply t' xs
    go xs                     (asConstant -> Just (_,Just body)) = go xs body
    go xs                     t                                 = foldM reapply t xs

    betaReduce :: (?cache :: Cache IO TermIndex Term) =>
      [WHNFElim] -> [Term] -> Term -> IO Term
    betaReduce (ElimApp x : xs) vs (asLambda -> Just (_,_,body)) =
      betaReduce xs (x:vs) body
    betaReduce xs vs body =
      instantiateVarList sc 0 vs body >>= go xs

    reapply :: Term -> WHNFElim -> IO Term
    reapply t (ElimApp x) = scApply sc t x
    reapply t (ElimProj i) = scRecordSelect sc t i
    reapply t (ElimPair i) = scPairSelector sc t i
    reapply t (ElimRecursor r _crec ixs) =
      scFlatTermF sc (RecursorApp r ixs t)

    tryDef :: (?cache :: Cache IO TermIndex Term) =>
              Ident -> [WHNFElim] -> Def -> IO Term
    tryDef _ xs (Def {defBody = Just t}) = go xs t
    tryDef ident xs _ = scGlobalDef sc ident >>= flip (foldM reapply) xs


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
   go c tm1 tm2

 where whnf :: Cache IO TermIndex Term -> Term -> IO (TermF Term)
       whnf _c t@(Unshared _) = unwrapTermF <$> eval sc t
       whnf c t@(STApp{ stAppIndex = idx}) =
         unwrapTermF <$> useCache c idx (eval sc t)

       go :: Cache IO TermIndex Term -> Term -> Term -> IO Bool
       go _c (STApp{ stAppIndex = idx1}) (STApp{ stAppIndex = idx2})
           | idx1 == idx2 = return True   -- succeed early case
       go c t1 t2 = join (goF c <$> whnf c t1 <*> whnf c t2)

       goF :: Cache IO TermIndex Term -> TermF Term -> TermF Term -> IO Bool

       goF _c (Constant ecx _) (Constant ecy _) | ecVarIndex ecx == ecVarIndex ecy = pure True
       goF c (Constant _ (Just x)) y | unfoldConst = join (goF c <$> whnf c x <*> return y)
       goF c x (Constant _ (Just y)) | unfoldConst = join (goF c <$> return x <*> whnf c y)

       goF c (FTermF ftf1) (FTermF ftf2) =
               case zipWithFlatTermF (go c) ftf1 ftf2 of
                 Nothing -> return False
                 Just zipped -> Fold.and <$> traverse id zipped

       goF _c (LocalVar i) (LocalVar j) = return (i == j)

       goF c (App f1 x1) (App f2 x2) =
              pure (&&) <*> go c f1 f2 <*> go c x1 x2

       goF c (Lambda _ ty1 body1) (Lambda _ ty2 body2) =
              pure (&&) <*> go c ty1 ty2 <*> go c body1 body2

       goF c (Pi _ ty1 body1) (Pi _ ty2 body2) =
              pure (&&) <*> go c ty1 ty2 <*> go c body1 body2

       -- final catch-all case
       goF _c _x _y = return False

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
    Just (_, _, body) -> instantiateVar sc 0 arg body
    _ ->
      fail $ unlines ["reducePi: not a Pi term", showTerm t']

-- | Compute the type of a global variable.
scTypeOfGlobal :: SharedContext -> Ident -> IO Term
scTypeOfGlobal sc ident =
  defType <$> scRequireDef sc ident

-- | Compute the type of a datatype given its name as an 'Ident'.
scTypeOfDataType :: SharedContext -> Ident -> IO Term
scTypeOfDataType sc ident =
  dtType <$> scRequireDataType sc ident

-- | Compute the type of a data constructor given its name as an 'Ident'.
scTypeOfCtor :: SharedContext -> Ident -> IO Term
scTypeOfCtor sc ident =
  ctorType <$> scRequireCtor sc ident

-- | Computes the type of a term as quickly as possible, assuming that
-- the term is well-typed.
scTypeOf :: SharedContext -> Term -> IO Term
scTypeOf sc t0 = scTypeOf' sc [] t0

-- | A version for open terms; the list argument encodes the type environment.
scTypeOf' :: SharedContext -> [Term] -> Term -> IO Term
scTypeOf' sc env t0 = State.evalStateT (memo t0) Map.empty
  where
    memo :: Term -> State.StateT (Map TermIndex Term) IO Term
    memo (Unshared t) = termf t
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
        Lambda name tp rhs -> do
          rtp <- lift $ scTypeOf' sc (tp : env) rhs
          lift $ scTermF sc (Pi name tp rtp)
        Pi _ tp rhs -> do
          ltp <- sort tp
          rtp <- toSort =<< lift (scTypeOf' sc (tp : env) rhs)

          -- NOTE: the rule for type-checking Pi types is that (Pi x a b) is a Prop
          -- when b is a Prop (this is a forall proposition), otherwise it is a
          -- (Type (max (sortOf a) (sortOf b)))
          let srt = if rtp == propSort then propSort else max ltp rtp

          lift $ scSort sc srt
        LocalVar i
          | i < length env -> lift $ incVars sc 0 (i + 1) (env !! i)
          | otherwise      -> fail $ "Dangling bound variable: " ++ show (i - length env)
        Constant ec _ -> return (ecType ec)
    ftermf :: FlatTermF Term
           -> State.StateT (Map TermIndex Term) IO Term
    ftermf tf =
      case tf of
        Primitive ec -> return (primType ec)
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
        CtorApp c params args -> do
          lift $ foldM (reducePi sc) (primType c) (params ++ args)
        DataTypeApp dt params args -> do
          lift $ foldM (reducePi sc) (primType dt) (params ++ args)
        RecursorType _d _ps _motive motive_ty -> do
          s <- sort motive_ty
          lift $ scSort sc s
        Recursor rec -> do
          lift $ scFlatTermF sc $
             RecursorType (recursorDataType rec)
                          (recursorParams rec)
                          (recursorMotive rec)
                          (recursorMotiveTy rec)
        RecursorApp r ixs arg ->
          do tp <- (liftIO . scWhnf sc) =<< memo r
             case asRecursorType tp of
               Just (_d, _ps, motive, _motivety) ->
                 lift $ scApplyAll sc motive (ixs ++ [arg])
               _ -> fail "Expected recursor type in recursor application"

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
        NatLit _ -> lift $ scNatType sc
        ArrayValue tp vs -> lift $ do
          n <- scNat sc (fromIntegral (V.length vs))
          scVecType sc n tp
        StringLit{} -> lift $ scStringType sc
        ExtCns ec   -> return $ ecType ec

--------------------------------------------------------------------------------

-- | The inverse function to @scSharedTerm@.
unshare :: Term -> Term
unshare t0 = State.evalState (go t0) Map.empty
  where
    go :: Term -> State.State (Map TermIndex Term) Term
    go (Unshared t) = Unshared <$> traverse go t
    go (STApp{ stAppIndex = i, stAppTermF = t}) = do
      memo <- State.get
      case Map.lookup i memo of
        Just x  -> return x
        Nothing -> do
          x <- Unshared <$> traverse go t
          State.modify (Map.insert i x)
          return x

-- | Perform hash-consing at every AST node to obtain maximal sharing.
--
-- FIXME: this should no longer be needed, since it was added to deal with the
-- fact that SAWCore files used to build all their terms as 'Unshared' terms,
-- but that is no longer how we are doing things...
scSharedTerm :: SharedContext -> Term -> IO Term
scSharedTerm sc = go
    where go t = scTermF sc =<< traverse go (unwrapTermF t)

-- | Imports a term built in a different shared context into the given
-- shared context. The caller must ensure that all the global constants
-- appearing in the term are valid in the new context.
scImport :: SharedContext -> Term -> IO Term
scImport sc t0 =
    do cache <- newCache
       go cache t0
  where
    go :: Cache IO TermIndex Term -> Term -> IO Term
    go cache (Unshared tf) =
          Unshared <$> traverse (go cache) tf
    go cache (STApp{ stAppIndex = idx, stAppTermF = tf}) =
          useCache cache idx (scTermF sc =<< traverse (go cache) tf)

--------------------------------------------------------------------------------
-- Instantiating variables

-- | The second argument is a function that takes the number of
-- enclosing lambdas and the de Bruijn index of the variable,
-- returning the new term to replace it with.
instantiateLocalVars ::
  SharedContext ->
  (DeBruijnIndex -> DeBruijnIndex -> IO Term) ->
  DeBruijnIndex -> Term -> IO Term
instantiateLocalVars sc f initialLevel t0 =
  do cache <- newCache
     let ?cache = cache in go initialLevel t0
  where
    go :: (?cache :: Cache IO (TermIndex, DeBruijnIndex) Term) =>
          DeBruijnIndex -> Term -> IO Term
    go l t =
      case t of
        Unshared tf -> go' l tf
        STApp{ stAppIndex = tidx, stAppFreeVars = fv, stAppTermF = tf}
          | fv == emptyBitSet -> return t -- closed terms map to themselves
          | otherwise -> useCache ?cache (tidx, l) (go' l tf)

    go' :: (?cache :: Cache IO (TermIndex, DeBruijnIndex) Term) =>
           DeBruijnIndex -> TermF Term -> IO Term
    go' _ (FTermF tf@(ExtCns _)) = scFlatTermF sc tf
    go' l (FTermF tf)       = scFlatTermF sc =<< (traverse (go l) tf)
    go' l (App x y)         = scTermF sc =<< (App <$> go l x <*> go l y)
    go' l (Lambda i tp rhs) = scTermF sc =<< (Lambda i <$> go l tp <*> go (l+1) rhs)
    go' l (Pi i lhs rhs)    = scTermF sc =<< (Pi i <$> go l lhs <*> go (l+1) rhs)
    go' l (LocalVar i)
      | i < l     = scTermF sc (LocalVar i)
      | otherwise = f l i
    go' _ tf@(Constant {}) = scTermF sc tf

instantiateVars :: SharedContext
                -> ((Term -> IO Term) -> DeBruijnIndex -> Either (ExtCns Term) DeBruijnIndex -> IO Term)
                -> DeBruijnIndex -> Term -> IO Term
instantiateVars sc f initialLevel t0 =
    do cache <- newCache
       let ?cache = cache in go initialLevel t0
  where
    go :: (?cache :: Cache IO (TermIndex, DeBruijnIndex) Term) =>
          DeBruijnIndex -> Term -> IO Term
    go l (Unshared tf) =
            go' l tf
    go l (STApp{ stAppIndex = tidx, stAppTermF = tf}) =
            useCache ?cache (tidx, l) (go' l tf)

    go' :: (?cache :: Cache IO (TermIndex, DeBruijnIndex) Term) =>
           DeBruijnIndex -> TermF Term -> IO Term
    go' l (FTermF (ExtCns ec)) = f (go l) l (Left ec)
    go' l (FTermF tf)       = scFlatTermF sc =<< (traverse (go l) tf)
    go' l (App x y)         = scTermF sc =<< (App <$> go l x <*> go l y)
    go' l (Lambda i tp rhs) = scTermF sc =<< (Lambda i <$> go l tp <*> go (l+1) rhs)
    go' l (Pi i lhs rhs)    = scTermF sc =<< (Pi i <$> go l lhs <*> go (l+1) rhs)
    go' l (LocalVar i)
      | i < l     = scTermF sc (LocalVar i)
      | otherwise = f (go l) l (Right i)
    go' _ tf@(Constant {}) = scTermF sc tf

-- | @incVars k j t@ increments free variables at least @k@ by @j@.
-- e.g., incVars 1 2 (C ?0 ?1) = C ?0 ?3
incVars :: SharedContext
        -> DeBruijnIndex -> DeBruijnIndex -> Term -> IO Term
incVars sc initialLevel j
  | j == 0    = return
  | otherwise = instantiateLocalVars sc fn initialLevel
  where
    fn _ i = scTermF sc (LocalVar (i+j))

-- | Substitute @t0@ for variable @k@ in @t@ and decrement all higher
-- dangling variables.
instantiateVar :: SharedContext
               -> DeBruijnIndex -> Term -> Term -> IO Term
instantiateVar sc k t0 t =
    do cache <- newCache
       let ?cache = cache in instantiateLocalVars sc fn k t
  where -- Use map reference to memoize instantiated versions of t.
        term :: (?cache :: Cache IO DeBruijnIndex Term) =>
                DeBruijnIndex -> IO Term
        term i = useCache ?cache i (incVars sc 0 i t0)
        -- Instantiate variable 0.
        fn :: (?cache :: Cache IO DeBruijnIndex Term) =>
              DeBruijnIndex -> DeBruijnIndex -> IO Term
        fn i j | j  > i     = scTermF sc (LocalVar (j - 1))
               | j == i     = term i
               | otherwise  = scTermF sc (LocalVar j)

-- | Substitute @ts@ for variables @[k .. k + length ts - 1]@ and decrement all
-- higher deBruijn indices by @length ts@. Assume that deBruijn index 0 in @ts@
-- refers to deBruijn index @k + length ts@ in the current term; i.e., this
-- substitution lifts terms in @ts@ by @k@ (plus any additional binders).
--
-- For example, @instantiateVarList 0 [x,y,z] t@ is the beta-reduced form of
--
-- > Lam (Lam (Lam t)) `App` z `App` y `App` x
--
-- Note that the first element of the @ts@ list corresponds to @x@, which is the
-- outermost, or last, application. In terms of 'instantiateVar', we can write
-- this as:
--
-- > instantiateVarList 0 [x,y,z] t ==
-- >    instantiateVar 0 x (instantiateVar 1 (incVars 0 1 y)
-- >                       (instantiateVar 2 (incVars 0 2 z) t))
instantiateVarList :: SharedContext
                   -> DeBruijnIndex -> [Term] -> Term -> IO Term
instantiateVarList _ _ [] t = return t
instantiateVarList sc k ts t =
    do caches <- mapM (const newCache) ts
       instantiateLocalVars sc (fn (zip caches ts)) k t
  where
    l = length ts
    -- Memoize instantiated versions of ts.
    term :: (Cache IO DeBruijnIndex Term, Term)
         -> DeBruijnIndex -> IO Term
    term (cache, x) i = useCache cache i (incVars sc 0 (i-k) x)
    -- Instantiate variables [k .. k+l-1].
    fn :: [(Cache IO DeBruijnIndex Term, Term)]
       -> DeBruijnIndex -> DeBruijnIndex -> IO Term
    fn rs i j | j >= i + l     = scTermF sc (LocalVar (j - l))
              | j >= i         = term (rs !! (j - i)) i
              | otherwise      = scTermF sc (LocalVar j)


--------------------------------------------------------------------------------
-- Beta Normalization

-- | Beta-reduce a term to normal form.
betaNormalize :: SharedContext -> Term -> IO Term
betaNormalize sc t0 =
  do cache <- newCache
     let ?cache = cache in go t0
  where
    go :: (?cache :: Cache IO TermIndex Term) => Term -> IO Term
    go t = case t of
      Unshared _ -> go' t
      STApp{ stAppIndex = i } -> useCache ?cache i (go' t)

    go' :: (?cache :: Cache IO TermIndex Term) => Term -> IO Term
    go' t = do
      let (f, args) = asApplyAll t
      let (params, body) = asLambdaList f
      let n = length (zip args params)
      if n == 0 then go3 t else do
        body' <- go body
        f' <- scLambdaList sc (drop n params) body'
        args' <- mapM go args
        f'' <- instantiateVarList sc 0 (reverse (take n args')) f'
        scApplyAll sc f'' (drop n args')

    go3 :: (?cache :: Cache IO TermIndex Term) => Term -> IO Term
    go3 (Unshared tf) = Unshared <$> traverseTF go tf
    go3 (STApp{ stAppTermF = tf }) = scTermF sc =<< traverseTF go tf

    traverseTF :: (a -> IO a) -> TermF a -> IO (TermF a)
    traverseTF _ tf@(Constant {}) = pure tf
    traverseTF f tf = traverse f tf


--------------------------------------------------------------------------------
-- Building shared terms

-- | Apply a function 'Term' to zero or more argument 'Term's.
scApplyAll :: SharedContext -> Term -> [Term] -> IO Term
scApplyAll sc = foldlM (scApply sc)

-- | Returns the defined constant with the given 'Ident'. Fails if no
-- such constant exists in the module.
scLookupDef :: SharedContext -> Ident -> IO Term
scLookupDef sc ident = scGlobalDef sc ident --FIXME: implement module check.

-- | Deprecated. Use scGlobalDef or scLookupDef instead.
scDefTerm :: SharedContext -> Def -> IO Term
scDefTerm sc d = scGlobalDef sc (defIdent d)

-- TODO: implement version of scCtorApp that looks up the arity of the
-- constructor identifier in the module.

-- | Deprecated. Use scCtorApp instead.
scApplyCtor :: SharedContext -> Ctor -> [Term] -> IO Term
scApplyCtor sc c args = scCtorApp sc (ctorName c) args

-- | Create a term from a 'Sort'.
scSort :: SharedContext -> Sort -> IO Term
scSort sc s = scFlatTermF sc (Sort s False)

-- | Create a term from a 'Sort', and set the advisory "inhabited" flag
scISort :: SharedContext -> Sort -> IO Term
scISort sc s = scFlatTermF sc (Sort s True)

-- | Create a literal term from a 'Natural'.
scNat :: SharedContext -> Natural -> IO Term
scNat sc n = scFlatTermF sc (NatLit n)

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
scFun sc a b = do b' <- incVars sc 0 1 b
                  scTermF sc (Pi "_" a b')

-- | Create a term representing the type of a non-dependent n-ary function,
-- given a list of parameter types and a result type (as terms).
scFunAll :: SharedContext
         -> [Term] -- ^ The parameter types
         -> Term   -- ^ The result type
         -> IO Term
scFunAll sc argTypes resultType = foldrM (scFun sc) resultType argTypes

-- | Create a lambda term from a parameter name (as a 'LocalName'), parameter type
-- (as a 'Term'), and a body. Regarding deBruijn indices, in the body of the
-- function, an index of 0 refers to the bound parameter.
scLambda :: SharedContext
         -> LocalName -- ^ The parameter name
         -> Term   -- ^ The parameter type
         -> Term   -- ^ The body
         -> IO Term
scLambda sc varname ty body = scTermF sc (Lambda varname ty body)

-- | Create a lambda term of multiple arguments (curried) from a list
-- associating parameter names to types (as 'Term's) and a body. As for
-- 'scLambda', there is a convention for deBruijn indices: 0 refers to the last
-- parameter in the list, and n-1 (where n is the list length) refers to the
-- first.
scLambdaList :: SharedContext
             -> [(LocalName, Term)] -- ^ List of parameter / parameter type pairs
             -> Term -- ^ The body
             -> IO Term
scLambdaList _ [] rhs = return rhs
scLambdaList sc ((nm,tp):r) rhs =
  scLambda sc nm tp =<< scLambdaList sc r rhs

-- | Create a (possibly dependent) function given a parameter name, parameter
-- type (as a 'Term'), and a body. This function follows the same deBruijn
-- index convention as 'scLambda'.
scPi :: SharedContext
     -> LocalName -- ^ The parameter name
     -> Term   -- ^ The parameter type
     -> Term   -- ^ The body
     -> IO Term
scPi sc nm tp body = scTermF sc (Pi nm tp body)

-- | Create a (possibly dependent) function of multiple arguments (curried)
-- from a list associating parameter names to types (as 'Term's) and a body.
-- This function follows the same deBruijn index convention as 'scLambdaList'.
scPiList :: SharedContext
         -> [(LocalName, Term)] -- ^ List of parameter / parameter type pairs
         -> Term -- ^ The body
         -> IO Term
scPiList _ [] rhs = return rhs
scPiList sc ((nm,tp):r) rhs = scPi sc nm tp =<< scPiList sc r rhs

-- | Create a local variable term from a 'DeBruijnIndex'.
scLocalVar :: SharedContext
           -> DeBruijnIndex
           -> IO Term
scLocalVar sc i = scTermF sc (LocalVar i)

-- | Create an abstract constant with the specified name, body, and
-- type. The term for the body must not have any loose de Bruijn
-- indices. If the body contains any ExtCns variables, they will be
-- abstracted over and reapplied to the resulting constant.
scConstant :: SharedContext
           -> Text   -- ^ The name
           -> Term   -- ^ The body
           -> Term   -- ^ The type
           -> IO Term
scConstant sc name rhs ty =
  do unless (looseVars rhs == emptyBitSet) $
       fail "scConstant: term contains loose variables"
     let ecs = getAllExts rhs
     rhs' <- scAbstractExts sc ecs rhs
     ty' <- scFunAll sc (map ecType ecs) ty
     ec <- scFreshEC sc name ty'
     t <- scTermF sc (Constant ec (Just rhs'))
     args <- mapM (scFlatTermF sc . ExtCns) ecs
     scApplyAll sc t args


-- | Create an abstract constant with the specified name, body, and
-- type. The term for the body must not have any loose de Bruijn
-- indices. If the body contains any ExtCns variables, they will be
-- abstracted over and reapplied to the resulting constant.
scConstant' :: SharedContext
           -> NameInfo -- ^ The name
           -> Term   -- ^ The body
           -> Term   -- ^ The type
           -> IO Term
scConstant' sc nmi rhs ty =
  do unless (looseVars rhs == emptyBitSet) $
       fail "scConstant: term contains loose variables"
     let ecs = getAllExts rhs
     rhs' <- scAbstractExts sc ecs rhs
     ty' <- scFunAll sc (map ecType ecs) ty
     i <- scFreshGlobalVar sc
     scRegisterName sc i nmi
     let ec = EC i nmi ty'
     t <- scTermF sc (Constant ec (Just rhs'))
     args <- mapM (scFlatTermF sc . ExtCns) ecs
     scApplyAll sc t args


-- | Create an abstract and opaque constant with the specified name and type.
--   Such a constant has no definition and, unlike an @ExtCns@, is not subject
--   to substitution.
scOpaqueConstant ::
  SharedContext ->
  NameInfo ->
  Term {- ^ type of the constant -} ->
  IO Term
scOpaqueConstant sc nmi ty =
  do i <- scFreshGlobalVar sc
     scRegisterName sc i nmi
     let ec = EC i nmi ty
     scTermF sc (Constant ec Nothing)

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
scNatType sc =
 do dt <- scRequireDataType sc preludeNatIdent
    scFlatTermF sc (DataTypeApp (dtPrimName dt) [] [])

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

-- | Create a term computing a bitvector of the given length representing the
-- given 'Integer' value (if possible).
scBvConst :: SharedContext -> Natural -> Integer -> IO Term
scBvConst sc w v = assert (w <= fromIntegral (maxBound :: Int)) $ do
  x <- scNat sc w
  y <- scNat sc $ fromInteger $ v .&. (1 `shiftL` fromIntegral w - 1)
  scGlobalApply sc "Prelude.bvNat" [x, y]

-- TODO: This doesn't appear to be used anywhere, and "FinVal" doesn't appear
-- in Prelude.sawcore... can this be deleted?
-- | FinVal :: (x r :: Nat) -> Fin (Succ (addNat r x));
scFinVal :: SharedContext -> Term -> Term -> IO Term
scFinVal sc a b = scCtorApp sc "Prelude.FinVal" [a, b]

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
  vr <- newMVar 0 -- Reference for getting variables.
  cr <- newMVar emptyAppCache
  gr <- newIORef HMap.empty
  let freshGlobalVar = modifyMVar vr (\i -> return (i+1, i))
  mod_map_ref <- newIORef HMap.empty
  envRef <- newIORef emptySAWNamingEnv
  return SharedContext {
             scModuleMap = mod_map_ref
           , scTermF = getTerm cr
           , scFreshGlobalVar = freshGlobalVar
           , scNamingEnv = envRef
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

-- | Return a list of all ExtCns subterms in the given term, sorted by
-- index. Does not traverse the unfoldings of @Constant@ terms.
getAllExts :: Term -> [ExtCns Term]
getAllExts t = Set.toList (getAllExtSet t)

-- | Return a set of all ExtCns subterms in the given term.
--   Does not traverse the unfoldings of @Constant@ terms.
getAllExtSet :: Term -> Set.Set (ExtCns Term)
getAllExtSet t = snd $ getExtCns (IntSet.empty, Set.empty) t
    where getExtCns acc@(is, _) (STApp{ stAppIndex = idx }) | IntSet.member idx is = acc
          getExtCns (is, a) (STApp{ stAppIndex = idx, stAppTermF = (FTermF (ExtCns ec)) }) =
            (IntSet.insert idx is, Set.insert ec a)
          getExtCns (is, a) (Unshared (FTermF (ExtCns ec))) =
            (is, Set.insert ec a)
          getExtCns acc (STApp{ stAppTermF = Constant {} }) = acc
          getExtCns acc (Unshared (Constant {})) = acc
          getExtCns (is, a) (STApp{ stAppIndex = idx, stAppTermF = tf'}) =
            foldl' getExtCns (IntSet.insert idx is, a) tf'
          getExtCns acc (Unshared tf') =
            foldl' getExtCns acc tf'

getConstantSet :: Term -> Map VarIndex (NameInfo, Term, Maybe Term)
getConstantSet t = snd $ go (IntSet.empty, Map.empty) t
  where
    go acc@(idxs, names) (STApp{ stAppIndex = i, stAppTermF = tf})
      | IntSet.member i idxs = acc
      | otherwise = termf (IntSet.insert i idxs, names) tf
    go acc (Unshared tf) = termf acc tf

    termf acc@(idxs, names) tf =
      case tf of
        Constant (EC vidx n ty) body -> (idxs, Map.insert vidx (n, ty, body) names)
        _ -> foldl' go acc tf

-- | Instantiate some of the external constants.
--   Note: this replacement is _not_ applied recursively
--   to the terms in the replacement map; so external constants
--   in those terms will not be replaced.
scInstantiateExt :: SharedContext
                 -> Map VarIndex Term
                 -> Term
                 -> IO Term
scInstantiateExt sc vmap = instantiateVars sc fn 0
  where fn _rec l (Left ec) =
            case Map.lookup (ecVarIndex ec) vmap of
               Just t  -> incVars sc 0 l t
               Nothing -> scFlatTermF sc $ ExtCns ec
        fn _ _ (Right i) = scTermF sc $ LocalVar i

{-
-- RWD: I'm pretty sure the following implementation gets incorrect results when
-- the terms being substituted have free deBruijn variables.  The above is a
-- reimplementation based on instantiateVars that does the necessary deBruijn
-- shifting.

scInstantiateExt sc vmap t0 = do
  tcache <- newCacheMap' Map.empty
  let go :: Term -> ChangeT IO Term
      go t@(Unshared tf) =
        case tf of
          -- | Lookup variable in term if it is bound.
          FTermF (ExtCns ec) ->
            maybe (return t) modified $ Map.lookup (ecVarIndex ec) vmap
          -- | Recurse on other terms.
          _ -> whenModified t (scTermF sc) (traverse go tf)
      go t@(STApp idx tf) =
        case tf of
          -- Lookup variable in term if it is bound.
          FTermF (ExtCns ec) ->
            maybe (return t) modified $ Map.lookup (ecVarIndex ec) vmap
          -- Recurse on other terms.
          _ -> useChangeCache tcache idx $
                 whenModified t (scTermF sc) (traverse go tf)
  commitChangeT (go t0)
-}

-- | Convert the given list of external constants to local variables,
-- with the right-most mapping to local variable 0. If the term is
-- open (i.e. it contains loose de Bruijn indices) then increment them
-- accordingly.
scExtsToLocals :: SharedContext -> [ExtCns Term] -> Term -> IO Term
scExtsToLocals _ [] x = return x
scExtsToLocals sc exts x = instantiateVars sc fn 0 x
  where
    m = Map.fromList [ (ecVarIndex ec, k) | (ec, k) <- zip (reverse exts) [0 ..] ]
    fn rec l e =
      case e of
        Left ec ->
          case Map.lookup (ecVarIndex ec) m of
            Just k  -> scLocalVar sc (l + k)
            Nothing -> scFlatTermF sc . ExtCns =<< traverse rec ec
        Right i ->
          scLocalVar sc (i + length exts)

-- | Abstract over the given list of external constants by wrapping
--   the given term with lambdas and replacing the external constant
--   occurrences with the appropriate local variables.
scAbstractExts :: SharedContext -> [ExtCns Term] -> Term -> IO Term
scAbstractExts _ [] x = return x
scAbstractExts sc exts x = loop (zip (inits exts) exts)
  where
    -- each pair contains a single ExtCns and a list of all
    -- the ExtCns values that appear before it in the original list.
    loop :: [([ExtCns Term], ExtCns Term)] -> IO Term

    -- specical case: outermost variable, no need to abstract
    -- inside the type of ec
    loop (([],ec):ecs) =
      do tm' <- loop ecs
         scLambda sc (toShortName (ecName ec)) (ecType ec) tm'

    -- ordinary case. We need to abstract over all the ExtCns in @begin@
    -- before apply scLambda.  This ensures any dependenices between the
    -- types are handled correctly.
    loop ((begin,ec):ecs) =
      do tm' <- loop ecs
         tp' <- scExtsToLocals sc begin (ecType ec)
         scLambda sc (toShortName (ecName ec)) tp' tm'

    -- base case, convert all the exts in the body of x into deBruijn variables
    loop [] = scExtsToLocals sc exts x


-- | Abstract over the given list of external constants by wrapping
--   the given term with lambdas and replacing the external constant
--   occurrences with the appropriate local variables.  However,
--   the term will be eta-collapsed as far as possible, so unnecessary
--   lambdas will simply be omitted.
scAbstractExtsEtaCollapse :: SharedContext -> [ExtCns Term] -> Term -> IO Term
scAbstractExtsEtaCollapse sc = \exts tm -> loop (reverse exts) tm
  where
    -- we eta-collapsed all the variables, nothing more to do
    loop [] tm = pure tm

    -- the final variable to abstract is applied to the
    -- term, and does not appear elsewhere in the term,
    -- so we can eta-collapse.
    loop (ec:exts) (asApp -> Just (f,asExtCns -> Just ec'))
      | ec == ec', not (Set.member ec (getAllExtSet f))
      = loop exts f

    -- cannot eta-collapse, do abstraction as usual
    loop exts tm = scAbstractExts sc (reverse exts) tm


-- | Generalize over the given list of external constants by wrapping
-- the given term with foralls and replacing the external constant
-- occurrences with the appropriate local variables.
scGeneralizeExts :: SharedContext -> [ExtCns Term] -> Term -> IO Term
scGeneralizeExts _ [] x = return x
scGeneralizeExts sc exts x = loop (zip (inits exts) exts)
  where
    -- each pair contains a single ExtCns and a list of all
    -- the ExtCns values that appear before it in the original list.
    loop :: [([ExtCns Term], ExtCns Term)] -> IO Term

    -- specical case: outermost variable, no need to abstract
    -- inside the type of ec
    loop (([],ec):ecs) =
      do tm' <- loop ecs
         scPi sc (toShortName (ecName ec)) (ecType ec) tm'

    -- ordinary case. We need to abstract over all the ExtCns in @begin@
    -- before apply scLambda.  This ensures any dependenices between the
    -- types are handled correctly.
    loop ((begin,ec):ecs) =
      do tm' <- loop ecs
         tp' <- scExtsToLocals sc begin (ecType ec)
         scPi sc (toShortName (ecName ec)) tp' tm'

    -- base case, convert all the exts in the body of x into deBruijn variables
    loop [] = scExtsToLocals sc exts x


scUnfoldConstants :: SharedContext -> [VarIndex] -> Term -> IO Term
scUnfoldConstants sc names t0 = scUnfoldConstantSet sc True (Set.fromList names) t0

-- | TODO: test whether this version is slower or faster.
scUnfoldConstants' :: SharedContext -> [VarIndex] -> Term -> IO Term
scUnfoldConstants' sc names t0 = scUnfoldConstantSet' sc True (Set.fromList names) t0

scUnfoldConstantSet :: SharedContext
                    -> Bool  -- ^ True: unfold constants in set. False: unfold constants NOT in set
                    -> Set VarIndex -- ^ Set of constant names
                    -> Term
                    -> IO Term
scUnfoldConstantSet sc b names t0 = do
  cache <- newCache
  let go :: Term -> IO Term
      go t@(Unshared tf) =
        case tf of
          Constant (EC idx _ _) (Just rhs)
            | Set.member idx names == b -> go rhs
            | otherwise                 -> return t
          _ -> Unshared <$> traverse go tf
      go t@(STApp{ stAppIndex = idx, stAppTermF = tf }) = useCache cache idx $
        case tf of
          Constant (EC ecidx _ _) (Just rhs)
            | Set.member ecidx names == b -> go rhs
            | otherwise                   -> return t
          _ -> scTermF sc =<< traverse go tf
  go t0


-- | TODO: test whether this version is slower or faster.
scUnfoldConstantSet' :: SharedContext
                    -> Bool  -- ^ True: unfold constants in set. False: unfold constants NOT in set
                    -> Set VarIndex -- ^ Set of constant names
                    -> Term
                    -> IO Term
scUnfoldConstantSet' sc b names t0 = do
  tcache <- newCacheMap' Map.empty
  let go :: Term -> ChangeT IO Term
      go t@(Unshared tf) =
        case tf of
          Constant (EC idx _ _) (Just rhs)
            | Set.member idx names == b -> taint (go rhs)
            | otherwise                 -> pure t
          _ -> whenModified t (return . Unshared) (traverse go tf)
      go t@(STApp{ stAppIndex = idx, stAppTermF = tf }) =
        case tf of
          Constant (EC ecidx _ _) (Just rhs)
            | Set.member ecidx names == b -> taint (go rhs)
            | otherwise                   -> pure t
          _ -> useChangeCache tcache idx $
                 whenModified t (scTermF sc) (traverse go tf)
  commitChangeT (go t0)


-- | Return the number of DAG nodes used by the given @Term@.
scSharedSize :: Term -> Integer
scSharedSize = fst . go (0, Set.empty)
  where
    go (sz, seen) (Unshared tf) = foldl' go (strictPair (sz + 1) seen) tf
    go (sz, seen) (STApp{ stAppIndex = idx, stAppTermF = tf })
      | Set.member idx seen = (sz, seen)
      | otherwise = foldl' go (strictPair (sz + 1) (Set.insert idx seen)) tf

strictPair :: a -> b -> (a, b)
strictPair x y = x `seq` y `seq` (x, y)

-- | Return the number of nodes that would be used by the given
-- @Term@ if it were represented as a tree instead of a DAG.
scTreeSize :: Term -> Integer
scTreeSize = fst . go (0, Map.empty)
  where
    go (sz, seen) (Unshared tf) = foldl' go (sz + 1, seen) tf
    go (sz, seen) (STApp{ stAppIndex = idx, stAppTermF = tf }) =
      case Map.lookup idx seen of
        Just sz' -> (sz + sz', seen)
        Nothing -> (sz + sz', Map.insert idx sz' seen')
          where (sz', seen') = foldl' go (1, seen) tf


-- | `openTerm sc nm ty i body` replaces the loose deBruijn variable `i`
--   with a fresh external constant (with name `nm`, and type `ty`) in `body`.
scOpenTerm :: SharedContext
         -> Text
         -> Term
         -> DeBruijnIndex
         -> Term
         -> IO (ExtCns Term, Term)
scOpenTerm sc nm tp idx body = do
    ec <- scFreshEC sc nm tp
    ec_term <- scFlatTermF sc (ExtCns ec)
    body' <- instantiateVar sc idx ec_term body
    return (ec, body')

-- | `closeTerm closer sc ec body` replaces the external constant `ec` in `body` by
--   a new deBruijn variable and binds it using the binding form given by 'close'.
--   The name and type of the new bound variable are given by the name and type of `ec`.
scCloseTerm :: (SharedContext -> LocalName -> Term -> Term -> IO Term)
          -> SharedContext
          -> ExtCns Term
          -> Term
          -> IO Term
scCloseTerm close sc ec body = do
    lv <- scLocalVar sc 0
    body' <- scInstantiateExt sc (Map.insert (ecVarIndex ec) lv Map.empty) =<< incVars sc 0 1 body
    close sc (toShortName (ecName ec)) (ecType ec) body'
