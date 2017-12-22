{- |
Module      : $Header$
Description : Provides type-checked representation for Crucible/LLVM function
              specifications and function for creating it from AST
              representation.
Maintainer  : atomb
Stability   : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}
module SAWScript.CrucibleMethodSpecIR where

import           Data.List (isPrefixOf)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans (lift)
import           Control.Lens

import           Lang.Crucible.LLVM.MemType
import qualified Text.LLVM.AST as L
import           Data.IORef
import           Data.Monoid ((<>))

import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Nonce as Crucible

import qualified Lang.Crucible.LLVM.Intrinsics as Crucible
import qualified Lang.Crucible.Types as Crucible
import qualified Lang.Crucible.CFG.Common as Crucible
--import qualified Verifier.LLVM.Codebase as LSS
--import qualified Lang.Crucible.LLVM.MemModel.Common as C
import SAWScript.SolverStats
import SAWScript.TypedTerm

import qualified Lang.Crucible.LLVM.MemModel as Crucible (MemImpl, LLVM)
import qualified Lang.Crucible.LLVM.Translation as Crucible
import qualified Lang.Crucible.LLVM.LLVMContext as TyCtx
import qualified Lang.Crucible.Simulator.ExecutionTree as Crucible
import qualified Lang.Crucible.Simulator.GlobalState as Crucible
import qualified Lang.Crucible.Simulator.Intrinsics as Crucible
import qualified Lang.Crucible.Solver.SAWCoreBackend as Crucible
import qualified Lang.Crucible.Solver.SimpleBuilder as Crucible

import Verifier.SAW.SharedTerm
import SAWScript.Options

newtype AllocIndex = AllocIndex Int
  deriving (Eq, Ord, Show)

nextAllocIndex :: AllocIndex -> AllocIndex
nextAllocIndex (AllocIndex n) = AllocIndex (n + 1)

data SetupValue where
  SetupVar    :: AllocIndex -> SetupValue
  SetupTerm   :: TypedTerm -> SetupValue
  SetupStruct :: [SetupValue] -> SetupValue
  SetupArray  :: [SetupValue] -> SetupValue
  SetupElem   :: SetupValue -> Int -> SetupValue
  SetupField  :: SetupValue -> String -> SetupValue
  SetupNull   :: SetupValue
  SetupGlobal :: String -> SetupValue
  deriving (Show)

setupToTypedTerm :: Options -> SharedContext -> SetupValue -> MaybeT IO TypedTerm
setupToTypedTerm opts sc sv =
  case sv of
    SetupTerm term -> return term
    _ -> do t <- setupToTerm opts sc sv
            lift $ mkTypedTerm sc t

-- | Convert a setup value to a SAW-Core term. This is a partial
-- function, as certain setup values ---SetupVar, SetupNull and
-- SetupGlobal--- don't have semantics outside of the symbolic
-- simulator.
setupToTerm :: Options -> SharedContext -> SetupValue -> MaybeT IO Term
setupToTerm opts sc sv =
  let intToNat = fromInteger . toInteger 
  in case sv of
    SetupTerm term -> return (ttTerm term)
    SetupStruct fields -> do ts <- mapM (setupToTerm opts sc) fields
                             lift $ scTuple sc ts
    SetupArray elems@(_:_) -> do ts@(t:_) <- mapM (setupToTerm opts sc) elems
                                 typt <- lift $ scTypeOf sc t
                                 vec <- lift $ scVector sc typt ts
                                 typ <- lift $ scTypeOf sc vec
                                 lift $ printOutLn opts Info $ show vec
                                 lift $ printOutLn opts Info $ show typ
                                 return vec
    SetupElem base ind ->
      case base of
        SetupArray elems@(e:_) -> do art <- setupToTerm opts sc base
                                     ixt <- lift $ scNat sc $ intToNat ind
                                     lent <- lift $ scNat sc $ intToNat $ length elems
                                     et <- setupToTerm opts sc e
                                     typ <- lift $ scTypeOf sc et
                                     lift $ scAt sc lent typ art ixt
        _                -> do st <- setupToTerm opts sc base
                               lift $ scTupleSelector sc st ind
    -- SetupVar, SetupNull, SetupGlobal
    _ -> MaybeT $ return Nothing

data PrePost
  = PreState | PostState
  deriving (Eq, Show)


data PointsTo = PointsTo SetupValue SetupValue
  deriving (Show)

data SetupCondition where
  SetupCond_Equal    :: SetupValue -> SetupValue -> SetupCondition
  SetupCond_Pred     :: TypedTerm -> SetupCondition
  SetupCond_Ghost    :: GhostGlobal ->
                        TypedTerm ->
                        SetupCondition
  deriving (Show)

-- | Verification state (either pre- or post-) specification
data StateSpec = StateSpec
  { _csAllocs        :: Map AllocIndex SymType
    -- ^ allocated pointers
  , _csFreshPointers :: Map AllocIndex SymType
    -- ^ symbolic pointers
  , _csPointsTos     :: [PointsTo]
    -- ^ points-to statements
  , _csConditions    :: [SetupCondition]
    -- ^ equality, propositions, and ghost-variable conditions
  , _csFreshVars     :: [TypedTerm]
    -- ^ fresh variables created in this state
  }
  deriving (Show)

data CrucibleMethodSpecIR =
  CrucibleMethodSpec
  { _csName            :: L.Symbol
  , _csArgs            :: [L.Type]
  , _csRet             :: L.Type
  , _csPreState        :: StateSpec -- ^ state before the function runs
  , _csPostState       :: StateSpec -- ^ state after the function runs
  , _csArgBindings     :: Map Integer (SymType, SetupValue) -- ^ function arguments
  , _csRetValue        :: Maybe SetupValue                  -- ^ function return value
  , _csSolverStats     :: SolverStats                       -- ^ statistics about the proof that produced this
  }
  deriving (Show)

type GhostValue  = "GhostValue"
type GhostType   = Crucible.IntrinsicType GhostValue Crucible.EmptyCtx
type GhostGlobal = Crucible.GlobalVar GhostType

instance Crucible.IntrinsicClass (Crucible.SAWCoreBackend n) GhostValue where
  type Intrinsic (Crucible.SAWCoreBackend n) GhostValue ctx = TypedTerm
  muxIntrinsic sym _namerep _ctx prd thn els =
    do st <- readIORef (Crucible.sbStateManager sym)
       let sc  = Crucible.saw_ctx st
       prd' <- Crucible.toSC sym prd
       typ  <- scTypeOf sc (ttTerm thn)
       res  <- scIte sc typ prd' (ttTerm thn) (ttTerm els)
       return thn { ttTerm = res }

makeLenses ''CrucibleMethodSpecIR
makeLenses ''StateSpec

csAllocations :: CrucibleMethodSpecIR -> Map AllocIndex SymType
csAllocations
  = Map.unions
  . toListOf ((csPreState <> csPostState) . (csAllocs <> csFreshPointers))

-- | Represent `CrucibleMethodSpecIR` as a function term in SAW-Core. 
methodSpecToTerm :: SharedContext -> CrucibleMethodSpecIR -> MaybeT IO Term
methodSpecToTerm sc spec =
      -- 1. fill in the post-state user variable holes with final
      -- symbolic state
  let _ppts = _csPointsTos $ _csPostState $ instantiateUserVars spec
      -- 2. get the free variables in post points to's (note: these
      -- should be contained in variables bound by pre-points-tos)

      -- 3. abstract the free variables in each post-points-to

      -- 4. put every abstracted post-points-to in a tuple

      -- 5. Create struct type with fields being names of free variables

      -- 6. Create a lambda term bound to a struct-typed variable that returns the tuple
  in lift $ scLambda sc undefined undefined undefined

-- | Rewrite the `csPostPointsTos` to substitute the elements of the
-- final symbolic state for the fresh variables created by the user in
-- the post-state.
instantiateUserVars :: CrucibleMethodSpecIR -> CrucibleMethodSpecIR
instantiateUserVars _spec = undefined

-- | A datatype to keep track of which parts of the simulator state
-- have been initialized already. For each allocation unit or global,
-- we keep a list of element-paths that identify the initialized
-- sub-components.
data ResolvedState =
  ResolvedState
  {_rsAllocs :: Map AllocIndex [[Int]]
  ,_rsGlobals :: Map String [[Int]]
  }

data CrucibleSetupState wptr =
  CrucibleSetupState
  {_csVarCounter      :: !AllocIndex
  ,_csPrePost         :: PrePost
  ,_csResolvedState   :: ResolvedState
  ,_csMethodSpec      :: CrucibleMethodSpecIR
  ,_csCrucibleContext :: CrucibleContext wptr
  }

type Sym = Crucible.SAWCoreBackend Crucible.GlobalNonceGenerator

data CrucibleContext wptr =
  CrucibleContext
  { _ccLLVMContext     :: Crucible.LLVMContext wptr
  , _ccLLVMModule      :: L.Module
  , _ccLLVMModuleTrans :: Crucible.ModuleTranslation
  , _ccBackend         :: Sym
  , _ccEmptyMemImpl    :: Crucible.MemImpl Sym -- ^ A heap where LLVM globals are allocated, but not initialized.
  , _ccSimContext      :: Crucible.SimContext Crucible.SAWCruciblePersonality Sym Crucible.LLVM
  , _ccGlobals         :: Crucible.SymGlobalState Sym
  }

makeLenses ''CrucibleContext
makeLenses ''CrucibleSetupState
makeLenses ''ResolvedState

ccTypeCtx :: Simple Lens (CrucibleContext wptr) TyCtx.LLVMContext
ccTypeCtx = ccLLVMContext . Crucible.llvmTypeCtx

--------------------------------------------------------------------------------

emptyResolvedState :: ResolvedState
emptyResolvedState = ResolvedState Map.empty Map.empty

-- | Record the initialization of the pointer represented by the given
-- SetupValue.
markResolved ::
  SetupValue ->
  ResolvedState ->
  ResolvedState
markResolved val0 rs = go [] val0
  where
    go path val =
      case val of
        SetupVar n    -> rs {_rsAllocs = Map.alter (ins path) n (_rsAllocs rs) }
        SetupGlobal c -> rs {_rsGlobals = Map.alter (ins path) c (_rsGlobals rs)}
        SetupElem v i -> go (i : path) v
        _             -> rs

    ins path Nothing = Just [path]
    ins path (Just paths) = Just (path : paths)

-- | Test whether the pointer represented by the given SetupValue has
-- been initialized already.
testResolved ::
  SetupValue ->
  ResolvedState ->
  Bool
testResolved val0 rs = go [] val0
  where
    go path val =
      case val of
        SetupVar n    -> test path (Map.lookup n (_rsAllocs rs))
        SetupGlobal c -> test path (Map.lookup c (_rsGlobals rs))
        SetupElem v i -> go (i : path) v
        _             -> False

    test _ Nothing = False
    test path (Just paths) = any (`isPrefixOf` path) paths


intrinsics :: MapF.MapF Crucible.SymbolRepr (Crucible.IntrinsicMuxFn
                (Crucible.SAWCoreBackend Crucible.GlobalNonceGenerator))
intrinsics =
  MapF.insert
    (Crucible.knownSymbol :: Crucible.SymbolRepr GhostValue)
    Crucible.IntrinsicMuxFn
    Crucible.llvmIntrinsicTypes

-------------------------------------------------------------------------------

initialStateSpec :: StateSpec
initialStateSpec =  StateSpec
  { _csAllocs        = Map.empty
  , _csFreshPointers = Map.empty
  , _csPointsTos     = []
  , _csConditions    = []
  , _csFreshVars     = []
  }

initialDefCrucibleMethodSpecIR :: L.Define -> CrucibleMethodSpecIR
initialDefCrucibleMethodSpecIR def =
  CrucibleMethodSpec
  {_csName            = L.defName def
  ,_csArgs            = L.typedType <$> L.defArgs def
  ,_csRet             = L.defRetType def
  ,_csPreState        = initialStateSpec
  ,_csPostState       = initialStateSpec
  ,_csArgBindings     = Map.empty
  ,_csRetValue        = Nothing
  ,_csSolverStats     = mempty
  }

initialDeclCrucibleMethodSpecIR :: L.Declare -> CrucibleMethodSpecIR
initialDeclCrucibleMethodSpecIR dec =
  CrucibleMethodSpec
  {_csName            = L.decName dec
  ,_csArgs            = L.decArgs dec
  ,_csRet             = L.decRetType dec
  ,_csPreState        = initialStateSpec
  ,_csPostState       = initialStateSpec
  ,_csArgBindings     = Map.empty
  ,_csRetValue        = Nothing
  ,_csSolverStats     = mempty
  }

initialCrucibleSetupState :: CrucibleContext wptr -> L.Define -> CrucibleSetupState wptr
initialCrucibleSetupState cc def = CrucibleSetupState
  { _csVarCounter      = AllocIndex 0
  , _csPrePost         = PreState
  , _csResolvedState   = emptyResolvedState
  , _csMethodSpec      = initialDefCrucibleMethodSpecIR def
  , _csCrucibleContext = cc
  }

initialCrucibleSetupStateDecl :: CrucibleContext wptr -> L.Declare -> CrucibleSetupState wptr
initialCrucibleSetupStateDecl cc dec = CrucibleSetupState
  { _csVarCounter      = AllocIndex 0
  , _csPrePost         = PreState
  , _csResolvedState   = emptyResolvedState
  , _csMethodSpec      = initialDeclCrucibleMethodSpecIR dec
  , _csCrucibleContext = cc
  }


