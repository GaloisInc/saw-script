{- |
Module      : SAWScript.CrucibleMethodSpecIR
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

module SAWScript.JVM.CrucibleMethodSpecIR where

import           Data.Map (Map)
import qualified Data.Map as Map
import           Control.Monad.ST (RealWorld)
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans (lift)
import           Control.Lens

import           Data.IORef
import           Data.Monoid ((<>))

import qualified Data.Parameterized.Nonce as Crucible

-- what4
import qualified What4.Expr.Builder as B
import           What4.ProgramLoc (ProgramLoc)

import qualified Lang.Crucible.Types as Crucible
  (IntrinsicType, EmptyCtx)
import qualified Lang.Crucible.CFG.Common as Crucible (GlobalVar)
import qualified Lang.Crucible.Backend.SAWCore as Crucible
  (SAWCoreBackend, saw_ctx, toSC)
import qualified Lang.Crucible.FunctionHandle as Crucible (HandleAllocator)
import qualified Lang.Crucible.Simulator.Intrinsics as Crucible
  (IntrinsicClass(Intrinsic, muxIntrinsic){-, IntrinsicMuxFn(IntrinsicMuxFn)-})

-- crucible-jvm
import qualified Lang.Crucible.JVM.Translation as CJ

-- jvm-verifier
-- TODO: transition to Lang.JVM.Codebase from crucible-jvm
import qualified Verifier.Java.Codebase as CB

-- jvm-parser
import qualified Language.JVM.Parser as J

-- saw-core
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedTerm

import SAWScript.Options
import SAWScript.Prover.SolverStats

newtype AllocIndex = AllocIndex Int
  deriving (Eq, Ord, Show)

nextAllocIndex :: AllocIndex -> AllocIndex
nextAllocIndex (AllocIndex n) = AllocIndex (n + 1)

data SetupValue where
  SetupVar    :: AllocIndex -> SetupValue
  SetupTerm   :: TypedTerm -> SetupValue
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
setupToTerm _opts _sc sv =
  case sv of
    SetupTerm term -> return (ttTerm term)
    _ -> MaybeT $ return Nothing

data PrePost
  = PreState | PostState
  deriving (Eq, Show)


data PointsTo
  = PointsToField ProgramLoc SetupValue String SetupValue
  | PointsToElem ProgramLoc SetupValue Int SetupValue
  deriving (Show)

data SetupCondition where
  SetupCond_Equal :: ProgramLoc -> SetupValue -> SetupValue -> SetupCondition
  SetupCond_Pred :: ProgramLoc -> TypedTerm -> SetupCondition
  deriving (Show)

data Allocation
  = AllocObject J.ClassName
  | AllocArray Int J.Type
  deriving (Show)

allocationType :: Allocation -> J.Type
allocationType alloc =
  case alloc of
    AllocObject cname -> J.ClassType cname
    AllocArray _len ty -> J.ArrayType ty

type JIdent = String -- FIXME: what to put here?

-- | Verification state (either pre- or post-) specification
data StateSpec' t = StateSpec
  { _csAllocs        :: Map AllocIndex t
    -- ^ allocated pointers
  , _csPointsTos     :: [PointsTo]
    -- ^ points-to statements
  , _csConditions    :: [SetupCondition]
    -- ^ equalities and propositions
  , _csFreshVars     :: [TypedTerm]
    -- ^ fresh variables created in this state
  , _csVarTypeNames  :: Map AllocIndex JIdent
    -- ^ names for types of variables, for diagnostics
  }
  deriving (Show)

type StateSpec = StateSpec' (ProgramLoc, Allocation)

data CrucibleMethodSpecIR' t =
  CrucibleMethodSpec
  { _csClassName       :: J.ClassName
  , _csMethodName      :: String
  , _csArgs            :: [t]
  , _csRet             :: Maybe t
  , _csPreState        :: StateSpec -- ^ state before the function runs
  , _csPostState       :: StateSpec -- ^ state after the function runs
  , _csArgBindings     :: Map Integer (t, SetupValue) -- ^ function arguments
  , _csRetValue        :: Maybe SetupValue            -- ^ function return value
  , _csSolverStats     :: SolverStats                 -- ^ statistics about the proof that produced this
  , _csLoc             :: ProgramLoc
  }
  deriving (Show)

type CrucibleMethodSpecIR = CrucibleMethodSpecIR' J.Type

type GhostValue  = "GhostValue"
type GhostType   = Crucible.IntrinsicType GhostValue Crucible.EmptyCtx
type GhostGlobal = Crucible.GlobalVar GhostType

instance Crucible.IntrinsicClass (Crucible.SAWCoreBackend n (B.Flags B.FloatReal)) GhostValue where
  type Intrinsic (Crucible.SAWCoreBackend n (B.Flags B.FloatReal)) GhostValue ctx = TypedTerm
  muxIntrinsic sym _ _namerep _ctx prd thn els =
    do st <- readIORef (B.sbStateManager sym)
       let sc  = Crucible.saw_ctx st
       prd' <- Crucible.toSC sym prd
       typ  <- scTypeOf sc (ttTerm thn)
       res  <- scIte sc typ prd' (ttTerm thn) (ttTerm els)
       return thn { ttTerm = res }

makeLenses ''CrucibleMethodSpecIR'
makeLenses ''StateSpec'

csAllocations :: CrucibleMethodSpecIR -> Map AllocIndex (ProgramLoc, Allocation)
csAllocations
  = Map.unions
  . toListOf ((csPreState <> csPostState) . csAllocs)

csTypeNames :: CrucibleMethodSpecIR -> Map AllocIndex JIdent
csTypeNames
  = Map.unions
  . toListOf ((csPreState <> csPostState) . csVarTypeNames)

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
  { _rsAllocs :: Map AllocIndex [Either String Int]
  , _rsGlobals :: Map String [Either String Int]
  }

data CrucibleSetupState =
  CrucibleSetupState
  { _csVarCounter      :: !AllocIndex
  , _csPrePost         :: PrePost
  , _csResolvedState   :: ResolvedState
  , _csMethodSpec      :: CrucibleMethodSpecIR
  , _csCrucibleContext :: CrucibleContext
  }

type Sym = Crucible.SAWCoreBackend Crucible.GlobalNonceGenerator (B.Flags B.FloatReal)

data CrucibleContext =
  CrucibleContext
  { _ccJVMClass       :: J.Class
  , _ccCodebase       :: CB.Codebase
  , _ccJVMContext     :: CJ.JVMContext
  , _ccBackend        :: Sym -- This is stored inside field _ctxSymInterface of Crucible.SimContext; why do we need another one?
  , _ccHandleAllocator :: Crucible.HandleAllocator RealWorld
  }

makeLenses ''CrucibleContext
makeLenses ''CrucibleSetupState
makeLenses ''ResolvedState

--------------------------------------------------------------------------------

emptyResolvedState :: ResolvedState
emptyResolvedState = ResolvedState Map.empty Map.empty

-- | Record the initialization of the pointer represented by the given
-- SetupValue.
markResolved ::
  SetupValue ->
  Either String Int ->
  ResolvedState ->
  ResolvedState
markResolved val0 path0 rs = go path0 val0
  where
    go path val =
      case val of
        SetupVar n    -> rs {_rsAllocs = Map.alter (ins path) n (_rsAllocs rs) }
        SetupGlobal c -> rs {_rsGlobals = Map.alter (ins path) c (_rsGlobals rs)}
        -- SetupElem v i -> go (i : path) v
        _             -> rs

    ins path Nothing = Just [path]
    ins path (Just paths) = Just (path : paths)

-- | Test whether the pointer represented by the given SetupValue has
-- been initialized already.
testResolved ::
  SetupValue ->
  Either String Int ->
  ResolvedState ->
  Bool
testResolved val0 path0 rs = go path0 val0
  where
    go path val =
      case val of
        SetupVar n    -> test path (Map.lookup n (_rsAllocs rs))
        SetupGlobal c -> test path (Map.lookup c (_rsGlobals rs))
        -- SetupElem v i -> go (i : path) v
        _             -> False

    test _ Nothing = False
    test path (Just paths) = path `elem` paths -- any (`isPrefixOf` path) paths

-------------------------------------------------------------------------------

initialStateSpec :: StateSpec
initialStateSpec =  StateSpec
  { _csAllocs        = Map.empty
  , _csPointsTos     = []
  , _csConditions    = []
  , _csFreshVars     = []
  , _csVarTypeNames  = Map.empty
  }

initialDefCrucibleMethodSpecIR ::
  J.ClassName ->
  J.Method ->
  ProgramLoc ->
  CrucibleMethodSpecIR
initialDefCrucibleMethodSpecIR cname method loc =
  CrucibleMethodSpec
    { _csClassName       = cname
    , _csMethodName      = J.methodName method
    , _csArgs            = thisType ++ J.methodParameterTypes method
    , _csRet             = J.methodReturnType method
    , _csPreState        = initialStateSpec
    , _csPostState       = initialStateSpec
    , _csArgBindings     = Map.empty
    , _csRetValue        = Nothing
    , _csSolverStats     = mempty
    , _csLoc             = loc
    }
  where
    thisType = if J.methodIsStatic method then [] else [J.ClassType cname]

initialCrucibleSetupState ::
  CrucibleContext ->
  J.Method ->
  ProgramLoc ->
  CrucibleSetupState
initialCrucibleSetupState cc method loc =
  CrucibleSetupState
    { _csVarCounter      = AllocIndex 0
    , _csPrePost         = PreState
    , _csResolvedState   = emptyResolvedState
    , _csMethodSpec      = initialDefCrucibleMethodSpecIR cname method loc
    , _csCrucibleContext = cc
    }
  where
    cname = J.className (cc^.ccJVMClass)
