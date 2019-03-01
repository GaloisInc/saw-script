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

module SAWScript.CrucibleMethodSpecIR where

import           Data.List (isPrefixOf)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans (lift)
import           Control.Lens
import Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>), (<>))

import qualified Text.LLVM.AST as L
import qualified Text.LLVM.PP as L
import           Data.IORef
import           Data.Monoid ((<>))

import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Nonce as Crucible

import SAWScript.Prover.SolverStats

import qualified What4.Expr.Builder as B
import           What4.ProgramLoc (ProgramLoc)
import qualified What4.Solver.Yices as Yices

import qualified Lang.Crucible.Types as Crucible
  (IntrinsicType, EmptyCtx, SymbolRepr, knownSymbol)
import qualified Lang.Crucible.CFG.Common as Crucible (GlobalVar)
import qualified Lang.Crucible.Backend.SAWCore as Crucible
  (SAWCoreBackend, saw_ctx, toSC, SAWCruciblePersonality)
import qualified Lang.Crucible.Simulator.ExecutionTree as Crucible (SimContext)
import qualified Lang.Crucible.Simulator.GlobalState as Crucible (SymGlobalState)
--import qualified Lang.Crucible.LLVM.MemModel as CL (MemImpl)
--import qualified Lang.Crucible.LLVM.Translation as CL
import qualified Lang.Crucible.Simulator.Intrinsics as Crucible
  (IntrinsicClass(Intrinsic, muxIntrinsic), IntrinsicMuxFn(IntrinsicMuxFn))

import qualified SAWScript.CrucibleLLVM as CL

import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedTerm
import SAWScript.Options

newtype AllocIndex = AllocIndex Int
  deriving (Eq, Ord, Show)

nextAllocIndex :: AllocIndex -> AllocIndex
nextAllocIndex (AllocIndex n) = AllocIndex (n + 1)

-- | From the manual: "The SetupValue type corresponds to values that can occur
-- during symbolic execution, which includes both Term values, pointers, and
-- composite types consisting of either of these (both structures and arrays)."
data SetupValue where
  SetupVar               :: AllocIndex -> SetupValue
  SetupTerm              :: TypedTerm -> SetupValue
  SetupStruct            :: Bool -> [SetupValue] -> SetupValue -- True = packed
  SetupArray             :: [SetupValue] -> SetupValue
  SetupElem              :: SetupValue -> Int -> SetupValue
  SetupField             :: SetupValue -> String -> SetupValue
  SetupNull              :: SetupValue
  -- | A pointer to a global variable
  SetupGlobal            :: String -> SetupValue
  -- | This represents the value of a global's initializer.
  SetupGlobalInitializer :: String -> SetupValue
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
    SetupStruct _ fields ->
      do ts <- mapM (setupToTerm opts sc) fields
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
        SetupStruct _ fs ->
          do st <- setupToTerm opts sc base
             lift $ scTupleSelector sc st ind (length fs)
        _ ->
          MaybeT $ return Nothing
    -- SetupVar, SetupNull, SetupGlobal
    _ -> MaybeT $ return Nothing

data PrePost
  = PreState | PostState
  deriving (Eq, Show)


data PointsTo = PointsTo ProgramLoc SetupValue SetupValue
  deriving (Show)

data SetupCondition where
  SetupCond_Equal    :: ProgramLoc ->SetupValue -> SetupValue -> SetupCondition
  SetupCond_Pred     :: ProgramLoc -> TypedTerm -> SetupCondition
  SetupCond_Ghost    :: ProgramLoc ->
                        GhostGlobal ->
                        TypedTerm ->
                        SetupCondition
  deriving (Show)

-- | Verification state (either pre- or post-) specification
data StateSpec' t = StateSpec
  { _csAllocs        :: Map AllocIndex t
    -- ^ allocated pointers
  , _csConstAllocs   :: Map AllocIndex t
    -- ^ allocated read-only pointers
  , _csFreshPointers :: Map AllocIndex t
    -- ^ symbolic pointers
  , _csPointsTos     :: [PointsTo]
    -- ^ points-to statements
  , _csConditions    :: [SetupCondition]
    -- ^ equality, propositions, and ghost-variable conditions
  , _csFreshVars     :: [TypedTerm]
    -- ^ fresh variables created in this state
  , _csVarTypeNames  :: Map AllocIndex CL.Ident
    -- ^ names for types of variables, for diagnostics
  }
  deriving (Show)

type StateSpec = StateSpec' (ProgramLoc, CL.MemType)

data CrucibleMethodSpecIR' t =
  CrucibleMethodSpec
  { _csName            :: String
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

type CrucibleMethodSpecIR = CrucibleMethodSpecIR' CL.MemType

type GhostValue  = "GhostValue"
type GhostType   = Crucible.IntrinsicType GhostValue Crucible.EmptyCtx
type GhostGlobal = Crucible.GlobalVar GhostType

instance Crucible.IntrinsicClass (Crucible.SAWCoreBackend n solver (B.Flags B.FloatReal)) GhostValue where
  type Intrinsic (Crucible.SAWCoreBackend n solver (B.Flags B.FloatReal)) GhostValue ctx = TypedTerm
  muxIntrinsic sym _ _namerep _ctx prd thn els =
    do st <- readIORef (B.sbStateManager sym)
       let sc  = Crucible.saw_ctx st
       prd' <- Crucible.toSC sym prd
       typ  <- scTypeOf sc (ttTerm thn)
       res  <- scIte sc typ prd' (ttTerm thn) (ttTerm els)
       return thn { ttTerm = res }

makeLenses ''CrucibleMethodSpecIR'
makeLenses ''StateSpec'

csAllocations :: CrucibleMethodSpecIR -> Map AllocIndex (ProgramLoc, CL.MemType)
csAllocations
  = Map.unions
  . toListOf ((csPreState <> csPostState) . (csAllocs <> csConstAllocs <> csFreshPointers))

csTypeNames :: CrucibleMethodSpecIR -> Map AllocIndex CL.Ident
csTypeNames
  = Map.unions
  . toListOf ((csPreState <> csPostState) . (csVarTypeNames))

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

type Sym = Crucible.SAWCoreBackend Crucible.GlobalNonceGenerator (Yices.Connection Crucible.GlobalNonceGenerator) (B.Flags B.FloatReal)

data CrucibleContext wptr =
  CrucibleContext
  { _ccLLVMModule      :: L.Module
  , _ccLLVMModuleTrans :: CL.ModuleTranslation wptr
  , _ccBackend         :: Sym
  , _ccLLVMEmptyMem    :: CL.MemImpl Sym -- ^ A heap where LLVM globals are allocated, but not initialized.
  , _ccLLVMSimContext  :: Crucible.SimContext (Crucible.SAWCruciblePersonality Sym) Sym (CL.LLVM wptr)
  , _ccLLVMGlobals     :: Crucible.SymGlobalState Sym
  }

makeLenses ''CrucibleContext
makeLenses ''CrucibleSetupState
makeLenses ''ResolvedState

ccLLVMContext :: Simple Lens (CrucibleContext wptr) (CL.LLVMContext wptr)
ccLLVMContext = ccLLVMModuleTrans . CL.transContext

ccTypeCtx :: Simple Lens (CrucibleContext wptr) CL.TypeContext
ccTypeCtx = ccLLVMContext . CL.llvmTypeCtx

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


intrinsics :: MapF.MapF Crucible.SymbolRepr (Crucible.IntrinsicMuxFn Sym)
intrinsics =
  MapF.insert
    (Crucible.knownSymbol :: Crucible.SymbolRepr GhostValue)
    Crucible.IntrinsicMuxFn
    CL.llvmIntrinsicTypes

-------------------------------------------------------------------------------

data SetupError
  = InvalidReturnType L.Type
  | InvalidArgTypes [L.Type]

ppSetupError :: SetupError -> PP.Doc
ppSetupError (InvalidReturnType t) =
  text "Can't lift return type" <+>
  text (show (L.ppType t)) <+>
  text "to a Crucible type."
ppSetupError (InvalidArgTypes ts) =
  text "Can't lift argument types " <+>
  encloseSep lparen rparen comma (map (text . show . L.ppType) ts) <+>
  text "to Crucible types."

resolveArgs ::
  (?lc :: CL.TypeContext) =>
  [L.Type] ->
  Either SetupError [CL.MemType]
resolveArgs args = do
  -- TODO: make sure we resolve aliases
  let mtys = traverse CL.liftMemType args
  -- TODO: should the error message be propagated?
  either (\_ -> Left (InvalidArgTypes args)) Right mtys

resolveRetTy ::
  (?lc :: CL.TypeContext) =>
  L.Type ->
  Either SetupError (Maybe CL.MemType)
resolveRetTy ty = do
  -- TODO: make sure we resolve aliases
  let ret = CL.liftRetType ty
  -- TODO: should the error message be propagated?
  either (\_ -> Left (InvalidReturnType ty)) Right ret

initialStateSpec :: StateSpec
initialStateSpec =  StateSpec
  { _csAllocs        = Map.empty
  , _csConstAllocs   = Map.empty
  , _csFreshPointers = Map.empty
  , _csPointsTos     = []
  , _csConditions    = []
  , _csFreshVars     = []
  , _csVarTypeNames  = Map.empty
  }

initialDefCrucibleMethodSpecIR ::
  (?lc :: CL.TypeContext) =>
  L.Define ->
  ProgramLoc ->
  Either SetupError CrucibleMethodSpecIR
initialDefCrucibleMethodSpecIR def loc = do
  args <- resolveArgs (L.typedType <$> L.defArgs def)
  ret <- resolveRetTy (L.defRetType def)
  let L.Symbol nm = L.defName def
  return CrucibleMethodSpec
    {_csName            = nm
    ,_csArgs            = args
    ,_csRet             = ret
    ,_csPreState        = initialStateSpec
    ,_csPostState       = initialStateSpec
    ,_csArgBindings     = Map.empty
    ,_csRetValue        = Nothing
    ,_csSolverStats     = mempty
    ,_csLoc             = loc
    }

initialDeclCrucibleMethodSpecIR ::
  (?lc :: CL.TypeContext) =>
  L.Declare ->
  ProgramLoc ->
  Either SetupError CrucibleMethodSpecIR
initialDeclCrucibleMethodSpecIR dec loc = do
  args <- resolveArgs (L.decArgs dec)
  ret <- resolveRetTy (L.decRetType dec)
  let L.Symbol nm = L.decName dec
  return CrucibleMethodSpec
    {_csName            = nm
    ,_csArgs            = args
    ,_csRet             = ret
    ,_csPreState        = initialStateSpec
    ,_csPostState       = initialStateSpec
    ,_csArgBindings     = Map.empty
    ,_csRetValue        = Nothing
    ,_csSolverStats     = mempty
    ,_csLoc             = loc
    }

initialCrucibleSetupState ::
  (?lc :: CL.TypeContext) =>
  CrucibleContext wptr ->
  L.Define ->
  ProgramLoc ->
  Either SetupError (CrucibleSetupState wptr)
initialCrucibleSetupState cc def loc = do
  ms <- initialDefCrucibleMethodSpecIR def loc
  return CrucibleSetupState
    { _csVarCounter      = AllocIndex 0
    , _csPrePost         = PreState
    , _csResolvedState   = emptyResolvedState
    , _csMethodSpec      = ms
    , _csCrucibleContext = cc
    }

initialCrucibleSetupStateDecl ::
  (?lc :: CL.TypeContext) =>
  CrucibleContext wptr ->
  L.Declare ->
  ProgramLoc ->
  Either SetupError (CrucibleSetupState wptr)
initialCrucibleSetupStateDecl cc dec loc = do
  ms <- initialDeclCrucibleMethodSpecIR dec loc
  return CrucibleSetupState
    { _csVarCounter      = AllocIndex 0
    , _csPrePost         = PreState
    , _csResolvedState   = emptyResolvedState
    , _csMethodSpec      = ms
    , _csCrucibleContext = cc
    }
