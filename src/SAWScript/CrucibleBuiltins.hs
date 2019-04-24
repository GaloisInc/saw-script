{- |
Module      : SAWScript.CrucibleBuiltins
Description : Implementations of Crucible-related SAW-Script primitives.
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances, MultiParamTypeClasses#-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}

{-# OPTIONS_GHC -Wno-orphans #-}

{-# OPTIONS_GHC -fno-warn-unused-local-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}


module SAWScript.CrucibleBuiltins
    ( show_cfg
    , crucible_llvm_cfg
    , crucible_llvm_extract
    , crucible_llvm_verify
    , crucible_setup_val_to_typed_term
    , crucible_spec_size
    , crucible_spec_solvers
    , crucible_ghost_value
    , crucible_return
    , crucible_declare_ghost_state
    , crucible_execute_func
    , crucible_postcond
    , crucible_precond
    , crucible_equal
    , crucible_points_to
    , crucible_fresh_pointer
    , crucible_llvm_unsafe_assume_spec
    , crucible_fresh_var
    , crucible_alloc
    , crucible_alloc_readonly
    , crucible_fresh_expanded_val

    --
    -- These function are common to LLVM & JVM implementation (not for external use)
    , setupArg
    , setupArgs
    , getGlobalPair
    , runCFG
    ) where

import           Control.Lens

import           Control.Monad.State
import           Control.Applicative
import qualified Data.Bimap as Bimap
import           Data.Foldable (for_, toList, find)
import           Data.Function
import           Data.IORef
import           Data.List
import           Data.List.Extra (groupOn, nubOrd)
import           Data.Maybe
import           Data.Monoid ((<>))
import           Data.String
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Set as Set
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import qualified Data.Vector as V
import           Numeric.Natural
import           System.IO

import qualified Text.LLVM.AST as L
import qualified Text.LLVM.PP as L (ppType)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>))
import qualified Control.Monad.Trans.Maybe as MaybeT

import           Data.Parameterized.Classes

import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some

import qualified What4.Config as W4
import qualified What4.FunctionName as W4
import qualified What4.ProgramLoc as W4
import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4
import           What4.Utils.MonadST

import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Backend.Online as Crucible
import qualified Lang.Crucible.Backend.SAWCore as CrucibleSAW
import qualified Lang.Crucible.CFG.Core as Crucible
import qualified Lang.Crucible.CFG.Extension as Crucible
  (IsSyntaxExtension)
import qualified Lang.Crucible.FunctionHandle as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Simulator.Breakpoint as Crucible
import qualified Lang.Crucible.Simulator.GlobalState as Crucible
import qualified Lang.Crucible.Simulator.PathSatisfiability as Crucible
import qualified Lang.Crucible.Simulator.RegMap as Crucible
import qualified Lang.Crucible.Simulator.SimError as Crucible

import qualified Lang.Crucible.LLVM.DataLayout as Crucible
import qualified Lang.Crucible.LLVM.MemModel as Crucible
import qualified Lang.Crucible.LLVM.Translation as Crucible

import qualified SAWScript.CrucibleLLVM as Crucible

import qualified Data.Parameterized.TraversableFC as Ctx
import qualified Data.Parameterized.Context as Ctx

import Verifier.SAW.FiniteValue (ppFirstOrderValue)
import Verifier.SAW.Prelude
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST
import Verifier.SAW.Recognizer
import Verifier.SAW.TypedTerm

import SAWScript.Proof
import SAWScript.Prover.SolverStats
import SAWScript.TopLevel
import SAWScript.Value
import SAWScript.Utils as SS
import SAWScript.Options

import SAWScript.CrucibleMethodSpecIR
import SAWScript.CrucibleOverride
import SAWScript.CrucibleResolveSetupValue


type MemImpl = Crucible.MemImpl Sym

show_cfg :: SAW_CFG -> String
show_cfg (LLVM_CFG (Crucible.AnyCFG cfg)) = show cfg
show_cfg (JVM_CFG (Crucible.AnyCFG cfg)) = show cfg

ppAbortedResult :: CrucibleContext arch
                -> Crucible.AbortedResult Sym a
                -> Doc
ppAbortedResult _ (Crucible.AbortedExec Crucible.InfeasibleBranch _) =
  text "Infeasible branch"
ppAbortedResult cc (Crucible.AbortedExec abt gp) = do
  Crucible.ppAbortExecReason abt <$$> ppGlobalPair cc gp
ppAbortedResult _ (Crucible.AbortedBranch _ _ _) =
  text "Aborted branch"
ppAbortedResult _ (Crucible.AbortedExit ec) =
  text "Branch exited:" <+> text (show ec)

resolveSpecName :: String -> TopLevel (L.Symbol, Maybe String)
resolveSpecName nm = if Crucible.testBreakpointFunction nm
  then return
    ( fromString (takeWhile (not . (== '#')) nm)
    , Just (tail (dropWhile (not . (== '#')) nm))
    )
  else return (fromString nm, Nothing)

crucible_llvm_verify ::
  BuiltinContext         ->
  Options                ->
  LLVMModule             ->
  String                 ->
  [CrucibleMethodSpecIR] ->
  Bool                   ->
  CrucibleSetupM ()      ->
  ProofScript SatResult  ->
  TopLevel CrucibleMethodSpecIR
crucible_llvm_verify bic opts lm nm lemmas checkSat setup tactic =
  setupCrucibleContext bic opts lm $ \cc -> do
     let sym = cc^.ccBackend
     (nm', parent) <- resolveSpecName nm
     let llmod = cc^.ccLLVMModule

     setupLoc <- toW4Loc "_SAW_verify_prestate" <$> getPosition

     st0 <- case initialCrucibleSetupState cc     <$> find (\d -> L.defName d == nm') (L.modDefines  llmod) <*> pure setupLoc <*> pure parent <|>
                 initialCrucibleSetupStateDecl cc <$> find (\d -> L.decName d == nm') (L.modDeclares llmod) <*> pure setupLoc <*> pure parent of
                    Nothing -> fail $ unlines $
                      [ "Could not find function named " ++ show nm
                      ] ++ if simVerbose opts < 3
                           then [ "Run SAW with --sim-verbose=3 to see all function names" ]
                           else "Available function names:" :
                                  map (("  " ++) . show . L.decName) (L.modDeclares llmod) ++
                                  -- " " ++
                                  map (("  " ++) . show . L.defName) (L.modDefines llmod)
                    Just (Left err) -> fail (show (ppSetupError err))
                    Just (Right st0) -> return st0

     -- execute commands of the method spec
     liftIO $ W4.setCurrentProgramLoc sym setupLoc
     methodSpec <- view csMethodSpec <$> execStateT (runCrucibleSetupM setup) st0

     -- set up the LLVM memory with a pristine heap
     let globals = cc^.ccLLVMGlobals
     let mvar = Crucible.llvmMemVar (cc^.ccLLVMContext)
     mem0 <- case Crucible.lookupGlobal mvar globals of
       Nothing   -> fail "internal error: LLVM Memory global not found"
       Just mem0 -> return mem0
     -- push a memory stack frame if starting from a breakpoint
     let mem = if isJust (methodSpec^.csParentName)
           then mem0
             { Crucible.memImplHeap = Crucible.pushStackFrameMem
                 (Crucible.memImplHeap mem0)
             }
           else mem0
     let globals1 = Crucible.llvmGlobals (cc^.ccLLVMContext) mem

     -- construct the initial state for verifications
     (args, assumes, env, globals2) <- io $ verifyPrestate cc methodSpec globals1

     -- save initial path conditions
     frameIdent <- io $ Crucible.pushAssumptionFrame sym

     -- run the symbolic execution
     top_loc <- toW4Loc "crucible_llvm_verify" <$> getPosition
     (ret, globals3)
        <- io $ verifySimulate opts cc methodSpec args assumes top_loc lemmas globals2 checkSat

     -- collect the proof obligations
     asserts <- verifyPoststate opts (biSharedContext bic) cc
                    methodSpec env globals3 ret

     -- restore previous assumption state
     _ <- io $ Crucible.popAssumptionFrame sym frameIdent

     -- attempt to verify the proof obligations
     stats <- verifyObligations cc methodSpec tactic assumes asserts
     return (methodSpec & csSolverStats .~ stats)

crucible_llvm_unsafe_assume_spec ::
  BuiltinContext   ->
  Options          ->
  LLVMModule       ->
  String          {- ^ Name of the function -} ->
  CrucibleSetupM () {- ^ Boundary specification -} ->
  TopLevel CrucibleMethodSpecIR
crucible_llvm_unsafe_assume_spec bic opts lm nm setup =
  setupCrucibleContext bic opts lm $ \cc -> do
    (nm', parent) <- resolveSpecName nm
    let llmod = cc^.ccLLVMModule
    loc <- toW4Loc "_SAW_assume_spec" <$> getPosition
    st0 <- case initialCrucibleSetupState cc     <$> find (\d -> L.defName d == nm') (L.modDefines  llmod) <*> pure loc <*> pure parent <|>
                initialCrucibleSetupStateDecl cc <$> find (\d -> L.decName d == nm') (L.modDeclares llmod) <*> pure loc <*> pure parent of
                   Nothing -> fail ("Could not find function named" ++ show nm)
                   Just (Left err) -> fail (show (ppSetupError err))
                   Just (Right st0) -> return st0
    (view csMethodSpec) <$> execStateT (runCrucibleSetupM setup) st0

verifyObligations :: CrucibleContext arch
                  -> CrucibleMethodSpecIR
                  -> ProofScript SatResult
                  -> [Crucible.LabeledPred Term Crucible.AssumptionReason]
                  -> [(String, Term)]
                  -> TopLevel SolverStats
verifyObligations cc mspec tactic assumes asserts = do
  let sym = cc^.ccBackend
  st     <- io $ readIORef $ W4.sbStateManager sym
  let sc  = CrucibleSAW.saw_ctx st
  assume <- io $ scAndList sc (toListOf (folded . Crucible.labeledPred) assumes)
  let nm  = mspec^.csName
  stats <- forM (zip [(0::Int)..] asserts) $ \(n, (msg, assert)) -> do
    goal   <- io $ scImplies sc assume assert
    goal'  <- io $ scGeneralizeExts sc (getAllExts goal) =<< scEqTrue sc goal
    let goalname = concat [nm, " (", takeWhile (/= '\n') msg, ")"]
        proofgoal = ProofGoal Universal n "vc" goalname goal'
    r      <- evalStateT tactic (startProof proofgoal)
    case r of
      Unsat stats -> return stats
      SatMulti stats vals -> do
        printOutLnTop Info $ unwords ["Subgoal failed:", nm, msg]
        printOutLnTop Info (show stats)
        printOutLnTop OnlyCounterExamples "----------Counterexample----------"
        opts <- sawPPOpts <$> rwPPOpts <$> getTopLevelRW
        let showAssignment (name, val) = "  " ++ name ++ ": " ++ show (ppFirstOrderValue opts val)
        mapM_ (printOutLnTop OnlyCounterExamples . showAssignment) vals
        io $ fail "Proof failed." -- Mirroring behavior of llvm_verify
  printOutLnTop Info $ unwords ["Proof succeeded!", nm]
  return (mconcat stats)

-- | Evaluate the precondition part of a Crucible method spec:
--
-- * Allocate heap space for each 'crucible_alloc' statement.
--
-- * Record an equality precondition for each 'crucible_equal'
-- statement.
--
-- * Write to memory for each 'crucible_points_to' statement. (Writes
-- to already-initialized locations are transformed into equality
-- preconditions.)
--
-- * Evaluate the function arguments from the 'crucible_execute_func'
-- statement.
--
-- Returns a tuple of (arguments, preconditions, pointer values,
-- memory).
verifyPrestate ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  CrucibleContext arch ->
  CrucibleMethodSpecIR ->
  Crucible.SymGlobalState Sym ->
  IO ([(Crucible.MemType, LLVMVal)],
      [Crucible.LabeledPred Term Crucible.AssumptionReason],
      Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)),
      Crucible.SymGlobalState Sym)
verifyPrestate cc mspec globals = do
  let ?lc = cc^.ccTypeCtx
  let sym = cc^.ccBackend
  let tyenvRW = mspec^.csPreState.csAllocs
  let tyenvRO = mspec^.csPreState.csConstAllocs
  let tyenv   = csAllocations mspec
  let nameEnv = mspec^.csPreState.csVarTypeNames

  let prestateLoc = W4.mkProgramLoc "_SAW_verify_prestate" W4.InternalPos
  liftIO $ W4.setCurrentProgramLoc sym prestateLoc

  let lvar = Crucible.llvmMemVar (cc^.ccLLVMContext)
  let Just mem = Crucible.lookupGlobal lvar globals

  -- Allocate LLVM memory for each 'crucible_alloc'
  (env1, mem') <- runStateT (traverse (doAlloc cc) tyenvRW) mem
  -- Allocate LLVM memory for each 'crucible_alloc_readonly'
  (env2, mem'') <- runStateT (traverse (doAllocConst cc) tyenvRO) mem'
  env3 <- Map.traverseWithKey
            (\k _ -> executeFreshPointer cc k)
            (mspec^.csPreState.csFreshPointers)
  let env = Map.unions [env1, env2, env3]

  mem''' <- setupPrePointsTos mspec cc env (mspec^.csPreState.csPointsTos) mem''
  let globals1 = Crucible.insertGlobal lvar mem''' globals
  (globals2,cs) <- setupPrestateConditions mspec cc env globals1 (mspec^.csPreState.csConditions)
  args <- resolveArguments cc mspec env

  -- Check the type of the return setup value
  case (mspec^.csRetValue, mspec^.csRet) of
    (Just _, Nothing) ->
         fail $ unlines
           [ "Could not resolve return type of " ++ mspec^.csName
           , "Raw type: " ++ show (mspec^.csRet)
           ]
    (Just sv, Just retTy) ->
      do retTy' <- typeOfSetupValue cc tyenv nameEnv sv
         b <- liftIO $ checkRegisterCompatibility retTy retTy'
         unless b $ fail $ unlines
           [ "Incompatible types for return value when verifying " ++ mspec^.csName
           , "Expected: " ++ show retTy
           , "but given value of type: " ++ show retTy'
           ]
    (Nothing, _) -> return ()

  return (args, cs, env, globals2)

-- | Check two MemTypes for register compatiblity.  This is a stricter
--   check than the memory compatiblity check that is done for points-to
--   assertions.
checkRegisterCompatibility ::
  (Crucible.HasPtrWidth wptr) =>
  Crucible.MemType ->
  Crucible.MemType ->
  IO Bool
checkRegisterCompatibility mt mt' =
  do st  <- Crucible.toStorableType mt
     st' <- Crucible.toStorableType mt'
     return (st == st')

resolveArguments ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  CrucibleContext arch       ->
  CrucibleMethodSpecIR       ->
  Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)) ->
  IO [(Crucible.MemType, LLVMVal)]
resolveArguments cc mspec env = mapM resolveArg [0..(nArgs-1)]
  where
    nArgs = toInteger (length (mspec^.csArgs))
    tyenv = csAllocations mspec
    nameEnv = mspec^.csPreState.csVarTypeNames
    nm = mspec^.csName

    checkArgTy i mt mt' =
      do b <- checkRegisterCompatibility mt mt'
         unless b $
           fail $ unlines [ "Type mismatch in argument " ++ show i ++ " when veriyfing " ++ show nm
                          , "Argument is declared with type: " ++ show mt
                          , "but provided argument has incompatible type: " ++ show mt'
                          , "Note: this may be because the signature of your " ++
                            "function changed during compilation. If using " ++
                            "Clang, check the signature in the disassembled " ++
                            ".ll file."
                          ]
    resolveArg i =
      case Map.lookup i (mspec^.csArgBindings) of
        Just (mt, sv) -> do
          mt' <- typeOfSetupValue cc tyenv nameEnv sv
          checkArgTy i mt mt'
          v <- resolveSetupVal cc env tyenv nameEnv sv
          return (mt, v)
        Nothing -> fail $ unwords ["Argument", show i, "unspecified when verifying", show nm]

--------------------------------------------------------------------------------

-- | For each points-to constraint in the pre-state section of the
-- function spec, write the given value to the address of the given
-- pointer.
setupPrePointsTos ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  CrucibleMethodSpecIR       ->
  CrucibleContext arch       ->
  Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)) ->
  [PointsTo]                 ->
  MemImpl                    ->
  IO MemImpl
setupPrePointsTos mspec cc env pts mem0 = foldM go mem0 pts
  where
    tyenv   = csAllocations mspec
    nameEnv = mspec^.csPreState.csVarTypeNames

    go :: MemImpl -> PointsTo -> IO MemImpl
    go mem (PointsTo _loc ptr val) =
      do val' <- resolveSetupVal cc env tyenv nameEnv val
         ptr' <- resolveSetupVal cc env tyenv nameEnv ptr
         ptr'' <- case ptr' of
           Crucible.LLVMValInt blk off
             | Just Refl <- testEquality (W4.bvWidth off) Crucible.PtrWidth
             -> return (Crucible.LLVMPointer blk off)
           _ -> fail "Non-pointer value found in points-to assertion"
         -- In case the types are different (from crucible_points_to_untyped)
         -- then the store type should be determined by the rhs.
         memTy <- typeOfSetupValue cc tyenv nameEnv val
         storTy <- Crucible.toStorableType memTy
         let alignment = Crucible.noAlignment -- default to byte-aligned (FIXME)
         let sym = cc^.ccBackend
         mem' <- Crucible.storeConstRaw sym mem ptr'' storTy alignment val'
         return mem'

-- | Sets up globals (ghost variable), and collects boolean terms
-- that should be assumed to be true.
setupPrestateConditions ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  CrucibleMethodSpecIR        ->
  CrucibleContext arch        ->
  Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)) ->
  Crucible.SymGlobalState Sym ->
  [SetupCondition]            ->
  IO (Crucible.SymGlobalState Sym, [Crucible.LabeledPred Term Crucible.AssumptionReason])
setupPrestateConditions mspec cc env = aux []
  where
    tyenv   = csAllocations mspec
    nameEnv = mspec^.csPreState.csVarTypeNames

    aux acc globals [] = return (globals, acc)

    aux acc globals (SetupCond_Equal loc val1 val2 : xs) =
      do val1' <- resolveSetupVal cc env tyenv nameEnv val1
         val2' <- resolveSetupVal cc env tyenv nameEnv val2
         t     <- assertEqualVals cc val1' val2'
         let lp = Crucible.LabeledPred t (Crucible.AssumptionReason loc "equality precondition")
         aux (lp:acc) globals xs

    aux acc globals (SetupCond_Pred loc tm : xs) =
      let lp = Crucible.LabeledPred (ttTerm tm) (Crucible.AssumptionReason loc "precondition") in
      aux (lp:acc) globals xs

    aux acc globals (SetupCond_Ghost _loc var val : xs) =
      aux acc (Crucible.insertGlobal var val globals) xs

--------------------------------------------------------------------------------

-- | Create a SAWCore formula asserting that two 'LLVMVal's are equal.
assertEqualVals ::
  CrucibleContext arch ->
  LLVMVal ->
  LLVMVal ->
  IO Term
assertEqualVals cc v1 v2 =
  CrucibleSAW.toSC (cc^.ccBackend) =<< equalValsPred cc v1 v2

--------------------------------------------------------------------------------

-- | Allocate space on the LLVM heap to store a value of the given
-- type. Returns the pointer to the allocated memory.
doAlloc ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  CrucibleContext arch       ->
  (W4.ProgramLoc, Crucible.MemType) ->
  StateT MemImpl IO (LLVMPtr (Crucible.ArchWidth arch))
doAlloc cc (_loc,tp) = StateT $ \mem ->
  do let sym = cc^.ccBackend
     let dl = Crucible.llvmDataLayout ?lc
     sz <- W4.bvLit sym Crucible.PtrWidth (Crucible.bytesToInteger (Crucible.memTypeSize dl tp))
     let alignment = Crucible.maxAlignment dl -- Use the maximum alignment required for any primitive type (FIXME?)
     Crucible.mallocRaw sym mem sz alignment

-- | Allocate read-only space on the LLVM heap to store a value of the
-- given type. Returns the pointer to the allocated memory.
doAllocConst ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  CrucibleContext arch       ->
  (W4.ProgramLoc, Crucible.MemType) ->
  StateT MemImpl IO (LLVMPtr (Crucible.ArchWidth arch))
doAllocConst cc (_loc,tp) = StateT $ \mem ->
  do let sym = cc^.ccBackend
     let dl = Crucible.llvmDataLayout ?lc
     sz <- W4.bvLit sym Crucible.PtrWidth (Crucible.bytesToInteger (Crucible.memTypeSize dl tp))
     let alignment = Crucible.maxAlignment dl -- Use the maximum alignment required for any primitive type (FIXME?)
     Crucible.mallocConstRaw sym mem sz alignment

--------------------------------------------------------------------------------

ppGlobalPair :: CrucibleContext arch
             -> Crucible.GlobalPair Sym a
             -> Doc
ppGlobalPair cc gp =
  let mvar = Crucible.llvmMemVar (cc^.ccLLVMContext)
      globals = gp ^. Crucible.gpGlobals in
  case Crucible.lookupGlobal mvar globals of
    Nothing -> text "LLVM Memory global variable not initialized"
    Just mem -> Crucible.ppMem mem


--------------------------------------------------------------------------------

registerOverride ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth wptr, wptr ~ Crucible.ArchWidth arch) =>
  Options                    ->
  CrucibleContext arch       ->
  Crucible.SimContext (CrucibleSAW.SAWCruciblePersonality Sym) Sym (Crucible.LLVM arch) ->
  W4.ProgramLoc              ->
  [CrucibleMethodSpecIR]     ->
  Crucible.OverrideSim (CrucibleSAW.SAWCruciblePersonality Sym) Sym (Crucible.LLVM arch) rtp args ret ()
registerOverride opts cc _ctx top_loc cs = do
  let sym = cc^.ccBackend
  sc <- CrucibleSAW.saw_ctx <$> liftIO (readIORef (W4.sbStateManager sym))
  let fsym = (head cs)^.csName
      llvmctx = cc^.ccLLVMContext
  liftIO $
    printOutLn opts Info $ "Registering override for `" ++ fsym ++ "`"
  case Map.lookup (L.Symbol fsym) (llvmctx ^. Crucible.symbolMap) of
    -- LLVMHandleInfo constructor has two existential type arguments,
    -- which are bound here. h :: FnHandle args' ret'
    Just (Crucible.LLVMHandleInfo _decl' h) -> do
      -- TODO: check that decl' matches (csDefine cs)
      let retType = Crucible.handleReturnType h
      Crucible.bindFnHandle h
        $ Crucible.UseOverride
        $ Crucible.mkOverride'
            (Crucible.handleName h)
            retType
            (methodSpecHandler opts sc cc top_loc cs retType)
    Nothing -> fail $ "Can't find declaration for `" ++ fsym ++ "`."

registerInvariantOverride
  :: (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch))
  => Options
  -> CrucibleContext arch
  -> W4.ProgramLoc
  -> HashMap Crucible.SomeHandle [Crucible.BreakpointName]
  -> [CrucibleMethodSpecIR]
  -> IO (Crucible.ExecutionFeature (CrucibleSAW.SAWCruciblePersonality Sym) Sym (Crucible.LLVM arch) rtp)
registerInvariantOverride opts cc top_loc all_breakpoints cs = do
  sc <- CrucibleSAW.saw_ctx <$>
    (liftIO $ readIORef $ W4.sbStateManager $ cc^.ccBackend)
  let name = (head cs) ^. csName
  parent <- case nubOrd $ map (view csParentName) cs of
    [Just unique_parent] -> return unique_parent
    _ -> fail $ "Multiple parent functions for breakpoint: " ++ name
  liftIO $ printOutLn opts Info $ "Registering breakpoint `" ++ name ++ "`"
  withBreakpointCfgAndBlockId cc name parent $ \cfg breakpoint_block_id -> do
    let breakpoint_name = Crucible.BreakpointName $ Text.pack name
    let arg_types = Crucible.blockInputs $
          Crucible.getBlock breakpoint_block_id $
          Crucible.cfgBlockMap cfg
    let ret_type = Crucible.handleReturnType $ Crucible.cfgHandle cfg
    Crucible.breakAndReturn
      cfg
      breakpoint_name
      arg_types
      ret_type
      (methodSpecHandler opts sc cc top_loc cs ret_type)
      all_breakpoints

--------------------------------------------------------------------------------

withCfg
  :: (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch))
  => CrucibleContext arch
  -> String
  -> (forall blocks init ret . Crucible.CFG (Crucible.LLVM arch) blocks init ret -> IO a)
  -> IO a
withCfg context name k = do
  let function_id = L.Symbol name
  case Map.lookup function_id (Crucible.cfgMap (context^.ccLLVMModuleTrans)) of
    Just (Crucible.AnyCFG cfg) -> k cfg
    Nothing -> fail $ "Unexpected function name: " ++ name

withCfgAndBlockId
  :: (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch))
  => CrucibleContext arch
  -> CrucibleMethodSpecIR
  -> (forall blocks init args ret . Crucible.CFG (Crucible.LLVM arch) blocks init ret -> Crucible.BlockID blocks args -> IO a)
  -> IO a
withCfgAndBlockId context method_spec k = case method_spec ^. csParentName of
  Nothing -> withCfg context (method_spec ^. csName) $ \cfg ->
    k cfg (Crucible.cfgEntryBlockID cfg)
  Just parent -> withBreakpointCfgAndBlockId
    context
    (method_spec ^. csName)
    parent
    k

withBreakpointCfgAndBlockId
  :: (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch))
  => CrucibleContext arch
  -> String
  -> String
  -> (forall blocks init args ret . Crucible.CFG (Crucible.LLVM arch) blocks init ret -> Crucible.BlockID blocks args -> IO a)
  -> IO a
withBreakpointCfgAndBlockId context name parent k = do
  let breakpoint_name = Crucible.BreakpointName $ Text.pack name
  withCfg context parent $ \cfg ->
    case Bimap.lookup breakpoint_name (Crucible.cfgBreakpoints cfg) of
      Just (Some breakpoint_block_id) -> k cfg breakpoint_block_id
      Nothing -> fail $ "Unexpected breakpoint name: " ++ name

verifySimulate ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth wptr, wptr ~ Crucible.ArchWidth arch) =>
  Options                       ->
  CrucibleContext arch          ->
  CrucibleMethodSpecIR          ->
  [(Crucible.MemType, LLVMVal)] ->
  [Crucible.LabeledPred Term Crucible.AssumptionReason] ->
  W4.ProgramLoc                 ->
  [CrucibleMethodSpecIR]        ->
  Crucible.SymGlobalState Sym   ->
  Bool                          ->
  IO (Maybe (Crucible.MemType, LLVMVal), Crucible.SymGlobalState Sym)
verifySimulate opts cc mspec args assumes top_loc lemmas globals checkSat =
  withCfgAndBlockId cc mspec $ \cfg entryId -> do
    let argTys = Crucible.blockInputs $
          Crucible.getBlock entryId $ Crucible.cfgBlockMap cfg
    let retTy = Crucible.handleReturnType $ Crucible.cfgHandle cfg

    args' <- prepareArgs argTys (map snd args)
    let simCtx = cc^.ccLLVMSimContext
    psatf <- Crucible.pathSatisfiabilityFeature sym
               (CrucibleSAW.considerSatisfiability sym)
    let patSatGenExecFeature = if checkSat then [psatf] else []
    let (funcLemmas, invLemmas) = partition
          (isNothing . view csParentName)
          lemmas

    breakpoints <- forM (groupOn (view csParentName) invLemmas) $ \specs -> do
      let parent = fromJust $ (head group) ^. csParentName
      let breakpoint_names = nubOrd $
            map (Crucible.BreakpointName . Text.pack . view csName) specs
      withCfg cc parent $ \parent_cfg ->
        return
          ( Crucible.SomeHandle (Crucible.cfgHandle parent_cfg)
          , breakpoint_names
          )

    invariantExecFeatures <- mapM
      (registerInvariantOverride opts cc top_loc (HashMap.fromList breakpoints))
      (groupOn (view csName) invLemmas)
    let execFeatures = invariantExecFeatures ++
          (map Crucible.genericToExecutionFeature patSatGenExecFeature)

    let initExecState =
          Crucible.InitialState simCtx globals Crucible.defaultAbortHandler $
          Crucible.runOverrideSim retTy $
          do mapM_ (registerOverride opts cc simCtx top_loc)
                   (groupOn (view csName) funcLemmas)
             liftIO $ do
               preds <- (traverse . Crucible.labeledPred) (resolveSAWPred cc) assumes
               Crucible.addAssumptions sym (Seq.fromList preds)
             Crucible.regValue <$> (Crucible.callBlock cfg entryId args')
    res <- Crucible.executeCrucible execFeatures initExecState
    case res of
      Crucible.FinishedResult _ pr ->
        do Crucible.GlobalPair retval globals1 <-
             case pr of
               Crucible.TotalRes gp -> return gp
               Crucible.PartialRes _ gp _ ->
                 do printOutLn opts Info "Symbolic simulation completed with side conditions."
                    return gp
           let ret_ty = mspec^.csRet
           retval' <- case ret_ty of
             Nothing -> return Nothing
             Just ret_mt ->
               do v <- Crucible.packMemValue sym
                         (fromMaybe (error ("Expected storable type:" ++ show ret_ty))
                              (Crucible.toStorableType ret_mt))
                         (Crucible.regType  retval)
                         (Crucible.regValue retval)
                  return (Just (ret_mt, v))
           return (retval', globals1)

      Crucible.TimeoutResult _ -> fail $ "Symbolic execution timed out"

      Crucible.AbortedResult _ ar ->
        do let resultDoc = ppAbortedResult cc ar
           fail $ unlines [ "Symbolic execution failed."
                          , show resultDoc
                          ]

  where
    sym = cc^.ccBackend
    prepareArgs ::
      Ctx.Assignment Crucible.TypeRepr xs ->
      [LLVMVal] ->
      IO (Crucible.RegMap Sym xs)
    prepareArgs ctx x =
      Crucible.RegMap <$>
      Ctx.traverseWithIndex (\idx tr ->
        do v <- Crucible.unpackMemValue sym tr (x !! Ctx.indexVal idx)
           return (Crucible.RegEntry tr v))
      ctx

-- | Build a conjunction from a list of boolean terms.
scAndList :: SharedContext -> [Term] -> IO Term
scAndList sc []       = scBool sc True
scAndList sc (x : xs) = foldM (scAnd sc) x xs

--------------------------------------------------------------------------------

verifyPoststate ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth wptr, wptr ~ Crucible.ArchWidth arch) =>
  Options                           {- ^ saw script debug and print options           -} ->
  SharedContext                     {- ^ saw core context                             -} ->
  CrucibleContext arch              {- ^ crucible context                             -} ->
  CrucibleMethodSpecIR              {- ^ specification                                -} ->
  Map AllocIndex (LLVMPtr wptr)     {- ^ allocation substitution                      -} ->
  Crucible.SymGlobalState Sym       {- ^ global variables                             -} ->
  Maybe (Crucible.MemType, LLVMVal) {- ^ optional return value                        -} ->
  TopLevel [(String, Term)]         {- ^ generated labels and verification conditions -}
verifyPoststate opts sc cc mspec env0 globals ret =
  do poststateLoc <- toW4Loc "_SAW_verify_poststate" <$> getPosition
     io $ W4.setCurrentProgramLoc sym poststateLoc

     let terms0 = Map.fromList
           [ (ecVarIndex ec, ttTerm tt)
           | tt <- mspec^.csPreState.csFreshVars
           , let Just ec = asExtCns (ttTerm tt) ]

     let initialFree = Set.fromList (map (termId . ttTerm)
                                    (view (csPostState.csFreshVars) mspec))
     matchPost <- io $
          runOverrideMatcher sym globals env0 terms0 initialFree poststateLoc $
           do matchResult
              learnCond opts sc cc mspec PostState (mspec ^. csPostState)

     st <- case matchPost of
             Left err      -> fail (show err)
             Right (_, st) -> return st
     io $ for_ (view osAsserts st) $ \(p, r) ->
       Crucible.addAssertion sym (Crucible.LabeledPred p r)

     obligations <- io $ Crucible.getProofObligations sym
     io $ Crucible.clearProofObligations sym
     io $ mapM verifyObligation (Crucible.proofGoalsToList obligations)

  where
    sym = cc^.ccBackend

    verifyObligation (Crucible.ProofGoal hyps (Crucible.LabeledPred concl (Crucible.SimError _loc err))) = do
      hypTerm <- CrucibleSAW.toSC sym =<< W4.andAllOf sym (folded . Crucible.labeledPred) hyps
      conclTerm  <- CrucibleSAW.toSC sym concl
      obligation <- scImplies sc hypTerm conclTerm
      return ("safety assertion: " ++ Crucible.simErrorReasonMsg err, obligation)

    matchResult =
      case (ret, mspec ^. csRetValue) of
        (Just (rty,r), Just expect) -> matchArg sc cc (mspec^.csLoc) PostState r rty expect
        (Nothing     , Just _ )     -> fail "verifyPoststate: unexpected crucible_return specification"
        _ -> return ()

--------------------------------------------------------------------------------

setupCrucibleContext ::
   BuiltinContext -> Options -> LLVMModule ->
   (forall arch. (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) => CrucibleContext arch -> TopLevel a) ->
   TopLevel a
setupCrucibleContext bic opts (LLVMModule _ llvm_mod (Some mtrans)) action = do
  halloc <- getHandleAlloc
  let ctx = mtrans^.Crucible.transContext
  Crucible.llvmPtrWidth ctx $ \wptr -> Crucible.withPtrWidth wptr $
    let ?lc = ctx^.Crucible.llvmTypeCtx in
    action =<< (io $ do
      let gen = globalNonceGenerator
      let sc  = biSharedContext bic
      let verbosity = simVerbose opts
      sym <- CrucibleSAW.newSAWCoreBackend sc gen

      let cfg = W4.getConfiguration sym
      verbSetting <- W4.getOptionSetting W4.verbosity cfg
      _ <- W4.setOpt verbSetting (toInteger verbosity)

      let bindings = Crucible.fnBindingsFromList []
      let simctx   = Crucible.initSimContext sym intrinsics halloc stdout
                        bindings Crucible.llvmExtensionImpl CrucibleSAW.SAWCruciblePersonality
      mem <- Crucible.populateConstGlobals sym (Crucible.globalInitMap mtrans)
               =<< Crucible.initializeMemory sym ctx llvm_mod

      let globals  = Crucible.llvmGlobals ctx mem

      let setupMem = do
             -- register the callable override functions
             _llvmctx' <- Crucible.register_llvm_overrides llvm_mod ctx

             -- register all the functions defined in the LLVM module
             mapM_ Crucible.registerModuleFn $ Map.toList $ Crucible.cfgMap mtrans

      let initExecState =
            Crucible.InitialState simctx globals Crucible.defaultAbortHandler $
            Crucible.runOverrideSim Crucible.UnitRepr setupMem
      res <- Crucible.executeCrucible [] initExecState
      (lglobals, lsimctx) <-
          case res of
            Crucible.FinishedResult st (Crucible.TotalRes gp) -> return (gp^.Crucible.gpGlobals, st)
            Crucible.FinishedResult st (Crucible.PartialRes _ gp _) -> return (gp^.Crucible.gpGlobals, st)
            _ -> fail "simulator initialization failed!"

      return
         CrucibleContext{ _ccLLVMModuleTrans = mtrans
                        , _ccLLVMModule = llvm_mod
                        , _ccBackend = sym
                        , _ccLLVMEmptyMem = mem
                        , _ccLLVMSimContext = lsimctx
                        , _ccLLVMGlobals = lglobals
                        }
      )


--------------------------------------------------------------------------------

setupArg :: SharedContext
         -> Sym
         -> IORef (Seq (ExtCns Term))
         -> Crucible.TypeRepr tp
         -> IO (Crucible.RegEntry Sym tp)
setupArg sc sym ecRef tp =
  case Crucible.asBaseType tp of
    Crucible.AsBaseType btp -> do
       sc_tp <- CrucibleSAW.baseSCType sym sc btp
       i     <- scFreshGlobalVar sc
       ecs   <- readIORef ecRef
       let len = Seq.length ecs
       let ec = EC i ("arg_"++show len) sc_tp
       writeIORef ecRef (ecs Seq.|> ec)
       t     <- scFlatTermF sc (ExtCns ec)
       elt   <- CrucibleSAW.bindSAWTerm sym btp t
       return (Crucible.RegEntry tp elt)

    Crucible.NotBaseType ->
      fail $ unwords ["Crucible extraction currently only supports Crucible base types", show tp]

setupArgs :: SharedContext
          -> Sym
          -> Crucible.FnHandle init ret
          -> IO (Seq (ExtCns Term), Crucible.RegMap Sym init)
setupArgs sc sym fn = do
  ecRef  <- newIORef Seq.empty
  regmap <- Crucible.RegMap <$> Ctx.traverseFC (setupArg sc sym ecRef) (Crucible.handleArgTypes fn)
  ecs    <- readIORef ecRef
  return (ecs, regmap)

--------------------------------------------------------------------------------

getGlobalPair ::
  Options ->
  Crucible.PartialResult sym ext v ->
  IO (Crucible.GlobalPair sym v)
getGlobalPair opts pr =
  case pr of
    Crucible.TotalRes gp -> return gp
    Crucible.PartialRes _ gp _ -> do
      printOutLn opts Info "Symbolic simulation completed with side conditions."
      return gp

runCFG ::
  (Crucible.IsSyntaxExtension ext, Crucible.IsSymInterface sym) =>
  Crucible.SimContext p sym ext ->
  Crucible.SymGlobalState sym ->
  Crucible.FnHandle args a ->
  Crucible.CFG ext blocks init a ->
  Crucible.RegMap sym init ->
  IO (Crucible.ExecResult p sym ext (Crucible.RegEntry sym a))
runCFG simCtx globals h cfg args = do
  let initExecState =
        Crucible.InitialState simCtx globals Crucible.defaultAbortHandler $
        Crucible.runOverrideSim (Crucible.handleReturnType h)
                 (Crucible.regValue <$> (Crucible.callCFG cfg args))
  Crucible.executeCrucible [] initExecState


extractFromLLVMCFG :: Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
   Options -> SharedContext -> CrucibleContext arch -> Crucible.AnyCFG (Crucible.LLVM arch) -> IO TypedTerm
extractFromLLVMCFG opts sc cc (Crucible.AnyCFG cfg) =
  do  let sym = cc^.ccBackend
      let h   = Crucible.cfgHandle cfg
      (ecs, args) <- setupArgs sc sym h
      let simCtx  = cc^.ccLLVMSimContext
      let globals = cc^.ccLLVMGlobals
      res  <- runCFG simCtx globals h cfg args
      case res of
        Crucible.FinishedResult _ pr -> do
            gp <- getGlobalPair opts pr
            t <- Crucible.asSymExpr
                   (gp^.Crucible.gpValue)
                   (CrucibleSAW.toSC sym)
                   (fail $ unwords ["Unexpected return type:", show (Crucible.regType (gp^.Crucible.gpValue))])
            t' <- scAbstractExts sc (toList ecs) t
            mkTypedTerm sc t'
        Crucible.AbortedResult _ ar -> do
          let resultDoc = ppAbortedResult cc ar
          fail $ unlines [ "Symbolic execution failed."
                         , show resultDoc
                         ]

        Crucible.TimeoutResult _ ->
          fail "Symbolic execution timed out."

--------------------------------------------------------------------------------

crucible_llvm_extract :: BuiltinContext -> Options -> LLVMModule -> String -> TopLevel TypedTerm
crucible_llvm_extract bic opts lm fn_name =
  setupCrucibleContext bic opts lm $ \cc ->
    case Map.lookup (fromString fn_name) (Crucible.cfgMap (cc^.ccLLVMModuleTrans)) of
      Nothing  -> fail $ unwords ["function", fn_name, "not found"]
      Just cfg -> io $ extractFromLLVMCFG opts (biSharedContext bic) cc cfg

crucible_llvm_cfg :: BuiltinContext -> Options -> LLVMModule -> String -> TopLevel SAW_CFG
crucible_llvm_cfg bic opts lm fn_name =
  setupCrucibleContext bic opts lm $ \cc ->
    case Map.lookup (fromString fn_name) (Crucible.cfgMap (cc^.ccLLVMModuleTrans)) of
      Nothing  -> fail $ unwords ["function", fn_name, "not found"]
      Just cfg -> return (LLVM_CFG cfg)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

diffMemTypes ::
  Crucible.HasPtrWidth wptr =>
  Crucible.MemType ->
  Crucible.MemType ->
  [([Maybe Int], Crucible.MemType, Crucible.MemType)]
diffMemTypes x0 y0 =
  let wptr :: Natural = fromIntegral (natValue ?ptrWidth) in
  case (x0, y0) of
    -- Special case; consider a one-element struct to be compatible with
    -- the type of its field
    (Crucible.StructType x, _)
      | V.length (Crucible.siFields x) == 1 -> diffMemTypes (Crucible.fiType (V.head (Crucible.siFields x))) y0
    (_, Crucible.StructType y)
      | V.length (Crucible.siFields y) == 1 -> diffMemTypes x0 (Crucible.fiType (V.head (Crucible.siFields y)))

    (Crucible.IntType x, Crucible.IntType y) | x == y -> []
    (Crucible.FloatType, Crucible.FloatType) -> []
    (Crucible.DoubleType, Crucible.DoubleType) -> []
    (Crucible.PtrType{}, Crucible.PtrType{}) -> []
    (Crucible.IntType w, Crucible.PtrType{}) | w == wptr -> []
    (Crucible.PtrType{}, Crucible.IntType w) | w == wptr -> []
    (Crucible.ArrayType xn xt, Crucible.ArrayType yn yt)
      | xn == yn ->
        [ (Nothing : path, l , r) | (path, l, r) <- diffMemTypes xt yt ]
    (Crucible.VecType xn xt, Crucible.VecType yn yt)
      | xn == yn ->
        [ (Nothing : path, l , r) | (path, l, r) <- diffMemTypes xt yt ]
    (Crucible.StructType x, Crucible.StructType y)
      | V.map Crucible.fiOffset (Crucible.siFields x) ==
        V.map Crucible.fiOffset (Crucible.siFields y) ->
          let xts = Crucible.siFieldTypes x
              yts = Crucible.siFieldTypes y
          in diffMemTypesList 1 (V.toList (V.zip xts yts))
    _ -> [([], x0, y0)]

diffMemTypesList ::
  Crucible.HasPtrWidth arch =>
  Int ->
  [(Crucible.MemType, Crucible.MemType)] ->
  [([Maybe Int], Crucible.MemType, Crucible.MemType)]
diffMemTypesList _ [] = []
diffMemTypesList i ((x, y) : ts) =
  [ (Just i : path, l , r) | (path, l, r) <- diffMemTypes x y ]
  ++ diffMemTypesList (i+1) ts

showMemTypeDiff :: ([Maybe Int], Crucible.MemType, Crucible.MemType) -> String
showMemTypeDiff (path, l, r) = showPath path
  where
    showStep Nothing  = "element type"
    showStep (Just i) = "field " ++ show i
    showPath []       = ""
    showPath [x]      = unlines [showStep x ++ ":", "  " ++ show l, "  " ++ show r]
    showPath (x : xs) = showStep x ++ " -> " ++ showPath xs

-- | Succeed if the types have compatible memory layouts. Otherwise,
-- fail with a detailed message indicating how the types differ.
checkMemTypeCompatibility ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  Crucible.MemType ->
  Crucible.MemType ->
  CrucibleSetup arch ()
checkMemTypeCompatibility t1 t2 =
  case diffMemTypes t1 t2 of
    [] -> return ()
    diffs ->
      fail $ unlines $
      ["types not memory-compatible:", show t1, show t2]
      ++ map showMemTypeDiff diffs

--------------------------------------------------------------------------------
-- Setup builtins

getCrucibleContext :: CrucibleSetup arch (CrucibleContext arch)
getCrucibleContext = view csCrucibleContext <$> get

currentState :: Lens' (CrucibleSetupState arch) StateSpec
currentState f x = case x^.csPrePost of
  PreState  -> csMethodSpec (csPreState f) x
  PostState -> csMethodSpec (csPostState f) x

addPointsTo :: PointsTo -> CrucibleSetup arch ()
addPointsTo pt = currentState.csPointsTos %= (pt : )

addCondition :: SetupCondition
             -> CrucibleSetup arch ()
addCondition cond = currentState.csConditions %= (cond : )

-- | Returns logical type of actual type if it is an array or primitive
-- type, or an appropriately-sized bit vector for pointer types.
logicTypeOfActual :: Crucible.DataLayout -> SharedContext -> Crucible.MemType
                  -> IO (Maybe Term)
logicTypeOfActual _ sc (Crucible.IntType w) = Just <$> logicTypeForInt sc w
logicTypeOfActual _ sc Crucible.FloatType = Just <$> scApplyPrelude_Float sc
logicTypeOfActual _ sc Crucible.DoubleType = Just <$> scApplyPrelude_Double sc
logicTypeOfActual dl sc (Crucible.ArrayType n ty) = do
  melTyp <- logicTypeOfActual dl sc ty
  case melTyp of
    Just elTyp -> do
      lTm <- scNat sc (fromIntegral n)
      Just <$> scVecType sc lTm elTyp
    Nothing -> return Nothing
logicTypeOfActual dl sc (Crucible.PtrType _) = do
  bType <- scBoolType sc
  lTm <- scNat sc (fromIntegral (Crucible.ptrBitwidth dl))
  Just <$> scVecType sc lTm bType
logicTypeOfActual dl sc (Crucible.StructType si) = do
  let memtypes = V.toList (Crucible.siFieldTypes si)
  melTyps <- traverse (logicTypeOfActual dl sc) memtypes
  case sequence melTyps of
    Just elTyps -> Just <$> scTupleType sc elTyps
    Nothing -> return Nothing
logicTypeOfActual _ _ t = fail (show t) -- return Nothing

logicTypeForInt :: SharedContext -> Natural -> IO Term
logicTypeForInt sc w =
  do bType <- scBoolType sc
     lTm <- scNat sc (fromIntegral w)
     scVecType sc lTm bType

-- | Generate a fresh variable term. The name will be used when
-- pretty-printing the variable in debug output.
crucible_fresh_var ::
  BuiltinContext          {- ^ context          -} ->
  Options                 {- ^ options          -} ->
  String                  {- ^ variable name    -} ->
  L.Type                  {- ^ variable type    -} ->
  CrucibleSetupM TypedTerm {- ^ fresh typed term -}
crucible_fresh_var bic _opts name lty = CrucibleSetupM $ do
  lty' <- memTypeForLLVMType bic lty
  cctx <- getCrucibleContext
  let sc = biSharedContext bic
  let dl = Crucible.llvmDataLayout (cctx^.ccTypeCtx)
  mty <- liftIO $ logicTypeOfActual dl sc lty'
  case mty of
    Nothing -> fail $ "Unsupported type in crucible_fresh_var: " ++ show (L.ppType lty)
    Just ty -> freshVariable sc name ty

-- | Allocated a fresh variable and record this allocation in the
-- setup state.
freshVariable ::
  SharedContext {- ^ shared context -} ->
  String        {- ^ variable name  -} ->
  Term          {- ^ variable type  -} ->
  CrucibleSetup arch TypedTerm
freshVariable sc name ty =
  do tt <- liftIO (mkTypedTerm sc =<< scFreshGlobal sc name ty)
     currentState . csFreshVars %= cons tt
     return tt


-- | Use the given LLVM type to compute a setup value that
-- covers expands all of the struct, array, and pointer
-- components of the LLVM type. Only the primitive types
-- suitable for import as SAW core terms will be matched
-- against fresh variables.
crucible_fresh_expanded_val ::
  BuiltinContext {- ^ context                -} ->
  Options        {- ^ options                -} ->
  L.Type         {- ^ variable type          -} ->
  CrucibleSetupM SetupValue
                 {- ^ elaborated setup value -}
crucible_fresh_expanded_val bic _opts lty = CrucibleSetupM $
  do let sc = biSharedContext bic
     lty' <- memTypeForLLVMType bic lty
     loc <- toW4Loc "crucible_fresh_expanded_val" <$> lift getPosition
     constructExpandedSetupValue sc loc lty'


memTypeForLLVMType :: BuiltinContext -> L.Type -> CrucibleSetup arch Crucible.MemType
memTypeForLLVMType _bic lty =
  do case Crucible.liftMemType lty of
       Right m -> return m
       Left err -> fail $ unlines [ "unsupported type: " ++ show (L.ppType lty)
                                  , "Details:"
                                  , err
                                  ]

-- | See 'crucible_fresh_expanded_val'
--
-- This is the recursively-called worker function.
constructExpandedSetupValue ::
  (?lc::Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  SharedContext    {- ^ shared context             -} ->
  W4.ProgramLoc ->
  Crucible.MemType {- ^ LLVM mem type              -} ->
  CrucibleSetup arch SetupValue
                   {- ^ fresh expanded setup value -}
constructExpandedSetupValue sc loc t =
  case t of
    Crucible.IntType w ->
      do ty <- liftIO (logicTypeForInt sc w)
         SetupTerm <$> freshVariable sc "" ty

    Crucible.StructType si ->
       SetupStruct False {- FIXME: should this always be unpacked? -} . toList <$>
       traverse (constructExpandedSetupValue sc loc) (Crucible.siFieldTypes si)

    Crucible.PtrType symTy ->
      case Crucible.asMemType symTy of
        Right memTy -> constructFreshPointer (symTypeAlias symTy) loc memTy
        Left err -> fail $ unlines [ "lhs not a valid pointer type: " ++ show symTy
                                   , "Details:"
                                   , err
                                   ]

    Crucible.ArrayType n memTy ->
       SetupArray <$> replicateM (fromIntegral n) (constructExpandedSetupValue sc loc memTy)

    Crucible.FloatType      -> failUnsupportedType "Float"
    Crucible.DoubleType     -> failUnsupportedType "Double"
    Crucible.MetadataType   -> failUnsupportedType "Metadata"
    Crucible.VecType{}      -> failUnsupportedType "Vec"
    Crucible.X86_FP80Type{} -> failUnsupportedType "X86_FP80"
  where failUnsupportedType tyName = fail $ unwords
          ["crucible_fresh_expanded_var: " ++ tyName ++ " not supported"]

llvmTypeAlias :: L.Type -> Maybe Crucible.Ident
llvmTypeAlias (L.Alias i) = Just i
llvmTypeAlias _ = Nothing

symTypeAlias :: Crucible.SymType -> Maybe Crucible.Ident
symTypeAlias (Crucible.Alias i) = Just i
symTypeAlias _ = Nothing

crucible_alloc ::
  BuiltinContext ->
  Options        ->
  L.Type         ->
  CrucibleSetupM SetupValue
crucible_alloc _bic _opt lty = CrucibleSetupM $
  do let ?dl = Crucible.llvmDataLayout ?lc
     loc <- toW4Loc "crucible_alloc" <$> lift getPosition
     memTy <- case Crucible.liftMemType lty of
       Right s -> return s
       Left err -> fail $ unlines [ "unsupported type in crucible_alloc: " ++ show (L.ppType lty)
                                  , "Details:"
                                  , err
                                  ]
     n <- csVarCounter <<%= nextAllocIndex
     currentState.csAllocs.at n ?= (loc,memTy)
     -- TODO: refactor
     case llvmTypeAlias lty of
       Just i -> currentState.csVarTypeNames.at n ?= i
       Nothing -> return ()
     return (SetupVar n)

crucible_alloc_readonly ::
  BuiltinContext ->
  Options        ->
  L.Type         ->
  CrucibleSetupM SetupValue
crucible_alloc_readonly _bic _opt lty = CrucibleSetupM $
  do let ?dl = Crucible.llvmDataLayout ?lc
     loc <- toW4Loc "crucible_alloc_readonly" <$> lift getPosition
     memTy <- case Crucible.liftMemType lty of
       Right s -> return s
       Left err -> fail $ unlines [ "unsupported type in crucible_alloc: " ++ show (L.ppType lty)
                                  , "Details:"
                                  , err
                                  ]
     n <- csVarCounter <<%= nextAllocIndex
     currentState.csConstAllocs.at n ?= (loc,memTy)
     case llvmTypeAlias lty of
       Just i -> currentState.csVarTypeNames.at n ?= i
       Nothing -> return ()
     return (SetupVar n)

crucible_fresh_pointer ::
  BuiltinContext ->
  Options        ->
  L.Type         ->
  CrucibleSetupM SetupValue
crucible_fresh_pointer bic _opt lty = CrucibleSetupM $
  do memTy <- memTypeForLLVMType bic lty
     loc <- toW4Loc "crucible_fresh_pointer" <$> lift getPosition
     constructFreshPointer (llvmTypeAlias lty) loc memTy

constructFreshPointer :: Maybe Crucible.Ident -> W4.ProgramLoc -> Crucible.MemType -> CrucibleSetup arch SetupValue
constructFreshPointer mid loc memTy =
  do n <- csVarCounter <<%= nextAllocIndex
     currentState.csFreshPointers.at n ?= (loc,memTy)
     -- TODO: refactor
     case mid of
       Just i -> currentState.csVarTypeNames.at n ?= i
       Nothing -> return ()
     return (SetupVar n)

crucible_points_to ::
  Bool {- ^ whether to check type compatibility -} ->
  BuiltinContext ->
  Options        ->
  SetupValue     ->
  SetupValue     ->
  CrucibleSetupM ()
crucible_points_to typed _bic _opt ptr val = CrucibleSetupM $
  do cc <- getCrucibleContext
     loc <- toW4Loc "crucible_points_to" <$> lift getPosition
     Crucible.llvmPtrWidth (cc^.ccLLVMContext) $ \wptr -> Crucible.withPtrWidth wptr $
       do let ?lc = cc^.ccTypeCtx
          st <- get
          let rs = st^.csResolvedState
          if st^.csPrePost == PreState && testResolved ptr rs
            then fail "Multiple points-to preconditions on same pointer"
            else csResolvedState %= markResolved ptr
          let env = csAllocations (st^.csMethodSpec)
              nameEnv = csTypeNames (st^.csMethodSpec)
          ptrTy <- typeOfSetupValue cc env nameEnv ptr
          lhsTy <- case ptrTy of
            Crucible.PtrType symTy ->
              case Crucible.asMemType symTy of
                Right lhsTy -> return lhsTy
                Left err -> fail $ unlines [ "lhs not a valid pointer type: " ++ show ptrTy
                                            , "Details:"
                                            , err
                                            ]

            _ -> fail $ "lhs not a pointer type: " ++ show ptrTy
          valTy <- typeOfSetupValue cc env nameEnv val
          when typed (checkMemTypeCompatibility lhsTy valTy)
          addPointsTo (PointsTo loc ptr val)

toW4Loc :: Text.Text -> SS.Pos -> W4.ProgramLoc
toW4Loc fnm SS.Unknown          = W4.mkProgramLoc (W4.functionNameFromText fnm) W4.InternalPos
toW4Loc fnm SS.PosREPL          = W4.mkProgramLoc (W4.functionNameFromText (fnm <> " <REPL>")) W4.InternalPos
toW4Loc fnm (SS.PosInternal nm) = W4.mkProgramLoc (W4.functionNameFromText (fnm <> " " <> fromString nm)) W4.InternalPos
toW4Loc fnm (SS.Range file sl sc _el _ec) = W4.mkProgramLoc (W4.functionNameFromText fnm) (W4.SourcePos (fromString file) sl sc)

crucible_equal ::
  BuiltinContext ->
  Options        ->
  SetupValue     ->
  SetupValue     ->
  CrucibleSetupM ()
crucible_equal _bic _opt val1 val2 = CrucibleSetupM $
  do cc <- getCrucibleContext
     st <- get
     let env = csAllocations (st^.csMethodSpec)
         nameEnv = csTypeNames (st^.csMethodSpec)
     ty1 <- typeOfSetupValue cc env nameEnv val1
     ty2 <- typeOfSetupValue cc env nameEnv val2
     b <- liftIO $ checkRegisterCompatibility ty1 ty2
     unless b $ fail $ unlines
       [ "Incompatible types when asserting equality:"
       , show ty1
       , show ty2
       ]
     loc <- toW4Loc "crucible_equal" <$> lift getPosition
     addCondition (SetupCond_Equal loc val1 val2)

crucible_precond ::
  TypedTerm      ->
  CrucibleSetupM ()
crucible_precond p = CrucibleSetupM $ do
  st <- get
  when (st^.csPrePost == PostState) $
    fail "attempt to use `crucible_precond` in post state"
  loc <- toW4Loc "crucible_precond" <$> lift getPosition
  addCondition (SetupCond_Pred loc p)

crucible_postcond ::
  TypedTerm      ->
  CrucibleSetupM ()
crucible_postcond p = CrucibleSetupM $ do
  st <- get
  when (st^.csPrePost == PreState) $
    fail "attempt to use `crucible_postcond` in pre state"
  loc <- toW4Loc "crucible_postcond" <$> lift getPosition
  addCondition (SetupCond_Pred loc p)

crucible_execute_func :: BuiltinContext
                      -> Options
                      -> [SetupValue]
                      -> CrucibleSetupM ()
crucible_execute_func _bic _opt args = CrucibleSetupM $ do
  let ?dl   = Crucible.llvmDataLayout ?lc
  tps <- use (csMethodSpec.csArgs)
  csPrePost .= PostState
  csMethodSpec.csArgBindings .= Map.fromList [ (i, (t,a))
                                             | i <- [0..]
                                             | a <- args
                                             | t <- tps
                                             ]

crucible_return :: BuiltinContext
                -> Options
                -> SetupValue
                -> CrucibleSetupM ()
crucible_return _bic _opt retval = CrucibleSetupM $ do
  ret <- use (csMethodSpec.csRetValue)
  case ret of
    Just _ -> fail "crucible_return: duplicate return value specification"
    Nothing -> csMethodSpec.csRetValue .= Just retval


crucible_declare_ghost_state ::
  BuiltinContext ->
  Options        ->
  String         ->
  TopLevel Value
crucible_declare_ghost_state _bic _opt name =
  do allocator <- getHandleAlloc
     global <- liftIO (liftST (Crucible.freshGlobalVar allocator (Text.pack name) knownRepr))
     return (VGhostVar global)

crucible_ghost_value ::
  BuiltinContext                      ->
  Options                             ->
  GhostGlobal                         ->
  TypedTerm                           ->
  CrucibleSetupM ()
crucible_ghost_value _bic _opt ghost val = CrucibleSetupM $
  do loc <- toW4Loc "crucible_ghost_value" <$> lift getPosition
     addCondition (SetupCond_Ghost loc ghost val)

crucible_spec_solvers :: CrucibleMethodSpecIR -> [String]
crucible_spec_solvers = Set.toList . solverStatsSolvers . (view csSolverStats)

crucible_spec_size :: CrucibleMethodSpecIR -> Integer
crucible_spec_size = solverStatsGoalSize . (view csSolverStats)

crucible_setup_val_to_typed_term :: BuiltinContext -> Options -> SetupValue -> TopLevel TypedTerm
crucible_setup_val_to_typed_term bic _opt sval = do
  opts <- getOptions
  mtt <- io $ MaybeT.runMaybeT $ setupToTypedTerm opts (biSharedContext bic) sval
  case mtt of
    Nothing -> fail $ "Could not convert a setup value to a term: " ++ show sval
    Just tt -> return tt
