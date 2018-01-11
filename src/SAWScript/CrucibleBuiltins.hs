{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances, MultiParamTypeClasses#-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{- |
Module      : $Header$
Description : Implementations of Crucible-related SAW-Script primitives.
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}
module SAWScript.CrucibleBuiltins
    ( load_llvm_cfg
    , show_cfg
    , extract_crucible_llvm
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
    , crucible_fresh_expanded_val
    ) where

import           Control.Lens
import           Control.Monad.ST
import           Control.Monad.State
import qualified Control.Monad.Trans.State.Strict as SState
import           Control.Applicative
import           Data.Foldable (for_, toList, find)
import           Data.Function
import           Data.IORef
import           Data.List
import           Data.Maybe (fromMaybe)
import           Data.String
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import qualified Data.Vector as V
import           Numeric.Natural
import           System.IO

import qualified Text.LLVM.AST as L
import qualified Text.LLVM.PP as L (ppType, ppSymbol)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Control.Monad.Trans.Maybe as MaybeT

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Nonce as Crucible
import           Data.Parameterized.Some

import qualified Lang.Crucible.Config as Crucible
import qualified Lang.Crucible.CFG.Core as Crucible
  (AnyCFG(..), SomeCFG(..), TypeRepr(..), cfgHandle,
   asBaseType, AsBaseType(..), freshGlobalVar)
import qualified Lang.Crucible.FunctionHandle as Crucible
import qualified Lang.Crucible.Simulator.ExecutionTree as Crucible
import qualified Lang.Crucible.Simulator.GlobalState as Crucible
import qualified Lang.Crucible.Simulator.OverrideSim as Crucible
import qualified Lang.Crucible.Simulator.RegMap as Crucible
import qualified Lang.Crucible.Simulator.SimError as Crucible
import qualified Lang.Crucible.Solver.Interface as Crucible hiding (mkStruct)
import qualified Lang.Crucible.Solver.SAWCoreBackend as Crucible
import qualified Lang.Crucible.Solver.SimpleBuilder as Crucible

import qualified Lang.Crucible.LLVM as Crucible
import qualified Lang.Crucible.LLVM.Bytes as Crucible
import qualified Lang.Crucible.LLVM.DataLayout as Crucible
import qualified Lang.Crucible.LLVM.Extension as Crucible
import qualified Lang.Crucible.LLVM.Intrinsics as Crucible
import qualified Lang.Crucible.LLVM.MemType as Crucible
import qualified Lang.Crucible.LLVM.LLVMContext as TyCtx
import qualified Lang.Crucible.LLVM.Translation as Crucible
import qualified Lang.Crucible.LLVM.MemModel as Crucible
import qualified Lang.Crucible.LLVM.MemModel.Pointer as Crucible

import Lang.Crucible.Utils.MonadST
import qualified Data.Parameterized.TraversableFC as Ctx
import qualified Data.Parameterized.Context as Ctx

import Verifier.SAW.Prelude
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST
import Verifier.SAW.Recognizer

import SAWScript.Builtins
import SAWScript.Options
import SAWScript.Proof
import SAWScript.SolverStats
import SAWScript.TypedTerm
import SAWScript.TopLevel
import SAWScript.Value

import SAWScript.CrucibleMethodSpecIR
import SAWScript.CrucibleOverride
import SAWScript.CrucibleResolveSetupValue


type MemImpl = Crucible.MemImpl Sym

show_cfg :: LLVM_CFG -> String
show_cfg (LLVM_CFG (Crucible.AnyCFG cfg)) = show cfg

ppAbortedResult :: CrucibleContext arch
                -> Crucible.AbortedResult Sym (Crucible.LLVM arch)
                -> Doc
ppAbortedResult cc (Crucible.AbortedExec err gp) = do
  Crucible.ppSimError err <$$> ppGlobalPair cc gp
ppAbortedResult _ (Crucible.AbortedBranch _ _ _) =
  text "Aborted branch"
ppAbortedResult _ Crucible.AbortedInfeasible =
  text "Infeasible branch"
ppAbortedResult _ (Crucible.AbortedExit ec) =
  text "Branch exited:" <+> text (show ec)

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
     let nm' = fromString nm
     let llmod = cc^.ccLLVMModule
     def <- case find (\d -> L.defName d == nm') (L.modDefines llmod) of
                    Nothing -> fail ("Could not find function named" ++ show nm)
                    Just decl -> return decl
     let st0 = initialCrucibleSetupState cc def
     -- execute commands of the method spec
     methodSpec <- view csMethodSpec <$> execStateT (runCrucibleSetupM setup) st0
     let globals = cc^.ccGlobals
     let mvar = Crucible.llvmMemVar (cc^.ccLLVMContext)
     mem0 <- case Crucible.lookupGlobal mvar globals of
       Nothing -> fail "internal error: LLVM Memory global not found"
       Just mem0 -> return mem0
     let globals1 = Crucible.llvmGlobals (cc^.ccLLVMContext) mem0
     -- construct the initial state for verifications
     (args, assumes, env, globals2) <- io $ verifyPrestate cc methodSpec globals1
     -- save initial path condition
     pathstate <- io $ Crucible.getCurrentState sym
     -- run the symbolic execution
     (ret, globals3)
        <- io $ verifySimulate opts cc methodSpec args assumes lemmas globals2 checkSat
     -- collect the proof obligations
     asserts <- io $ verifyPoststate opts (biSharedContext bic) cc
                       methodSpec env globals3 ret
     -- restore initial path condition
     io $ Crucible.resetCurrentState sym pathstate
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
    let nm' = fromString nm
    let llmod = cc^.ccLLVMModule
    st0 <- case initialCrucibleSetupState cc     <$> find (\d -> L.defName d == nm') (L.modDefines  llmod) <|>
                initialCrucibleSetupStateDecl cc <$> find (\d -> L.decName d == nm') (L.modDeclares llmod) of
                   Nothing -> fail ("Could not find function named" ++ show nm)
                   Just st0 -> return st0
    (view csMethodSpec) <$> execStateT (runCrucibleSetupM setup) st0

verifyObligations :: CrucibleContext arch
                  -> CrucibleMethodSpecIR
                  -> ProofScript SatResult
                  -> [Term]
                  -> [(String, Term)]
                  -> TopLevel SolverStats
verifyObligations cc mspec tactic assumes asserts = do
  let sym = cc^.ccBackend
  st     <- io $ readIORef $ Crucible.sbStateManager sym
  let sc  = Crucible.saw_ctx st
  assume <- io $ scAndList sc assumes
  let nm  = show (L.ppSymbol (mspec^.csName))
  stats <- forM (zip [(0::Int)..] asserts) $ \(n, (msg, assert)) -> do
    goal   <- io $ scImplies sc assume assert
    goal'  <- io $ scAbstractExts sc (getAllExts goal) goal
    let goalname = concat [nm, " (", takeWhile (/= '\n') msg, ")"]
        proofgoal = ProofGoal Universal n "vc" goalname goal'
    r      <- evalStateT tactic (startProof proofgoal)
    case r of
      Unsat stats -> return stats
      SatMulti stats vals -> do
        printOutLnTop Info $ unwords ["Subgoal failed:", nm, msg]
        printOutLnTop Info (show stats)
        printOutLnTop OnlyCounterExamples "----------Counterexample----------"
        mapM_ (printOutLnTop OnlyCounterExamples . show) vals
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
      [Term],
      Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)),
      Crucible.SymGlobalState Sym)
verifyPrestate cc mspec globals = do
  let ?lc = cc^.ccTypeCtx

  let lvar = Crucible.llvmMemVar (cc^.ccLLVMContext)
  let Just mem = Crucible.lookupGlobal lvar globals

  let Just memtypes = traverse TyCtx.asMemType (mspec^.csPreState.csAllocs)
  -- Allocate LLVM memory for each 'crucible_alloc'
  (env1, mem') <- runStateT (traverse (doAlloc cc) memtypes) mem
  env2 <- Map.traverseWithKey
            (\k _ -> executeFreshPointer cc k)
            (mspec^.csPreState.csFreshPointers)
  let env = Map.union env1 env2

  mem'' <- setupPrePointsTos mspec cc env (mspec^.csPreState.csPointsTos) mem'
  let globals1 = Crucible.insertGlobal lvar mem'' globals
  (globals2,cs) <- setupPrestateConditions mspec cc env globals1 (mspec^.csPreState.csConditions)
  args <- resolveArguments cc mspec env
  return (args, cs, env, globals2)


resolveArguments ::
  (?lc :: TyCtx.LLVMContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  CrucibleContext arch       ->
  CrucibleMethodSpecIR       ->
  Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)) ->
  IO [(Crucible.MemType, LLVMVal)]
resolveArguments cc mspec env = mapM resolveArg [0..(nArgs-1)]
  where
    nArgs = toInteger (length (mspec^.csArgs))
    tyenv = mspec^.csPreState.csAllocs
    resolveArg i =
      case Map.lookup i (mspec^.csArgBindings) of
        Just (tp, sv) -> do
          let mt = fromMaybe (error ("Expected memory type:" ++ show tp)) (TyCtx.asMemType tp)
          v <- resolveSetupVal cc env tyenv sv
          return (mt, v)
        Nothing -> fail $ unwords ["Argument", show i, "unspecified"]

--------------------------------------------------------------------------------

-- | For each points-to constraint in the pre-state section of the
-- function spec, write the given value to the address of the given
-- pointer.
setupPrePointsTos ::
  (?lc :: TyCtx.LLVMContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  CrucibleMethodSpecIR       ->
  CrucibleContext arch       ->
  Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)) ->
  [PointsTo]                 ->
  MemImpl                    ->
  IO MemImpl
setupPrePointsTos mspec cc env pts mem0 = foldM go mem0 pts
  where
    tyenv = mspec^.csPreState.csAllocs

    go :: MemImpl -> PointsTo -> IO MemImpl
    go mem (PointsTo ptr val) =
      do val' <- resolveSetupVal cc env tyenv val
         ptr' <- resolveSetupVal cc env tyenv ptr
         ptr'' <- case ptr' of
           Crucible.LLVMValInt blk off
             | Just Crucible.Refl <- Crucible.testEquality (Crucible.bvWidth off) Crucible.PtrWidth
             -> return (Crucible.LLVMPointer blk off)
           _ -> fail "Non-pointer value found in points-to assertion"
         -- In case the types are different (from crucible_points_to_untyped)
         -- then the store type should be determined by the rhs.
         memTy <- typeOfSetupValue cc tyenv val
         storTy <- Crucible.toStorableType memTy
         let sym = cc^.ccBackend
         mem' <- Crucible.storeRaw sym mem ptr'' storTy val'
         return mem'

setupPrestateConditions ::
  (?lc :: TyCtx.LLVMContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  CrucibleMethodSpecIR        ->
  CrucibleContext arch        ->
  Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)) ->
  Crucible.SymGlobalState Sym ->
  [SetupCondition]            ->
  IO (Crucible.SymGlobalState Sym, [Term])
setupPrestateConditions mspec cc env = aux []
  where
    tyenv = mspec^.csPreState.csAllocs

    aux acc globals [] = return (globals, acc)

    aux acc globals (SetupCond_Equal val1 val2 : xs) =
      do val1' <- resolveSetupVal cc env tyenv val1
         val2' <- resolveSetupVal cc env tyenv val2
         t     <- assertEqualVals cc val1' val2'
         aux (t:acc) globals xs

    aux acc globals (SetupCond_Pred tm : xs) =
      aux (ttTerm tm : acc) globals xs

    aux acc globals (SetupCond_Ghost var val : xs) =
      aux acc (Crucible.insertGlobal var val globals) xs

--------------------------------------------------------------------------------

-- | Create a SAWCore formula asserting that two 'LLVMVal's are equal.
assertEqualVals ::
  CrucibleContext arch ->
  LLVMVal ->
  LLVMVal ->
  IO Term
assertEqualVals cc v1 v2 =
  Crucible.toSC (cc^.ccBackend) =<< equalValsPred cc v1 v2

--------------------------------------------------------------------------------

-- | Allocate space on the LLVM heap to store a value of the given
-- type. Returns the pointer to the allocated memory.
doAlloc ::
  (?lc :: TyCtx.LLVMContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  CrucibleContext arch       ->
  Crucible.MemType           ->
  StateT MemImpl IO (LLVMPtr (Crucible.ArchWidth arch))
doAlloc cc tp = StateT $ \mem ->
  do let sym = cc^.ccBackend
     let dl = TyCtx.llvmDataLayout ?lc
     sz <- Crucible.bvLit sym Crucible.PtrWidth (Crucible.bytesToInteger (Crucible.memTypeSize dl tp))
     Crucible.mallocRaw sym mem sz

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
  (?lc :: TyCtx.LLVMContext, Crucible.HasPtrWidth wptr, wptr ~ Crucible.ArchWidth arch) =>
  Options                    ->
  CrucibleContext arch       ->
  Crucible.SimContext Crucible.SAWCruciblePersonality Sym (Crucible.LLVM arch) ->
  [CrucibleMethodSpecIR]     ->
  Crucible.OverrideSim Crucible.SAWCruciblePersonality Sym (Crucible.LLVM arch) rtp args ret ()
registerOverride opts cc _ctx cs = do
  let sym = cc^.ccBackend
  sc <- Crucible.saw_ctx <$> liftIO (readIORef (Crucible.sbStateManager sym))
  let s@(L.Symbol fsym) = (head cs)^.csName
      llvmctx = cc^.ccLLVMContext
  liftIO $
    printOutLn opts Info $ "Registering override for `" ++ fsym ++ "`"
  case Map.lookup s (llvmctx ^. Crucible.symbolMap) of
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
            (methodSpecHandler opts sc cc cs retType)
    Nothing -> fail $ "Can't find declaration for `" ++ fsym ++ "`."

--------------------------------------------------------------------------------

verifySimulate ::
  (?lc :: TyCtx.LLVMContext, Crucible.HasPtrWidth wptr, wptr ~ Crucible.ArchWidth arch) =>
  Options                       ->
  CrucibleContext arch          ->
  CrucibleMethodSpecIR          ->
  [(Crucible.MemType, LLVMVal)] ->
  [Term]                        ->
  [CrucibleMethodSpecIR]        ->
  Crucible.SymGlobalState Sym   ->
  Bool                          ->
  IO (Maybe (Crucible.MemType, LLVMVal), Crucible.SymGlobalState Sym)
verifySimulate opts cc mspec args assumes lemmas globals checkSat =
  do let nm = mspec^.csName
     case Map.lookup nm (Crucible.cfgMap (cc^.ccLLVMModuleTrans)) of
       Nothing -> fail $ unwords ["function", show nm, "not found"]
       Just (Crucible.AnyCFG cfg) ->
         do let h   = Crucible.cfgHandle cfg
                rty = Crucible.handleReturnType h
            args' <- prepareArgs (Crucible.handleArgTypes h) (map snd args)
            let simCtx = cc^.ccSimContext
                conf = Crucible.simConfig simCtx
            simCtx' <- flip SState.execStateT simCtx $
                         Crucible.runSimConfigMonad
                           (Crucible.setConfigValue Crucible.sawCheckPathSat conf checkSat)
            let simSt = Crucible.initSimState simCtx' globals Crucible.defaultErrorHandler
            res <-
              Crucible.runOverrideSim simSt rty $
                do mapM_ (registerOverride opts cc simCtx')
                         (groupOn (view csName) lemmas)
                   liftIO $ do
                     preds <- mapM (resolveSAWPred cc) assumes
                     mapM_ (Crucible.addAssumption sym) preds
                   Crucible.regValue <$> (Crucible.callCFG cfg args')
            case res of
              Crucible.FinishedExecution _ pr ->
                do Crucible.GlobalPair retval globals1 <-
                     case pr of
                       Crucible.TotalRes gp -> return gp
                       Crucible.PartialRes _ gp _ ->
                         do printOutLn opts Error "Symbolic simulation failed along some paths!"
                            return gp
                   let ret_ty = mspec^.csRet
                   let ret_ty' = fromMaybe (error ("Expected return type:" ++ show ret_ty))
                                 (TyCtx.liftRetType ret_ty)
                   retval' <- case ret_ty' of
                     Nothing -> return Nothing
                     Just ret_mt ->
                       do v <- Crucible.packMemValue sym
                                 (fromMaybe (error ("Expected storable type:" ++ show ret_ty))
                                      (Crucible.toStorableType ret_mt))
                                 (Crucible.regType  retval)
                                 (Crucible.regValue retval)
                          return (Just (ret_mt, v))

                   return (retval', globals1)

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
        do a <- Crucible.unpackMemValue sym (x !! Ctx.indexVal idx)
           v <- Crucible.coerceAny sym tr a
           return (Crucible.RegEntry tr v))
      ctx

-- | Build a conjunction from a list of boolean terms.
scAndList :: SharedContext -> [Term] -> IO Term
scAndList sc []       = scBool sc True
scAndList sc (x : xs) = foldM (scAnd sc) x xs

--------------------------------------------------------------------------------

verifyPoststate ::
  (?lc :: TyCtx.LLVMContext, Crucible.HasPtrWidth wptr, wptr ~ Crucible.ArchWidth arch) =>
  Options                           {- ^ saw script debug and print options           -} ->
  SharedContext                     {- ^ saw core context                             -} ->
  CrucibleContext arch              {- ^ crucible context                             -} ->
  CrucibleMethodSpecIR              {- ^ specification                                -} ->
  Map AllocIndex (LLVMPtr wptr)     {- ^ allocation substitution                      -} ->
  Crucible.SymGlobalState Sym       {- ^ global variables                             -} ->
  Maybe (Crucible.MemType, LLVMVal) {- ^ optional return value                        -} ->
  IO [(String, Term)]               {- ^ generated labels and verification conditions -}
verifyPoststate opts sc cc mspec env0 globals ret =

  do let terms0 = Map.fromList
           [ (ecVarIndex ec, ttTerm tt)
           | tt <- mspec^.csPreState.csFreshVars
           , let Just ec = asExtCns (ttTerm tt) ]

     let initialFree = Set.fromList (map (termId . ttTerm)
                                    (view (csPostState.csFreshVars) mspec))
     matchPost <-
          runOverrideMatcher sym globals env0 terms0 initialFree $
           do matchResult
              learnCond opts sc cc mspec PostState (mspec ^. csPostState)

     st <- case matchPost of
             Left err      -> fail (show err)
             Right (_, st) -> return st
     for_ (view osAsserts st) $ \(p, r) ->
       Crucible.sbAddAssertion sym p r

     obligations <- Crucible.getProofObligations sym
     Crucible.setProofObligations sym []
     mapM verifyObligation obligations

  where
    sym = cc^.ccBackend

    verifyObligation (_, (Crucible.Assertion _ _ Nothing)) =
      fail "Found an assumption in final proof obligation list"
    verifyObligation (hyps, (Crucible.Assertion _ concl (Just err))) = do
      hypTerm    <- scAndList sc =<< mapM (Crucible.toSC sym) hyps
      conclTerm  <- Crucible.toSC sym concl
      obligation <- scImplies sc hypTerm conclTerm
      return ("safety assertion: " ++ Crucible.simErrorReasonMsg err, obligation)

    matchResult =
      case (ret, mspec ^. csRetValue) of
        (Nothing     , Just _ )     -> fail "verifyPoststate: unexpected crucible_return specification"
        (Just _      , Nothing)     -> fail "verifyPoststate: missing crucible_return specification"
        (Nothing     , Nothing)     -> return ()
        (Just (rty,r), Just expect) -> matchArg sc cc PostState r rty expect


--------------------------------------------------------------------------------

setupCrucibleContext ::
   BuiltinContext -> Options -> LLVMModule ->
   (forall arch. (?lc :: TyCtx.LLVMContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) => CrucibleContext arch -> TopLevel a) ->
   TopLevel a
setupCrucibleContext bic opts (LLVMModule _ llvm_mod) action = do
  halloc <- getHandleAlloc
  Some mtrans <- io $ stToIO $ Crucible.translateModule halloc llvm_mod
  let ctx = mtrans^.Crucible.transContext
  Crucible.llvmPtrWidth ctx $ \wptr -> Crucible.withPtrWidth wptr $
    let ?lc = ctx^.Crucible.llvmTypeCtx in
    action =<< (io $ do
      let gen = Crucible.globalNonceGenerator
      let sc  = biSharedContext bic
      let verbosity = simVerbose opts
      cfg <- Crucible.initialConfig verbosity Crucible.sawOptions
      sym <- Crucible.newSAWCoreBackend sc gen cfg
      let bindings = Crucible.fnBindingsFromList []
      let simctx   = Crucible.initSimContext sym intrinsics cfg halloc stdout
                        bindings Crucible.llvmExtensionImpl Crucible.SAWCruciblePersonality
      mem <- Crucible.initializeMemory sym ctx llvm_mod
      let globals  = Crucible.llvmGlobals ctx mem

      let setupMem = do
             -- register the callable override functions
             _llvmctx' <- execStateT Crucible.register_llvm_overrides ctx

             -- initialize LLVM global variables
             _ <- case Crucible.initMemoryCFG mtrans of
                     Crucible.SomeCFG initCFG ->
                       Crucible.callCFG initCFG Crucible.emptyRegMap

             -- register all the functions defined in the LLVM module
             mapM_ Crucible.registerModuleFn $ Map.toList $ Crucible.cfgMap mtrans

      let simSt = Crucible.initSimState simctx globals Crucible.defaultErrorHandler
      res <- Crucible.runOverrideSim simSt Crucible.UnitRepr setupMem
      (globals', simctx') <-
          case res of
            Crucible.FinishedExecution st (Crucible.TotalRes gp) -> return (gp^.Crucible.gpGlobals, st)
            Crucible.FinishedExecution st (Crucible.PartialRes _ gp _) -> return (gp^.Crucible.gpGlobals, st)
            Crucible.AbortedResult _ _ -> fail "Memory initialization failed!"
      return
         CrucibleContext{ _ccLLVMModuleTrans = mtrans
                        , _ccLLVMModule = llvm_mod
                        , _ccBackend = sym
                        , _ccEmptyMemImpl = mem
                        , _ccSimContext = simctx'
                        , _ccGlobals = globals'
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
       sc_tp <- Crucible.baseSCType sc btp
       i     <- scFreshGlobalVar sc
       ecs   <- readIORef ecRef
       let len = Seq.length ecs
       let ec = EC i ("arg_"++show len) sc_tp
       writeIORef ecRef (ecs Seq.|> ec)
       t     <- scFlatTermF sc (ExtCns ec)
       elt   <- Crucible.bindSAWTerm sym btp t
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

extractFromCFG :: Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
   Options -> SharedContext -> CrucibleContext arch -> Crucible.AnyCFG (Crucible.LLVM arch) -> IO TypedTerm
extractFromCFG opts sc cc (Crucible.AnyCFG cfg) =
  do  let sym = cc^.ccBackend
      let h   = Crucible.cfgHandle cfg
      (ecs, args) <- setupArgs sc sym h
      let simCtx  = cc^.ccSimContext
      let globals = cc^.ccGlobals
      let simSt = Crucible.initSimState simCtx globals Crucible.defaultErrorHandler
      res  <- Crucible.runOverrideSim simSt (Crucible.handleReturnType h)
                 (Crucible.regValue <$> (Crucible.callCFG cfg args))
      case res of
        Crucible.FinishedExecution _ pr -> do
            gp <- case pr of
                    Crucible.TotalRes gp -> return gp
                    Crucible.PartialRes _ gp _ -> do
                      printOutLn opts Error "Symbolic simulation failed along some paths!"
                      return gp
            t <- Crucible.asSymExpr
                       (gp^.Crucible.gpValue)
                       (Crucible.toSC sym)
                       (fail $ unwords ["Unexpected return type:", show (Crucible.regType (gp^.Crucible.gpValue))])
            t' <- scAbstractExts sc (toList ecs) t
            tt <- mkTypedTerm sc t'
            return tt
        Crucible.AbortedResult _ ar -> do
          let resultDoc = ppAbortedResult cc ar
          fail $ unlines [ "Symbolic execution failed."
                         , show resultDoc
                         ]
    
--------------------------------------------------------------------------------

extract_crucible_llvm :: BuiltinContext -> Options -> LLVMModule -> String -> TopLevel TypedTerm
extract_crucible_llvm bic opts lm fn_name =
  setupCrucibleContext bic opts lm $ \cc ->
    case Map.lookup (fromString fn_name) (Crucible.cfgMap (cc^.ccLLVMModuleTrans)) of
      Nothing  -> fail $ unwords ["function", fn_name, "not found"]
      Just cfg -> io $ extractFromCFG opts (biSharedContext bic) cc cfg

load_llvm_cfg :: BuiltinContext -> Options -> LLVMModule -> String -> TopLevel LLVM_CFG
load_llvm_cfg bic opts lm fn_name =
  setupCrucibleContext bic opts lm $ \cc ->
    case Map.lookup (fromString fn_name) (Crucible.cfgMap (cc^.ccLLVMModuleTrans)) of
      Nothing  -> fail $ unwords ["function", fn_name, "not found"]
      Just cfg -> return (LLVM_CFG cfg)

--------------------------------------------------------------------------------

diffMemTypes ::
  Crucible.HasPtrWidth wptr =>
  Crucible.MemType ->
  Crucible.MemType ->
  [([Maybe Int], Crucible.MemType, Crucible.MemType)]
diffMemTypes x0 y0 =
  let wptr :: Natural = fromIntegral (Crucible.natValue ?ptrWidth) in
  case (x0, y0) of
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
      | Crucible.siIsPacked x == Crucible.siIsPacked y
        && V.length (Crucible.siFields x) == V.length (Crucible.siFields y) ->
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
logicTypeOfActual _ sc Crucible.FloatType = Just <$> scPrelude_Float sc
logicTypeOfActual _ sc Crucible.DoubleType = Just <$> scPrelude_Double sc
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
logicTypeOfActual _ _ _ = return Nothing

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
  let dl = TyCtx.llvmDataLayout (cctx^.ccTypeCtx)
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
     constructExpandedSetupValue sc lty'


memTypeForLLVMType :: BuiltinContext -> L.Type -> CrucibleSetup arch Crucible.MemType
memTypeForLLVMType _bic lty =
  do case TyCtx.liftMemType lty of
       Just m -> return m
       Nothing -> fail ("unsupported type: " ++ show (L.ppType lty))

symTypeForLLVMType :: BuiltinContext -> L.Type -> CrucibleSetup arch Crucible.SymType
symTypeForLLVMType _bic lty =
  do case TyCtx.liftType lty of
       Just m -> return m
       Nothing -> fail ("unsupported type: " ++ show (L.ppType lty))

-- | See 'crucible_fresh_expanded_val'
--
-- This is the recursively-called worker function.
constructExpandedSetupValue ::
  (?lc::TyCtx.LLVMContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  SharedContext    {- ^ shared context             -} ->
  Crucible.MemType {- ^ LLVM mem type              -} ->
  CrucibleSetup arch SetupValue
                   {- ^ fresh expanded setup value -}
constructExpandedSetupValue sc t =
  case t of
    Crucible.IntType w ->
      do ty <- liftIO (logicTypeForInt sc w)
         SetupTerm <$> freshVariable sc "" ty

    Crucible.StructType si ->
       SetupStruct . toList <$> traverse (constructExpandedSetupValue sc) (Crucible.siFieldTypes si)

    Crucible.PtrType symTy ->
      case TyCtx.asMemType symTy of
        Just memTy ->  constructFreshPointer (Crucible.MemType memTy)
        Nothing    -> fail ("lhs not a valid pointer type: " ++ show symTy)

    Crucible.ArrayType n memTy ->
       SetupArray <$> replicateM n (constructExpandedSetupValue sc memTy)

    Crucible.FloatType    -> fail "crucible_fresh_expanded_var: Float not supported"
    Crucible.DoubleType   -> fail "crucible_fresh_expanded_var: Double not supported"
    Crucible.MetadataType -> fail "crucible_fresh_expanded_var: Metadata not supported"
    Crucible.VecType{}    -> fail "crucible_fresh_expanded_var: Vec not supported"

crucible_alloc :: BuiltinContext
               -> Options
               -> L.Type
               -> CrucibleSetupM SetupValue
crucible_alloc _bic _opt lty = CrucibleSetupM $
  do let ?dl = TyCtx.llvmDataLayout ?lc
     symTy <- case TyCtx.liftType lty of
       Just s -> return s
       Nothing -> fail ("unsupported type in crucible_alloc: " ++ show (L.ppType lty))
     n <- csVarCounter <<%= nextAllocIndex
     currentState.csAllocs.at n ?= symTy
     return (SetupVar n)


crucible_fresh_pointer ::
  BuiltinContext ->
  Options        ->
  L.Type         ->
  CrucibleSetupM SetupValue
crucible_fresh_pointer bic _opt lty = CrucibleSetupM $
  do symTy <- symTypeForLLVMType bic lty
     constructFreshPointer symTy

constructFreshPointer :: Crucible.SymType -> CrucibleSetup arch SetupValue
constructFreshPointer symTy =
  do n <- csVarCounter <<%= nextAllocIndex
     currentState.csFreshPointers.at n ?= symTy
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
     Crucible.llvmPtrWidth (cc^.ccLLVMContext) $ \wptr -> Crucible.withPtrWidth wptr $
       do let ?lc = cc^.ccTypeCtx
          st <- get
          let rs = st^.csResolvedState
          if st^.csPrePost == PreState && testResolved ptr rs
            then fail "Multiple points-to preconditions on same pointer"
            else csResolvedState %= markResolved ptr
          let env = csAllocations (st^.csMethodSpec)
          ptrTy <- typeOfSetupValue cc env ptr
          lhsTy <- case ptrTy of
            Crucible.PtrType symTy ->
              case TyCtx.asMemType symTy of
                Just lhsTy -> return lhsTy
                Nothing -> fail $ "lhs not a valid pointer type: " ++ show ptrTy
            _ -> fail $ "lhs not a pointer type: " ++ show ptrTy
          valTy <- typeOfSetupValue cc env val
          when typed (checkMemTypeCompatibility lhsTy valTy)
          addPointsTo (PointsTo ptr val)

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
     ty1 <- typeOfSetupValue cc env val1
     ty2 <- typeOfSetupValue cc env val2
     checkMemTypeCompatibility ty1 ty2
     addCondition (SetupCond_Equal val1 val2)

crucible_precond ::
  TypedTerm      ->
  CrucibleSetupM ()
crucible_precond p = CrucibleSetupM $ do
  st <- get
  when (st^.csPrePost == PostState) $
    fail "attempt to use `crucible_precond` in post state"
  addCondition (SetupCond_Pred p)

crucible_postcond ::
  TypedTerm      ->
  CrucibleSetupM ()
crucible_postcond p = CrucibleSetupM $ do
  st <- get
  when (st^.csPrePost == PreState) $
    fail "attempt to use `crucible_postcond` in pre state"
  addCondition (SetupCond_Pred p)

crucible_execute_func :: BuiltinContext
                      -> Options
                      -> [SetupValue]
                      -> CrucibleSetupM ()
crucible_execute_func _bic _opt args = CrucibleSetupM $ do
  let ?dl   = TyCtx.llvmDataLayout ?lc
  tps <- use (csMethodSpec.csArgs)
  case traverse TyCtx.liftType tps of
    Just tps' -> do
      csPrePost .= PostState
      csMethodSpec.csArgBindings .= Map.fromList [ (i, (t,a))
                                                 | i <- [0..]
                                                 | a <- args
                                                 | t <- tps'
                                                 ]

    _ -> fail $ unlines ["Function signature not supported:", show tps]


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
  addCondition (SetupCond_Ghost ghost val)

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

--------------------------------------------------------------------------------

-- | Sort a list of things and group them into equivalence classes.
groupOn ::
  Ord b =>
  (a -> b) {- ^ equivalence class projection -} ->
  [a] -> [[a]]
groupOn f = groupBy ((==) `on` f) . sortBy (compare `on` f)
