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


module SAWScript.JVM.CrucibleBuiltins
    ( {- crucible_jvm_cfg
    , crucible_jvm_extract
    , crucible_jvm_verify
    , crucible_jvm_unsafe_assume_spec
    , -} jvm_return
    , jvm_execute_func
    , jvm_postcond
    , jvm_precond
    , jvm_field_is
    , jvm_elem_is
    , jvm_fresh_var
    , jvm_alloc_object
    , jvm_alloc_array
    ) where

import           Control.Lens

import           Control.Monad.State
import           Control.Applicative
import           Data.Foldable (for_, toList, find)
import           Data.Function
import           Data.IORef
import           Data.List
import           Data.Maybe (fromMaybe)
import           Data.Monoid ((<>))
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

import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>))
--import qualified Control.Monad.Trans.Maybe as MaybeT

import           Data.Parameterized.Classes

import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some

import qualified Verifier.Java.Codebase as JSS

import qualified What4.Config as W4
import qualified What4.FunctionName as W4
import qualified What4.ProgramLoc as W4
import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4
--import           What4.Utils.MonadST

import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Backend.SAWCore as Crucible
import qualified Lang.Crucible.CFG.Core as Crucible
  (AnyCFG(..), SomeCFG(..), CFG, TypeRepr(..), cfgHandle,
   asBaseType, AsBaseType(..))
import qualified Lang.Crucible.CFG.Extension as Crucible
  (IsSyntaxExtension)
import qualified Lang.Crucible.FunctionHandle as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Simulator.GlobalState as Crucible
import qualified Lang.Crucible.Simulator.RegMap as Crucible
import qualified Lang.Crucible.Simulator.SimError as Crucible

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

import SAWScript.JavaExpr (JavaType(..))

import SAWScript.JVM.CrucibleMethodSpecIR
import SAWScript.JVM.CrucibleOverride
import SAWScript.JVM.CrucibleResolveSetupValue


{-
ppAbortedResult :: CrucibleContext
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

crucible_jvm_verify ::
  BuiltinContext         ->
  Options                ->
  JSS.Class              ->
  String                 ->
  [CrucibleMethodSpecIR] ->
  Bool                   ->
  JVMSetupM ()      ->
  ProofScript SatResult  ->
  TopLevel CrucibleMethodSpecIR
crucible_jvm_verify bic opts lm nm lemmas checkSat setup tactic =
  setupCrucibleContext bic opts lm $ \cc ->
  do let sym = cc^.ccBackend
     let nm' = fromString nm
     let llmod = error "llmod" --cc^.ccLLVMModule

     setupLoc <- toW4Loc "_SAW_verify_prestate" <$> getPosition

     def <- error "def" {-case find (\d -> L.defName d == nm') (L.modDefines llmod) of
                    Nothing -> fail ("Could not find function named" ++ show nm)
                    Just decl -> return decl-}
     st0 <- either (fail . show . ppSetupError) return (initialCrucibleSetupState cc def setupLoc)

     -- execute commands of the method spec
     liftIO $ W4.setCurrentProgramLoc sym setupLoc
     methodSpec <- view csMethodSpec <$> execStateT (runJVMSetupM setup) st0

     -- set up the LLVM memory with a pristine heap
     let globals = cc^.cjcJavaGlobals

     -- construct the initial state for verifications
     (args, assumes, env, globals2) <- io $ verifyPrestate cc methodSpec globals1

     -- save initial path conditions
     frameIdent <- io $ Crucible.pushAssumptionFrame sym

     -- run the symbolic execution
     (ret, globals3)
        <- io $ verifySimulate opts cc methodSpec args assumes lemmas globals2 checkSat

     -- collect the proof obligations
     asserts <- verifyPoststate opts (biSharedContext bic) cc
                    methodSpec env globals3 ret

     -- restore previous assumption state
     _ <- io $ Crucible.popAssumptionFrame sym frameIdent

     -- attempt to verify the proof obligations
     stats <- verifyObligations cc methodSpec tactic assumes asserts
     return (methodSpec & csSolverStats .~ stats)

crucible_jvm_unsafe_assume_spec ::
  BuiltinContext   ->
  Options          ->
  JavaClass        ->
  String          {- ^ Name of the method -} ->
  JVMSetupM () {- ^ Boundary specification -} ->
  TopLevel CrucibleMethodSpecIR
crucible_jvm_unsafe_assume_spec bic opts lm nm setup =
  setupCrucibleContext bic opts lm $ \cc -> do
    let nm' = fromString nm
    let llmod = cc^.ccJVMClass
    loc <- toW4Loc "_SAW_assume_spec" <$> getPosition
    st0 <- case initialCrucibleSetupState cc     <$> find (\d -> L.defName d == nm') (L.modDefines  llmod) <*> pure loc <|>
                initialCrucibleSetupStateDecl cc <$> find (\d -> L.decName d == nm') (L.modDeclares llmod) <*> pure loc of
                   Nothing -> fail ("Could not find function named" ++ show nm)
                   Just (Left err) -> fail (show (ppSetupError err))
                   Just (Right st0) -> return st0
    (view csMethodSpec) <$> execStateT (runJVMSetupM setup) st0
-}

verifyObligations ::
  CrucibleContext ->
  CrucibleMethodSpecIR ->
  ProofScript SatResult ->
  [Crucible.LabeledPred Term Crucible.AssumptionReason] ->
  [(String, Term)] ->
  TopLevel SolverStats
verifyObligations cc mspec tactic assumes asserts =
  do let sym = cc^.ccBackend
     st     <- io $ readIORef $ W4.sbStateManager sym
     let sc  = Crucible.saw_ctx st
     assume <- io $ scAndList sc (toListOf (folded . Crucible.labeledPred) assumes)
     let nm  = mspec^.csName
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
           opts <- sawPPOpts <$> rwPPOpts <$> getTopLevelRW
           let showAssignment (name, val) = "  " ++ name ++ ": " ++ show (ppFirstOrderValue opts val)
           mapM_ (printOutLnTop OnlyCounterExamples . showAssignment) vals
           io $ fail "Proof failed." -- Mirroring behavior of llvm_verify
     printOutLnTop Info $ unwords ["Proof succeeded!", nm]
     return (mconcat stats)

{-
-- | Evaluate the precondition part of a Crucible method spec:
--
-- * Allocate heap space for each 'jvm_alloc' statement.
--
-- * Record an equality precondition for each 'jvm_equal'
-- statement.
--
-- * Write to memory for each 'jvm_points_to' statement. (Writes
-- to already-initialized locations are transformed into equality
-- preconditions.)
--
-- * Evaluate the function arguments from the 'jvm_execute_func'
-- statement.
--
-- Returns a tuple of (arguments, preconditions, pointer values,
-- memory).
verifyPrestate ::
  CrucibleContext ->
  CrucibleMethodSpecIR ->
  Crucible.SymGlobalState Sym ->
  IO ([(JavaType, JVMVal)],
      [Crucible.LabeledPred Term Crucible.AssumptionReason],
      Map AllocIndex JVMRefVal,
      Crucible.SymGlobalState Sym)
verifyPrestate cc mspec globals = do
  let ?lc = cc^.ccTypeCtx
  let sym = cc^.ccBackend
  let tyenvRW = mspec^.csPreState.csAllocs
  let tyenv   = csAllocations mspec
  let nameEnv = mspec^.csPreState.csVarTypeNames

  let prestateLoc = W4.mkProgramLoc "_SAW_verify_prestate" W4.InternalPos
  liftIO $ W4.setCurrentProgramLoc sym prestateLoc

  --let lvar = Crucible.llvmMemVar (cc^.ccLLVMContext)
  --let Just mem = Crucible.lookupGlobal lvar globals

  -- Allocate objects in memory for each 'jvm_alloc'
  (env1, mem') <- runStateT (traverse (doAlloc cc) tyenvRW) mem
  env2 <- Map.traverseWithKey
            (\k _ -> executeFreshPointer cc k)
            (mspec^.csPreState.csFreshPointers)
  let env = Map.unions [env1, env2]

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
-}

{-
-- | Check two MemTypes for register compatiblity.  This is a stricter
--   check than the memory compatiblity check that is done for points-to
--   assertions.
checkRegisterCompatibility ::
  Crucible.MemType ->
  Crucible.MemType ->
  IO Bool
checkRegisterCompatibility mt mt' =
  do st  <- Crucible.toStorableType mt
     st' <- Crucible.toStorableType mt'
     return (st == st')

resolveArguments ::
  CrucibleContext          ->
  CrucibleMethodSpecIR     ->
  Map AllocIndex JVMRefVal ->
  IO [(JavaType, JVMVal)]
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
-}

--------------------------------------------------------------------------------

{-
-- | For each points-to constraint in the pre-state section of the
-- function spec, write the given value to the address of the given
-- pointer.
setupPrePointsTos ::
  CrucibleMethodSpecIR     ->
  CrucibleContext          ->
  Map AllocIndex JVMRefVal ->
  [PointsTo]               ->
  MemImpl                  ->
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
         -- In case the types are different (from jvm_points_to_untyped)
         -- then the store type should be determined by the rhs.
         memTy <- typeOfSetupValue cc tyenv nameEnv val
         storTy <- Crucible.toStorableType memTy
         let sym = cc^.ccBackend
         mem' <- Crucible.storeConstRaw sym mem ptr'' storTy val'
         return mem'
-}

-- | Sets up globals (ghost variable), and collects boolean terms
-- that shuld be assumed to be true.
setupPrestateConditions ::
  CrucibleMethodSpecIR        ->
  CrucibleContext             ->
  Map AllocIndex JVMRefVal    ->
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

-- | Create a SAWCore formula asserting that two 'JVMVal's are equal.
assertEqualVals ::
  CrucibleContext ->
  JVMVal ->
  JVMVal ->
  IO Term
assertEqualVals cc v1 v2 =
  Crucible.toSC (cc^.ccBackend) =<< equalValsPred cc v1 v2

--------------------------------------------------------------------------------

{-
-- | Allocate space on the LLVM heap to store a value of the given
-- type. Returns the pointer to the allocated memory.
doAlloc ::
  CrucibleContext        ->
  (W4.ProgramLoc, JavaType) ->
  StateT MemImpl IO JVMRefVal
doAlloc cc (_loc,tp) = StateT $ \mem ->
  do let sym = cc^.ccBackend
     let dl = Crucible.llvmDataLayout ?lc
     sz <- W4.bvLit sym Crucible.PtrWidth (Crucible.bytesToInteger (Crucible.memTypeSize dl tp))
     Crucible.mallocRaw sym mem sz

-- | Allocate read-only space on the LLVM heap to store a value of the
-- given type. Returns the pointer to the allocated memory.
doAllocConst ::
  CrucibleContext           ->
  (W4.ProgramLoc, JavaType) ->
  StateT MemImpl IO JVMRefVal
doAllocConst cc (_loc,tp) = StateT $ \mem ->
  do let sym = cc^.ccBackend
     let dl = Crucible.llvmDataLayout ?lc
     sz <- W4.bvLit sym Crucible.PtrWidth (Crucible.bytesToInteger (Crucible.memTypeSize dl tp))
     Crucible.mallocConstRaw sym mem sz
-}

--------------------------------------------------------------------------------

--ppGlobalPair :: CrucibleContext arch
--             -> Crucible.GlobalPair Sym a
--             -> Doc
--ppGlobalPair cc gp =
--  let mvar = Crucible.llvmMemVar (cc^.ccLLVMContext)
--      globals = gp ^. Crucible.gpGlobals in
--  case Crucible.lookupGlobal mvar globals of
--    Nothing -> text "LLVM Memory global variable not initialized"
--    Just mem -> Crucible.ppMem mem


--------------------------------------------------------------------------------

{-
registerOverride ::
  Options                    ->
  CrucibleContext            ->
  Crucible.SimContext (Crucible.SAWCruciblePersonality Sym) Sym JVM ->
  [CrucibleMethodSpecIR]     ->
  Crucible.OverrideSim (Crucible.SAWCruciblePersonality Sym) Sym JVM rtp args ret ()
registerOverride opts cc _ctx cs = do
  let sym = cc^.ccBackend
  sc <- Crucible.saw_ctx <$> liftIO (readIORef (W4.sbStateManager sym))
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
            (methodSpecHandler opts sc cc cs retType)
    Nothing -> fail $ "Can't find declaration for `" ++ fsym ++ "`."
-}

--------------------------------------------------------------------------------

{-
verifySimulate ::
  Options                       ->
  CrucibleContext               ->
  CrucibleMethodSpecIR          ->
  [(JavaType, JVMVal)]          ->
  [Crucible.LabeledPred Term Crucible.AssumptionReason] ->
  [CrucibleMethodSpecIR]        ->
  Crucible.SymGlobalState Sym   ->
  Bool                          ->
  IO (Maybe (JavaType, JVMVal), Crucible.SymGlobalState Sym)
verifySimulate opts cc mspec args assumes lemmas globals checkSat =
  do let nm = mspec^.csName
     case Map.lookup (L.Symbol nm) (Crucible.cfgMap (cc^.ccLLVMModuleTrans)) of
       Nothing -> fail $ unwords ["function", show nm, "not found"]
       Just (Crucible.AnyCFG cfg) ->
         do let h   = Crucible.cfgHandle cfg
                rty = Crucible.handleReturnType h
            args' <- prepareArgs (Crucible.handleArgTypes h) (map snd args)
            let simCtx = cc^.ccLLVMSimContext
                conf = W4.getConfiguration sym
            checkSatOpt <- W4.getOptionSetting Crucible.sawCheckPathSat conf
            _ <- W4.setOpt checkSatOpt checkSat

            let simSt = Crucible.initSimState simCtx globals Crucible.defaultAbortHandler
            res <-
              Crucible.executeCrucible simSt $ Crucible.runOverrideSim rty $
                do mapM_ (registerOverride opts cc simCtx)
                         (groupOn (view csName) lemmas)
                   liftIO $ do
                     preds <- (traverse . Crucible.labeledPred) (resolveSAWPred cc) assumes
                     Crucible.addAssumptions sym (Seq.fromList preds)
                   Crucible.regValue <$> (Crucible.callCFG cfg args')
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

              Crucible.AbortedResult _ ar ->
                do let resultDoc = ppAbortedResult cc ar
                   fail $ unlines [ "Symbolic execution failed."
                                  , show resultDoc
                                  ]

  where
    sym = cc^.ccBackend
    prepareArgs ::
      Ctx.Assignment Crucible.TypeRepr xs ->
      [JVMVal] ->
      IO (Crucible.RegMap Sym xs)
    prepareArgs ctx x =
      Crucible.RegMap <$>
      Ctx.traverseWithIndex (\idx tr ->
        do a <- Crucible.unpackMemValue sym (x !! Ctx.indexVal idx)
           v <- Crucible.coerceAny sym tr a
           return (Crucible.RegEntry tr v))
      ctx
-}

-- | Build a conjunction from a list of boolean terms.
scAndList :: SharedContext -> [Term] -> IO Term
scAndList sc []       = scBool sc True
scAndList sc (x : xs) = foldM (scAnd sc) x xs

--------------------------------------------------------------------------------

verifyPoststate ::
  Options                           {- ^ saw script debug and print options           -} ->
  SharedContext                     {- ^ saw core context                             -} ->
  CrucibleContext                   {- ^ crucible context                             -} ->
  CrucibleMethodSpecIR              {- ^ specification                                -} ->
  Map AllocIndex JVMRefVal          {- ^ allocation substitution                      -} ->
  Crucible.SymGlobalState Sym       {- ^ global variables                             -} ->
  Maybe (JavaType, JVMVal)          {- ^ optional return value                        -} ->
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
      hypTerm    <- scAndList sc =<< mapM (Crucible.toSC sym) (toListOf (folded . Crucible.labeledPred) hyps)
      conclTerm  <- Crucible.toSC sym concl
      obligation <- scImplies sc hypTerm conclTerm
      return ("safety assertion: " ++ Crucible.simErrorReasonMsg err, obligation)

    matchResult =
      case (ret, mspec ^. csRetValue) of
        (Just (rty,r), Just expect) -> matchArg sc cc (mspec^.csLoc) PostState r rty expect
        (Nothing     , Just _ )     -> fail "verifyPoststate: unexpected jvm_return specification"
        _ -> return ()

--------------------------------------------------------------------------------

{-
setupCrucibleContext ::
  BuiltinContext -> Options -> JavaClass ->
  (CrucibleContext -> TopLevel a) ->
  TopLevel a
setupCrucibleContext bic opts (LLVMModule _ llvm_mod (Some mtrans)) action =
  do
  halloc <- getHandleAlloc
  AIGProxy proxy <- getProxy
  let ctx = mtrans^.Crucible.transContext
  Crucible.llvmPtrWidth ctx $ \wptr -> Crucible.withPtrWidth wptr $
    let ?lc = ctx^.Crucible.llvmTypeCtx in
    action =<< (io $ do
      let gen = globalNonceGenerator
      let sc  = biSharedContext bic
      let verbosity = simVerbose opts
      sym <- Crucible.newSAWCoreBackend proxy sc gen

      let cfg = W4.getConfiguration sym
      verbSetting <- W4.getOptionSetting W4.verbosity cfg
      _ <- W4.setOpt verbSetting (toInteger verbosity)

      let bindings = Crucible.fnBindingsFromList []
      let simctx   = Crucible.initSimContext sym intrinsics halloc stdout
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

      let simSt = Crucible.initSimState simctx globals Crucible.defaultAbortHandler
      res <- Crucible.executeCrucible simSt $ Crucible.runOverrideSim Crucible.UnitRepr setupMem
      (lglobals, lsimctx) <-
          case res of
            Crucible.FinishedResult st (Crucible.TotalRes gp) -> return (gp^.Crucible.gpGlobals, st)
            Crucible.FinishedResult st (Crucible.PartialRes _ gp _) -> return (gp^.Crucible.gpGlobals, st)
            Crucible.AbortedResult _ _ -> fail "Memory initialization failed!"
      return
         CrucibleContext{ _ccLLVMModuleTrans = mtrans
                        , _ccLLVMModule = llvm_mod
                        , _ccBackend = sym
                        , _ccLLVMEmptyMem = mem
                        , _ccLLVMSimContext = lsimctx
                        , _ccLLVMGlobals = lglobals
                        }
      )
-}


--------------------------------------------------------------------------------

setupArg ::
  SharedContext -> Sym ->
  IORef (Seq (ExtCns Term)) ->
  Crucible.TypeRepr tp ->
  IO (Crucible.RegEntry Sym tp)
setupArg sc sym ecRef tp =
  case Crucible.asBaseType tp of
    Crucible.AsBaseType btp ->
      do sc_tp <- Crucible.baseSCType sym sc btp
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

setupArgs ::
  SharedContext -> Sym -> Crucible.FnHandle init ret ->
  IO (Seq (ExtCns Term), Crucible.RegMap Sym init)
setupArgs sc sym fn =
  do ecRef  <- newIORef Seq.empty
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


{-
extractFromJVMCFG ::
  Options -> SharedContext -> CrucibleContext -> Crucible.AnyCFG JVM -> IO TypedTerm
extractFromJVMCFG opts sc cc (Crucible.AnyCFG cfg) =
  do let sym = cc^.ccBackend
     let h   = Crucible.cfgHandle cfg
     (ecs, args) <- setupArgs sc sym h
     let simCtx  = cc^.ccLLVMSimContext
     let globals = cc^.ccLLVMGlobals
     res <- runCFG simCtx globals h cfg args
     case res of
       Crucible.FinishedResult _ pr ->
         do gp <- getGlobalPair opts pr
            t <- Crucible.asSymExpr
                   (gp^.Crucible.gpValue)
                   (Crucible.toSC sym)
                   (fail $ unwords ["Unexpected return type:", show (Crucible.regType (gp^.Crucible.gpValue))])
            t' <- scAbstractExts sc (toList ecs) t
            mkTypedTerm sc t'
       Crucible.AbortedResult _ ar ->
         do let resultDoc = ppAbortedResult cc ar
            fail $ unlines [ "Symbolic execution failed."
                           , show resultDoc
                           ]
-}


--------------------------------------------------------------------------------

{-
crucible_jvm_extract :: BuiltinContext -> Options -> JavaClass -> String -> TopLevel TypedTerm
crucible_jvm_extract bic opts cls fn_name =
  setupCrucibleContext bic opts cls $ \cc ->
    case Map.lookup (fromString fn_name) (Crucible.cfgMap (cc^.ccLLVMModuleTrans)) of
      Nothing  -> fail $ unwords ["function", fn_name, "not found"]
      Just cfg -> io $ extractFromLLVMCFG opts (biSharedContext bic) cc cfg

crucible_jvm_cfg :: BuiltinContext -> Options -> JavaClass -> String -> TopLevel SAW_CFG
crucible_jvm_cfg bic opts cls fn_name =
  setupCrucibleContext bic opts cls $ \cc ->
    case Map.lookup (fromString fn_name) (Crucible.cfgMap (cc^.ccLLVMModuleTrans)) of
      Nothing  -> fail $ unwords ["function", fn_name, "not found"]
      Just cfg -> return (LLVM_CFG cfg)
-}

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

--diffMemTypes ::
--  Crucible.HasPtrWidth wptr =>
--  Crucible.MemType ->
--  Crucible.MemType ->
--  [([Maybe Int], Crucible.MemType, Crucible.MemType)]
--diffMemTypes x0 y0 =
--  let wptr :: Natural = fromIntegral (natValue ?ptrWidth) in
--  case (x0, y0) of
--    -- Special case; consider a one-element struct to be compatiable with
--    -- the type of its field
--    (Crucible.StructType x, _)
--      | V.length (Crucible.siFields x) == 1 -> diffMemTypes (Crucible.fiType (V.head (Crucible.siFields x))) y0
--    (_, Crucible.StructType y)
--      | V.length (Crucible.siFields y) == 1 -> diffMemTypes x0 (Crucible.fiType (V.head (Crucible.siFields y)))
--
--    (Crucible.IntType x, Crucible.IntType y) | x == y -> []
--    (Crucible.FloatType, Crucible.FloatType) -> []
--    (Crucible.DoubleType, Crucible.DoubleType) -> []
--    (Crucible.PtrType{}, Crucible.PtrType{}) -> []
--    (Crucible.IntType w, Crucible.PtrType{}) | w == wptr -> []
--    (Crucible.PtrType{}, Crucible.IntType w) | w == wptr -> []
--    (Crucible.ArrayType xn xt, Crucible.ArrayType yn yt)
--      | xn == yn ->
--        [ (Nothing : path, l , r) | (path, l, r) <- diffMemTypes xt yt ]
--    (Crucible.VecType xn xt, Crucible.VecType yn yt)
--      | xn == yn ->
--        [ (Nothing : path, l , r) | (path, l, r) <- diffMemTypes xt yt ]
--    (Crucible.StructType x, Crucible.StructType y)
--      | Crucible.siIsPacked x == Crucible.siIsPacked y
--        && V.length (Crucible.siFields x) == V.length (Crucible.siFields y) ->
--          let xts = Crucible.siFieldTypes x
--              yts = Crucible.siFieldTypes y
--          in diffMemTypesList 1 (V.toList (V.zip xts yts))
--    _ -> [([], x0, y0)]

--diffMemTypesList ::
--  Crucible.HasPtrWidth arch =>
--  Int ->
--  [(Crucible.MemType, Crucible.MemType)] ->
--  [([Maybe Int], Crucible.MemType, Crucible.MemType)]
--diffMemTypesList _ [] = []
--diffMemTypesList i ((x, y) : ts) =
--  [ (Just i : path, l , r) | (path, l, r) <- diffMemTypes x y ]
--  ++ diffMemTypesList (i+1) ts

--showMemTypeDiff :: ([Maybe Int], Crucible.MemType, Crucible.MemType) -> String
--showMemTypeDiff (path, l, r) = showPath path
--  where
--    showStep Nothing  = "element type"
--    showStep (Just i) = "field " ++ show i
--    showPath []       = ""
--    showPath [x]      = unlines [showStep x ++ ":", "  " ++ show l, "  " ++ show r]
--    showPath (x : xs) = showStep x ++ " -> " ++ showPath xs

---- | Succeed if the types have compatible memory layouts. Otherwise,
---- fail with a detailed message indicating how the types differ.
--checkMemTypeCompatibility ::
--  JavaType ->
--  JavaType ->
--  CrucibleSetup ()
--checkMemTypeCompatibility t1 t2 =
--  case diffMemTypes t1 t2 of
--    [] -> return ()
--    diffs ->
--      fail $ unlines $
--      ["types not memory-compatible:", show t1, show t2]
--      ++ map showMemTypeDiff diffs

--------------------------------------------------------------------------------
-- Setup builtins

getCrucibleContext :: JVMSetup CrucibleContext
getCrucibleContext = view csCrucibleContext <$> get

currentState :: Lens' CrucibleSetupState StateSpec
currentState f x = case x^.csPrePost of
  PreState  -> csMethodSpec (csPreState f) x
  PostState -> csMethodSpec (csPostState f) x

addPointsTo :: PointsTo -> JVMSetup ()
addPointsTo pt = currentState.csPointsTos %= (pt : )

addCondition :: SetupCondition
             -> JVMSetup ()
addCondition cond = currentState.csConditions %= (cond : )

-- | Returns logical type of actual type if it is an array or primitive
-- type, or an appropriately-sized bit vector for pointer types.
logicTypeOfActual :: SharedContext -> JavaType -> IO (Maybe Term)
logicTypeOfActual sc jty =
  case jty of
    JavaBoolean -> Just <$> scBoolType sc
    JavaByte    -> Just <$> scBitvector sc 8
    JavaChar    -> Just <$> scBitvector sc 16
    JavaShort   -> Just <$> scBitvector sc 16
    JavaInt     -> Just <$> scBitvector sc 32
    JavaLong    -> Just <$> scBitvector sc 64
    JavaFloat   -> Just <$> scApplyPrelude_Float sc
    JavaDouble  -> Just <$> scApplyPrelude_Double sc
    JavaArray len ety ->
      do mety' <- logicTypeOfActual sc ety
         case mety' of
           Just ety' -> do len' <- scNat sc (fromIntegral len)
                           Just <$> scVecType sc len' ety'
           Nothing   -> return Nothing
    JavaClass _ -> return Nothing

-- | Generate a fresh variable term. The name will be used when
-- pretty-printing the variable in debug output.
jvm_fresh_var ::
  BuiltinContext      {- ^ context          -} ->
  Options             {- ^ options          -} ->
  String              {- ^ variable name    -} ->
  JavaType            {- ^ variable type    -} ->
  JVMSetupM TypedTerm {- ^ fresh typed term -}
jvm_fresh_var bic _opts name jty =
  JVMSetupM $
  do cctx <- getCrucibleContext
     let sc = biSharedContext bic
     mty <- liftIO $ logicTypeOfActual sc jty
     case mty of
       Nothing -> fail $ "Unsupported type in jvm_fresh_var: " ++ show jty
       Just ty -> freshVariable sc name ty

-- | Allocate a fresh variable and record this allocation in the
-- setup state.
freshVariable ::
  SharedContext {- ^ shared context -} ->
  String        {- ^ variable name  -} ->
  Term          {- ^ variable type  -} ->
  JVMSetup TypedTerm
freshVariable sc name ty =
  do tt <- liftIO (mkTypedTerm sc =<< scFreshGlobal sc name ty)
     currentState . csFreshVars %= cons tt
     return tt


jvm_alloc_object ::
  BuiltinContext ->
  Options        ->
  String {- ^ class name -} ->
  JVMSetupM SetupValue
jvm_alloc_object _bic _opt cname = JVMSetupM $
  do loc <- toW4Loc "jvm_alloc_object" <$> lift getPosition
     n <- csVarCounter <<%= nextAllocIndex
     currentState.csAllocs.at n ?= (loc, JavaClass cname)
     return (SetupVar n)

jvm_alloc_array ::
  BuiltinContext ->
  Options        ->
  Int {- array size -} ->
  JavaType       ->
  JVMSetupM SetupValue
jvm_alloc_array _bic _opt len ety =
  JVMSetupM $
  do loc <- toW4Loc "jvm_alloc_array" <$> lift getPosition
     n <- csVarCounter <<%= nextAllocIndex
     currentState.csAllocs.at n ?= (loc, JavaArray len ety)
     return (SetupVar n)

jvm_field_is ::
  Bool {- ^ whether to check type compatibility -} ->
  BuiltinContext ->
  Options        ->
  SetupValue {- ^ object -} ->
  String     {- ^ field name -} ->
  SetupValue {- ^ field value -} ->
  JVMSetupM ()
jvm_field_is typed _bic _opt ptr fname val =
  JVMSetupM $
  do cc <- getCrucibleContext
     loc <- toW4Loc "jvm_field_is" <$> lift getPosition
     st <- get
     let rs = st^.csResolvedState
     if st^.csPrePost == PreState && testResolved ptr rs
       then fail "Multiple points-to preconditions on same pointer"
       else csResolvedState %= markResolved ptr
     let env = csAllocations (st^.csMethodSpec)
         nameEnv = csTypeNames (st^.csMethodSpec)
     ptrTy <- typeOfSetupValue cc env nameEnv ptr
     valTy <- typeOfSetupValue cc env nameEnv val
     --when typed (checkMemTypeCompatibility lhsTy valTy)
     addPointsTo (PointsToField loc ptr fname val)

jvm_elem_is ::
  Bool {- ^ whether to check type compatibility -} ->
  BuiltinContext ->
  Options        ->
  SetupValue {- ^ array -} ->
  Int        {- ^ index -} ->
  SetupValue {- ^ element value -} ->
  JVMSetupM ()
jvm_elem_is typed _bic _opt ptr idx val =
  JVMSetupM $
  do cc <- getCrucibleContext
     loc <- toW4Loc "jvm_elem_is" <$> lift getPosition
     st <- get
     let rs = st^.csResolvedState
     if st^.csPrePost == PreState && testResolved ptr rs
       then fail "Multiple points-to preconditions on same pointer"
       else csResolvedState %= markResolved ptr
     let env = csAllocations (st^.csMethodSpec)
         nameEnv = csTypeNames (st^.csMethodSpec)
     --ptrTy <- typeOfSetupValue cc env nameEnv ptr
     --lhsTy <- case ptrTy of
     --  Crucible.PtrType symTy ->
     --    case Crucible.asMemType symTy of
     --      Just lhsTy -> return lhsTy
     --      Nothing -> fail $ "lhs not a valid pointer type: " ++ show ptrTy
     --  _ -> fail $ "lhs not a pointer type: " ++ show ptrTy
     --valTy <- typeOfSetupValue cc env nameEnv val
     --when typed (checkMemTypeCompatibility lhsTy valTy)
     addPointsTo (PointsToElem loc ptr idx val)

toW4Loc :: Text.Text -> SS.Pos -> W4.ProgramLoc
toW4Loc fnm SS.Unknown          = W4.mkProgramLoc (W4.functionNameFromText fnm) W4.InternalPos
toW4Loc fnm SS.PosREPL          = W4.mkProgramLoc (W4.functionNameFromText (fnm <> " <REPL>")) W4.InternalPos
toW4Loc fnm (SS.PosInternal nm) = W4.mkProgramLoc (W4.functionNameFromText (fnm <> " " <> fromString nm)) W4.InternalPos
toW4Loc fnm (SS.Range file sl sc _el _ec) = W4.mkProgramLoc (W4.functionNameFromText fnm) (W4.SourcePos (fromString file) sl sc)

{-
_jvm_equal ::
  BuiltinContext ->
  Options        ->
  SetupValue     ->
  SetupValue     ->
  JVMSetupM ()
_jvm_equal _bic _opt val1 val2 = JVMSetupM $
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
     loc <- toW4Loc "jvm_equal" <$> lift getPosition
     addCondition (SetupCond_Equal loc val1 val2)
-}

jvm_precond :: TypedTerm -> JVMSetupM ()
jvm_precond p =
  JVMSetupM $
  do st <- get
     when (st^.csPrePost == PostState) $
       fail "attempt to use `jvm_precond` in post state"
     loc <- toW4Loc "jvm_precond" <$> lift getPosition
     addCondition (SetupCond_Pred loc p)

jvm_postcond :: TypedTerm -> JVMSetupM ()
jvm_postcond p =
  JVMSetupM $
  do st <- get
     when (st^.csPrePost == PreState) $
       fail "attempt to use `jvm_postcond` in pre state"
     loc <- toW4Loc "jvm_postcond" <$> lift getPosition
     addCondition (SetupCond_Pred loc p)

jvm_execute_func :: BuiltinContext -> Options -> [SetupValue] -> JVMSetupM ()
jvm_execute_func _bic _opt args =
  JVMSetupM $
  do tps <- use (csMethodSpec.csArgs)
     csPrePost .= PostState
     csMethodSpec.csArgBindings .= Map.fromList [ (i, (t,a))
                                                | i <- [0..]
                                                | a <- args
                                                | t <- tps
                                                ]

jvm_return ::
  BuiltinContext -> Options -> SetupValue -> JVMSetupM ()
jvm_return _bic _opt retval =
  JVMSetupM $
  do ret <- use (csMethodSpec.csRetValue)
     case ret of
       Just _ -> fail "jvm_return: duplicate return value specification"
       Nothing -> csMethodSpec.csRetValue .= Just retval


--------------------------------------------------------------------------------

-- | Sort a list of things and group them into equivalence classes.
groupOn ::
  Ord b =>
  (a -> b) {- ^ equivalence class projection -} ->
  [a] -> [[a]]
groupOn f = groupBy ((==) `on` f) . sortBy (compare `on` f)
