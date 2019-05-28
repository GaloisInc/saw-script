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
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wno-orphans #-}

{-# OPTIONS_GHC -fno-warn-unused-local-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}


module SAWScript.JVM.CrucibleBuiltins
    ( crucible_jvm_verify
    , crucible_jvm_unsafe_assume_spec
    , jvm_return
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
import qualified Control.Monad.State.Strict as Strict
import           Data.Foldable (for_)
import           Data.Function
import           Data.IORef
import           Data.List
import           Data.Monoid ((<>))
import           Data.String
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import qualified Data.Vector as V
import           System.IO

import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>))

-- jvm-verifier
-- TODO: transition to Lang.JVM.Codebase from crucible-jvm
import qualified Verifier.Java.Codebase as CB

-- cryptol
import qualified Cryptol.TypeCheck.Type as Cryptol

-- cryptol-verifier
import Verifier.SAW.Cryptol (importType, emptyEnv)

-- what4
import qualified What4.FunctionName as W4
import qualified What4.Partial as W4
import qualified What4.ProgramLoc as W4
import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4

-- jvm-parser
import qualified Language.JVM.Parser as J
import qualified Language.JVM.Common as J (dotsToSlashes)

-- crucible
import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Backend.SAWCore as Crucible
import qualified Lang.Crucible.CFG.Core as Crucible (TypeRepr(..))
import qualified Lang.Crucible.FunctionHandle as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Simulator.GlobalState as Crucible
import qualified Lang.Crucible.Simulator.SimError as Crucible

-- crucible-jvm
import qualified Lang.Crucible.JVM as CJ

-- parameterized-utils
import           Data.Parameterized.Classes
import           Data.Parameterized.Nonce
import qualified Data.Parameterized.Context as Ctx

import Verifier.SAW.FiniteValue (ppFirstOrderValue)
import Verifier.SAW.SharedTerm
import Verifier.SAW.Recognizer
import Verifier.SAW.TypedTerm

import SAWScript.Proof
import SAWScript.Prover.SolverStats
import SAWScript.TopLevel
import SAWScript.Value
import SAWScript.Utils as SS
import SAWScript.Options
import SAWScript.CrucibleBuiltinsJVM (prepareClassTopLevel)

import SAWScript.JavaExpr (JavaType(..))

import SAWScript.JVM.CrucibleMethodSpecIR
import SAWScript.JVM.CrucibleOverride
import SAWScript.JVM.CrucibleResolveSetupValue
import SAWScript.CrucibleBuiltinsJVM ()

ppAbortedResult :: CrucibleContext
                -> Crucible.AbortedResult Sym a
                -> Doc
ppAbortedResult _ (Crucible.AbortedExec Crucible.InfeasibleBranch _) =
  text "Infeasible branch"
ppAbortedResult cc (Crucible.AbortedExec abt gp) = do
  Crucible.ppAbortExecReason abt -- <$$> ppGlobalPair cc gp
ppAbortedResult _ (Crucible.AbortedBranch _ _ _) =
  text "Aborted branch"
ppAbortedResult _ (Crucible.AbortedExit ec) =
  text "Branch exited:" <+> text (show ec)

-- FIXME: We need a better way to identify a set of class names to
-- load. This function has two problems: First, unless we put in a
-- bunch of hard-wired exclusions, we often end up trying to load
-- classes for which we don't have any parseable bytecode. Second, the
-- number of classes we load is way too large, and the classes take a
-- long time to parse and translate.

allClassRefs :: CB.Codebase -> J.ClassName -> IO (Set J.ClassName)
allClassRefs cb c0 = go seen0 [c0]
  where
    seen0 = Set.fromList CJ.initClasses
    go seen [] = return seen
    go seen (c : cs) =
      do -- putStrLn $ "allClassRefs: " ++ show (J.unClassName c)
         cls <- CJ.findClass cb (J.unClassName c)
         let refs = Set.filter (not . excludedClassName) (CJ.classRefs cls)
         -- putStrLn $ " -> " ++ show (Set.toList refs)
         let seen' = Set.union seen refs
         let next = Set.toList (Set.difference refs seen)
         go seen' (next ++ cs)

excludedClassName :: J.ClassName -> Bool
excludedClassName cname
  | "java/time/"             `isPrefixOf` s = True
  | "javax/"                 `isPrefixOf` s = True
  | "java/lang/invoke/"      `isPrefixOf` s = True
  | "java/util/stream/"      `isPrefixOf` s = True
  | "java/util/Collections$" `isPrefixOf` s = True
  | "sun/"                   `isPrefixOf` s = True
  | otherwise = Set.member cname excludedRefs
  where s = J.unClassName cname

-- hack to fix ecdsa proof
excludedRefs :: Set J.ClassName
excludedRefs = Set.fromList
  [ "java/util/Comparator"
  , "java/util/Arrays"
  , "java/lang/reflect/AccessibleObject"
  , "java/lang/reflect/AnnotatedElement"
  , "java/lang/invoke/SerializedLambda"
  , "java/lang/Package"
  , "java/util/TreeMap$EntrySpliterator"
  , "java/lang/invoke/MethodHandleInfo"
  ]

crucible_jvm_verify ::
  BuiltinContext ->
  Options ->
  J.Class ->
  String {- ^ method name -} ->
  [CrucibleMethodSpecIR] {- ^ overrides -} ->
  Bool {- ^ path sat checking -} ->
  JVMSetupM () ->
  ProofScript SatResult ->
  TopLevel CrucibleMethodSpecIR
crucible_jvm_verify bic opts cls nm lemmas checkSat setup tactic =
  do cb <- getJavaCodebase
     -- allocate all of the handles/static vars that are referenced
     -- (directly or indirectly) by this class
     allRefs <- io $ Set.toList <$> allClassRefs cb (J.className cls)
     let refs = CJ.initClasses ++ allRefs -- ++ superRefs
     mapM_ (prepareClassTopLevel bic . J.unClassName) refs

     cc <- setupCrucibleContext bic opts cls
     let sym = cc^.ccBackend
     let jc = cc^.ccJVMContext

     pos <- getPosition
     let loc = toW4Loc "_SAW_verify_prestate" pos

     (cls', method) <- io $ findMethod cb pos nm cls -- TODO: switch to crucible-jvm version
     let st0 = initialCrucibleSetupState cc method loc

     -- execute commands of the method spec
     io $ W4.setCurrentProgramLoc sym loc
     methodSpec <- view csMethodSpec <$> execStateT (runJVMSetupM setup) st0

     -- construct the dynamic class table and declare static fields
     globals1 <- liftIO $ setupGlobalState sym jc

     -- construct the initial state for verifications
     (args, assumes, env, globals2) <- io $ verifyPrestate cc methodSpec globals1

     -- save initial path conditions
     frameIdent <- io $ Crucible.pushAssumptionFrame sym

     -- run the symbolic execution
     top_loc <- toW4Loc "crucible_jvm_verify" <$> getPosition
     (ret, globals3) <-
       io $ verifySimulate opts cc methodSpec args assumes top_loc lemmas globals2 checkSat

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
  J.Class          ->
  String          {- ^ Name of the method -} ->
  JVMSetupM () {- ^ Boundary specification -} ->
  TopLevel CrucibleMethodSpecIR
crucible_jvm_unsafe_assume_spec bic opts cls nm setup =
  do cc <- setupCrucibleContext bic opts cls
     cb <- getJavaCodebase
     -- cls' is either cls or a subclass of cls
     pos <- getPosition
     (cls', method) <- io $ findMethod cb pos nm cls -- TODO: switch to crucible-jvm version
     let loc = toW4Loc "_SAW_assume_spec" pos
     let st0 = initialCrucibleSetupState cc method loc
     (view csMethodSpec) <$> execStateT (runJVMSetupM setup) st0

verifyObligations ::
  CrucibleContext ->
  CrucibleMethodSpecIR ->
  ProofScript SatResult ->
  [Crucible.LabeledPred Term Crucible.AssumptionReason] ->
  [(String, Term)] ->
  TopLevel SolverStats
verifyObligations cc mspec tactic assumes asserts =
  do let sym = cc^.ccBackend
     st <- io $ readIORef $ W4.sbStateManager sym
     let sc = Crucible.saw_ctx st
     assume <- io $ scAndList sc (toListOf (folded . Crucible.labeledPred) assumes)
     let nm = mspec^.csMethodName
     stats <- forM (zip [(0::Int)..] asserts) $ \(n, (msg, assert)) -> do
       goal   <- io $ scImplies sc assume assert
       goal'  <- io $ scGeneralizeExts sc (getAllExts goal) =<< scEqTrue sc goal
       let goalname = concat [nm, " (", takeWhile (/= '\n') msg, ")"]
           proofgoal = ProofGoal n "vc" goalname goal'
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
  IO ([(J.Type, JVMVal)],
      [Crucible.LabeledPred Term Crucible.AssumptionReason],
      Map AllocIndex JVMRefVal,
      Crucible.SymGlobalState Sym)
verifyPrestate cc mspec globals0 =
  do let sym = cc^.ccBackend
     let jc = cc^.ccJVMContext
     let preallocs = mspec^.csPreState.csAllocs
     let tyenv = csAllocations mspec
     let nameEnv = mspec^.csPreState.csVarTypeNames

     let prestateLoc = W4.mkProgramLoc "_SAW_verify_prestate" W4.InternalPos
     W4.setCurrentProgramLoc sym prestateLoc

     --let cvar = CJ.dynamicClassTable (cc^.ccJVMContext)
     --let Just mem = Crucible.lookupGlobal lvar globals

     -- Allocate objects in memory for each 'jvm_alloc'
     (env, globals1) <- runStateT (traverse (doAlloc cc . snd) preallocs) globals0

     globals2 <- setupPrePointsTos mspec cc env (mspec^.csPreState.csPointsTos) globals1
     cs <- setupPrestateConditions mspec cc env (mspec^.csPreState.csConditions)
     args <- resolveArguments cc mspec env

     -- Check the type of the return setup value
     case (mspec^.csRetValue, mspec^.csRet) of
       (Just _, Nothing) ->
            fail $ unlines
              [ "Could not resolve return type of " ++ mspec^.csMethodName
              , "Raw type: " ++ show (mspec^.csRet)
              ]
       (Just sv, Just retTy) ->
         do retTy' <- typeOfSetupValue cc tyenv nameEnv sv
            b <- liftIO $ checkRegisterCompatibility retTy retTy'
            unless b $ fail $ unlines
              [ "Incompatible types for return value when verifying " ++ mspec^.csMethodName
              , "Expected: " ++ show retTy
              , "but given value of type: " ++ show retTy'
              ]
       (Nothing, _) -> return ()

     return (args, cs, env, globals2)

-- | Check two Types for register compatibility.
checkRegisterCompatibility :: J.Type -> J.Type -> IO Bool
checkRegisterCompatibility mt mt' =
  return (storageType mt == storageType mt')

data StorageType = STInt | STLong | STFloat | STDouble | STRef
  deriving Eq

storageType :: J.Type -> StorageType
storageType ty =
  case ty of
    J.BooleanType -> STInt
    J.ByteType    -> STInt
    J.CharType    -> STInt
    J.ShortType   -> STInt
    J.IntType     -> STInt
    J.LongType    -> STLong
    J.FloatType   -> STFloat
    J.DoubleType  -> STDouble
    J.ArrayType{} -> STRef
    J.ClassType{} -> STRef

resolveArguments ::
  CrucibleContext          ->
  CrucibleMethodSpecIR     ->
  Map AllocIndex JVMRefVal ->
  IO [(J.Type, JVMVal)]
resolveArguments cc mspec env = mapM resolveArg [0..(nArgs-1)]
  where
    nArgs = toInteger (length (mspec^.csArgs))
    tyenv = csAllocations mspec
    nameEnv = mspec^.csPreState.csVarTypeNames
    nm = mspec^.csMethodName

    checkArgTy i mt mt' =
      do b <- checkRegisterCompatibility mt mt'
         unless b $
           fail $ unlines [ "Type mismatch in argument " ++ show i ++ " when verifying " ++ show nm
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
  CrucibleMethodSpecIR     ->
  CrucibleContext          ->
  Map AllocIndex JVMRefVal ->
  [PointsTo]               ->
  Crucible.SymGlobalState Sym ->
  IO (Crucible.SymGlobalState Sym)
setupPrePointsTos mspec cc env pts mem0 = foldM doPointsTo mem0 pts
  where
    sym = cc^.ccBackend
    tyenv = csAllocations mspec
    nameEnv = mspec^.csPreState.csVarTypeNames

    resolveJVMRefVal :: SetupValue -> IO JVMRefVal
    resolveJVMRefVal lhs =
      do let msg = Crucible.GenericSimError "Non-reference value found in points-to assertion"
         lhs' <- resolveSetupVal cc env tyenv nameEnv lhs
         case lhs' of
           RVal ref -> return ref
           _ -> liftIO $ Crucible.addFailedAssertion sym msg

    doPointsTo :: Crucible.SymGlobalState Sym -> PointsTo -> IO (Crucible.SymGlobalState Sym)
    doPointsTo mem pt =
      case pt of
        PointsToField _loc lhs fld rhs ->
          do lhs' <- resolveJVMRefVal lhs
             rhs' <- resolveSetupVal cc env tyenv nameEnv rhs
             CJ.doFieldStore sym mem lhs' fld (injectJVMVal sym rhs')
        PointsToElem _loc lhs idx rhs ->
          do lhs' <- resolveJVMRefVal lhs
             rhs' <- resolveSetupVal cc env tyenv nameEnv rhs
             CJ.doArrayStore sym mem lhs' idx (injectJVMVal sym rhs')

-- | Collects boolean terms that should be assumed to be true.
setupPrestateConditions ::
  CrucibleMethodSpecIR        ->
  CrucibleContext             ->
  Map AllocIndex JVMRefVal    ->
  [SetupCondition]            ->
  IO [Crucible.LabeledPred Term Crucible.AssumptionReason]
setupPrestateConditions mspec cc env = aux []
  where
    tyenv   = csAllocations mspec
    nameEnv = mspec^.csPreState.csVarTypeNames

    aux acc [] = return acc

    aux acc (SetupCond_Equal loc val1 val2 : xs) =
      do val1' <- resolveSetupVal cc env tyenv nameEnv val1
         val2' <- resolveSetupVal cc env tyenv nameEnv val2
         t     <- assertEqualVals cc val1' val2'
         let lp = Crucible.LabeledPred t (Crucible.AssumptionReason loc "equality precondition")
         aux (lp:acc) xs

    aux acc (SetupCond_Pred loc tm : xs) =
      let lp = Crucible.LabeledPred (ttTerm tm) (Crucible.AssumptionReason loc "precondition") in
      aux (lp:acc) xs

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

doAlloc ::
  CrucibleContext ->
  Allocation ->
  StateT (Crucible.SymGlobalState Sym) IO JVMRefVal
doAlloc cc alloc =
  case alloc of
    AllocObject cname -> StateT (CJ.doAllocateObject sym halloc jc cname)
    AllocArray len ty -> StateT (CJ.doAllocateArray sym halloc jc len ty)
  where
    sym = cc^.ccBackend
    halloc = cc^.ccHandleAllocator
    jc = cc^.ccJVMContext

--------------------------------------------------------------------------------

registerOverride ::
  Options ->
  CrucibleContext ->
  Crucible.SimContext (Crucible.SAWCruciblePersonality Sym) Sym CJ.JVM ->
  W4.ProgramLoc ->
  [CrucibleMethodSpecIR] ->
  Crucible.OverrideSim (Crucible.SAWCruciblePersonality Sym) Sym CJ.JVM rtp args ret ()
registerOverride opts cc _ctx top_loc cs =
  do let sym = cc^.ccBackend
     let cb = cc^.ccCodebase
     let jc = cc^.ccJVMContext
     let c0 = head cs
     let cname = c0^.csClassName
     let mname = c0^.csMethodName
     let pos = PosInternal "registerOverride"
     sc <- Crucible.saw_ctx <$> liftIO (readIORef (W4.sbStateManager sym))

     (mcls, meth) <- liftIO $ findMethod cb pos mname =<< lookupClass cb pos cname
     mhandle <- liftIO $ CJ.findMethodHandle jc mcls meth
     case mhandle of
       -- LLVMHandleInfo constructor has two existential type arguments,
       -- which are bound here. h :: FnHandle args' ret'
       CJ.JVMHandleInfo _ h ->
         do let retType = Crucible.handleReturnType h
            Crucible.bindFnHandle h
              $ Crucible.UseOverride
              $ Crucible.mkOverride'
                  (Crucible.handleName h)
                  retType
                  (methodSpecHandler opts sc cc top_loc cs retType)


--------------------------------------------------------------------------------

verifySimulate ::
  Options                       ->
  CrucibleContext               ->
  CrucibleMethodSpecIR          ->
  [(a, JVMVal)]                 ->
  [Crucible.LabeledPred Term Crucible.AssumptionReason] ->
  W4.ProgramLoc                 ->
  [CrucibleMethodSpecIR]        ->
  Crucible.SymGlobalState Sym   ->
  Bool {- ^ path sat checking -} ->
  IO (Maybe (J.Type, JVMVal), Crucible.SymGlobalState Sym)
verifySimulate opts cc mspec args assumes top_loc lemmas globals checkSat =
  do let jc = cc^.ccJVMContext
     let cb = cc^.ccCodebase
     let sym = cc^.ccBackend
     let cls = cc^.ccJVMClass
     let cname = J.className cls
     let mname = mspec^.csMethodName
     let verbosity = simVerbose opts
     let personality = Crucible.SAWCruciblePersonality
     let pos = PosInternal "verifySimulate"
     let halloc = cc^.ccHandleAllocator

     -- executeCrucibleJVM

     when (verbosity > 2) $
          putStrLn "starting executeCrucibleJVM"

     CJ.setSimulatorVerbosity verbosity sym

     (mcls, meth) <- findMethod cb pos mname =<< lookupClass cb pos cname
     --when (not (J.methodIsStatic meth)) $ do
     --  fail $ unlines [ "Crucible can only extract static methods" ]

     (CJ.JVMHandleInfo _ h) <- CJ.findMethodHandle jc mcls meth
     regmap <- prepareArgs (Crucible.handleArgTypes h) (map snd args)
     res <-
       do let feats = []
          let simctx = CJ.jvmSimContext sym halloc stdout jc verbosity Crucible.SAWCruciblePersonality
          let simSt = Crucible.InitialState simctx globals Crucible.defaultAbortHandler
          let fnCall = Crucible.regValue <$> Crucible.callFnVal (Crucible.HandleFnVal h) regmap
          let overrideSim =
                do liftIO $ putStrLn "registering standard overrides"
                   _ <- Strict.runStateT (mapM_ CJ.register_jvm_override CJ.stdOverrides) jc
                   liftIO $ putStrLn "registering user-provided overrides"
                   mapM_ (registerOverride opts cc simctx top_loc) (groupOn (view csMethodName) lemmas)
                   liftIO $ putStrLn "registering assumptions"
                   liftIO $ do
                     preds <- (traverse . Crucible.labeledPred) (resolveSAWPred cc) assumes
                     Crucible.addAssumptions sym (Seq.fromList preds)
                   liftIO $ putStrLn "simulating function"
                   fnCall
          Crucible.executeCrucible (map Crucible.genericToExecutionFeature feats)
            (simSt (Crucible.runOverrideSim (Crucible.handleReturnType h) overrideSim))

     case res of
       Crucible.FinishedResult _ pr ->
         do Crucible.GlobalPair retval globals1 <-
              case pr of
                Crucible.TotalRes gp -> return gp
                Crucible.PartialRes _ gp _ ->
                  do printOutLn opts Info "Symbolic simulation completed with side conditions."
                     return gp
            let ret_ty = mspec^.csRet
            retval' <-
              case ret_ty of
                Nothing -> return Nothing
                Just ret_mt ->
                  case retval of
                    Crucible.RegEntry ty val ->
                      case decodeJVMVal ret_mt (Crucible.AnyValue ty val) of
                        Nothing -> error $ "FIXME: Unsupported return type: " ++ show ret_ty
                        Just v -> return (Just (ret_mt, v))
            return (retval', globals1)

       Crucible.AbortedResult _ ar ->
         do let resultDoc = ppAbortedResult cc ar
            fail $ unlines [ "Symbolic execution failed."
                           , show resultDoc
                           ]

  where
    prepareArg :: forall tp. Crucible.TypeRepr tp -> JVMVal -> IO (Crucible.RegValue Sym tp)
    prepareArg ty v =
      case v of
        RVal x -> case testEquality ty CJ.refRepr  of Just Refl -> return x; _ -> fail "argument type mismatch"
        IVal x -> case testEquality ty CJ.intRepr  of Just Refl -> return x; _ -> fail "argument type mismatch"
        LVal x -> case testEquality ty CJ.longRepr of Just Refl -> return x; _ -> fail "argument type mismatch"

    prepareArgs ::
      forall xs.
      Ctx.Assignment Crucible.TypeRepr xs ->
      [JVMVal] ->
      IO (Crucible.RegMap Sym xs)
    prepareArgs ctx xs | length xs /= Ctx.sizeInt (Ctx.size ctx) =
      fail $ "Wrong number of arguments: found " ++ show xs ++ ", expected " ++ show ctx --(Ctx.sizeInt (Ctx.size ctx))
    prepareArgs ctx xs =
      Crucible.RegMap <$>
      Ctx.traverseWithIndex (\idx tr ->
        do v <- prepareArg tr (xs !! Ctx.indexVal idx)
           return (Crucible.RegEntry tr v))
      ctx

-- | Build a conjunction from a list of boolean terms.
scAndList :: SharedContext -> [Term] -> IO Term
scAndList sc = conj . filter nontrivial
  where
    nontrivial x = asBool x /= Just True
    conj [] = scBool sc True
    conj (x : xs) = foldM (scAnd sc) x xs

--------------------------------------------------------------------------------

verifyPoststate ::
  Options                           {- ^ saw script debug and print options           -} ->
  SharedContext                     {- ^ saw core context                             -} ->
  CrucibleContext                   {- ^ crucible context                             -} ->
  CrucibleMethodSpecIR              {- ^ specification                                -} ->
  Map AllocIndex JVMRefVal          {- ^ allocation substitution                      -} ->
  Crucible.SymGlobalState Sym       {- ^ global variables                             -} ->
  Maybe (J.Type, JVMVal)            {- ^ optional return value                        -} ->
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

setupCrucibleContext :: BuiltinContext -> Options -> J.Class -> TopLevel CrucibleContext
setupCrucibleContext bic opts jclass =
  do halloc <- getHandleAlloc
     jc <- getJVMTrans
     cb <- getJavaCodebase
     let sc  = biSharedContext bic
     let gen = globalNonceGenerator
     sym <- io $ Crucible.newSAWCoreBackend sc gen
     io $ CJ.setSimulatorVerbosity (simVerbose opts) sym
     return CrucibleContext { _ccJVMClass = jclass
                            , _ccCodebase = cb
                            , _ccBackend = sym
                            , _ccJVMContext = jc
                            , _ccHandleAllocator = halloc
                            }

--------------------------------------------------------------------------------

-- | Construct the dynamic class table, and also declare all static
-- fields (leaving them with uninitialized contents).
setupGlobalState :: Sym -> CJ.JVMContext -> IO (Crucible.SymGlobalState Sym)
setupGlobalState sym jc =
  do classTab <- setupDynamicClassTable sym jc
     let classTabVar = CJ.dynamicClassTable jc
     let globals0 = Crucible.insertGlobal classTabVar classTab Crucible.emptyGlobals
     let declareGlobal var = Crucible.insertGlobal var CJ.unassignedJVMValue
     return $ foldr declareGlobal globals0 (Map.elems (CJ.staticFields jc))

setupDynamicClassTable :: Sym -> CJ.JVMContext -> IO (Crucible.RegValue Sym CJ.JVMClassTableType)
setupDynamicClassTable sym jc = foldM addClass Map.empty (Map.assocs (CJ.classTable jc))
  where
    addClass ::
      Crucible.RegValue Sym CJ.JVMClassTableType ->
      (J.ClassName, J.Class) ->
      IO (Crucible.RegValue Sym CJ.JVMClassTableType)
    addClass tab (cname, cls) =
      do cls' <- setupClass cls
         return $ Map.insert (CJ.classNameText cname) (W4.justPartExpr sym cls') tab

    setupClass :: J.Class -> IO (Crucible.RegValue Sym CJ.JVMClassType)
    setupClass cls =
      do let cname = J.className cls
         name <- W4.stringLit sym (CJ.classNameText (J.className cls))
         status <- W4.bvLit sym knownRepr 0
         super <-
           case J.superClass cls of
             Nothing -> return W4.Unassigned
             Just cname' ->
               case Map.lookup cname' (CJ.classTable jc) of
                 Nothing -> return W4.Unassigned -- this should never happen
                 Just cls' -> W4.justPartExpr sym <$> setupClass cls'
         let methods = foldr (addMethod cname) Map.empty (J.classMethods cls)
         interfaces <- V.fromList <$> traverse (W4.stringLit sym . CJ.classNameText) (J.classInterfaces cls)
         return $
           Crucible.RolledType $
           Ctx.Empty
           Ctx.:> Crucible.RV name
           Ctx.:> Crucible.RV status
           Ctx.:> Crucible.RV super
           Ctx.:> Crucible.RV methods
           Ctx.:> Crucible.RV interfaces

    addMethod ::
      J.ClassName ->
      J.Method ->
      Crucible.RegValue Sym CJ.JVMMethodTableType ->
      Crucible.RegValue Sym CJ.JVMMethodTableType
    addMethod cname m tab =
      case Map.lookup (cname, J.methodKey m) (CJ.methodHandles jc) of
        Nothing -> tab -- should never happen
        Just (CJ.JVMHandleInfo key handle) ->
          Map.insert (CJ.methodKeyText key) (W4.justPartExpr sym v) tab
          where v = Crucible.AnyValue (Crucible.handleType handle) (Crucible.HandleFnVal handle)

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

-- | Returns Cryptol type of actual type if it is an array or
-- primitive type.
cryptolTypeOfActual :: JavaType -> Maybe Cryptol.Type
cryptolTypeOfActual jty =
  case jty of
    JavaBoolean   -> Just Cryptol.tBit
    JavaByte      -> Just $ Cryptol.tWord (Cryptol.tNum (8 :: Integer))
    JavaChar      -> Just $ Cryptol.tWord (Cryptol.tNum (16 :: Integer))
    JavaShort     -> Just $ Cryptol.tWord (Cryptol.tNum (16 :: Integer))
    JavaInt       -> Just $ Cryptol.tWord (Cryptol.tNum (32 :: Integer))
    JavaLong      -> Just $ Cryptol.tWord (Cryptol.tNum (64 :: Integer))
    JavaFloat     -> Nothing
    JavaDouble    -> Nothing
    JavaArray n t -> Cryptol.tSeq (Cryptol.tNum n) <$> cryptolTypeOfActual t
    JavaClass _   -> Nothing

parseClassName :: String -> J.ClassName
parseClassName cname = J.mkClassName (J.dotsToSlashes cname)

typeOfJavaType :: JavaType -> J.Type
typeOfJavaType jty =
  case jty of
    JavaBoolean   -> J.BooleanType
    JavaByte      -> J.ByteType
    JavaChar      -> J.CharType
    JavaShort     -> J.ShortType
    JavaInt       -> J.IntType
    JavaLong      -> J.IntType
    JavaFloat     -> J.FloatType
    JavaDouble    -> J.DoubleType
    JavaArray _ t -> J.ArrayType (typeOfJavaType t)
    JavaClass c   -> J.ClassType (parseClassName c)

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
     case cryptolTypeOfActual jty of
       Nothing -> fail $ "Unsupported type in jvm_fresh_var: " ++ show jty
       Just ty -> freshVariable sc name ty

-- | Allocate a fresh variable and record this allocation in the
-- setup state.
freshVariable ::
  SharedContext {- ^ shared context -} ->
  String        {- ^ variable name  -} ->
  Cryptol.Type  {- ^ variable type  -} ->
  JVMSetup TypedTerm
freshVariable sc name cty =
  do let schema = Cryptol.Forall [] [] cty
     ty <- liftIO $ importType sc emptyEnv cty
     var <- liftIO $ scFreshGlobal sc name ty
     let tt = TypedTerm schema var
     currentState . csFreshVars %= cons tt
     return tt


jvm_alloc_object ::
  BuiltinContext ->
  Options        ->
  String {- ^ class name -} ->
  JVMSetupM SetupValue
jvm_alloc_object _bic _opt cname =
  JVMSetupM $
  do loc <- toW4Loc "jvm_alloc_object" <$> lift getPosition
     n <- csVarCounter <<%= nextAllocIndex
     currentState.csAllocs.at n ?= (loc, AllocObject (parseClassName cname))
     return (SetupVar n)

jvm_alloc_array ::
  BuiltinContext       ->
  Options              ->
  Int {- array size -} ->
  JavaType             ->
  JVMSetupM SetupValue
jvm_alloc_array _bic _opt len ety =
  JVMSetupM $
  do loc <- toW4Loc "jvm_alloc_array" <$> lift getPosition
     n <- csVarCounter <<%= nextAllocIndex
     currentState.csAllocs.at n ?= (loc, AllocArray len (typeOfJavaType ety))
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
     let path = Left fname
     if st^.csPrePost == PreState && testResolved ptr path rs
       then fail $ "Multiple points-to preconditions on same pointer (field " ++ fname ++ ")"
       else csResolvedState %= markResolved ptr path
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
     let path = Right idx
     if st^.csPrePost == PreState && testResolved ptr path rs
       then fail "Multiple points-to preconditions on same pointer"
       else csResolvedState %= markResolved ptr path
     let env = csAllocations (st^.csMethodSpec)
         nameEnv = csTypeNames (st^.csMethodSpec)
     addPointsTo (PointsToElem loc ptr idx val)

toW4Loc :: Text.Text -> SS.Pos -> W4.ProgramLoc
toW4Loc fnm SS.Unknown          = W4.mkProgramLoc (W4.functionNameFromText fnm) W4.InternalPos
toW4Loc fnm SS.PosREPL          = W4.mkProgramLoc (W4.functionNameFromText (fnm <> " <REPL>")) W4.InternalPos
toW4Loc fnm (SS.PosInternal nm) = W4.mkProgramLoc (W4.functionNameFromText (fnm <> " " <> fromString nm)) W4.InternalPos
toW4Loc fnm (SS.Range file sl sc _el _ec) = W4.mkProgramLoc (W4.functionNameFromText fnm) (W4.SourcePos (fromString file) sl sc)

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
