{- |
Module      : SAWScript.Crucible.JVM.Builtins
Description : Implementations of crucible-jvm-related SAW-Script primitives.
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

module SAWScript.Crucible.JVM.Builtins
    ( jvm_verify
    , jvm_unsafe_assume_spec
    , jvm_return
    , jvm_execute_func
    , jvm_postcond
    , jvm_precond
    , jvm_field_is
    , jvm_static_field_is
    , jvm_elem_is
    , jvm_array_is
    , jvm_fresh_var
    , jvm_alloc_object
    , jvm_alloc_array
    ) where

import           Control.Lens

import qualified Control.Monad.Catch as X
import           Control.Monad.State
import qualified Control.Monad.State.Strict as Strict
import           Control.Monad.Trans.Except (runExceptT)
import qualified Data.BitVector.Sized as BV
import           Data.Foldable (for_)
import           Data.Function
import           Data.List
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import qualified Data.Vector as V
import           Data.Void (absurd)
import           Prettyprinter
import           System.IO

-- cryptol
import qualified Cryptol.Eval.Type as Cryptol (evalValType)
import qualified Cryptol.TypeCheck.Type as Cryptol
import qualified Cryptol.Utils.PP as Cryptol (pp)

-- what4
import qualified What4.Partial as W4
import qualified What4.ProgramLoc as W4
import qualified What4.Interface as W4
import qualified What4.Utils.StringLiteral as W4S

-- jvm-parser
import qualified Language.JVM.Parser as J
import qualified Language.JVM.Common as J (dotsToSlashes)

-- crucible
import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.CFG.Core as Crucible (TypeRepr(..))
import qualified Lang.Crucible.FunctionHandle as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Simulator.GlobalState as Crucible
import qualified Lang.Crucible.Simulator.SimError as Crucible

-- crucible-jvm
import qualified Lang.JVM.Codebase as CB
import qualified Lang.Crucible.JVM as CJ

-- parameterized-utils
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx

import Verifier.SAW.FiniteValue (ppFirstOrderValue)
import Verifier.SAW.Name (toShortName)
import Verifier.SAW.SharedTerm
import Verifier.SAW.Recognizer
import Verifier.SAW.TypedTerm

import Verifier.SAW.Simulator.What4.ReturnTrip

import SAWScript.Exceptions
import SAWScript.Proof
import SAWScript.Prover.SolverStats
import SAWScript.TopLevel
import SAWScript.Value
import SAWScript.Utils as SS
import qualified SAWScript.Position as SS
import SAWScript.Options
import SAWScript.Crucible.JVM.BuiltinsJVM (prepareClassTopLevel)

import SAWScript.JavaExpr (JavaType(..))

import qualified SAWScript.Crucible.Common as Common
import           SAWScript.Crucible.Common
import           SAWScript.Crucible.Common.MethodSpec (AllocIndex(..), nextAllocIndex, PrePost(..))

import qualified SAWScript.Crucible.Common.MethodSpec as MS
import qualified SAWScript.Crucible.Common.Setup.Type as Setup
import qualified SAWScript.Crucible.Common.Setup.Builtins as Setup
import SAWScript.Crucible.JVM.MethodSpecIR
import SAWScript.Crucible.JVM.Override
import SAWScript.Crucible.JVM.ResolveSetupValue
import SAWScript.Crucible.JVM.BuiltinsJVM ()

type SetupValue = MS.SetupValue CJ.JVM
type CrucibleMethodSpecIR = MS.CrucibleMethodSpecIR CJ.JVM
type SetupCondition = MS.SetupCondition CJ.JVM

-- TODO: something useful with the global pair?
ppJVMAbortedResult :: JVMCrucibleContext
                -> Crucible.AbortedResult Sym a
                -> Doc ann
ppJVMAbortedResult _cc = Common.ppAbortedResult (\_gp -> mempty)

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
  , "java/lang/reflect/AccessibleObject"
  , "java/lang/reflect/AnnotatedElement"
  , "java/lang/invoke/SerializedLambda"
  , "java/lang/Package"
  , "java/util/TreeMap$EntrySpliterator"
  , "java/lang/invoke/MethodHandleInfo"
  ]

jvm_verify ::
  J.Class ->
  String {- ^ method name -} ->
  [CrucibleMethodSpecIR] {- ^ overrides -} ->
  Bool {- ^ path sat checking -} ->
  JVMSetupM () ->
  ProofScript () ->
  TopLevel CrucibleMethodSpecIR
jvm_verify cls nm lemmas checkSat setup tactic =
  do cb <- getJavaCodebase
     opts <- getOptions
     -- allocate all of the handles/static vars that are referenced
     -- (directly or indirectly) by this class
     allRefs <- io $ Set.toList <$> allClassRefs cb (J.className cls)
     let refs = CJ.initClasses ++ allRefs -- ++ superRefs
     mapM_ (prepareClassTopLevel . J.unClassName) refs

     cc <- setupCrucibleContext cls
     let sym = cc^.jccBackend
     let jc = cc^.jccJVMContext

     pos <- getPosition
     let loc = SS.toW4Loc "_SAW_verify_prestate" pos

     profFile <- rwProfilingFile <$> getTopLevelRW
     (writeFinalProfile, pfs) <- io $ setupProfiling sym "jvm_verify" profFile

     (cls', method) <- io $ findMethod cb pos nm cls -- TODO: switch to crucible-jvm version
     let st0 = initialCrucibleSetupState cc (cls', method) loc

     -- execute commands of the method spec
     io $ W4.setCurrentProgramLoc sym loc
     methodSpec <- view Setup.csMethodSpec <$> execStateT (runJVMSetupM setup) st0

     -- construct the dynamic class table and declare static fields
     globals1 <- liftIO $ setupGlobalState sym jc

     -- construct the initial state for verifications
     (args, assumes, env, globals2) <- io $ verifyPrestate cc methodSpec globals1

     -- save initial path conditions
     frameIdent <- io $ Crucible.pushAssumptionFrame sym

     -- run the symbolic execution
     top_loc <- SS.toW4Loc "jvm_verify" <$> getPosition
     (ret, globals3) <-
       io $ verifySimulate opts cc pfs methodSpec args assumes top_loc lemmas globals2 checkSat

     -- collect the proof obligations
     asserts <- verifyPoststate cc
                    methodSpec env globals3 ret

     -- restore previous assumption state
     _ <- io $ Crucible.popAssumptionFrame sym frameIdent

     -- attempt to verify the proof obligations
     stats <- verifyObligations cc methodSpec tactic assumes asserts
     io $ writeFinalProfile
     returnProof (methodSpec & MS.csSolverStats .~ stats)


jvm_unsafe_assume_spec ::
  J.Class          ->
  String          {- ^ Name of the method -} ->
  JVMSetupM () {- ^ Boundary specification -} ->
  TopLevel CrucibleMethodSpecIR
jvm_unsafe_assume_spec cls nm setup =
  do cc <- setupCrucibleContext cls
     cb <- getJavaCodebase
     pos <- getPosition
     -- cls' is either cls or a (transitive) superclass of cls
     (cls', method) <- io $ findMethod cb pos nm cls -- TODO: switch to crucible-jvm version
     let loc = SS.toW4Loc "_SAW_assume_spec" pos
     let st0 = initialCrucibleSetupState cc (cls', method) loc
     ms <- (view Setup.csMethodSpec) <$> execStateT (runJVMSetupM setup) st0
     returnProof ms

verifyObligations ::
  JVMCrucibleContext ->
  CrucibleMethodSpecIR ->
  ProofScript () ->
  [Crucible.LabeledPred Term Crucible.AssumptionReason] ->
  [(String, Term)] ->
  TopLevel SolverStats
verifyObligations cc mspec tactic assumes asserts =
  do let sym = cc^.jccBackend
     st <- io $ sawCoreState sym
     let sc = saw_ctx st
     assume <- io $ scAndList sc (toListOf (folded . Crucible.labeledPred) assumes)
     let nm = mspec ^. csMethodName
     stats <- forM (zip [(0::Int)..] asserts) $ \(n, (msg, assert)) -> do
       goal   <- io $ scImplies sc assume assert
       goal'  <- io $ boolToProp sc [] goal -- TODO, generalize over inputs
       let goalname = concat [nm, " (", takeWhile (/= '\n') msg, ")"]
           proofgoal = ProofGoal n "vc" goalname goal'
       res <- runProofScript tactic proofgoal
       case res of
         ValidProof stats _thm -> return stats -- TODO, do something with these theorems!
         InvalidProof stats vals _pst -> do
           printOutLnTop Info $ unwords ["Subgoal failed:", nm, msg]
           printOutLnTop Info (show stats)
           printOutLnTop OnlyCounterExamples "----------Counterexample----------"
           opts <- sawPPOpts <$> rwPPOpts <$> getTopLevelRW
           let showEC ec = Text.unpack (toShortName (ecName ec))
           let showAssignment (name, val) = "  " ++ showEC name ++ ": " ++ show (ppFirstOrderValue opts val)
           mapM_ (printOutLnTop OnlyCounterExamples . showAssignment) vals
           io $ fail "Proof failed." -- Mirroring behavior of llvm_verify
         UnfinishedProof pst ->
           io $ fail $ "Proof failed " ++ show (length (psGoals pst)) ++ " goals remaining."

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
  JVMCrucibleContext ->
  CrucibleMethodSpecIR ->
  Crucible.SymGlobalState Sym ->
  IO ([(J.Type, JVMVal)],
      [Crucible.LabeledPred Term Crucible.AssumptionReason],
      Map AllocIndex JVMRefVal,
      Crucible.SymGlobalState Sym)
verifyPrestate cc mspec globals0 =
  do let sym = cc^.jccBackend
     let preallocs = mspec ^. MS.csPreState . MS.csAllocs
     let tyenv = MS.csAllocations mspec
     let nameEnv = mspec ^. MS.csPreState . MS.csVarTypeNames

     let prestateLoc = W4.mkProgramLoc "_SAW_verify_prestate" W4.InternalPos
     W4.setCurrentProgramLoc sym prestateLoc

     --let cvar = CJ.dynamicClassTable (cc^.jccJVMContext)
     --let Just mem = Crucible.lookupGlobal lvar globals

     -- Allocate objects in memory for each 'jvm_alloc'
     (env, globals1) <- runStateT (traverse (doAlloc cc . snd) preallocs) globals0

     globals2 <- setupPrePointsTos mspec cc env (mspec ^. MS.csPreState . MS.csPointsTos) globals1
     cs <- setupPrestateConditions mspec cc env (mspec ^. MS.csPreState . MS.csConditions)
     args <- resolveArguments cc mspec env

     -- Check the type of the return setup value
     case (mspec ^. MS.csRetValue, mspec ^. MS.csRet) of
       (Just _, Nothing) ->
            fail $ unlines
              [ "Return value specified, but method " ++ mspec ^. csMethodName ++
                " has void return type"
              ]
       (Just sv, Just retTy) ->
         do retTy' <- typeOfSetupValue cc tyenv nameEnv sv
            unless (registerCompatible retTy retTy') $
              fail $ unlines
              [ "Incompatible types for return value when verifying " ++ mspec ^. csMethodName
              , "Expected: " ++ show retTy
              , "but given value of type: " ++ show retTy'
              ]
       (Nothing, _) -> return ()

     return (args, cs, env, globals2)

-- | Check two Types for register compatibility.
registerCompatible :: J.Type -> J.Type -> Bool
registerCompatible mt mt' = storageType mt == storageType mt'

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
  JVMCrucibleContext          ->
  CrucibleMethodSpecIR     ->
  Map AllocIndex JVMRefVal ->
  IO [(J.Type, JVMVal)]
resolveArguments cc mspec env = mapM resolveArg [0..(nArgs-1)]
  where
    nArgs = toInteger (length (mspec ^. MS.csArgs))
    tyenv = MS.csAllocations mspec
    nameEnv = mspec ^. MS.csPreState . MS.csVarTypeNames
    nm = mspec ^. csMethodName

    checkArgTy i mt mt' =
      unless (registerCompatible mt mt') $
           fail $ unlines [ "Type mismatch in argument " ++ show i ++ " when verifying " ++ show nm
                          , "Argument is declared with type: " ++ show mt
                          , "but provided argument has incompatible type: " ++ show mt'
                          , "Note: this may be because the signature of your " ++
                            "function changed during compilation. If using " ++
                            "Clang, check the signature in the disassembled " ++
                            ".ll file."
                          ]
    resolveArg i =
      case Map.lookup i (mspec ^. MS.csArgBindings) of
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
  JVMCrucibleContext          ->
  Map AllocIndex JVMRefVal ->
  [JVMPointsTo]               ->
  Crucible.SymGlobalState Sym ->
  IO (Crucible.SymGlobalState Sym)
setupPrePointsTos mspec cc env pts mem0 = foldM doPointsTo mem0 pts
  where
    sym = cc^.jccBackend
    jc = cc ^. jccJVMContext
    tyenv = MS.csAllocations mspec
    nameEnv = mspec ^. MS.csPreState . MS.csVarTypeNames

    injectSetupVal :: SetupValue -> IO (Crucible.RegValue Sym CJ.JVMValueType)
    injectSetupVal rhs =
      injectJVMVal sym <$> resolveSetupVal cc env tyenv nameEnv rhs

    doPointsTo :: Crucible.SymGlobalState Sym -> JVMPointsTo -> IO (Crucible.SymGlobalState Sym)
    doPointsTo mem pt =
      case pt of
        JVMPointsToField _loc lhs fid rhs ->
          do let lhs' = lookupAllocIndex env lhs
             rhs' <- injectSetupVal rhs
             CJ.doFieldStore sym mem lhs' fid rhs'
        JVMPointsToStatic _loc fid rhs ->
          do rhs' <- injectSetupVal rhs
             CJ.doStaticFieldStore sym jc mem fid rhs'
        JVMPointsToElem _loc lhs idx rhs ->
          do let lhs' = lookupAllocIndex env lhs
             rhs' <- injectSetupVal rhs
             CJ.doArrayStore sym mem lhs' idx rhs'
        JVMPointsToArray _loc lhs rhs ->
          do sc <- saw_ctx <$> sawCoreState sym
             let lhs' = lookupAllocIndex env lhs
             (_ety, tts) <-
               destVecTypedTerm sc rhs >>=
               \case
                 Nothing -> fail "setupPrePointsTos: not a monomorphic sequence type"
                 Just x -> pure x
             rhs' <- traverse (injectSetupVal . MS.SetupTerm) tts
             doEntireArrayStore sym mem lhs' rhs'

-- | Collects boolean terms that should be assumed to be true.
setupPrestateConditions ::
  CrucibleMethodSpecIR        ->
  JVMCrucibleContext             ->
  Map AllocIndex JVMRefVal    ->
  [SetupCondition]            ->
  IO [Crucible.LabeledPred Term Crucible.AssumptionReason]
setupPrestateConditions mspec cc env = aux []
  where
    tyenv   = MS.csAllocations mspec
    nameEnv = mspec ^. MS.csPreState . MS.csVarTypeNames

    aux acc [] = return acc

    aux acc (MS.SetupCond_Equal loc val1 val2 : xs) =
      do val1' <- resolveSetupVal cc env tyenv nameEnv val1
         val2' <- resolveSetupVal cc env tyenv nameEnv val2
         t     <- assertEqualVals cc val1' val2'
         let lp = Crucible.LabeledPred t (Crucible.AssumptionReason loc "equality precondition")
         aux (lp:acc) xs

    aux acc (MS.SetupCond_Pred loc tm : xs) =
      let lp = Crucible.LabeledPred (ttTerm tm) (Crucible.AssumptionReason loc "precondition") in
      aux (lp:acc) xs

    aux _ (MS.SetupCond_Ghost empty_ _ _ _ : _) = absurd empty_

--------------------------------------------------------------------------------

-- | Create a SAWCore formula asserting that two 'JVMVal's are equal.
assertEqualVals ::
  JVMCrucibleContext ->
  JVMVal ->
  JVMVal ->
  IO Term
assertEqualVals cc v1 v2 =
  do let sym = cc^.jccBackend
     st <- sawCoreState sym
     toSC sym st =<< equalValsPred cc v1 v2

--------------------------------------------------------------------------------

doAlloc ::
  JVMCrucibleContext ->
  Allocation ->
  StateT (Crucible.SymGlobalState Sym) IO JVMRefVal
doAlloc cc alloc =
  case alloc of
    AllocObject cname -> StateT (CJ.doAllocateObject sym halloc jc cname)
    AllocArray len ty -> StateT (CJ.doAllocateArray sym halloc jc len ty)
  where
    sym = cc^.jccBackend
    halloc = cc^.jccHandleAllocator
    jc = cc^.jccJVMContext

--------------------------------------------------------------------------------

getMethodHandle :: CJ.JVMContext -> JVMMethodId -> IO CJ.JVMHandleInfo
getMethodHandle jc (JVMMethodId mkey cname) =
  case Map.lookup (cname, mkey) (CJ.methodHandles jc) of
    Just handle -> return handle
    Nothing ->
      fail $
      "BUG: cannot find handle for " ++ J.unClassName cname ++
      "/" ++ J.methodKeyName mkey

registerOverride ::
  Options ->
  JVMCrucibleContext ->
  Crucible.SimContext (SAWCruciblePersonality Sym) Sym CJ.JVM ->
  W4.ProgramLoc ->
  [CrucibleMethodSpecIR] ->
  Crucible.OverrideSim (SAWCruciblePersonality Sym) Sym CJ.JVM rtp args ret ()
registerOverride opts cc _ctx top_loc cs =
  do let sym = cc^.jccBackend
     let jc = cc^.jccJVMContext
     let c0 = head cs
     let method = c0 ^. MS.csMethod

     sc <- saw_ctx <$> liftIO (sawCoreState sym)

     mhandle <- liftIO $ getMethodHandle jc method
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
                  (methodSpecHandler opts sc cc top_loc cs h)


--------------------------------------------------------------------------------

verifySimulate ::
  Options                       ->
  JVMCrucibleContext               ->
  [Crucible.GenericExecutionFeature Sym] ->
  CrucibleMethodSpecIR          ->
  [(a, JVMVal)]                 ->
  [Crucible.LabeledPred Term Crucible.AssumptionReason] ->
  W4.ProgramLoc                 ->
  [CrucibleMethodSpecIR]        ->
  Crucible.SymGlobalState Sym   ->
  Bool {- ^ path sat checking -} ->
  IO (Maybe (J.Type, JVMVal), Crucible.SymGlobalState Sym)
verifySimulate opts cc pfs mspec args assumes top_loc lemmas globals _checkSat =
  do let jc = cc^.jccJVMContext
     let sym = cc^.jccBackend
     let method = mspec ^. MS.csMethod
     let verbosity = simVerbose opts
     let halloc = cc^.jccHandleAllocator

     -- executeCrucibleJVM

     when (verbosity > 2) $
          putStrLn "starting executeCrucibleJVM"

     CJ.setSimulatorVerbosity verbosity sym

     --when (not (J.methodIsStatic meth)) $ do
     --  fail $ unlines [ "Crucible can only extract static methods" ]

     (CJ.JVMHandleInfo _ h) <- getMethodHandle jc method
     regmap <- prepareArgs (Crucible.handleArgTypes h) (map snd args)
     res <-
       do let feats = pfs
          let simctx = CJ.jvmSimContext sym halloc stdout jc verbosity SAWCruciblePersonality
          let simSt = Crucible.InitialState simctx globals Crucible.defaultAbortHandler (Crucible.handleReturnType h)
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
                Crucible.PartialRes _ _ gp _ ->
                  do printOutLn opts Info "Symbolic simulation completed with side conditions."
                     return gp
            let ret_ty = mspec ^. MS.csRet
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
         do let resultDoc = ppJVMAbortedResult cc ar
            fail $ unlines [ "Symbolic execution failed."
                           , show resultDoc
                           ]

       Crucible.TimeoutResult _cxt -> fail "Symbolic execution timed out."

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
  JVMCrucibleContext                   {- ^ crucible context                             -} ->
  CrucibleMethodSpecIR              {- ^ specification                                -} ->
  Map AllocIndex JVMRefVal          {- ^ allocation substitution                      -} ->
  Crucible.SymGlobalState Sym       {- ^ global variables                             -} ->
  Maybe (J.Type, JVMVal)            {- ^ optional return value                        -} ->
  TopLevel [(String, Term)]         {- ^ generated labels and verification conditions -}
verifyPoststate cc mspec env0 globals ret =
  do opts <- getOptions
     sc <- getSharedContext
     poststateLoc <- SS.toW4Loc "_SAW_verify_poststate" <$> getPosition
     io $ W4.setCurrentProgramLoc sym poststateLoc

     let ecs0 = Map.fromList
           [ (ecVarIndex ec, ec)
           | tt <- mspec ^. MS.csPreState . MS.csFreshVars
           , let ec = tecExt tt ]
     terms0 <- io $ traverse (scExtCns sc) ecs0

     let initialFree = Set.fromList (map (ecVarIndex . tecExt)
                                    (view (MS.csPostState . MS.csFreshVars) mspec))
     matchPost <- io $
          runOverrideMatcher sym globals env0 terms0 initialFree poststateLoc $
           do matchResult opts sc
              learnCond opts sc cc mspec PostState (mspec ^. MS.csPostState)

     st <- case matchPost of
             Left err      -> fail (show err)
             Right (_, st) -> return st
     io $ for_ (view osAsserts st) $ \assert -> Crucible.addAssertion sym assert

     obligations <- io $ Crucible.getProofObligations sym
     io $ Crucible.clearProofObligations sym
     io $ mapM (verifyObligation sc) (Crucible.proofGoalsToList obligations)

  where
    sym = cc^.jccBackend

    verifyObligation sc (Crucible.ProofGoal hyps (Crucible.LabeledPred concl (Crucible.SimError _loc err))) =
      do st         <- sawCoreState sym
         hypTerm    <- scAndList sc =<< mapM (toSC sym st) (toListOf (folded . Crucible.labeledPred) hyps)
         conclTerm  <- toSC sym st concl
         obligation <- scImplies sc hypTerm conclTerm
         return ("safety assertion: " ++ Crucible.simErrorReasonMsg err, obligation)

    matchResult opts sc =
      case (ret, mspec ^. MS.csRetValue) of
        (Just (rty,r), Just expect) -> matchArg opts sc cc mspec PostState r rty expect
        (Nothing     , Just _ )     -> fail "verifyPoststate: unexpected jvm_return specification"
        _ -> return ()

--------------------------------------------------------------------------------

setupCrucibleContext :: J.Class -> TopLevel JVMCrucibleContext
setupCrucibleContext jclass =
  do halloc <- getHandleAlloc
     jc <- getJVMTrans
     cb <- getJavaCodebase
     sc <- getSharedContext
     sym <- io $ newSAWCoreBackend sc
     opts <- getOptions
     io $ CJ.setSimulatorVerbosity (simVerbose opts) sym

     -- TODO! there's a lot of options setup we need to replicate
     --  from SAWScript.Crucible.LLVM.Builtins

     return JVMCrucibleContext { _jccJVMClass = jclass
                               , _jccCodebase = cb
                               , _jccBackend = sym
                               , _jccJVMContext = jc
                               , _jccHandleAllocator = halloc
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
         name <- W4.stringLit sym (W4S.UnicodeLiteral $ CJ.classNameText (J.className cls))
         -- Set every class to status 2 (initialized). In the absence
         -- of JVMSetup commands for specifying initialization status,
         -- this will allow verifications to proceed without the
         -- interference of any static initializers.
         status <- W4.bvLit sym knownRepr (BV.mkBV knownRepr 2)
         super <-
           case J.superClass cls of
             Nothing -> return W4.Unassigned
             Just cname' ->
               case Map.lookup cname' (CJ.classTable jc) of
                 Nothing -> return W4.Unassigned -- this should never happen
                 Just cls' -> W4.justPartExpr sym <$> setupClass cls'
         let methods = foldr (addMethod cname) Map.empty (J.classMethods cls)
         interfaces <- V.fromList <$> traverse (W4.stringLit sym . W4S.UnicodeLiteral . CJ.classNameText) (J.classInterfaces cls)
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

data JVMSetupError
  = JVMFreshVarInvalidType JavaType
  | JVMFieldNonReference SetupValue String
  | JVMFieldMultiple AllocIndex J.FieldId
  | JVMFieldFailure String -- TODO: switch to a more structured type
  | JVMFieldTypeMismatch J.FieldId J.Type
  | JVMStaticMultiple J.FieldId
  | JVMStaticFailure String -- TODO: switch to a more structured type
  | JVMStaticTypeMismatch J.FieldId J.Type
  | JVMElemNonReference SetupValue Int
  | JVMElemNonArray J.Type
  | JVMElemInvalidIndex J.Type Int Int -- element type, length, index
  | JVMElemTypeMismatch Int J.Type J.Type -- index, expected, found
  | JVMElemMultiple AllocIndex Int -- reference and array index
  | JVMArrayNonReference SetupValue
  | JVMArrayTypeMismatch Int J.Type Cryptol.Schema
  | JVMArrayMultiple AllocIndex
  | JVMArgTypeMismatch Int J.Type J.Type -- argument position, expected, found
  | JVMArgNumberWrong Int Int -- number expected, number found
  | JVMReturnUnexpected J.Type -- found
  | JVMReturnTypeMismatch J.Type J.Type -- expected, found

instance X.Exception JVMSetupError where
  toException = topLevelExceptionToException
  fromException = topLevelExceptionFromException

instance Show JVMSetupError where
  show err =
    case err of
      JVMFreshVarInvalidType jty ->
        "jvm_fresh_var: Invalid type: " ++ show jty
      JVMFieldNonReference ptr fname ->
        unlines
        [ "jvm_field_is: Left-hand side is not a valid object reference"
        , "Left-hand side: " ++ show (MS.ppSetupValue ptr)
        , "Field name: " ++ fname
        ]
      JVMFieldMultiple _ptr fid ->
        "jvm_field_is: Multiple specifications for the same instance field (" ++ J.fieldIdName fid ++ ")"
      JVMFieldFailure msg ->
        "jvm_field_is: JVM field resolution failed:\n" ++ msg
      JVMFieldTypeMismatch fid found ->
         -- FIXME: use a pretty printing function for J.Type instead of show
        unlines
        [ "jvm_field_is: Incompatible types for field " ++ show (J.fieldIdName fid)
        , "Expected type: " ++ show (J.fieldIdType fid)
        , "Given type: " ++ show found
        ]
      JVMStaticMultiple fid ->
        "jvm_static_field_is: Multiple specifications for the same static field (" ++ J.fieldIdName fid ++ ")"
      JVMStaticFailure msg ->
        "jvm_static_field_is: JVM field resolution failed:\n" ++ msg
      JVMStaticTypeMismatch fid found ->
         -- FIXME: use a pretty printing function for J.Type instead of show
        unlines
        [ "jvm_static_field_is: Incompatible types for field " ++ show (J.fieldIdName fid)
        , "Expected type: " ++ show (J.fieldIdType fid)
        , "Given type: " ++ show found
        ]
      JVMElemNonReference ptr idx ->
        unlines
        [ "jvm_elem_is: Left-hand side is not a valid object reference"
        , "Left-hand side: " ++ show (MS.ppSetupValue ptr)
        , "Index: " ++ show idx
        ]
      JVMElemNonArray jty ->
        "jvm_elem_is: Not an array type: " ++ show jty
      JVMElemInvalidIndex ty len idx ->
        unlines
        [ "jvm_elem_is: Array index out of bounds"
        , "Element type: " ++ show ty
        , "Array length: " ++ show len
        , "Given index: " ++ show idx
        ]
      JVMElemTypeMismatch idx expected found ->
        unlines
        [ "jvm_elem_is: Incompatible types for array index " ++ show idx
        , "Expected type: " ++ show expected
        , "Given type: " ++ show found
        ]
      JVMElemMultiple _ptr idx ->
        "jvm_elem_is: Multiple specifications for the same array index (" ++ show idx ++ ")"
      JVMArrayNonReference ptr ->
        unlines
        [ "jvm_array_is: Left-hand side is not a valid object reference"
        , "Left-hand side: " ++ show (MS.ppSetupValue ptr)
        ]
      JVMArrayTypeMismatch len ty schema ->
        unlines
        [ "jvm_array_is: Specified value does not have the expected type"
        , "Expected array length: " ++ show len
        , "Expected element type: " ++ show ty
        , "Given type: " ++ show (Cryptol.pp schema)
        ]
      JVMArrayMultiple _ptr ->
        "jvm_array_is: Multiple specifications for the same array reference"
      JVMArgTypeMismatch i expected found ->
        unlines
        [ "jvm_execute_func: Argument type mismatch"
        , "Argument position: " ++ show i
        , "Expected type: " ++ show expected
        , "Given type: " ++ show found
        ]
      JVMArgNumberWrong expected found ->
        unlines
        [ "jvm_execute_func: Wrong number of arguments"
        , "Expected: " ++ show expected
        , "Given: " ++ show found
        ]
      JVMReturnUnexpected found ->
        unlines
        [ "jvm_return: Unexpected return value for void method"
        , "Given type: " ++ show found
        ]
      JVMReturnTypeMismatch expected found ->
        unlines
        [ "jvm_return: Return type mismatch"
        , "Expected type: " ++ show expected
        , "Given type: " ++ show found
        ]

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
    JavaLong      -> J.LongType
    JavaFloat     -> J.FloatType
    JavaDouble    -> J.DoubleType
    JavaArray _ t -> J.ArrayType (typeOfJavaType t)
    JavaClass c   -> J.ClassType (parseClassName c)

-- | Generate a fresh variable term. The name will be used when
-- pretty-printing the variable in debug output.
jvm_fresh_var ::
  String              {- ^ variable name    -} ->
  JavaType            {- ^ variable type    -} ->
  JVMSetupM TypedTerm {- ^ fresh typed term -}
jvm_fresh_var name jty =
  JVMSetupM $
  do sc <- lift getSharedContext
     case cryptolTypeOfActual jty of
       Nothing -> X.throwM $ JVMFreshVarInvalidType jty
       Just cty -> Setup.freshVariable sc name cty

jvm_alloc_object ::
  String {- ^ class name -} ->
  JVMSetupM SetupValue
jvm_alloc_object cname =
  JVMSetupM $
  do loc <- SS.toW4Loc "jvm_alloc_object" <$> lift getPosition
     n <- Setup.csVarCounter <<%= nextAllocIndex
     Setup.currentState . MS.csAllocs . at n ?=
       (loc, AllocObject (parseClassName cname))
     return (MS.SetupVar n)

jvm_alloc_array ::
  Int {- array size -} ->
  JavaType             ->
  JVMSetupM SetupValue
jvm_alloc_array len ety =
  JVMSetupM $
  do loc <- SS.toW4Loc "jvm_alloc_array" <$> lift getPosition
     n <- Setup.csVarCounter <<%= nextAllocIndex
     Setup.currentState . MS.csAllocs . at n ?= (loc, AllocArray len (typeOfJavaType ety))
     return (MS.SetupVar n)

jvm_field_is ::
  SetupValue {- ^ object -} ->
  String     {- ^ field name -} ->
  SetupValue {- ^ field value -} ->
  JVMSetupM ()
jvm_field_is ptr fname val =
  JVMSetupM $
  do pos <- lift getPosition
     loc <- SS.toW4Loc "jvm_field_is" <$> lift getPosition
     ptr' <-
       case ptr of
         MS.SetupVar ptr' -> pure ptr'
         _ -> X.throwM $ JVMFieldNonReference ptr fname
     st <- get
     let cc = st ^. Setup.csCrucibleContext
     let cb = cc ^. jccCodebase
     let env = MS.csAllocations (st ^. Setup.csMethodSpec)
     let nameEnv = MS.csTypeNames (st ^. Setup.csMethodSpec)
     ptrTy <- typeOfSetupValue cc env nameEnv ptr
     valTy <- typeOfSetupValue cc env nameEnv val
     fid <- either (X.throwM . JVMFieldFailure) pure =<< (liftIO $ runExceptT $ findField cb pos ptrTy fname)
     unless (registerCompatible (J.fieldIdType fid) valTy) $
       X.throwM $ JVMFieldTypeMismatch fid valTy
     let pt = JVMPointsToField loc ptr' fid val
     let pts = st ^. Setup.csMethodSpec . MS.csPreState . MS.csPointsTos
     when (st ^. Setup.csPrePost == PreState && any (overlapPointsTo pt) pts) $
       X.throwM $ JVMFieldMultiple ptr' fid
     Setup.addPointsTo pt

jvm_static_field_is ::
  String     {- ^ field name -} ->
  SetupValue {- ^ field value -} ->
  JVMSetupM ()
jvm_static_field_is fname val =
  JVMSetupM $
  do pos <- lift getPosition
     loc <- SS.toW4Loc "jvm_static_field_is" <$> lift getPosition
     st <- get
     let cc = st ^. Setup.csCrucibleContext
     let cb = cc ^. jccCodebase
     let env = MS.csAllocations (st ^. Setup.csMethodSpec)
     let nameEnv = MS.csTypeNames (st ^. Setup.csMethodSpec)
     let cname =
           case dropWhileEnd (/= '.') fname of
             "" -> J.className (cc ^. jccJVMClass)
             s -> J.mkClassName (init s)
     -- liftIO $ putStrLn $ "jvm_static_field_is " ++ J.unClassName cname ++ " " ++ fname
     let ptrTy = J.ClassType cname
     valTy <- typeOfSetupValue cc env nameEnv val
     fid <- either (X.throwM . JVMStaticFailure) pure =<< (liftIO $ runExceptT $ findField cb pos ptrTy fname)
     unless (registerCompatible (J.fieldIdType fid) valTy) $
       X.throwM $ JVMStaticTypeMismatch fid valTy
     -- let name = J.unClassName (J.fieldIdClass fid) ++ "." ++ J.fieldIdName fid
     -- liftIO $ putStrLn $ "resolved to: " ++ name
     let pt = JVMPointsToStatic loc fid val
     let pts = st ^. Setup.csMethodSpec . MS.csPreState . MS.csPointsTos
     when (st ^. Setup.csPrePost == PreState && any (overlapPointsTo pt) pts) $
       X.throwM $ JVMStaticMultiple fid
     Setup.addPointsTo pt

jvm_elem_is ::
  SetupValue {- ^ array -} ->
  Int        {- ^ index -} ->
  SetupValue {- ^ element value -} ->
  JVMSetupM ()
jvm_elem_is ptr idx val =
  JVMSetupM $
  do loc <- SS.toW4Loc "jvm_elem_is" <$> lift getPosition
     ptr' <-
       case ptr of
         MS.SetupVar ptr' -> pure ptr'
         _ -> X.throwM $ JVMElemNonReference ptr idx
     st <- get
     let cc = st ^. Setup.csCrucibleContext
     let env = MS.csAllocations (st ^. Setup.csMethodSpec)
     let nameEnv = MS.csTypeNames (st ^. Setup.csMethodSpec)
     (len, elTy) <-
       case snd (lookupAllocIndex env ptr') of
         AllocObject cname -> X.throwM $ JVMElemNonArray (J.ClassType cname)
         AllocArray len elTy -> pure (len, elTy)
     valTy <- typeOfSetupValue cc env nameEnv val
     unless (0 <= idx && idx < len) $
       X.throwM $ JVMElemInvalidIndex elTy len idx
     unless (registerCompatible elTy valTy) $
       X.throwM $ JVMElemTypeMismatch idx elTy valTy
     let pt = JVMPointsToElem loc ptr' idx val
     let pts = st ^. Setup.csMethodSpec . MS.csPreState . MS.csPointsTos
     when (st ^. Setup.csPrePost == PreState && any (overlapPointsTo pt) pts) $
       X.throwM $ JVMElemMultiple ptr' idx
     Setup.addPointsTo pt

jvm_array_is ::
  SetupValue {- ^ array reference -} ->
  TypedTerm {- ^ array value -} ->
  JVMSetupM ()
jvm_array_is ptr val =
  JVMSetupM $
  do loc <- SS.toW4Loc "jvm_array_is" <$> lift getPosition
     ptr' <-
       case ptr of
         MS.SetupVar ptr' -> pure ptr'
         _ -> X.throwM $ JVMArrayNonReference ptr
     st <- get
     let env = MS.csAllocations (st ^. Setup.csMethodSpec)
     (len, elTy) <-
       case snd (lookupAllocIndex env ptr') of
         AllocObject cname -> X.throwM $ JVMElemNonArray (J.ClassType cname)
         AllocArray len elTy -> pure (len, elTy)
     let schema = ttSchema val
     let checkVal =
           do ty <- Cryptol.isMono schema
              (n, a) <- Cryptol.tIsSeq ty
              guard (Cryptol.tIsNum n == Just (toInteger len))
              jty <- toJVMType (Cryptol.evalValType mempty a)
              guard (registerCompatible elTy jty)
     case checkVal of
       Nothing -> X.throwM (JVMArrayTypeMismatch len elTy schema)
       Just () -> pure ()
     let pt = JVMPointsToArray loc ptr' val
     let pts = st ^. Setup.csMethodSpec . MS.csPreState . MS.csPointsTos
     when (st ^. Setup.csPrePost == PreState && any (overlapPointsTo pt) pts) $
       X.throwM $ JVMArrayMultiple ptr'
     Setup.addPointsTo pt

jvm_precond :: TypedTerm -> JVMSetupM ()
jvm_precond term = JVMSetupM $ do
  loc <- SS.toW4Loc "jvm_precond" <$> lift getPosition
  Setup.crucible_precond loc term

jvm_postcond :: TypedTerm -> JVMSetupM ()
jvm_postcond term = JVMSetupM $ do
  loc <- SS.toW4Loc "jvm_postcond" <$> lift getPosition
  Setup.crucible_postcond loc term

jvm_execute_func :: [SetupValue] -> JVMSetupM ()
jvm_execute_func args =
  JVMSetupM $
  do st <- get
     let cc = st ^. Setup.csCrucibleContext
     let mspec = st ^. Setup.csMethodSpec
     let env = MS.csAllocations mspec
     let nameEnv = MS.csTypeNames mspec
     let argTys = mspec ^. MS.csArgs
     let
       checkArg i expectedTy val =
         do valTy <- typeOfSetupValue cc env nameEnv val
            unless (registerCompatible expectedTy valTy) $
              X.throwM (JVMArgTypeMismatch i expectedTy valTy)
     let
       checkArgs _ [] [] = pure ()
       checkArgs i [] vals =
         X.throwM (JVMArgNumberWrong i (i + length vals))
       checkArgs i tys [] =
         X.throwM (JVMArgNumberWrong (i + length tys) i)
       checkArgs i (ty : tys) (val : vals) =
         do checkArg i ty val
            checkArgs (i + 1) tys vals
     checkArgs 0 argTys args
     Setup.crucible_execute_func args

jvm_return :: SetupValue -> JVMSetupM ()
jvm_return retVal =
  JVMSetupM $
  do st <- get
     let cc = st ^. Setup.csCrucibleContext
     let mspec = st ^. Setup.csMethodSpec
     let env = MS.csAllocations mspec
     let nameEnv = MS.csTypeNames mspec
     valTy <- typeOfSetupValue cc env nameEnv retVal
     case mspec ^. MS.csRet of
       Nothing ->
         X.throwM (JVMReturnUnexpected valTy)
       Just retTy ->
         unless (registerCompatible retTy valTy) $
         X.throwM (JVMReturnTypeMismatch retTy valTy)
     Setup.crucible_return retVal

--------------------------------------------------------------------------------

-- | Sort a list of things and group them into equivalence classes.
groupOn ::
  Ord b =>
  (a -> b) {- ^ equivalence class projection -} ->
  [a] -> [[a]]
groupOn f = groupBy ((==) `on` f) . sortBy (compare `on` f)
