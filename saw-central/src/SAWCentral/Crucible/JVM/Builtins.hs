{- |
Module      : SAWCentral.Crucible.JVM.Builtins
Description : Implementations of crucible-jvm-related SAW-Script primitives.
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SAWCentral.Crucible.JVM.Builtins
    ( jvm_verify
    , jvm_unsafe_assume_spec
    , jvm_return
    , jvm_execute_func
    , jvm_postcond
    , jvm_precond
    , jvm_assert
    , jvm_modifies_field
    , jvm_modifies_static_field
    , jvm_modifies_elem
    , jvm_modifies_array
    , jvm_field_is
    , jvm_static_field_is
    , jvm_elem_is
    , jvm_array_is
    , jvm_fresh_var
    , jvm_alloc_object
    , jvm_alloc_array
    , jvm_setup_with_tag
    , jvm_ghost_value
    , jvm_equal
    , jvm_unint
    ) where

import           Control.Lens

import qualified Control.Monad.Catch as X
import           Control.Monad (foldM, forM, forM_, guard, unless, when)
import           Control.Monad.IO.Class (MonadIO(..))
import           Control.Monad.Reader (runReaderT)
import           Control.Monad.State (MonadState(..), StateT(..), execStateT, gets)
import qualified Control.Monad.State.Strict as Strict
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.Except (runExceptT)
import qualified Data.BitVector.Sized as BV
import           Data.Foldable (for_)
import           Data.Function
import qualified Data.IntMap as IntMap
import           Data.IORef
import           Data.List (isPrefixOf, sortBy)
import           Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe, isNothing)
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Time.Clock (getCurrentTime, diffUTCTime)
import qualified Data.Vector as V
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
import qualified Lang.Crucible.Backend.Online as Crucible
import qualified Lang.Crucible.CFG.Core as Crucible (TypeRepr(..))
import qualified Lang.Crucible.FunctionHandle as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Simulator.GlobalState as Crucible
import qualified Lang.Crucible.Simulator.PathSatisfiability as Crucible
import qualified Lang.Crucible.Simulator.SimError as Crucible

-- crucible-jvm
import qualified Lang.JVM.Codebase as CB
import qualified Lang.Crucible.JVM as CJ

-- parameterized-utils
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx

import SAWCore.FiniteValue (ppFirstOrderValue)
import SAWCore.Name (VarName(..))
import SAWCore.SharedTerm
import CryptolSAWCore.TypedTerm

import SAWCoreWhat4.ReturnTrip

import SAWCentral.Builtins (ghost_value)
import SAWCentral.Exceptions
import SAWCentral.Panic
import SAWCentral.Proof
import SAWCentral.Prover.SolverStats
import SAWCentral.TopLevel
import SAWCentral.Value
import SAWCentral.Utils as SS
import qualified SAWCentral.Position as SS
import SAWCentral.Options
import SAWCentral.Crucible.JVM.BuiltinsJVM (prepareClassTopLevel)

import SAWCentral.JavaExpr (JavaType(..))

import qualified SAWCentral.Crucible.Common as Common
import           SAWCentral.Crucible.Common
import           SAWCentral.Crucible.Common.Override (MetadataMap)
import           SAWCentral.Crucible.Common.MethodSpec (AllocIndex(..), nextAllocIndex, PrePost(..))
import qualified SAWCentral.Crucible.Common.Vacuity as Vacuity

import qualified SAWCentral.Crucible.Common.MethodSpec as MS
import qualified SAWCentral.Crucible.Common.Setup.Type as Setup
import qualified SAWCentral.Crucible.Common.Setup.Builtins as Setup
import SAWCentral.Crucible.JVM.Setup.Value(jccUninterp)
import SAWCentral.Crucible.JVM.MethodSpecIR
import SAWCentral.Crucible.JVM.Override
import SAWCentral.Crucible.JVM.ResolveSetupValue
import SAWCentral.Crucible.JVM.BuiltinsJVM ()

type AssumptionReason = (MS.ConditionMetadata, String)
type SetupValue = MS.SetupValue CJ.JVM
type Lemma = MS.ProvedSpec CJ.JVM
type MethodSpec = MS.CrucibleMethodSpecIR CJ.JVM
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
  Text {- ^ method name -} ->
  [Lemma] {- ^ overrides -} ->
  Bool {- ^ path sat checking -} ->
  JVMSetupM () ->
  ProofScript () ->
  TopLevel Lemma
jvm_verify cls nm lemmas checkSat setup tactic =
  do start <- io getCurrentTime
     cb <- getJavaCodebase
     opts <- getOptions

     -- set up the metadata map for tracking proof obligation metadata
     mdMap <- io $ newIORef mempty

     -- allocate all of the handles/static vars that are referenced
     -- (directly or indirectly) by this class
     allRefs <- io $ Set.toList <$> allClassRefs cb (J.className cls)
     let refs = CJ.initClasses ++ allRefs -- ++ superRefs
     mapM_ (prepareClassTopLevel . Text.pack . J.unClassName) refs

     cc <- setupCrucibleContext cls
     SomeOnlineBackend bak <- pure (cc^.jccBackend)
     let sym = cc^.jccSym
     let jc = cc^.jccJVMContext

     pos <- getPosition
     let loc = SS.toW4Loc "_SAW_jvm_verify" pos

     profFile <- rwProfilingFile <$> getTopLevelRW
     (writeFinalProfile, pfs) <- io $ setupProfiling sym "jvm_verify" profFile

     (cls', method) <- io $ findMethod cb pos (Text.unpack nm) cls -- TODO: switch to crucible-jvm version
     let st0 = initialCrucibleSetupState cc (cls', method) loc

     -- execute commands of the method spec
     io $ W4.setCurrentProgramLoc sym loc
     methodSpec <- execJVMSetup setup st0

     -- construct the dynamic class table and declare static fields
     globals1 <- liftIO $ setupGlobalState sym jc

     -- construct the initial state for verifications
     (args, assumes, env, globals2) <- io $ verifyPrestate cc methodSpec globals1

     -- check for contradictory preconditions
     when (detectVacuity opts) $
       Vacuity.checkAssumptionsForContradictions
         sym
         methodSpec
         tactic
         assumes

     -- save initial path conditions
     frameIdent <- io $ Crucible.pushAssumptionFrame bak

     -- run the symbolic execution
     top_loc <- SS.toW4Loc "jvm_verify" <$> getPosition
     (ret, globals3) <-
       io $ verifySimulate opts cc pfs methodSpec args assumes top_loc lemmas globals2 checkSat mdMap

     -- collect the proof obligations
     asserts <- verifyPoststate cc
                    methodSpec env globals3 ret mdMap

     -- restore previous assumption state
     _ <- io $ Crucible.popAssumptionFrame bak frameIdent

     -- attempt to verify the proof obligations
     (stats,vcstats) <- verifyObligations cc methodSpec tactic assumes asserts
     io $ writeFinalProfile

     let lemmaSet = Set.fromList (map (view MS.psSpecIdent) lemmas)
     end <- io getCurrentTime
     let diff = diffUTCTime end start
     ps <- io (MS.mkProvedSpec MS.SpecProved methodSpec stats vcstats lemmaSet diff)
     returnJVMProof ps


jvm_unsafe_assume_spec ::
  J.Class          ->
  Text         {- ^ Name of the method -} ->
  JVMSetupM () {- ^ Boundary specification -} ->
  TopLevel Lemma
jvm_unsafe_assume_spec cls nm setup =
  do cc <- setupCrucibleContext cls
     cb <- getJavaCodebase
     pos <- getPosition
     -- cls' is either cls or a (transitive) superclass of cls
     (cls', method) <- io $ findMethod cb pos (Text.unpack nm) cls -- TODO: switch to crucible-jvm version
     let loc = SS.toW4Loc "_SAW_JVM_unsafe_assume_spec" pos
     let st0 = initialCrucibleSetupState cc (cls', method) loc
     ms <- execJVMSetup setup st0
     ps <- io (MS.mkProvedSpec MS.SpecAdmitted ms mempty mempty mempty 0)
     returnJVMProof ps

execJVMSetup :: JVMSetupM a -> Setup.CrucibleSetupState CJ.JVM -> TopLevel MethodSpec
execJVMSetup setup st0 =
  do st' <- execStateT (runReaderT (runJVMSetupM setup) Setup.makeCrucibleSetupRO) st0
     -- check for missing jvm_execute_func
     unless (st' ^. Setup.csPrePost == PostState) $
       X.throwM JVMExecuteMissing
     -- check that jvm_return value is present if return type is non-void
     let mspec = st' ^. Setup.csMethodSpec
     case mspec ^. MS.csRet of
       Nothing -> pure ()
       Just retTy ->
         case mspec ^. MS.csRetValue of
           Just _ -> pure ()
           Nothing ->
             X.throwM $ JVMReturnMissing retTy
     pure mspec

verifyObligations ::
  JVMCrucibleContext ->
  MethodSpec ->
  ProofScript () ->
  [Crucible.LabeledPred Term AssumptionReason] ->
  [(String, MS.ConditionMetadata, Term)] ->
  TopLevel (SolverStats, [MS.VCStats])
verifyObligations cc mspec tactic assumes asserts =
  do let sym = cc^.jccSym
     st <- io $ sawCoreState sym
     let sc = saw_ctx st
     assume <- io $ scAndList sc (toListOf (folded . Crucible.labeledPred) assumes)
     let nm = mspec ^. csMethodName
     outs <- forM (zip [(0::Int)..] asserts) $ \(n, (msg, md, assert)) -> do
       goal   <- io $ scImplies sc assume assert
       goal'  <- io $ boolToProp sc [] goal -- TODO, generalize over inputs
       let ploc = MS.conditionLoc md
       let gloc = (unwords [show (W4.plSourceLoc ploc)
                          ,"in"
                          , show (W4.plFunction ploc)]) ++
                  (if Prelude.null (MS.conditionContext md) then [] else
                     "\n" ++ MS.conditionContext md)
       let goalname = concat [nm, " (", takeWhile (/= '\n') msg, ")"]
       let proofgoal = ProofGoal
                       { goalNum  = n
                       , goalType = MS.conditionType md
                       , goalName = nm
                       , goalLoc  = gloc
                       , goalDesc = msg
                       , goalSequent = propToSequent goal'
                       , goalTags = MS.conditionTags md
                       }
       res <- runProofScript tactic goal' proofgoal (Just ploc)
                (Text.unwords
                 ["JVM verification condition:", Text.pack (show n), Text.pack goalname])
                False -- do not record in the theorem database
                False -- TODO, useSequentGoals...
       case res of
         ValidProof stats thm ->
           return (stats, MS.VCStats md stats (thmSummary thm) (thmNonce thm) (thmDepends thm) (thmElapsedTime thm))
         InvalidProof stats vals _pst -> do
           printOutLnTop Info $ unwords ["Subgoal failed:", nm, msg]
           printOutLnTop Info (show stats)
           printOutLnTop OnlyCounterExamples "----------Counterexample----------"
           opts <- rwPPOpts <$> getTopLevelRW
           let showVar x = Text.unpack (vnName x)
           let showAssignment (name, val) = "  " ++ showVar name ++ ": " ++ show (ppFirstOrderValue opts val)
           mapM_ (printOutLnTop OnlyCounterExamples . showAssignment) vals
           io $ fail "Proof failed." -- Mirroring behavior of llvm_verify
         UnfinishedProof pst ->
           io $ fail $ "Proof failed " ++ show (length (psGoals pst)) ++ " goals remaining."

     printOutLnTop Info $ unwords ["Proof succeeded!", nm]

     let stats = mconcat (map fst outs)
     let vcstats = map snd outs
     return (stats, vcstats)

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
  MethodSpec ->
  Crucible.SymGlobalState Sym ->
  IO ([(J.Type, JVMVal)],
      [Crucible.LabeledPred Term AssumptionReason],
      Map AllocIndex JVMRefVal,
      Crucible.SymGlobalState Sym)
verifyPrestate cc mspec globals0 =
  jccWithBackend cc $ \bak ->
  do let sym = cc^.jccSym
     let jc = cc^.jccJVMContext
     let halloc = cc^.jccHandleAllocator
     let preallocs = mspec ^. MS.csPreState . MS.csAllocs
     let tyenv = MS.csAllocations mspec
     let nameEnv = mspec ^. MS.csPreState . MS.csVarTypeNames

     let prestateLoc = W4.mkProgramLoc "_SAW_JVM_verifyPrestate" W4.InternalPos
     W4.setCurrentProgramLoc sym prestateLoc

     --let cvar = CJ.dynamicClassTable (cc^.jccJVMContext)
     --let Just mem = Crucible.lookupGlobal lvar globals
     let postPointsTos = mspec ^. MS.csPostState . MS.csPointsTos

     -- make static fields mentioned in post-state section writable
     let updatedStaticFields = [ fid | JVMPointsToStatic _ fid _ <- postPointsTos ]
     let makeWritable gs fid = CJ.doStaticFieldWritable bak jc gs fid (W4.truePred sym)
     globals0' <- liftIO $ foldM makeWritable globals0 updatedStaticFields

     -- determine which arrays and instance fields need to be writable
     let addUpdates pt (as, es, fs) =
           case pt of
             JVMPointsToField _ a fid _ -> (as, es, Map.insertWith (++) a [fid] fs)
             JVMPointsToStatic{} -> (as, es, fs)
             JVMPointsToElem _ a i _ -> (as, Map.insertWith (++) a [i] es, fs)
             JVMPointsToArray _ a _ -> (Set.insert a as, es, fs)
     let (updatedArrays, updatedElems, updatedFields) =
           foldr addUpdates (Set.empty, Map.empty, Map.empty) postPointsTos

     -- Allocate objects in memory for each 'jvm_alloc'
     let doAlloc a (_loc, alloc) =
           case alloc of
             AllocObject cname ->
               StateT (CJ.doAllocateObject bak halloc jc cname (flip elem fids))
               where fids = fromMaybe [] (Map.lookup a updatedFields)
             AllocArray len ty ->
               StateT (CJ.doAllocateArray bak halloc jc len ty writable)
               where
                 writable
                   | Set.member a updatedArrays = const True
                   | otherwise = maybe (const False) (flip elem) (Map.lookup a updatedElems)
     (env, globals1) <- runStateT (Map.traverseWithKey doAlloc preallocs) globals0'

     globals2 <- setupPrePointsTos mspec cc env (mspec ^. MS.csPreState . MS.csPointsTos) globals1
     (globals3, cs) <-
       setupPrestateConditions mspec cc env globals2 (mspec ^. MS.csPreState . MS.csConditions)
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

     return (args, cs, env, globals3)

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
  JVMCrucibleContext ->
  MethodSpec ->
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
  MethodSpec ->
  JVMCrucibleContext ->
  Map AllocIndex JVMRefVal ->
  [JVMPointsTo] ->
  Crucible.SymGlobalState Sym ->
  IO (Crucible.SymGlobalState Sym)
setupPrePointsTos mspec cc env pts mem0 = foldM doPointsTo mem0 pts
  where
    sym = cc^.jccSym
    jc = cc ^. jccJVMContext
    tyenv = MS.csAllocations mspec
    nameEnv = mspec ^. MS.csPreState . MS.csVarTypeNames

    injectSetupVal :: SetupValue -> IO (Crucible.RegValue Sym CJ.JVMValueType)
    injectSetupVal rhs =
      injectJVMVal sym <$> resolveSetupVal cc env tyenv nameEnv rhs

    doPointsTo :: Crucible.SymGlobalState Sym -> JVMPointsTo -> IO (Crucible.SymGlobalState Sym)
    doPointsTo mem pt =
      jccWithBackend cc $ \bak ->
      case pt of
        JVMPointsToField _loc lhs fid (Just rhs) ->
          do let lhs' = lookupAllocIndex env lhs
             rhs' <- injectSetupVal rhs
             CJ.doFieldStore bak mem lhs' fid rhs'
        JVMPointsToStatic _loc fid (Just rhs) ->
          do rhs' <- injectSetupVal rhs
             CJ.doStaticFieldStore bak jc mem fid rhs'
        JVMPointsToElem _loc lhs idx (Just rhs) ->
          do let lhs' = lookupAllocIndex env lhs
             rhs' <- injectSetupVal rhs
             CJ.doArrayStore bak mem lhs' idx rhs'
        JVMPointsToArray _loc lhs (Just rhs) ->
          do sc <- saw_ctx <$> sawCoreState sym
             let lhs' = lookupAllocIndex env lhs
             (_ety, tts) <-
               destVecTypedTerm sc rhs >>=
               \case
                 Nothing -> fail "setupPrePointsTos: not a monomorphic sequence type"
                 Just x -> pure x
             rhs' <- traverse (injectSetupVal . MS.SetupTerm) tts
             doEntireArrayStore bak mem lhs' rhs'
        _ ->
          panic "setupPrePointsTo" ["invalid invariant", "jvm_modifies in pre-state"]

-- | Sets up globals (ghost variable), and collects boolean terms
-- that should be assumed to be true.
setupPrestateConditions ::
  MethodSpec ->
  JVMCrucibleContext ->
  Map AllocIndex JVMRefVal ->
  Crucible.SymGlobalState Sym ->
  [SetupCondition] ->
  IO ( Crucible.SymGlobalState Sym, [Crucible.LabeledPred Term AssumptionReason]
     )
setupPrestateConditions mspec cc env = aux []
  where
    tyenv   = MS.csAllocations mspec
    nameEnv = mspec ^. MS.csPreState . MS.csVarTypeNames

    aux acc globals [] = return (globals, acc)

    aux acc globals (MS.SetupCond_Equal loc val1 val2 : xs) =
      do val1' <- resolveSetupVal cc env tyenv nameEnv val1
         val2' <- resolveSetupVal cc env tyenv nameEnv val2
         t     <- assertEqualVals cc val1' val2'
         let lp = Crucible.LabeledPred t (loc, "equality precondition")
         aux (lp:acc) globals xs

    aux acc globals (MS.SetupCond_Pred loc tm : xs) =
      let lp = Crucible.LabeledPred (ttTerm tm) (loc, "precondition") in
      aux (lp:acc) globals xs

    aux acc globals (MS.SetupCond_Ghost _md var val : xs) =
      case val of
        TypedTerm (TypedTermSchema sch) tm ->
          aux acc (Crucible.insertGlobal var (sch,tm) globals) xs
        TypedTerm tp _ ->
          fail $ unlines
            [ "Setup term for global variable expected to have Cryptol schema type, but got"
            , show (prettyTypedTermTypePure tp)
            ]

--------------------------------------------------------------------------------

-- | Create a SAWCore formula asserting that two 'JVMVal's are equal.
assertEqualVals ::
  JVMCrucibleContext ->
  JVMVal ->
  JVMVal ->
  IO Term
assertEqualVals cc v1 v2 =
  do let sym = cc^.jccSym
     st <- sawCoreState sym
     toSC sym st =<< equalValsPred cc v1 v2

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
  IORef MetadataMap {- ^ metadata map -} ->
  NonEmpty MethodSpec ->
  Crucible.OverrideSim (SAWCruciblePersonality Sym) Sym CJ.JVM rtp args ret ()
registerOverride opts cc _ctx top_loc mdMap cs =
  do let sym = cc^.jccSym
     let jc = cc^.jccJVMContext
     let c0 = NE.head cs
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
                  (methodSpecHandler opts sc cc top_loc mdMap cs h)


--------------------------------------------------------------------------------

-- | Simulate a JVM function with Crucible as part of a 'jvm_verify' command,
-- making sure to install any overrides that the user supplies.
verifySimulate ::
  Options ->
  JVMCrucibleContext ->
  [Crucible.GenericExecutionFeature Sym] ->
  MethodSpec ->
  [(a, JVMVal)] ->
  [Crucible.LabeledPred Term AssumptionReason] ->
  W4.ProgramLoc ->
  [Lemma] ->
  Crucible.SymGlobalState Sym ->
  Bool {- ^ path sat checking -} ->
  IORef MetadataMap {- ^ metadata map -} ->
  IO (Maybe (J.Type, JVMVal), Crucible.SymGlobalState Sym)
verifySimulate opts cc pfs mspec args assumes top_loc lemmas globals checkSat mdMap =
  jccWithBackend cc $ \bak ->
  do let jc = cc^.jccJVMContext
     let sym = cc^.jccSym
     let method = mspec ^. MS.csMethod
     let verbosity = simVerbose opts
     let halloc = cc^.jccHandleAllocator

     -- executeCrucibleJVM

     when (verbosity > 2) $
          putStrLn "starting executeCrucibleJVM"

     CJ.setSimulatorVerbosity verbosity sym

     pathSatFeature <-
       Crucible.pathSatisfiabilityFeature (cc ^. jccSym)
         (Crucible.considerSatisfiability bak)

     --when (not (J.methodIsStatic meth)) $ do
     --  fail $ unlines [ "Crucible can only extract static methods" ]

     (CJ.JVMHandleInfo _ h) <- getMethodHandle jc method
     regmap <- prepareArgs (Crucible.handleArgTypes h) (map snd args)
     res <-
       do let feats = if checkSat then pathSatFeature : pfs else pfs
          -- TODO: Use crucible-jvm's jvmSimContext here (instead of manually
          -- calling mkDelayedBindings/initSimContext), once
          -- https://github.com/GaloisInc/crucible/issues/1128 has been fixed
          -- upstream.
          let bindings = CJ.mkDelayedBindings jc verbosity
          let simctx = Crucible.initSimContext bak intrinsics halloc stdout
                         bindings CJ.jvmExtensionImpl SAWCruciblePersonality
          let simSt = Crucible.InitialState simctx globals Crucible.defaultAbortHandler (Crucible.handleReturnType h)
          let fnCall = Crucible.regValue <$> Crucible.callFnVal (Crucible.HandleFnVal h) regmap
          let overrideSim =
                do liftIO $ putStrLn "registering standard overrides"
                   _ <- Strict.runStateT (mapM_ CJ.register_jvm_override CJ.stdOverrides) jc
                   liftIO $ putStrLn "registering user-provided overrides"
                   mapM_ (registerOverride opts cc simctx top_loc mdMap)
                           (groupOn (view csMethodName) (map (view MS.psSpec) lemmas))
                   liftIO $ putStrLn "registering assumptions"
                   liftIO $
                     for_ assumes $ \(Crucible.LabeledPred p (md, reason)) ->
                       do expr <- resolveSAWPred cc p
                          let loc = MS.conditionLoc md
                          Crucible.addAssumption bak (Crucible.GenericAssumption loc reason expr)
                   liftIO $ putStrLn "simulating function"
                   fnCall
          Crucible.executeCrucible (map Crucible.genericToExecutionFeature feats)
            (simSt (Crucible.runOverrideSim (Crucible.handleReturnType h) overrideSim))

     case res of
       Crucible.FinishedResult _ pr ->
         do Crucible.GlobalPair retval globals1 <- getGlobalPair opts pr
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

--------------------------------------------------------------------------------

verifyPoststate ::
  JVMCrucibleContext                {- ^ crucible context                             -} ->
  MethodSpec                        {- ^ specification                                -} ->
  Map AllocIndex JVMRefVal          {- ^ allocation substitution                      -} ->
  Crucible.SymGlobalState Sym       {- ^ global variables                             -} ->
  Maybe (J.Type, JVMVal)            {- ^ optional return value                        -} ->
  IORef MetadataMap {- ^ metadata map -} ->
  TopLevel [(String, MS.ConditionMetadata, Term)] {- ^ generated labels and verification conditions -}
verifyPoststate cc mspec env0 globals ret mdMap =
  jccWithBackend cc $ \bak ->
  do opts <- getOptions
     sc <- getSharedContext
     poststateLoc <- SS.toW4Loc "_SAW_JVM_verifyPoststate" <$> getPosition
     io $ W4.setCurrentProgramLoc sym poststateLoc

     -- This discards all the obligations generated during
     -- symbolic execution itself, i.e., which are not directly
     -- generated from specification postconditions. This
     -- is, in general, unsound.
     skipSafetyProofs <- gets rwSkipSafetyProofs
     when skipSafetyProofs (io (Crucible.clearProofObligations bak))

     let vars0 = IntMap.fromList
           [ (vnIndex vn, (vn, tvType tt))
           | tt <- mspec ^. MS.csPreState . MS.csFreshVars
           , let vn = tvName tt ]
     terms0 <- io $ scVariables sc vars0

     let initialFree = Set.fromList (map (vnIndex . tvName)
                                    (view (MS.csPostState . MS.csFreshVars) mspec))
     matchPost <- io $
          runOverrideMatcher sym globals env0 terms0 initialFree poststateLoc $
           do matchResult opts sc
              learnCond opts sc cc mspec PostState (mspec ^. MS.csPostState)

     st <- case matchPost of
             Left err      -> fail (show err)
             Right (_, st) -> return st
     io $ forM_ (view osAsserts st) $ \(md, Crucible.LabeledPred p r) ->
       do (ann,p') <- W4.annotateTerm sym p
          modifyIORef mdMap (Map.insert ann md)
          Crucible.addAssertion bak (Crucible.LabeledPred p' r)

     finalMdMap <- io $ readIORef mdMap
     obligations <- io $ Crucible.getProofObligations bak
     io $ Crucible.clearProofObligations bak
     io $ mapM (verifyObligation sc finalMdMap) (maybe [] Crucible.goalsToList obligations)

  where
    sym = cc^.jccSym

    verifyObligation sc finalMdMap
      (Crucible.ProofGoal hyps (Crucible.LabeledPred concl (Crucible.SimError loc err))) =
      do st         <- sawCoreState sym
         hypTerm <- toSC sym st =<< Crucible.assumptionsPred sym hyps
         conclTerm  <- toSC sym st concl
         obligation <- scImplies sc hypTerm conclTerm
         let defaultMd = MS.ConditionMetadata
                         { MS.conditionLoc = loc
                         , MS.conditionTags = mempty
                         , MS.conditionType = "safety assertion"
                         , MS.conditionContext = ""
                         }
         let md = fromMaybe defaultMd $
                    do ann <- W4.getAnnotation sym concl
                       Map.lookup ann finalMdMap
         return (Crucible.simErrorReasonMsg err, md, obligation)

    matchResult opts sc =
      case (ret, mspec ^. MS.csRetValue) of
        (Just (rty,r), Just expect) ->
            let md = MS.ConditionMetadata
                     { MS.conditionLoc = mspec ^. MS.csLoc
                     , MS.conditionTags = mempty
                     , MS.conditionType = "return value matching"
                     , MS.conditionContext = ""
                     } in
            matchArg opts sc cc mspec PostState md r rty expect
        (Nothing     , Just _ )     -> fail "verifyPoststate: unexpected jvm_return specification"
        _ -> return ()

--------------------------------------------------------------------------------

setupCrucibleContext :: J.Class -> TopLevel JVMCrucibleContext
setupCrucibleContext jclass =
  do halloc <- getHandleAlloc
     jc <- getJVMTrans
     cb <- getJavaCodebase
     sc <- getSharedContext
     pathSatSolver <- gets rwPathSatSolver
     sym <- io $ newSAWCoreExprBuilder sc False
     timeout <- gets rwCrucibleTimeout
     bak <- io $ newSAWCoreBackendWithTimeout pathSatSolver sym timeout
     opts <- getOptions
     io $ CJ.setSimulatorVerbosity (simVerbose opts) sym

     -- TODO! there's a lot of options setup we need to replicate
     --  from SAWCentral.Crucible.LLVM.Builtins

     return JVMCrucibleContext { _jccJVMClass = jclass
                               , _jccCodebase = cb
                               , _jccBackend = bak
                               , _jccJVMContext = jc
                               , _jccHandleAllocator = halloc
                               , _jccUninterp = mempty
                               }

--------------------------------------------------------------------------------

-- | Construct the dynamic class table, and also declare all static
-- fields (leaving them with uninitialized contents).
setupGlobalState :: Sym -> CJ.JVMContext -> IO (Crucible.SymGlobalState Sym)
setupGlobalState sym jc =
  do classTab <- setupDynamicClassTable sym jc
     let classTabVar = CJ.dynamicClassTable jc
     let globals0 = Crucible.insertGlobal classTabVar classTab Crucible.emptyGlobals
     let writable = W4.falsePred sym -- static fields default to read-only
     let declareGlobal info =
           Crucible.insertGlobal (CJ.staticFieldWritable info) writable .
           Crucible.insertGlobal (CJ.staticFieldValue info) CJ.unassignedJVMValue
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
  | JVMFieldNonReference SetupValue Text
  | JVMFieldMultiple AllocIndex J.FieldId
  | JVMFieldFailure String -- TODO: switch to a more structured type
  | JVMFieldTypeMismatch J.FieldId J.Type
  | JVMFieldModifyPrestate AllocIndex J.FieldId
  | JVMStaticMultiple J.FieldId
  | JVMStaticFailure String -- TODO: switch to a more structured type
  | JVMStaticTypeMismatch J.FieldId J.Type
  | JVMStaticModifyPrestate J.FieldId
  | JVMElemNonReference SetupValue Int
  | JVMElemNonArray J.Type
  | JVMElemInvalidIndex J.Type Int Int -- element type, length, index
  | JVMElemTypeMismatch Int J.Type J.Type -- index, expected, found
  | JVMElemMultiple AllocIndex Int -- reference and array index
  | JVMElemModifyPrestate AllocIndex Int
  | JVMArrayNonReference SetupValue
  | JVMArrayTypeMismatch Int J.Type Cryptol.Schema
  | JVMArrayMultiple AllocIndex
  | JVMArrayModifyPrestate AllocIndex
  | JVMExecuteMissing
  | JVMExecuteMultiple
  | JVMArgTypeMismatch Int J.Type J.Type -- argument position, expected, found
  | JVMArgNumberWrong Int Int -- number expected, number found
  | JVMReturnMissing J.Type -- expected
  | JVMReturnUnexpected J.Type -- found
  | JVMReturnTypeMismatch J.Type J.Type -- expected, found
  | JVMNonValueType TypedTermType

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
        , "Left-hand side: " ++ show (MS.prettySetupValue ptr)
        , "Field name: " ++ Text.unpack fname
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
      JVMFieldModifyPrestate _ptr fid ->
        "jvm_modifies_field: Invalid use before jvm_execute_func (" ++ J.fieldIdName fid ++ ")"
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
      JVMStaticModifyPrestate fid ->
        "jvm_modifies_static_field: Invalid use before jvm_execute_func (" ++ J.fieldIdName fid ++ ")"
      JVMElemNonReference ptr idx ->
        unlines
        [ "jvm_elem_is: Left-hand side is not a valid object reference"
        , "Left-hand side: " ++ show (MS.prettySetupValue ptr)
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
      JVMElemModifyPrestate _ptr idx ->
        "jvm_modifies_elem: Invalid use before jvm_execute_func (" ++ show idx ++ ")"
      JVMArrayNonReference ptr ->
        unlines
        [ "jvm_array_is: Left-hand side is not a valid object reference"
        , "Left-hand side: " ++ show (MS.prettySetupValue ptr)
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
      JVMArrayModifyPrestate _ptr ->
        "jvm_modifies_array: Invalid use before jvm_execute_func"
      JVMExecuteMissing ->
        "JVMSetup: Missing jvm_execute_func specification"
      JVMExecuteMultiple ->
        "jvm_execute_func: Multiple jvm_execute_func specifications"
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
      JVMReturnMissing expected ->
        unlines
        [ "JVMSetup: Missing jvm_return specification"
        , "Expected type: " ++ show expected
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
      JVMNonValueType tp ->
        unlines
        [ "Expected term with value type, but got"
        , show (prettyTypedTermTypePure tp)
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

parseClassName :: Text -> J.ClassName
parseClassName cname = J.mkClassName (J.dotsToSlashes $ Text.unpack cname)

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
  Text                {- ^ variable name    -} ->
  JavaType            {- ^ variable type    -} ->
  JVMSetupM TypedTerm {- ^ fresh typed term -}
jvm_fresh_var name jty =
  JVMSetupM $
  do sc <- lift $ lift getSharedContext
     case cryptolTypeOfActual jty of
       Nothing -> X.throwM $ JVMFreshVarInvalidType jty
       Just cty -> Setup.freshVariable sc name cty

jvm_alloc_object ::
  Text {- ^ class name -} ->
  JVMSetupM SetupValue
jvm_alloc_object cname =
  JVMSetupM $
  do loc <- SS.toW4Loc "jvm_alloc_object" <$> lift (lift getPosition)
     tags <- view Setup.croTags
     let md = MS.ConditionMetadata
              { MS.conditionLoc = loc
              , MS.conditionTags = tags
              , MS.conditionType = "object allocation"
              , MS.conditionContext = ""
              }
     n <- Setup.csVarCounter <<%= nextAllocIndex
     Setup.currentState . MS.csAllocs . at n ?=
       (md, AllocObject (parseClassName cname))
     return (MS.SetupVar n)

jvm_alloc_array ::
  Int {- array size -} ->
  JavaType             ->
  JVMSetupM SetupValue
jvm_alloc_array len ety =
  JVMSetupM $
  do loc <- SS.toW4Loc "jvm_alloc_array" <$> lift (lift getPosition)
     tags <- view Setup.croTags
     let md = MS.ConditionMetadata
              { MS.conditionLoc = loc
              , MS.conditionTags = tags
              , MS.conditionType = "array allocation"
              , MS.conditionContext = ""
              }
     n <- Setup.csVarCounter <<%= nextAllocIndex
     Setup.currentState . MS.csAllocs . at n ?= (md, AllocArray len (typeOfJavaType ety))
     return (MS.SetupVar n)

jvm_modifies_field ::
  SetupValue {- ^ object -} ->
  Text       {- ^ field name -} ->
  JVMSetupM ()
jvm_modifies_field ptr fname = generic_field_is ptr fname Nothing

jvm_field_is ::
  SetupValue {- ^ object -} ->
  Text       {- ^ field name -} ->
  SetupValue {- ^ field value -} ->
  JVMSetupM ()
jvm_field_is ptr fname val = generic_field_is ptr fname (Just val)

generic_field_is ::
  SetupValue {- ^ object -} ->
  Text {- ^ field name -} ->
  Maybe SetupValue {- ^ field value -} ->
  JVMSetupM ()
generic_field_is ptr fname mval =
  JVMSetupM $
  do pos <- lift (lift getPosition)
     let loc = SS.toW4Loc "jvm_field_is" pos
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
     fid <- either (X.throwM . JVMFieldFailure) pure =<< (liftIO $ runExceptT $ findField cb pos ptrTy (Text.unpack fname))
     case mval of
       Nothing -> pure ()
       Just val ->
         do valTy <- typeOfSetupValue cc env nameEnv val
            unless (registerCompatible (J.fieldIdType fid) valTy) $
              X.throwM $ JVMFieldTypeMismatch fid valTy
     tags <- view Setup.croTags
     let md = MS.ConditionMetadata
              { MS.conditionLoc = loc
              , MS.conditionTags = tags
              , MS.conditionType = "JVM field-is"
              , MS.conditionContext = ""
              }
     let pt = JVMPointsToField md ptr' fid mval
     let pts = st ^. Setup.csMethodSpec . MS.csPreState . MS.csPointsTos
     when (st ^. Setup.csPrePost == PreState && any (overlapPointsTo pt) pts) $
       X.throwM $ JVMFieldMultiple ptr' fid
     when (st ^. Setup.csPrePost == PreState && isNothing mval) $
       X.throwM $ JVMFieldModifyPrestate ptr' fid
     Setup.addPointsTo pt

jvm_modifies_static_field ::
  Text {- ^ field name -} ->
  JVMSetupM ()
jvm_modifies_static_field fname = generic_static_field_is fname Nothing

jvm_static_field_is ::
  Text       {- ^ field name -} ->
  SetupValue {- ^ field value -} ->
  JVMSetupM ()
jvm_static_field_is fname val = generic_static_field_is fname (Just val)

generic_static_field_is ::
  Text {- ^ field name -} ->
  Maybe SetupValue {- ^ field value -} ->
  JVMSetupM ()
generic_static_field_is fname mval =
  JVMSetupM $
  do pos <- lift (lift getPosition)
     let loc = SS.toW4Loc "jvm_static_field_is" pos
     st <- get
     let cc = st ^. Setup.csCrucibleContext
     let cb = cc ^. jccCodebase
     let env = MS.csAllocations (st ^. Setup.csMethodSpec)
     let nameEnv = MS.csTypeNames (st ^. Setup.csMethodSpec)
     let cname =
           case Text.unsnoc $ Text.dropWhileEnd (/= '.') fname of
               Nothing -> J.className (cc ^. jccJVMClass)
               Just (fname', _) -> J.mkClassName (Text.unpack fname')
     -- liftIO $ putStrLn $ "jvm_static_field_is " ++ J.unClassName cname ++ " " ++ fname
     let ptrTy = J.ClassType cname
     fid <- either (X.throwM . JVMStaticFailure) pure =<< (liftIO $ runExceptT $ findField cb pos ptrTy (Text.unpack fname))
     case mval of
       Nothing -> pure ()
       Just val ->
         do valTy <- typeOfSetupValue cc env nameEnv val
            unless (registerCompatible (J.fieldIdType fid) valTy) $
              X.throwM $ JVMStaticTypeMismatch fid valTy
     -- let name = J.unClassName (J.fieldIdClass fid) ++ "." ++ J.fieldIdName fid
     -- liftIO $ putStrLn $ "resolved to: " ++ name
     tags <- view Setup.croTags
     let md = MS.ConditionMetadata
              { MS.conditionLoc = loc
              , MS.conditionTags = tags
              , MS.conditionType = "JVM field-is (static)"
              , MS.conditionContext = ""
              }
     let pt = JVMPointsToStatic md fid mval
     let pts = st ^. Setup.csMethodSpec . MS.csPreState . MS.csPointsTos
     when (st ^. Setup.csPrePost == PreState && any (overlapPointsTo pt) pts) $
       X.throwM $ JVMStaticMultiple fid
     when (st ^. Setup.csPrePost == PreState && isNothing mval) $
       X.throwM $ JVMStaticModifyPrestate fid
     Setup.addPointsTo pt

jvm_modifies_elem ::
  SetupValue {- ^ array -} ->
  Int        {- ^ index -} ->
  JVMSetupM ()
jvm_modifies_elem ptr idx = generic_elem_is ptr idx Nothing

jvm_elem_is ::
  SetupValue {- ^ array -} ->
  Int        {- ^ index -} ->
  SetupValue {- ^ element value -} ->
  JVMSetupM ()
jvm_elem_is ptr idx val = generic_elem_is ptr idx (Just val)

generic_elem_is ::
  SetupValue {- ^ array -} ->
  Int {- ^ index -} ->
  Maybe SetupValue {- ^ element value -} ->
  JVMSetupM ()
generic_elem_is ptr idx mval =
  JVMSetupM $
  do loc <- SS.toW4Loc "jvm_elem_is" <$> lift (lift getPosition)
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
     unless (0 <= idx && idx < len) $
       X.throwM $ JVMElemInvalidIndex elTy len idx
     case mval of
       Nothing -> pure ()
       Just val ->
         do valTy <- typeOfSetupValue cc env nameEnv val
            unless (registerCompatible elTy valTy) $
              X.throwM $ JVMElemTypeMismatch idx elTy valTy
     tags <- view Setup.croTags
     let md = MS.ConditionMetadata
              { MS.conditionLoc = loc
              , MS.conditionTags = tags
              , MS.conditionType = "JVM elem-is"
              , MS.conditionContext = ""
              }
     let pt = JVMPointsToElem md ptr' idx mval
     let pts = st ^. Setup.csMethodSpec . MS.csPreState . MS.csPointsTos
     when (st ^. Setup.csPrePost == PreState && any (overlapPointsTo pt) pts) $
       X.throwM $ JVMElemMultiple ptr' idx
     when (st ^. Setup.csPrePost == PreState && isNothing mval) $
       X.throwM $ JVMElemModifyPrestate ptr' idx
     Setup.addPointsTo pt

jvm_modifies_array ::
  SetupValue {- ^ array reference -} ->
  JVMSetupM ()
jvm_modifies_array ptr = generic_array_is ptr Nothing

jvm_array_is ::
  SetupValue {- ^ array reference -} ->
  TypedTerm {- ^ array value -} ->
  JVMSetupM ()
jvm_array_is ptr val = generic_array_is ptr (Just val)

generic_array_is ::
  SetupValue {- ^ array reference -} ->
  Maybe TypedTerm {- ^ array value -} ->
  JVMSetupM ()
generic_array_is ptr mval =
  JVMSetupM $
  do loc <- SS.toW4Loc "jvm_array_is" <$> lift (lift getPosition)
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
     case mval of
       Nothing -> pure ()
       Just val ->
         do schema <- case ttType val of
              TypedTermSchema sch -> pure sch
              tp -> X.throwM (JVMNonValueType tp)
            let checkVal =
                  do ty <- Cryptol.isMono schema
                     (n, a) <- Cryptol.tIsSeq ty
                     guard (Cryptol.tIsNum n == Just (toInteger len))
                     jty <- toJVMType (Cryptol.evalValType mempty a)
                     guard (registerCompatible elTy jty)
            case checkVal of
              Nothing -> X.throwM (JVMArrayTypeMismatch len elTy schema)
              Just () -> pure ()

     tags <- view Setup.croTags
     let md = MS.ConditionMetadata
              { MS.conditionLoc = loc
              , MS.conditionTags = tags
              , MS.conditionType = "JVM array-is"
              , MS.conditionContext = ""
              }
     let pt = JVMPointsToArray md ptr' mval
     let pts = st ^. Setup.csMethodSpec . MS.csPreState . MS.csPointsTos
     when (st ^. Setup.csPrePost == PreState && any (overlapPointsTo pt) pts) $
       X.throwM $ JVMArrayMultiple ptr'
     when (st ^. Setup.csPrePost == PreState && isNothing mval) $
       X.throwM $ JVMArrayModifyPrestate ptr'
     Setup.addPointsTo pt

jvm_assert :: TypedTerm -> JVMSetupM ()
jvm_assert term = JVMSetupM $ do
  loc <- SS.toW4Loc "jvm_assert" <$> lift (lift getPosition)
  tags <- view Setup.croTags
  let md = MS.ConditionMetadata
           { MS.conditionLoc = loc
           , MS.conditionTags = tags
           , MS.conditionType = "specification assertion"
           , MS.conditionContext = ""
           }
  Setup.addCondition (MS.SetupCond_Pred md term)

jvm_precond :: TypedTerm -> JVMSetupM ()
jvm_precond term = JVMSetupM $ do
  loc <- SS.toW4Loc "jvm_precond" <$> lift (lift getPosition)
  Setup.crucible_precond loc term

jvm_postcond :: TypedTerm -> JVMSetupM ()
jvm_postcond term = JVMSetupM $ do
  loc <- SS.toW4Loc "jvm_postcond" <$> lift (lift getPosition)
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
     unless (st ^. Setup.csPrePost == PreState) $
       X.throwM JVMExecuteMultiple
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

jvm_setup_with_tag ::
  Text ->
  JVMSetupM () ->
  JVMSetupM ()
jvm_setup_with_tag tag m =
  JVMSetupM (Setup.setupWithTag tag (runJVMSetupM m))

jvm_ghost_value ::
  MS.GhostGlobal ->
  TypedTerm ->
  JVMSetupM ()
jvm_ghost_value ghost val = JVMSetupM $
  ghost_value ghost val

jvm_equal :: SetupValue -> SetupValue -> JVMSetupM ()
jvm_equal val1 val2 =
  JVMSetupM $
  do loc <- getW4Position "jvm_equal"
     st <- get
     let cc = st ^. Setup.csCrucibleContext
         env = MS.csAllocations (st ^. Setup.csMethodSpec)
         nameEnv = MS.csTypeNames (st ^. Setup.csMethodSpec)
     ty1 <- typeOfSetupValue cc env nameEnv val1
     ty2 <- typeOfSetupValue cc env nameEnv val2

     let b = registerCompatible ty1 ty2
     unless b $ throwCrucibleSetup loc $ unlines
       [ "Incompatible types when asserting equality:"
       , show ty1
       , show ty2
       ]
     Setup.crucible_equal loc val1 val2

jvm_unint :: [Text] -> JVMSetupM ()
jvm_unint term = JVMSetupM (Setup.declare_unint "jvm_unint" jccUninterp term)

--------------------------------------------------------------------------------

-- | Sort a list of things and group them into equivalence classes.
groupOn ::
  Ord b =>
  (a -> b) {- ^ equivalence class projection -} ->
  [a] -> [NonEmpty a]
groupOn f = NE.groupBy ((==) `on` f) . sortBy (compare `on` f)
