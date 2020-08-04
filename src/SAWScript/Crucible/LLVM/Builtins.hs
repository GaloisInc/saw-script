{- |
Module      : SAWScript.Crucible.LLVM.Builtins
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
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module SAWScript.Crucible.LLVM.Builtins
    ( show_cfg
    , crucible_execute_func
    , crucible_return
    , crucible_precond
    , crucible_postcond
    , crucible_llvm_cfg
    , crucible_llvm_extract
    , crucible_llvm_compositional_extract
    , crucible_llvm_verify
    , crucible_llvm_array_size_profile
    , crucible_setup_val_to_typed_term
    , crucible_spec_size
    , crucible_spec_solvers
    , crucible_ghost_value
    , crucible_declare_ghost_state
    , crucible_equal
    , crucible_points_to
    , crucible_conditional_points_to
    , crucible_points_to_array_prefix
    , crucible_fresh_pointer
    , crucible_llvm_unsafe_assume_spec
    , crucible_fresh_var
    , crucible_fresh_cryptol_var
    , crucible_alloc
    , crucible_alloc_aligned
    , crucible_alloc_readonly
    , crucible_alloc_readonly_aligned
    , crucible_alloc_with_size
    , crucible_symbolic_alloc
    , crucible_alloc_global
    , crucible_fresh_expanded_val

    --
    -- These function are common to LLVM & JVM implementation (not for external use)
    , setupArg
    , setupArgs
    , getGlobalPair
    , runCFG
    , baseCryptolType

    , displayVerifExceptionOpts
    , findDecl
    , findDefMaybeStatic
    , setupLLVMCrucibleContext
    ) where

import Prelude hiding (fail)

import qualified Control.Exception as X
import           Control.Lens

import           Control.Monad.State hiding (fail)
import           Control.Monad.Fail (MonadFail(..))
import qualified Data.Bimap as Bimap
import           Data.Char (isDigit)
import           Data.Foldable (for_, toList, fold)
import           Data.Function
import           Data.IORef
import           Data.List
import           Data.List.Extra (nubOrd)
import qualified Data.List.NonEmpty as NE
import           Data.Maybe
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
import           System.IO

import qualified Text.LLVM.AST as L
import qualified Text.LLVM.PP as L (ppType, ppSymbol)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>))
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import qualified Control.Monad.Trans.Maybe as MaybeT

-- parameterized-utils
import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some

-- cryptol
import qualified Cryptol.TypeCheck.Type as Cryptol
import qualified Cryptol.TypeCheck.PP as Cryptol
import qualified Verifier.SAW.Cryptol as Cryptol

-- what4
import qualified What4.Concrete as W4
import qualified What4.Config as W4
import qualified What4.FunctionName as W4
import qualified What4.LabeledPred as W4
import qualified What4.ProgramLoc as W4
import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4

-- crucible
import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Backend.SAWCore as CrucibleSAW
import qualified Lang.Crucible.CFG.Core as Crucible
import qualified Lang.Crucible.CFG.Extension as Crucible
  (IsSyntaxExtension)
import qualified Lang.Crucible.FunctionHandle as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Simulator.Breakpoint as Crucible
import qualified Lang.Crucible.Simulator.GlobalState as Crucible
import qualified Lang.Crucible.Simulator.PathSatisfiability as Crucible

-- crucible-llvm
import qualified Lang.Crucible.LLVM.ArraySizeProfile as Crucible
import qualified Lang.Crucible.LLVM.DataLayout as Crucible
import           Lang.Crucible.LLVM.Extension (LLVM)
import qualified Lang.Crucible.LLVM.Bytes as Crucible
import qualified Lang.Crucible.LLVM.MemModel as Crucible
import qualified Lang.Crucible.LLVM.MemType as Crucible
import qualified Lang.Crucible.LLVM.Translation as Crucible

import qualified SAWScript.Crucible.LLVM.CrucibleLLVM as Crucible

-- parameterized-utils
import qualified Data.Parameterized.TraversableFC as Ctx
import qualified Data.Parameterized.Context as Ctx

-- saw-core
import Verifier.SAW.FiniteValue (ppFirstOrderValue)
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST
import Verifier.SAW.Recognizer

-- cryptol-verifier
import Verifier.SAW.TypedTerm

-- saw-script
import SAWScript.AST (Located(..))
import SAWScript.Proof
import SAWScript.Prover.SolverStats
import SAWScript.Prover.Versions
import SAWScript.TopLevel
import SAWScript.Value
import SAWScript.Position
import SAWScript.Exceptions
import SAWScript.Options

import qualified SAWScript.Crucible.Common as Common
import           SAWScript.Crucible.Common (Sym)
import           SAWScript.Crucible.Common.MethodSpec (AllocIndex(..), nextAllocIndex, PrePost(..))
import qualified SAWScript.Crucible.Common.MethodSpec as MS
import           SAWScript.Crucible.Common.MethodSpec (SetupValue(..))
import           SAWScript.Crucible.Common.Override hiding (getSymInterface)
import qualified SAWScript.Crucible.Common.Setup.Builtins as Setup
import qualified SAWScript.Crucible.Common.Setup.Type as Setup

import SAWScript.Crucible.LLVM.Override
import SAWScript.Crucible.LLVM.ResolveSetupValue
import SAWScript.Crucible.LLVM.MethodSpecIR

type MemImpl = Crucible.MemImpl Sym

data LLVMVerificationException
  = MultipleStaticFunctions L.Symbol
  | DefNotFound L.Symbol [L.Symbol]
  | DeclNotFound L.Symbol [L.Symbol]
  | SetupError SetupError

displayVerifExceptionOpts :: Options -> LLVMVerificationException -> String
displayVerifExceptionOpts _ (MultipleStaticFunctions (L.Symbol nm)) =
  "Multiple non-equal definitions for `" ++ nm ++ "`."
displayVerifExceptionOpts opts (DefNotFound (L.Symbol nm) nms) =
  unlines $
  [ "Could not find definition for function named `" ++ nm ++ "`."
  ] ++ if simVerbose opts < 3
       then [ "Run SAW with --sim-verbose=3 to see all function names" ]
       else "Available function names:" : map (("  " ++) . show . L.ppSymbol) nms
displayVerifExceptionOpts opts (DeclNotFound (L.Symbol nm) nms) =
  unlines $
  [ "Could not find declaration for function named `" ++ nm ++ "`."
  ] ++ if simVerbose opts < 3
       then [ "Run SAW with --sim-verbose=3 to see all function names" ]
       else "Available function names:" : map (("  " ++) . show . L.ppSymbol) nms
displayVerifExceptionOpts _ (SetupError e) =
  "Error during simulation setup: " ++ show (ppSetupError e)

show_cfg :: SAW_CFG -> String
show_cfg (LLVM_CFG (Crucible.AnyCFG cfg)) = show cfg
show_cfg (JVM_CFG (Crucible.AnyCFG cfg)) = show cfg

-- | Determines whether one LLVM symbol is equivalent to another except
-- for a numeric suffix. This can determine whether one symbol is the
-- disambiguated name of a duplicated static function.
matchingStatics :: L.Symbol -> L.Symbol -> Bool
matchingStatics (L.Symbol a) (L.Symbol b) = go a b
  where
    go [] [] = True
    go (x:xs) (y:ys) = x == y && go xs ys
    go [] ('.':ds) = all isDigit ds
    go ('.':ds) [] = all isDigit ds
    go _ _ = False

findDefMaybeStatic :: L.Module -> String -> Either LLVMVerificationException (NE.NonEmpty L.Define)
findDefMaybeStatic llmod nm =
  case NE.nonEmpty (filter (\d -> matchingStatics (L.defName d) nm') (L.modDefines llmod)) of
    Nothing -> Left $ DefNotFound nm' $ map L.defName $ L.modDefines llmod
    Just defs -> Right defs
  where
    nm' = fromString nm

findDecl :: L.Module -> String -> Either LLVMVerificationException L.Declare
findDecl llmod nm =
  case find (\d -> (L.decName d) == nm') (L.modDeclares llmod) of
    Just decl -> Right decl
    Nothing -> Left $ DeclNotFound nm' $ map L.decName $ L.modDeclares llmod
  where
    nm' = fromString nm

resolveSpecName :: String -> TopLevel (String, Maybe String)
resolveSpecName nm =
  if Crucible.testBreakpointFunction nm
  then return
    ( (takeWhile (not . (== '#')) nm)
    , Just (tail (dropWhile (not . (== '#')) nm))
    )
  else return (nm, Nothing)

crucible_llvm_verify ::
  BuiltinContext         ->
  Options                ->
  Some LLVMModule        ->
  String                 ->
  [SomeLLVM MS.CrucibleMethodSpecIR] ->
  Bool                   ->
  LLVMCrucibleSetupM ()      ->
  ProofScript SatResult  ->
  TopLevel (SomeLLVM MS.CrucibleMethodSpecIR)
crucible_llvm_verify bic opts (Some lm) nm lemmas checkSat setup tactic =
  do lemmas' <- checkModuleCompatibility lm lemmas
     withMethodSpec bic opts lm nm setup $ \cc method_spec ->
       do (res_method_spec, _) <- verifyMethodSpec bic opts cc method_spec lemmas' checkSat tactic Nothing
          return $ SomeLLVM res_method_spec

crucible_llvm_unsafe_assume_spec ::
  BuiltinContext   ->
  Options          ->
  Some LLVMModule  ->
  String          {- ^ Name of the function -} ->
  LLVMCrucibleSetupM () {- ^ Boundary specification -} ->
  TopLevel (SomeLLVM MS.CrucibleMethodSpecIR)
crucible_llvm_unsafe_assume_spec bic opts (Some lm) nm setup =
  withMethodSpec bic opts lm nm setup $ \_ method_spec ->
  do printOutLnTop Info $
       unwords ["Assume override", (method_spec ^. csName)]
     return $ SomeLLVM method_spec

crucible_llvm_array_size_profile ::
  BuiltinContext ->
  Options ->
  Some LLVMModule ->
  String ->
  LLVMCrucibleSetupM () ->
  TopLevel [Crucible.Profile]
crucible_llvm_array_size_profile bic opts (Some lm) nm setup =
  withMethodSpec bic opts lm nm setup $ \cc method_spec ->
  do cell <- io $ newIORef Map.empty
     void $ verifyMethodSpec bic opts cc method_spec [] False undefined (Just cell)
     profiles <- io $ readIORef cell
     pure $ Map.toList profiles

crucible_llvm_compositional_extract ::
  BuiltinContext ->
  Options ->
  Some LLVMModule ->
  String ->
  String ->
  [SomeLLVM MS.CrucibleMethodSpecIR] ->
  Bool ->
  LLVMCrucibleSetupM () ->
  ProofScript SatResult ->
  TopLevel (SomeLLVM MS.CrucibleMethodSpecIR)
crucible_llvm_compositional_extract bic opts (Some lm) nm func_name lemmas checkSat setup tactic =
  do lemmas' <- checkModuleCompatibility lm lemmas
     withMethodSpec bic opts lm nm setup $ \cc method_spec ->
       do let value_input_parameters = mapMaybe
                (\(_, setup_value) -> setupValueAsExtCns setup_value)
                (Map.elems $ method_spec ^. MS.csArgBindings)
          let reference_input_parameters = mapMaybe
                (\(LLVMPointsTo _ _ _ setup_value) -> llvmPointsToValueAsExtCns setup_value)
                (method_spec ^. MS.csPreState ^. MS.csPointsTos)
          let input_parameters = nub $ value_input_parameters ++ reference_input_parameters
          let pre_free_variables = Map.fromList $
                map (\x -> (fromJust $ asExtCns $ ttTerm x, x)) $ method_spec ^. MS.csPreState ^. MS.csFreshVars
          let unsupported_input_parameters = Set.difference
                (Map.keysSet pre_free_variables)
                (Set.fromList input_parameters)
          when (not $ Set.null unsupported_input_parameters) $
            fail $ unlines
              [ "Unsupported input parameters:"
              , show unsupported_input_parameters
              , "An input parameter must be bound by crucible_execute_func or crucible_points_to."
              ]

          let return_output_parameter =
                case method_spec ^. MS.csRetValue of
                  Just setup_value -> setupValueAsExtCns setup_value
                  Nothing -> Nothing
          let reference_output_parameters =
                mapMaybe
                (\(LLVMPointsTo _ _ _ setup_value) -> llvmPointsToValueAsExtCns setup_value)
                (method_spec ^. MS.csPostState ^. MS.csPointsTos)
          let output_parameters =
                nub $ filter (isNothing . (Map.!?) pre_free_variables) $
                maybeToList return_output_parameter ++ reference_output_parameters
          let post_free_variables =
                Map.fromList $
                map (\x -> (fromJust $ asExtCns $ ttTerm x, x)) $ method_spec ^. MS.csPostState ^. MS.csFreshVars
          let unsupported_output_parameters =
                Set.difference (Map.keysSet post_free_variables) (Set.fromList output_parameters)
          when (not $ Set.null unsupported_output_parameters) $
            fail $ unlines
              [ "Unsupported output parameters:"
              , show unsupported_output_parameters
              , "An output parameter must be bound by crucible_return or crucible_points_to."
              ]

          (res_method_spec, post_override_state) <- verifyMethodSpec bic opts cc method_spec lemmas' checkSat tactic Nothing

          let shared_context = biSharedContext bic

          let output_values =
                map (((Map.!) $ post_override_state ^. termSub) . ecVarIndex) output_parameters

          extracted_func <-
            io $ scAbstractExts shared_context input_parameters
            =<< scTuple shared_context output_values
          when ([] /= getAllExts extracted_func) $
            fail "Non-functional simulation summary."

          extracted_func_const <-
            io $ scConstant shared_context func_name extracted_func
            =<< scTypeOf shared_context extracted_func
          let input_terms = map ttTerm $ map ((Map.!) pre_free_variables) input_parameters
          applied_extracted_func <- io $ scApplyAll shared_context extracted_func_const input_terms
          applied_extracted_func_selectors <-
            io $ forM [1 .. (length output_parameters)] $ \i ->
            mkTypedTerm shared_context
              =<< scTupleSelector shared_context applied_extracted_func i (length output_parameters)
          let output_parameter_substitution =
                Map.fromList $
                zip (map ecVarIndex output_parameters) (map ttTerm applied_extracted_func_selectors)
          let substitute_output_parameters =
                ttTermLens $ scInstantiateExt shared_context output_parameter_substitution
          let setup_value_substitute_output_parameter setup_value
                | SetupTerm term <- setup_value = SetupTerm <$> substitute_output_parameters term
                | otherwise = return $ setup_value
          let llvm_points_to_value_substitute_output_parameter = \case
                ConcreteSizeValue val -> ConcreteSizeValue <$> setup_value_substitute_output_parameter val
                SymbolicSizeValue arr sz ->
                  SymbolicSizeValue <$> substitute_output_parameters arr <*> substitute_output_parameters sz

          extracted_ret_value <- liftIO $ mapM
            setup_value_substitute_output_parameter
            (res_method_spec ^. MS.csRetValue)
          extracted_post_state_points_tos <- liftIO $ mapM
            (\(LLVMPointsTo x y z value) ->
              LLVMPointsTo x y z <$> llvm_points_to_value_substitute_output_parameter value)
            (res_method_spec ^. MS.csPostState ^. MS.csPointsTos)
          let extracted_method_spec = res_method_spec &
                MS.csRetValue .~ extracted_ret_value &
                MS.csPostState . MS.csPointsTos .~ extracted_post_state_points_tos

          typed_extracted_func_const <- io $ mkTypedTerm shared_context extracted_func_const
          modify' $
            extendEnv
              (Located func_name func_name $ PosInternal "crucible_llvm_compositional_extract")
              Nothing
              Nothing
              (VTerm typed_extracted_func_const)

          return $ SomeLLVM extracted_method_spec

setupValueAsExtCns :: SetupValue (Crucible.LLVM arch) -> Maybe (ExtCns Term)
setupValueAsExtCns =
  \case
    SetupTerm term -> asExtCns $ ttTerm term
    _ -> Nothing

llvmPointsToValueAsExtCns :: LLVMPointsToValue arch -> Maybe (ExtCns Term)
llvmPointsToValueAsExtCns =
  \case
    ConcreteSizeValue val -> setupValueAsExtCns val
    SymbolicSizeValue arr _sz -> asExtCns $ ttTerm arr

-- | Check that all the overrides/lemmas were actually from this module
checkModuleCompatibility ::
  LLVMModule arch ->
  [SomeLLVM MS.CrucibleMethodSpecIR] ->
  TopLevel [MS.CrucibleMethodSpecIR (LLVM arch)]
checkModuleCompatibility llvmModule = foldM step []
  where
    step accum (SomeLLVM lemma) =
      case testEquality (lemma ^. MS.csCodebase) llvmModule of
        Nothing -> throwTopLevel $ unlines
          [ "Failed to apply an override that was verified against a"
          , "different LLVM module"
          ]
        Just Refl -> pure (lemma:accum)


withMethodSpec ::
  BuiltinContext   ->
  Options          ->
  LLVMModule arch ->
  String            {- ^ Name of the function -} ->
  LLVMCrucibleSetupM () {- ^ Boundary specification -} ->
  ((?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch), Crucible.HasLLVMAnn Sym) =>
   LLVMCrucibleContext arch -> MS.CrucibleMethodSpecIR (LLVM arch) -> TopLevel a) ->
  TopLevel a
withMethodSpec bic opts lm nm setup action =
  do (nm', parent) <- resolveSpecName nm
     let edef = findDefMaybeStatic (modAST lm) nm'
     let edecl = findDecl (modAST lm) nm'
     let mtrans = modTrans lm
     defOrDecls <-
       case (edef, edecl) of
         (Right defs, _) -> return (NE.map Left defs)
         (_, Right decl) -> return (Right decl NE.:| [])
         (Left err, Left _) -> throwTopLevel (displayVerifExceptionOpts opts err)

     let ?lc = mtrans ^. Crucible.transContext . Crucible.llvmTypeCtx

     Crucible.llvmPtrWidth (mtrans ^. Crucible.transContext) $ \_ ->
       fmap NE.head $ forM defOrDecls $ \defOrDecl ->
         setupLLVMCrucibleContext bic opts lm $ \cc ->
           do let sym = cc^.ccBackend

              pos <- getPosition
              let setupLoc = toW4Loc "_SAW_verify_prestate" pos

              let est0 =
                    case defOrDecl of
                      Left def -> initialCrucibleSetupState cc def setupLoc parent
                      Right decl -> initialCrucibleSetupStateDecl cc decl setupLoc parent
              st0 <- either (throwTopLevel . show . ppSetupError) return est0

              -- execute commands of the method spec
              io $ W4.setCurrentProgramLoc sym setupLoc

              methodSpec <-
                view Setup.csMethodSpec <$>
                execStateT (runLLVMCrucibleSetupM setup) st0

              io $ checkSpecArgumentTypes cc methodSpec
              io $ checkSpecReturnType cc methodSpec

              action cc methodSpec

verifyMethodSpec ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch), Crucible.HasLLVMAnn Sym) =>
  BuiltinContext ->
  Options ->
  LLVMCrucibleContext arch ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  [MS.CrucibleMethodSpecIR (LLVM arch)] ->
  Bool ->
  ProofScript SatResult ->
  Maybe (IORef (Map Text.Text [[Maybe Int]])) ->
  TopLevel (MS.CrucibleMethodSpecIR (LLVM arch), OverrideState (LLVM arch))
verifyMethodSpec bic opts cc methodSpec lemmas checkSat tactic asp =
  do printOutLnTop Info $
       unwords ["Verifying", (methodSpec ^. csName) , "..."]

     let sym = cc^.ccBackend

     profFile <- rwProfilingFile <$> getTopLevelRW
     (writeFinalProfile, pfs) <- io $ Common.setupProfiling sym "crucible_llvm_verify" profFile

     -- set up the LLVM memory with a pristine heap
     let globals = cc^.ccLLVMGlobals
     let mvar = Crucible.llvmMemVar (ccLLVMContext cc)
     mem0 <-
       case Crucible.lookupGlobal mvar globals of
         Nothing   -> fail "internal error: LLVM Memory global not found"
         Just mem0 -> return mem0
     -- push a memory stack frame if starting from a breakpoint
     let mem = if isJust (methodSpec^.csParentName)
               then mem0
                 { Crucible.memImplHeap = Crucible.pushStackFrameMem
                   (Crucible.memImplHeap mem0)
                 }
               else mem0
     let globals1 = Crucible.llvmGlobals (ccLLVMContext cc) mem

     -- construct the initial state for verifications
     (args, assumes, env, globals2) <-
       io $ verifyPrestate opts cc methodSpec globals1

     -- save initial path conditions
     frameIdent <- io $ Crucible.pushAssumptionFrame sym

     -- run the symbolic execution
     printOutLnTop Info $
       unwords ["Simulating", (methodSpec ^. csName) , "..."]
     top_loc <- toW4Loc "crucible_llvm_verify" <$> getPosition
     (ret, globals3) <-
       io $ verifySimulate opts cc pfs methodSpec args assumes top_loc lemmas globals2 checkSat asp

     -- collect the proof obligations
     (asserts, post_override_state) <-
       verifyPoststate opts (biSharedContext bic) cc
       methodSpec env globals3 ret

     -- restore previous assumption state
     _ <- io $ Crucible.popAssumptionFrame sym frameIdent

     -- attempt to verify the proof obligations
     printOutLnTop Info $
       unwords ["Checking proof obligations", (methodSpec ^. csName), "..."]
     stats <- verifyObligations cc methodSpec tactic assumes asserts
     io $ writeFinalProfile

     return (methodSpec & MS.csSolverStats .~ stats, post_override_state)


verifyObligations :: LLVMCrucibleContext arch
                  -> MS.CrucibleMethodSpecIR (LLVM arch)
                  -> ProofScript SatResult
                  -> [Crucible.LabeledPred Term Crucible.AssumptionReason]
                  -> [(String, Term)]
                  -> TopLevel SolverStats
verifyObligations cc mspec tactic assumes asserts =
  do let sym = cc^.ccBackend
     st     <- io $ readIORef $ W4.sbStateManager sym
     let sc  = CrucibleSAW.saw_ctx st
     assume <- io $ scAndList sc (toListOf (folded . Crucible.labeledPred) assumes)
     let nm  = mspec ^. csName
     stats <-
       forM (zip [(0::Int)..] asserts) $ \(n, (msg, assert)) ->
       do goal   <- io $ scImplies sc assume assert
          goal'  <- io $ scEqTrue sc goal
          let goalname = concat [nm, " (", takeWhile (/= '\n') msg, ")"]
              proofgoal = ProofGoal n "vc" goalname (Prop goal')
          r <- evalStateT tactic (startProof proofgoal)
          case r of
            Unsat stats -> return stats
            SatMulti stats vals ->
              do printOutLnTop Info $ unwords ["Subgoal failed:", nm, msg]
                 printOutLnTop Info (show stats)
                 printOutLnTop OnlyCounterExamples "----------Counterexample----------"
                 opts <- sawPPOpts <$> rwPPOpts <$> getTopLevelRW
                 if null vals then
                   printOutLnTop OnlyCounterExamples "<<All settings of the symbolic variables constitute a counterexample>>"
                 else
                   let showAssignment (name, val) = "  " ++ name ++ ": " ++ show (ppFirstOrderValue opts val) in
                   mapM_ (printOutLnTop OnlyCounterExamples . showAssignment) vals
                 printOutLnTop OnlyCounterExamples "----------------------------------"
                 throwTopLevel "Proof failed." -- Mirroring behavior of llvm_verify
     printOutLnTop Info $ unwords ["Proof succeeded!", nm]
     return (mconcat stats)

throwMethodSpec :: MS.CrucibleMethodSpecIR (LLVM arch) -> String -> IO a
throwMethodSpec mspec msg = X.throw $ LLVMMethodSpecException (mspec ^. MS.csLoc) msg

-- | Check that the specified arguments have the expected types.
--
-- The expected types are inferred from the LLVM module.
checkSpecArgumentTypes ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  LLVMCrucibleContext arch ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  IO ()
checkSpecArgumentTypes cc mspec = mapM_ resolveArg [0..(nArgs-1)]
  where
    nArgs = toInteger (length (mspec ^. MS.csArgs))
    tyenv = MS.csAllocations mspec
    nameEnv = mspec ^. MS.csPreState . MS.csVarTypeNames
    nm = mspec^.csName

    checkArgTy i mt mt' =
      do b <- checkRegisterCompatibility mt mt'
         unless b $
           throwMethodSpec mspec $ unlines
           [ "Type mismatch in argument " ++ show i ++ " when verifying " ++ show nm
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
        Nothing -> throwMethodSpec mspec $ unwords
          ["Argument", show i, "unspecified when verifying", show nm]


-- | Check that the specified return value has the expected type.
--
-- The expected type is inferred from the LLVM module.
--
-- TODO: generalize, put in Setup.Builtins
checkSpecReturnType ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  LLVMCrucibleContext arch ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  IO ()
checkSpecReturnType cc mspec =
  case (mspec ^. MS.csRetValue, mspec ^. MS.csRet) of
    (Just _, Nothing) ->
         throwMethodSpec mspec $ unlines
           [ "Could not resolve return type of " ++ mspec ^. csName
           , "Raw type: " ++ show (mspec ^. MS.csRet)
           ]
    (Just sv, Just retTy) ->
      do retTy' <-
           typeOfSetupValue cc
             (MS.csAllocations mspec) -- map allocation indices to allocations
             (mspec ^. MS.csPreState . MS.csVarTypeNames) -- map alloc indices to var names
             sv
         -- This check is too lax, see saw-script#443
         b <- checkRegisterCompatibility retTy retTy'
         unless b $ throwMethodSpec mspec $ unlines
           [ "Incompatible types for return value when verifying " ++ mspec^.csName
           , "Expected: " ++ show retTy
           , "but given value of type: " ++ show retTy'
           ]
    (Nothing, _) -> return ()

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
  (Crucible.HasPtrWidth (Crucible.ArchWidth arch), Crucible.HasLLVMAnn Sym) =>
  Options ->
  LLVMCrucibleContext arch ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  Crucible.SymGlobalState Sym ->
  IO ([(Crucible.MemType, LLVMVal)],
      [Crucible.LabeledPred Term Crucible.AssumptionReason],
      Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)),
      Crucible.SymGlobalState Sym)
verifyPrestate opts cc mspec globals =
  do let ?lc = ccTypeCtx cc
     let sym = cc^.ccBackend
     let prestateLoc = W4.mkProgramLoc "_SAW_verify_prestate" W4.InternalPos
     liftIO $ W4.setCurrentProgramLoc sym prestateLoc

     let lvar = Crucible.llvmMemVar (ccLLVMContext cc)
     let Just mem = Crucible.lookupGlobal lvar globals

     -- Allocate LLVM memory for each 'crucible_alloc'
     (env1, mem') <- runStateT
       (traverse (doAlloc cc)  $ mspec ^. MS.csPreState . MS.csAllocs)
       mem

     env2 <-
       Map.traverseWithKey
         (\k _ -> executeFreshPointer cc k)
         (mspec ^. MS.csPreState . MS.csFreshPointers)
     let env = Map.unions [env1, env2]

     mem'' <- setupGlobalAllocs cc mspec mem'

     mem''' <- setupPrePointsTos mspec opts cc env (mspec ^. MS.csPreState . MS.csPointsTos) mem''

     let globals1 = Crucible.insertGlobal lvar mem''' globals
     (globals2,cs) <-
       setupPrestateConditions mspec cc mem''' env globals1 (mspec ^. MS.csPreState . MS.csConditions)
     args <- resolveArguments cc mem''' mspec env

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
  LLVMCrucibleContext arch       ->
  Crucible.MemImpl Sym ->
  MS.CrucibleMethodSpecIR (LLVM arch)       ->
  Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)) ->
  IO [(Crucible.MemType, LLVMVal)]
resolveArguments cc mem mspec env = mapM resolveArg [0..(nArgs-1)]
  where
    nArgs = toInteger (length (mspec ^. MS.csArgs))
    tyenv = MS.csAllocations mspec
    nameEnv = mspec ^. MS.csPreState . MS.csVarTypeNames
    nm = mspec^.csName

    resolveArg i =
      case Map.lookup i (mspec ^. MS.csArgBindings) of
        Just (mt, sv) -> do
          v <- resolveSetupVal cc mem env tyenv nameEnv sv
          return (mt, v)
        Nothing -> throwMethodSpec mspec $ unwords
          ["Argument", show i, "unspecified when verifying", show nm]

--------------------------------------------------------------------------------

-- | For each "crucible_global_alloc" in the method specification, allocate and
-- register the appropriate memory.
setupGlobalAllocs :: forall arch.
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  LLVMCrucibleContext arch ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  MemImpl ->
  IO MemImpl
setupGlobalAllocs cc mspec mem0 = foldM go mem0 $ mspec ^. MS.csGlobalAllocs
  where
    sym = cc ^. ccBackend

    go :: MemImpl -> MS.AllocGlobal (LLVM arch) -> IO MemImpl
    go mem (LLVMAllocGlobal _ symbol@(L.Symbol name)) = do
      let mtrans = ccLLVMModuleTrans cc
          gimap = Crucible.globalInitMap mtrans
      case Map.lookup symbol gimap of
        Just (g, Right (mt, _)) ->
          do when (L.gaConstant $ L.globalAttrs g) . throwMethodSpec mspec $ mconcat
               [ "Global variable \""
               , name
               , "\" is not mutable"
               ]
             let sz = Crucible.memTypeSize (Crucible.llvmDataLayout ?lc) mt
             sz' <- W4.bvLit sym ?ptrWidth $ Crucible.bytesToBV ?ptrWidth sz
             alignment <-
               case L.globalAlign g of
                 Just a | a > 0 ->
                   case Crucible.toAlignment $ Crucible.toBytes a of
                     Nothing -> throwMethodSpec mspec $ mconcat
                       [ "Global variable \""
                       , name
                       , "\" has invalid alignment: "
                       , show a
                       ]
                     Just al -> return al
                 _ -> pure $ Crucible.memTypeAlign (Crucible.llvmDataLayout ?lc) mt
             (ptr, mem') <- Crucible.doMalloc sym Crucible.GlobalAlloc Crucible.Mutable name mem sz' alignment
             pure $ Crucible.registerGlobal mem' [symbol] ptr
        _ -> throwMethodSpec mspec $ mconcat
          [ "Global variable \""
          , name
          , "\" does not exist"
          ]

-- | For each points-to constraint in the pre-state section of the
-- function spec, write the given value to the address of the given
-- pointer.
setupPrePointsTos :: forall arch.
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch), Crucible.HasLLVMAnn Sym) =>
  MS.CrucibleMethodSpecIR (LLVM arch)       ->
  Options ->
  LLVMCrucibleContext arch       ->
  Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)) ->
  [MS.PointsTo (LLVM arch)]                 ->
  MemImpl                    ->
  IO MemImpl
setupPrePointsTos mspec opts cc env pts mem0 = foldM go mem0 pts
  where
    tyenv   = MS.csAllocations mspec
    nameEnv = mspec ^. MS.csPreState . MS.csVarTypeNames

    go :: MemImpl -> MS.PointsTo (LLVM arch) -> IO MemImpl
    go mem (LLVMPointsTo _loc cond ptr val) =
      do ptr' <- resolveSetupVal cc mem env tyenv nameEnv ptr
         ptr'' <- case ptr' of
           Crucible.LLVMValInt blk off
             | Just Refl <- testEquality (W4.bvWidth off) Crucible.PtrWidth
             -> return (Crucible.LLVMPointer blk off)
           _ -> throwMethodSpec mspec "Non-pointer value found in points-to assertion"

         cond' <- mapM (resolveSAWPred cc . ttTerm) cond

         storePointsToValue opts cc env tyenv nameEnv mem cond' ptr'' val Nothing

-- | Sets up globals (ghost variable), and collects boolean terms
-- that should be assumed to be true.
setupPrestateConditions ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  MS.CrucibleMethodSpecIR (LLVM arch)        ->
  LLVMCrucibleContext arch        ->
  Crucible.MemImpl Sym ->
  Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)) ->
  Crucible.SymGlobalState Sym ->
  [MS.SetupCondition (LLVM arch)]            ->
  IO (Crucible.SymGlobalState Sym, [Crucible.LabeledPred Term Crucible.AssumptionReason])
setupPrestateConditions mspec cc mem env = aux []
  where
    tyenv   = MS.csAllocations mspec
    nameEnv = mspec ^. MS.csPreState . MS.csVarTypeNames

    aux acc globals [] = return (globals, acc)

    aux acc globals (MS.SetupCond_Equal loc val1 val2 : xs) =
      do val1' <- resolveSetupVal cc mem env tyenv nameEnv val1
         val2' <- resolveSetupVal cc mem env tyenv nameEnv val2
         t     <- assertEqualVals cc val1' val2'
         let lp = Crucible.LabeledPred t (Crucible.AssumptionReason loc "equality precondition")
         aux (lp:acc) globals xs

    aux acc globals (MS.SetupCond_Pred loc tm : xs) =
      let lp = Crucible.LabeledPred (ttTerm tm) (Crucible.AssumptionReason loc "precondition") in
      aux (lp:acc) globals xs

    aux acc globals (MS.SetupCond_Ghost () _loc var val : xs) =
      aux acc (Crucible.insertGlobal var val globals) xs

--------------------------------------------------------------------------------

-- | Create a SAWCore formula asserting that two 'LLVMVal's are equal.
assertEqualVals ::
  LLVMCrucibleContext arch ->
  LLVMVal ->
  LLVMVal ->
  IO Term
assertEqualVals cc v1 v2 =
  CrucibleSAW.toSC (cc^.ccBackend) =<< equalValsPred cc v1 v2

--------------------------------------------------------------------------------

-- TODO(langston): combine with/move to executeAllocation
doAlloc ::
  (Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  LLVMCrucibleContext arch       ->
  LLVMAllocSpec ->
  StateT MemImpl IO (LLVMPtr (Crucible.ArchWidth arch))
doAlloc cc (LLVMAllocSpec mut _memTy alignment sz loc) = StateT $ \mem ->
  do let sym = cc^.ccBackend
     sz' <- liftIO $ resolveSAWSymBV cc Crucible.PtrWidth sz
     let l = show (W4.plSourceLoc loc)
     liftIO $
       Crucible.doMalloc sym Crucible.HeapAlloc mut l mem sz' alignment

--------------------------------------------------------------------------------

ppAbortedResult :: LLVMCrucibleContext arch
                -> Crucible.AbortedResult Sym a
                -> Doc
ppAbortedResult cc = Common.ppAbortedResult (ppGlobalPair cc)

ppGlobalPair :: LLVMCrucibleContext arch
             -> Crucible.GlobalPair Sym a
             -> Doc
ppGlobalPair cc gp =
  let mvar = Crucible.llvmMemVar (ccLLVMContext cc)
      globals = gp ^. Crucible.gpGlobals in
  case Crucible.lookupGlobal mvar globals of
    Nothing -> text "LLVM Memory global variable not initialized"
    Just mem -> Crucible.ppMem mem


--------------------------------------------------------------------------------

registerOverride ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth wptr, wptr ~ Crucible.ArchWidth arch, Crucible.HasLLVMAnn Sym) =>
  Options                    ->
  LLVMCrucibleContext arch       ->
  Crucible.SimContext (CrucibleSAW.SAWCruciblePersonality Sym) Sym (Crucible.LLVM arch) ->
  W4.ProgramLoc              ->
  [MS.CrucibleMethodSpecIR (LLVM arch)]     ->
  Crucible.OverrideSim (CrucibleSAW.SAWCruciblePersonality Sym) Sym (Crucible.LLVM arch) rtp args ret ()
registerOverride opts cc sim_ctx top_loc cs =
  do let sym = cc^.ccBackend
     sc <- CrucibleSAW.saw_ctx <$> liftIO (readIORef (W4.sbStateManager sym))
     let fstr = (head cs)^.csName
         fsym = L.Symbol fstr
         llvmctx = ccLLVMContext cc
         mvar = Crucible.llvmMemVar llvmctx
         halloc = Crucible.simHandleAllocator sim_ctx
         matches dec = matchingStatics (L.decName dec) fsym
     liftIO $
       printOutLn opts Info $ "Registering overrides for `" ++ fstr ++ "`"

     case filter matches (Crucible.allModuleDeclares (ccLLVMModuleAST cc)) of
       [] -> fail $ "Couldn't find declaration for `" ++ fstr ++ "` when registering override for it."
       (d:ds) ->
         Crucible.llvmDeclToFunHandleRepr' d $ \argTypes retType ->
           do let fn_name = W4.functionNameFromText $ Text.pack fstr
              h <- liftIO $ Crucible.mkHandle' halloc fn_name argTypes retType
              Crucible.bindFnHandle h
                $ Crucible.UseOverride
                $ Crucible.mkOverride' fn_name retType
                $ methodSpecHandler opts sc cc top_loc cs h
              mem <- Crucible.readGlobal mvar
              let bindPtr m decl =
                    do printOutLn opts Info $ "  variant `" ++ show (L.decName decl) ++ "`"
                       Crucible.bindLLVMFunPtr sym decl h m
              mem' <- liftIO $ foldM bindPtr mem (d:ds)
              Crucible.writeGlobal mvar mem'

registerInvariantOverride ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch), Crucible.HasLLVMAnn Sym) =>
  Options ->
  LLVMCrucibleContext arch ->
  W4.ProgramLoc ->
  HashMap Crucible.SomeHandle [Crucible.BreakpointName] ->
  [MS.CrucibleMethodSpecIR (LLVM arch)] ->
  IO (Crucible.ExecutionFeature (CrucibleSAW.SAWCruciblePersonality Sym) Sym (Crucible.LLVM arch) rtp)
registerInvariantOverride opts cc top_loc all_breakpoints cs =
  do sc <- CrucibleSAW.saw_ctx <$> (liftIO $ readIORef $ W4.sbStateManager $ cc^.ccBackend)
     let name = (head cs) ^. csName
     parent <-
       case nubOrd $ map (view csParentName) cs of
         [Just unique_parent] -> return unique_parent
         _ -> fail $ "Multiple parent functions for breakpoint: " ++ name
     liftIO $ printOutLn opts Info $ "Registering breakpoint `" ++ name ++ "`"
     withBreakpointCfgAndBlockId cc name parent $ \cfg breakpoint_block_id ->
       do let breakpoint_name = Crucible.BreakpointName $ Text.pack name
          let h = Crucible.cfgHandle cfg
          let arg_types = Crucible.blockInputs $
                Crucible.getBlock breakpoint_block_id $
                Crucible.cfgBlockMap cfg
          let ret_type = Crucible.handleReturnType h
          let halloc = Crucible.simHandleAllocator (cc ^. ccLLVMSimContext)
          hInvariant <- Crucible.mkHandle' halloc (W4.plFunction top_loc) arg_types ret_type
          Crucible.breakAndReturn
            cfg
            breakpoint_name
            arg_types
            ret_type
            (methodSpecHandler opts sc cc top_loc cs hInvariant)
            all_breakpoints

--------------------------------------------------------------------------------

withCfg ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch), Crucible.HasLLVMAnn Sym) =>
  LLVMCrucibleContext arch ->
  String ->
  (forall blocks init ret . Crucible.CFG (Crucible.LLVM arch) blocks init ret -> IO a) ->
  IO a
withCfg context name k =
  do let function_id = L.Symbol name
     case Map.lookup function_id (Crucible.cfgMap (ccLLVMModuleTrans context)) of
       Just (_, Crucible.AnyCFG cfg) -> k cfg
       Nothing -> fail $ "Unexpected function name: " ++ name

withCfgAndBlockId ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch), Crucible.HasLLVMAnn Sym) =>
  LLVMCrucibleContext arch ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  (forall blocks init args ret . Crucible.CFG (Crucible.LLVM arch) blocks init ret -> Crucible.BlockID blocks args -> IO a) ->
  IO a
withCfgAndBlockId context method_spec k =
  case method_spec ^. csParentName of
    Nothing -> withCfg context (method_spec ^. csName) $ \cfg ->
      k cfg (Crucible.cfgEntryBlockID cfg)
    Just parent -> withBreakpointCfgAndBlockId
      context
      (method_spec ^. csName)
      parent
      k

withBreakpointCfgAndBlockId ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch), Crucible.HasLLVMAnn Sym) =>
  LLVMCrucibleContext arch ->
  String ->
  String ->
  (forall blocks init args ret . Crucible.CFG (Crucible.LLVM arch) blocks init ret -> Crucible.BlockID blocks args -> IO a) ->
  IO a
withBreakpointCfgAndBlockId context name parent k =
  do let breakpoint_name = Crucible.BreakpointName $ Text.pack name
     withCfg context parent $ \cfg ->
       case Bimap.lookup breakpoint_name (Crucible.cfgBreakpoints cfg) of
         Just (Some breakpoint_block_id) -> k cfg breakpoint_block_id
         Nothing -> fail $ "Unexpected breakpoint name: " ++ name

verifySimulate ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth wptr, wptr ~ Crucible.ArchWidth arch, Crucible.HasLLVMAnn Sym) =>
  Options ->
  LLVMCrucibleContext arch ->
  [Crucible.GenericExecutionFeature Sym] ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  [(Crucible.MemType, LLVMVal)] ->
  [Crucible.LabeledPred Term Crucible.AssumptionReason] ->
  W4.ProgramLoc ->
  [MS.CrucibleMethodSpecIR (LLVM arch)] ->
  Crucible.SymGlobalState Sym ->
  Bool ->
  Maybe (IORef (Map Text.Text [[Maybe Int]])) ->
  IO (Maybe (Crucible.MemType, LLVMVal), Crucible.SymGlobalState Sym)
verifySimulate opts cc pfs mspec args assumes top_loc lemmas globals checkSat asp =
  withCfgAndBlockId cc mspec $ \cfg entryId ->
  do let argTys = Crucible.blockInputs $
           Crucible.getBlock entryId $ Crucible.cfgBlockMap cfg
     let retTy = Crucible.handleReturnType $ Crucible.cfgHandle cfg

     args' <- prepareArgs argTys (map snd args)
     let simCtx = cc^.ccLLVMSimContext
     psatf <-
       Crucible.pathSatisfiabilityFeature sym
         (CrucibleSAW.considerSatisfiability sym)
     let patSatGenExecFeature = if checkSat then [psatf] else []
     when checkSat checkYicesVersion
     let (funcLemmas, invLemmas) =
           partition (isNothing . view csParentName) lemmas

     breakpoints <-
       forM (groupOn (view csParentName) invLemmas) $ \specs ->
       do let parent = fromJust $ (head specs) ^. csParentName
          let breakpoint_names = nubOrd $
                map (Crucible.BreakpointName . Text.pack . view csName) specs
          withCfg cc parent $ \parent_cfg ->
            return
              ( Crucible.SomeHandle (Crucible.cfgHandle parent_cfg)
              , breakpoint_names
              )

     invariantExecFeatures <-
       mapM
       (registerInvariantOverride opts cc top_loc (HashMap.fromList breakpoints))
       (groupOn (view csName) invLemmas)

     additionalFeatures <-
       mapM (Crucible.arraySizeProfile (ccLLVMContext cc)) $ maybeToList asp

     let execFeatures =
           invariantExecFeatures ++
           map Crucible.genericToExecutionFeature (patSatGenExecFeature ++ pfs) ++
           additionalFeatures

     let initExecState =
           Crucible.InitialState simCtx globals Crucible.defaultAbortHandler retTy $
           Crucible.runOverrideSim retTy $
           do mapM_ (registerOverride opts cc simCtx top_loc)
                    (groupOn (view csName) funcLemmas)
              liftIO $
                do preds <- (traverse . Crucible.labeledPred) (resolveSAWPred cc) assumes
                   Crucible.addAssumptions sym (Seq.fromList preds)
              Crucible.regValue <$> (Crucible.callBlock cfg entryId args')
     res <- Crucible.executeCrucible execFeatures initExecState
     case res of
       Crucible.FinishedResult _ partialResult ->
         do Crucible.GlobalPair retval globals1 <-
              getGlobalPair opts partialResult
            let ret_ty = mspec ^. MS.csRet
            retval' <-
              case ret_ty of
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
scAndList sc = conj . filter nontrivial
  where
    nontrivial x = asBool x /= Just True
    conj [] = scBool sc True
    conj (x : xs) = foldM (scAnd sc) x xs

--------------------------------------------------------------------------------

verifyPoststate ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth wptr, wptr ~ Crucible.ArchWidth arch, Crucible.HasLLVMAnn Sym) =>
  Options                           {- ^ saw script debug and print options           -} ->
  SharedContext                     {- ^ saw core context                             -} ->
  LLVMCrucibleContext arch              {- ^ crucible context                             -} ->
  MS.CrucibleMethodSpecIR (LLVM arch)              {- ^ specification                                -} ->
  Map AllocIndex (LLVMPtr wptr)     {- ^ allocation substitution                      -} ->
  Crucible.SymGlobalState Sym       {- ^ global variables                             -} ->
  Maybe (Crucible.MemType, LLVMVal) {- ^ optional return value                        -} ->
  TopLevel ([(String, Term)], OverrideState (LLVM arch))         {- ^ generated labels and verification conditions -}
verifyPoststate opts sc cc mspec env0 globals ret =
  do poststateLoc <- toW4Loc "_SAW_verify_poststate" <$> getPosition
     io $ W4.setCurrentProgramLoc sym poststateLoc

     let terms0 = Map.fromList
           [ (ecVarIndex ec, ttTerm tt)
           | tt <- mspec ^. MS.csPreState . MS.csFreshVars
           , let Just ec = asExtCns (ttTerm tt) ]

     let initialFree =
           Set.fromList
           (map (termId . ttTerm) (view (MS.csPostState . MS.csFreshVars) mspec))
     matchPost <-
       io $
       runOverrideMatcher sym globals env0 terms0 initialFree poststateLoc $
       do matchResult
          learnCond opts sc cc mspec PostState (mspec ^. MS.csGlobalAllocs) (mspec ^. MS.csPostState)

     st <-
       case matchPost of
         Left err      -> throwTopLevel (show err)
         Right (_, st) -> return st
     io $ for_ (view osAsserts st) $ \(W4.LabeledPred p r) ->
       Crucible.addAssertion sym (Crucible.LabeledPred p r)

     obligations <- io $ Crucible.getProofObligations sym
     io $ Crucible.clearProofObligations sym
     sc_obligations <- io $ mapM verifyObligation (Crucible.proofGoalsToList obligations)
     return (sc_obligations, st)

  where
    sym = cc^.ccBackend

    verifyObligation (Crucible.ProofGoal hyps (Crucible.LabeledPred concl err)) =
      do hypTerm <- CrucibleSAW.toSC sym =<< W4.andAllOf sym (folded . Crucible.labeledPred) hyps
         conclTerm  <- CrucibleSAW.toSC sym concl
         obligation <- scImplies sc hypTerm conclTerm
         return (unlines ["safety assertion:", show err], obligation)

    matchResult =
      case (ret, mspec ^. MS.csRetValue) of
        (Just (rty,r), Just expect) -> matchArg opts sc cc mspec PostState r rty expect
        (Nothing     , Just _ )     ->
          fail "verifyPoststate: unexpected crucible_return specification"
        _ -> return ()

--------------------------------------------------------------------------------

setupLLVMCrucibleContext ::
  BuiltinContext ->
  Options ->
  LLVMModule arch ->
  ((?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch), Crucible.HasLLVMAnn Sym) =>
   LLVMCrucibleContext arch -> TopLevel a) ->
  TopLevel a
setupLLVMCrucibleContext bic opts lm action =
  do halloc <- getHandleAlloc
     let llvm_mod = modAST lm
     let mtrans = modTrans lm
     let ctx = mtrans^.Crucible.transContext
     smt_array_memory_model_enabled <- gets rwSMTArrayMemoryModel
     crucible_assert_then_assume_enabled <- gets rwCrucibleAssertThenAssume
     what4HashConsing <- gets rwWhat4HashConsing
     Crucible.llvmPtrWidth ctx $ \wptr ->
       Crucible.withPtrWidth wptr $
       do let ?lc = ctx^.Crucible.llvmTypeCtx
          bbMapRef <- io $ newIORef mempty
          let ?badBehaviorMap = bbMapRef
          cc <-
            io $
            do let gen = globalNonceGenerator
               let sc  = biSharedContext bic
               let verbosity = simVerbose opts
               sym <- CrucibleSAW.newSAWCoreBackend W4.FloatRealRepr sc gen

               let cfg = W4.getConfiguration sym
               verbSetting <- W4.getOptionSetting W4.verbosity cfg
               _ <- W4.setOpt verbSetting (toInteger verbosity)

               cacheTermsSetting <- W4.getOptionSetting W4.cacheTerms cfg
               _ <- W4.setOpt cacheTermsSetting what4HashConsing

               W4.extendConfig
                 [ W4.opt
                     enableSMTArrayMemoryModel
                     (W4.ConcreteBool smt_array_memory_model_enabled)
                     (PP.text "Enable SMT array memory model")
                 ]
                 cfg

               crucible_assert_then_assume_option_setting <- W4.getOptionSetting
                 Crucible.assertThenAssumeConfigOption
                 cfg
               _ <- W4.setOpt
                 crucible_assert_then_assume_option_setting
                 crucible_assert_then_assume_enabled

               let bindings = Crucible.fnBindingsFromList []
               let simctx   = Crucible.initSimContext sym intrinsics halloc stdout
                                 bindings (Crucible.llvmExtensionImpl Crucible.defaultMemOptions) CrucibleSAW.SAWCruciblePersonality
               mem <- Crucible.populateConstGlobals sym (Crucible.globalInitMap mtrans)
                        =<< Crucible.initializeMemoryConstGlobals sym ctx llvm_mod

               let globals  = Crucible.llvmGlobals ctx mem

               let setupMem =
                     do -- register the callable override functions
                        Crucible.register_llvm_overrides llvm_mod [] [] ctx
                        -- register all the functions defined in the LLVM module
                        mapM_ (Crucible.registerModuleFn ctx) $ Map.elems $ Crucible.cfgMap mtrans

               let initExecState =
                     Crucible.InitialState simctx globals Crucible.defaultAbortHandler Crucible.UnitRepr $
                     Crucible.runOverrideSim Crucible.UnitRepr setupMem
               res <- Crucible.executeCrucible [] initExecState
               (lglobals, lsimctx) <-
                   case res of
                     Crucible.FinishedResult st (Crucible.TotalRes gp) -> return (gp^.Crucible.gpGlobals, st)
                     Crucible.FinishedResult st (Crucible.PartialRes _ _ gp _) ->
                       return (gp^.Crucible.gpGlobals, st)
                     _ -> fail "simulator initialization failed!"

               return
                  LLVMCrucibleContext{ _ccLLVMModule = lm
                                     , _ccBackend = sym
                                     , _ccLLVMSimContext = lsimctx
                                     , _ccLLVMGlobals = lglobals
                                     , _ccBasicSS = biBasicSS bic
                                     }
          action cc

--------------------------------------------------------------------------------

baseCryptolType :: Crucible.BaseTypeRepr tp -> Maybe Cryptol.Type
baseCryptolType bt =
  case bt of
    Crucible.BaseBoolRepr -> pure $ Cryptol.tBit
    Crucible.BaseBVRepr w -> pure $ Cryptol.tWord (Cryptol.tNum (natValue w))
    Crucible.BaseNatRepr  -> Nothing
    Crucible.BaseIntegerRepr -> pure $ Cryptol.tInteger
    Crucible.BaseArrayRepr indexTypes range ->
      do ts <- baseCryptolTypes indexTypes
         t <- baseCryptolType range
         pure $ foldr Cryptol.tFun t ts
    Crucible.BaseFloatRepr _ -> Nothing
    Crucible.BaseStringRepr _ -> Nothing
    Crucible.BaseComplexRepr  -> Nothing
    Crucible.BaseRealRepr     -> Nothing
    Crucible.BaseStructRepr ts ->
      Cryptol.tTuple <$> baseCryptolTypes ts
  where
    baseCryptolTypes :: Ctx.Assignment Crucible.BaseTypeRepr args -> Maybe [Cryptol.Type]
    baseCryptolTypes Ctx.Empty = pure []
    baseCryptolTypes (xs Ctx.:> x) =
      do ts <- baseCryptolTypes xs
         t <- baseCryptolType x
         pure (ts ++ [t])

setupArg ::
  forall tp.
  SharedContext ->
  Sym ->
  IORef (Seq (Cryptol.Type, ExtCns Term)) ->
  Crucible.TypeRepr tp ->
  IO (Crucible.RegEntry Sym tp)
setupArg sc sym ecRef tp =
  case (Crucible.asBaseType tp, tp) of
    (Crucible.AsBaseType btp, _) ->
      do cty <-
           case baseCryptolType btp of
             Just cty -> pure cty
             Nothing ->
               fail $ unwords ["Unsupported type for Crucible extraction:", show btp]
         sc_tp <- CrucibleSAW.baseSCType sym sc btp
         t     <- freshGlobal cty sc_tp
         elt   <- CrucibleSAW.bindSAWTerm sym btp t
         return (Crucible.RegEntry tp elt)

    (Crucible.NotBaseType, Crucible.LLVMPointerRepr w) ->
      do let cty = Cryptol.tWord (Cryptol.tNum (natValue w))
         sc_tp <- scBitvector sc (natValue w)
         t     <- freshGlobal cty sc_tp
         elt   <- CrucibleSAW.bindSAWTerm sym (Crucible.BaseBVRepr w) t
         elt'  <- Crucible.llvmPointer_bv sym elt
         return (Crucible.RegEntry tp elt')

    (Crucible.NotBaseType, _) ->
      fail $ unwords ["Crucible extraction currently only supports Crucible base types", show tp]
  where
    freshGlobal cty sc_tp =
      do i     <- scFreshGlobalVar sc
         ecs   <- readIORef ecRef
         let len = Seq.length ecs
         let ec = EC i ("arg_"++show len) sc_tp
         writeIORef ecRef (ecs Seq.|> (cty, ec))
         scFlatTermF sc (ExtCns ec)

setupArgs ::
  SharedContext ->
  Sym ->
  Crucible.FnHandle init ret ->
  IO (Seq (Cryptol.Type, ExtCns Term), Crucible.RegMap Sym init)
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
    Crucible.PartialRes _ _ gp _ -> do
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
runCFG simCtx globals h cfg args =
  do let initExecState =
           Crucible.InitialState simCtx globals Crucible.defaultAbortHandler (Crucible.handleReturnType h) $
           Crucible.runOverrideSim (Crucible.handleReturnType h)
                    (Crucible.regValue <$> (Crucible.callCFG cfg args))
     Crucible.executeCrucible [] initExecState

extractFromLLVMCFG ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  Options -> SharedContext -> LLVMCrucibleContext arch -> Crucible.AnyCFG (Crucible.LLVM arch) -> IO TypedTerm
extractFromLLVMCFG opts sc cc (Crucible.AnyCFG cfg) =
  do let sym = cc^.ccBackend
     let h   = Crucible.cfgHandle cfg
     (ecs, args) <- setupArgs sc sym h
     let simCtx  = cc^.ccLLVMSimContext
     let globals = cc^.ccLLVMGlobals
     res <- runCFG simCtx globals h cfg args
     case res of
       Crucible.FinishedResult _ pr ->
         do gp <- getGlobalPair opts pr
            let regv = gp^.Crucible.gpValue
                rt = Crucible.regType regv
                rv = Crucible.regValue regv
            (cty, t) <-
              case rt of
                Crucible.LLVMPointerRepr w ->
                  do bv <- Crucible.projectLLVM_bv sym rv
                     t <- CrucibleSAW.toSC sym bv
                     let cty = Cryptol.tWord (Cryptol.tNum (natValue w))
                     return (cty, t)
                Crucible.BVRepr w ->
                  do t <- CrucibleSAW.toSC sym rv
                     let cty = Cryptol.tWord (Cryptol.tNum (natValue w))
                     return (cty, t)
                _ -> fail $ unwords ["Unexpected return type:", show rt]
            t' <- scAbstractExts sc (map snd (toList ecs)) t
            let cty' = foldr Cryptol.tFun cty (map fst (toList ecs))
            return $ TypedTerm (Cryptol.tMono cty') t'
       Crucible.AbortedResult _ ar ->
         do let resultDoc = ppAbortedResult cc ar
            fail $ unlines [ "Symbolic execution failed."
                           , show resultDoc
                           ]

       Crucible.TimeoutResult _ ->
         fail "Symbolic execution timed out."

--------------------------------------------------------------------------------

crucible_llvm_extract ::
  BuiltinContext ->
  Options ->
  Some LLVMModule ->
  String ->
  TopLevel TypedTerm
crucible_llvm_extract bic opts (Some lm) fn_name =
  do let ctx = modTrans lm ^. Crucible.transContext
     let ?lc = ctx^.Crucible.llvmTypeCtx
     let edef = findDefMaybeStatic (modAST lm) fn_name
     case edef of
       Right defs ->
         do let defTypes =
                  fold $
                  NE.map (map L.typedType . L.defArgs) defs <>
                  NE.map (\d -> [L.defRetType d]) defs
            when (any L.isPointer defTypes) $
              throwTopLevel "Pointer types are not supported by `crucible_llvm_extract`."
            when (any L.isAlias defTypes) $
              throwTopLevel "Type aliases are not supported by `crucible_llvm_extract`."
       Left err -> throwTopLevel (displayVerifExceptionOpts opts err)
     setupLLVMCrucibleContext bic opts lm $ \cc ->
       case Map.lookup (fromString fn_name) (Crucible.cfgMap (ccLLVMModuleTrans cc)) of
         Nothing  -> throwTopLevel $ unwords ["function", fn_name, "not found"]
         Just (_,cfg) -> io $ extractFromLLVMCFG opts (biSharedContext bic) cc cfg

crucible_llvm_cfg ::
  BuiltinContext ->
  Options ->
  Some LLVMModule ->
  String ->
  TopLevel SAW_CFG
crucible_llvm_cfg bic opts (Some lm) fn_name =
  do let ctx = modTrans lm ^. Crucible.transContext
     let ?lc = ctx^.Crucible.llvmTypeCtx
     setupLLVMCrucibleContext bic opts lm $ \cc ->
       case Map.lookup (fromString fn_name) (Crucible.cfgMap (ccLLVMModuleTrans cc)) of
         Nothing  -> throwTopLevel $ unwords ["function", fn_name, "not found"]
         Just (_,cfg) -> return (LLVM_CFG cfg)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

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
  W4.ProgramLoc ->
  Crucible.MemType ->
  Crucible.MemType ->
  CrucibleSetup (LLVM arch) ()
checkMemTypeCompatibility loc t1 t2 =
  case diffMemTypes t1 t2 of
    [] -> return ()
    diffs ->
      throwCrucibleSetup loc $ unlines $
      ["types not memory-compatible:", show t1, show t2]
      ++ map showMemTypeDiff diffs

--------------------------------------------------------------------------------
-- Setup builtins

crucible_precond :: TypedTerm -> LLVMCrucibleSetupM ()
crucible_precond term =
  LLVMCrucibleSetupM $
  do loc <- getW4Position "crucible_precond"
     Setup.crucible_precond loc term

crucible_postcond :: TypedTerm -> LLVMCrucibleSetupM ()
crucible_postcond term =
  LLVMCrucibleSetupM $
  do loc <- getW4Position "crucible_postcond"
     Setup.crucible_postcond loc term

crucible_return ::
  BuiltinContext ->
  Options ->
  AllLLVM MS.SetupValue ->
  LLVMCrucibleSetupM ()
crucible_return bic opts val =
  LLVMCrucibleSetupM $
  do Setup.crucible_return bic opts (getAllLLVM val)

crucible_execute_func ::
  BuiltinContext ->
  Options ->
  [AllLLVM MS.SetupValue] ->
  LLVMCrucibleSetupM ()
crucible_execute_func bic opts args =
  LLVMCrucibleSetupM $ Setup.crucible_execute_func bic opts (map getAllLLVM args)

getLLVMCrucibleContext :: CrucibleSetup (LLVM arch) (LLVMCrucibleContext arch)
getLLVMCrucibleContext = view Setup.csCrucibleContext <$> get

-- | Returns Cryptol type of actual type if it is an array or primitive
-- type, or an appropriately-sized bit vector for pointer types.
cryptolTypeOfActual :: Crucible.DataLayout -> Crucible.MemType -> Maybe Cryptol.Type
cryptolTypeOfActual dl mt =
  case mt of
    Crucible.IntType w ->
      return $ Cryptol.tWord (Cryptol.tNum w)
    Crucible.FloatType ->
      Nothing -- FIXME: update when Cryptol gets float types
    Crucible.DoubleType ->
      Nothing -- FIXME: update when Cryptol gets float types
    Crucible.ArrayType n ty ->
      do cty <- cryptolTypeOfActual dl ty
         return $ Cryptol.tSeq (Cryptol.tNum n) cty
    Crucible.PtrType _ ->
      return $ Cryptol.tWord (Cryptol.tNum (Crucible.ptrBitwidth dl))
    Crucible.StructType si ->
      do let memtypes = V.toList (Crucible.siFieldTypes si)
         ctys <- traverse (cryptolTypeOfActual dl) memtypes
         case ctys of
           [cty] -> return cty
           _ -> return $ Cryptol.tTuple ctys
    _ ->
      Nothing

-- | Generate a fresh variable term. The name will be used when
-- pretty-printing the variable in debug output.
crucible_fresh_var ::
  BuiltinContext          {- ^ context          -} ->
  Options                 {- ^ options          -} ->
  String                  {- ^ variable name    -} ->
  L.Type                  {- ^ variable type    -} ->
  LLVMCrucibleSetupM TypedTerm {- ^ fresh typed term -}
crucible_fresh_var bic _opts name lty =
  LLVMCrucibleSetupM $
  do cctx <- getLLVMCrucibleContext
     let ?lc = ccTypeCtx cctx
     loc <- getW4Position "crucible_fresh_var"
     lty' <- memTypeForLLVMType loc bic lty
     let sc = biSharedContext bic
     let dl = Crucible.llvmDataLayout (ccTypeCtx cctx)
     case cryptolTypeOfActual dl lty' of
       Nothing -> throwCrucibleSetup loc $ "Unsupported type in crucible_fresh_var: " ++ show (L.ppType lty)
       Just cty -> Setup.freshVariable sc name cty

crucible_fresh_cryptol_var ::
  BuiltinContext ->
  Options ->
  String ->
  Cryptol.Schema ->
  LLVMCrucibleSetupM TypedTerm
crucible_fresh_cryptol_var bic _opts name s =
  LLVMCrucibleSetupM $
  do loc <- getW4Position "crucible_fresh_var"
     case s of
       Cryptol.Forall [] [] ty ->
         Setup.freshVariable (biSharedContext bic) name ty
       _ ->
         throwCrucibleSetup loc $ "Unsupported polymorphic Cryptol type schema: " ++ show s

-- | Use the given LLVM type to compute a setup value that
-- covers expands all of the struct, array, and pointer
-- components of the LLVM type. Only the primitive types
-- suitable for import as SAW core terms will be matched
-- against fresh variables.
crucible_fresh_expanded_val ::
  BuiltinContext {- ^ context                -} ->
  Options        {- ^ options                -} ->
  L.Type         {- ^ variable type          -} ->
  LLVMCrucibleSetupM (AllLLVM SetupValue)
                 {- ^ elaborated setup value -}
crucible_fresh_expanded_val bic _opts lty =
  LLVMCrucibleSetupM $
  do let sc = biSharedContext bic
     cctx <- getLLVMCrucibleContext
     let ?lc = ccTypeCtx cctx
     loc <- getW4Position "crucible_fresh_expanded_val"
     lty' <- memTypeForLLVMType loc bic lty
     constructExpandedSetupValue cctx sc loc lty'

-- | See 'crucible_fresh_expanded_val'
--
-- This is the recursively-called worker function.
constructExpandedSetupValue ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  LLVMCrucibleContext arch ->
  SharedContext ->
  W4.ProgramLoc ->
  Crucible.MemType {- ^ LLVM mem type -} ->
  CrucibleSetup (LLVM arch) (AllLLVM SetupValue)
constructExpandedSetupValue cc sc loc t =
  case t of
    Crucible.IntType w ->
      do let cty = Cryptol.tWord (Cryptol.tNum w)
         fv <- Setup.freshVariable sc "" cty
         pure $ mkAllLLVM (SetupTerm fv)

    Crucible.StructType si -> do
      fields <- toList <$>
         traverse (constructExpandedSetupValue cc sc loc)
                  (Crucible.siFieldTypes si)
      -- FIXME: should this always be unpacked?
      pure $ mkAllLLVM $ SetupStruct () False $ map getAllLLVM fields

    Crucible.PtrType symTy ->
      case Crucible.asMemType symTy of
        Right memTy -> constructFreshPointer (symTypeAlias symTy) loc memTy
        Left err -> throwCrucibleSetup loc $ unlines
          [ "lhs not a valid pointer type: " ++ show symTy
          , "Details:"
          , err
          ]

    Crucible.ArrayType n memTy -> do
      elements_ <-
        replicateM (fromIntegral n) (constructExpandedSetupValue cc sc loc memTy)
      pure $ mkAllLLVM $ SetupArray () $ map getAllLLVM elements_

    Crucible.FloatType      -> failUnsupportedType "Float"
    Crucible.DoubleType     -> failUnsupportedType "Double"
    Crucible.MetadataType   -> failUnsupportedType "Metadata"
    Crucible.VecType{}      -> failUnsupportedType "Vec"
    Crucible.X86_FP80Type{} -> failUnsupportedType "X86_FP80"
  where failUnsupportedType tyName = throwCrucibleSetup loc $ unwords
          ["crucible_fresh_expanded_var: " ++ tyName ++ " not supported"]


memTypeForLLVMType ::
  (?lc :: Crucible.TypeContext) =>
  W4.ProgramLoc ->
  BuiltinContext ->
  L.Type ->
  CrucibleSetup arch Crucible.MemType
memTypeForLLVMType loc _bic lty =
  case Crucible.liftMemType lty of
    Right m -> return m
    Left err -> throwCrucibleSetup loc $ unlines
      [ "unsupported type: " ++ show (L.ppType lty)
      , "Details:"
      , err
      ]

llvmTypeAlias :: L.Type -> Maybe Crucible.Ident
llvmTypeAlias (L.Alias i) = Just i
llvmTypeAlias _ = Nothing

symTypeAlias :: Crucible.SymType -> Maybe Crucible.Ident
symTypeAlias (Crucible.Alias i) = Just i
symTypeAlias _ = Nothing

-- | Does the hard work for 'crucible_alloc', 'crucible_alloc_with_size',
--   'crucible_alloc_readonly', etc.
crucible_alloc_internal ::
  BuiltinContext ->
  Options        ->
  L.Type  ->
  LLVMAllocSpec  ->
  CrucibleSetup (Crucible.LLVM arch) (AllLLVM SetupValue)
crucible_alloc_internal _bic _opt lty spec =
  do cctx <- getLLVMCrucibleContext
     let ?lc = ccTypeCtx cctx
     let ?dl = Crucible.llvmDataLayout ?lc
     n <- Setup.csVarCounter <<%= nextAllocIndex
     Setup.currentState . MS.csAllocs . at n ?= spec
     -- TODO: refactor
     case llvmTypeAlias lty of
       Just i -> Setup.currentState . MS.csVarTypeNames.at n ?= i
       Nothing -> return ()
     return (mkAllLLVM (SetupVar n))

crucible_alloc_with_mutability_and_size ::
  Crucible.Mutability    ->
  Maybe (Crucible.Bytes) ->
  Maybe Crucible.Alignment ->
  BuiltinContext   ->
  Options          ->
  L.Type           ->
  LLVMCrucibleSetupM (AllLLVM SetupValue)
crucible_alloc_with_mutability_and_size mut sz alignment bic opts lty =
  LLVMCrucibleSetupM $
  do cctx <- getLLVMCrucibleContext
     loc <- getW4Position "crucible_alloc"
     memTy <- memTypeForLLVMType loc bic lty

     let lc = ccTypeCtx cctx
     let dl = Crucible.llvmDataLayout lc
     let memTySize = Crucible.memTypeSize dl memTy
     let memTyAlign = Crucible.memTypeAlign dl memTy

     sz' <-
       case sz of
         Just sz_ ->
           do when (sz_ < memTySize) $ throwCrucibleSetup loc $ unlines
                [ "User error: manually-specified allocation size was less than needed"
                , "Needed for this type: " ++ show memTySize
                , "Specified: " ++ show sz_
                ]
              pure sz_
         Nothing -> pure (Crucible.toBytes memTySize)

     sz'' <- liftIO $ scPtrWidthBvNat cctx sz'

     alignment' <-
       case alignment of
         Just a ->
           do when (a < memTyAlign) $ liftIO $ printOutLn opts Info $ unlines
                [ "Warning: manually-specified alignment was less than default for type"
                , "Allocation type: " ++ show memTy
                , "Default alignment for type: " ++ show (Crucible.fromAlignment memTyAlign) ++ "-byte"
                , "Specified alignment: " ++ show (Crucible.fromAlignment a) ++ "-byte"
                ]
              pure a
         Nothing -> pure memTyAlign

     crucible_alloc_internal bic opts lty $
       LLVMAllocSpec
       { _allocSpecMut = mut
       , _allocSpecType = memTy
       , _allocSpecAlign = alignment'
       , _allocSpecBytes = sz''
       , _allocSpecLoc = loc
       }

crucible_alloc ::
  BuiltinContext ->
  Options        ->
  L.Type         ->
  LLVMCrucibleSetupM (AllLLVM SetupValue)
crucible_alloc =
  crucible_alloc_with_mutability_and_size Crucible.Mutable Nothing Nothing

crucible_alloc_aligned ::
  BuiltinContext ->
  Options        ->
  Int            ->
  L.Type         ->
  LLVMCrucibleSetupM (AllLLVM SetupValue)
crucible_alloc_aligned =
  crucible_alloc_aligned_with_mutability Crucible.Mutable

crucible_alloc_readonly ::
  BuiltinContext ->
  Options        ->
  L.Type         ->
  LLVMCrucibleSetupM (AllLLVM SetupValue)
crucible_alloc_readonly =
  crucible_alloc_with_mutability_and_size Crucible.Immutable Nothing Nothing

crucible_alloc_readonly_aligned ::
  BuiltinContext ->
  Options        ->
  Int            ->
  L.Type         ->
  LLVMCrucibleSetupM (AllLLVM SetupValue)
crucible_alloc_readonly_aligned =
  crucible_alloc_aligned_with_mutability Crucible.Immutable

crucible_alloc_aligned_with_mutability ::
  Crucible.Mutability ->
  BuiltinContext ->
  Options ->
  Int ->
  L.Type ->
  LLVMCrucibleSetupM (AllLLVM SetupValue)
crucible_alloc_aligned_with_mutability mut bic opts n lty =
  do alignment <- LLVMCrucibleSetupM $ coerceAlignment n
     crucible_alloc_with_mutability_and_size
       mut
       Nothing
       (Just alignment)
       bic
       opts
       lty

coerceAlignment :: Int -> CrucibleSetup (LLVM arch) Crucible.Alignment
coerceAlignment n =
  case Crucible.toAlignment (Crucible.toBytes n) of
    Nothing ->
      do loc <- getW4Position "crucible_alloc_aligned_with_mutability"
         throwCrucibleSetup loc $ unwords
           [ "crucible_alloc_aligned/crucible_alloc_readonly_aligned:"
           , "invalid non-power-of-2 alignment:"
           , show n
           ]
    Just alignment -> return alignment

crucible_alloc_with_size ::
  BuiltinContext ->
  Options        ->
  Int {-^ allocation size (in bytes) -} ->
  L.Type         ->
  LLVMCrucibleSetupM (AllLLVM SetupValue)
crucible_alloc_with_size bic opts sz lty =
  crucible_alloc_with_mutability_and_size
    Crucible.Mutable
    (Just (Crucible.toBytes sz))
    Nothing
    bic
    opts
    lty

crucible_symbolic_alloc ::
  BuiltinContext ->
  Options ->
  Bool ->
  Int ->
  Term ->
  LLVMCrucibleSetupM (AllLLVM SetupValue)
crucible_symbolic_alloc bic _opts ro align_bytes sz =
  LLVMCrucibleSetupM $
  do alignment <- coerceAlignment align_bytes
     loc <- getW4Position "crucible_symbolic_alloc"
     let sc = biSharedContext bic
     sz_ty <- liftIO $ Cryptol.scCryptolType sc =<< scTypeOf sc sz
     when (Just 64 /= asCryptolBVType sz_ty) $
       throwCrucibleSetup loc $ unwords
         [ "crucible_symbolic_alloc:"
         , "unexpected type of size term, expected [64], found"
         , Cryptol.pretty sz_ty
         ]
     let spec = LLVMAllocSpec
           { _allocSpecMut = if ro then Crucible.Immutable else Crucible.Mutable
           , _allocSpecType = Crucible.i8p
           , _allocSpecAlign = alignment
           , _allocSpecBytes = sz
           , _allocSpecLoc = loc
           }
     n <- Setup.csVarCounter <<%= nextAllocIndex
     Setup.currentState . MS.csAllocs . at n ?= spec
     return $ mkAllLLVM $ SetupVar n

asCryptolBVType :: Cryptol.Type -> Maybe Integer
asCryptolBVType ty
  | Just (n, ety) <- Cryptol.tIsSeq ty
  , Cryptol.tIsBit ety =
    Cryptol.tIsNum n
  | otherwise = Nothing

crucible_alloc_global ::
  BuiltinContext ->
  Options        ->
  String         ->
  LLVMCrucibleSetupM ()
crucible_alloc_global _bic _opts name =
  LLVMCrucibleSetupM $
  do loc <- getW4Position "crucible_alloc_global"
     Setup.addAllocGlobal . LLVMAllocGlobal loc $ L.Symbol name

crucible_fresh_pointer ::
  BuiltinContext ->
  Options        ->
  L.Type         ->
  LLVMCrucibleSetupM (AllLLVM SetupValue)
crucible_fresh_pointer bic _opt lty =
  LLVMCrucibleSetupM $
  do loc <- getW4Position "crucible_fresh_pointer"
     memTy <- memTypeForLLVMType loc bic lty
     constructFreshPointer (llvmTypeAlias lty) loc memTy

constructFreshPointer ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  Maybe Crucible.Ident ->
  W4.ProgramLoc ->
  Crucible.MemType ->
  CrucibleSetup (LLVM arch) (AllLLVM SetupValue)
constructFreshPointer mid loc memTy =
  do cctx <- getLLVMCrucibleContext
     let ?lc = ccTypeCtx cctx
     let ?dl = Crucible.llvmDataLayout ?lc
     n <- Setup.csVarCounter <<%= nextAllocIndex
     sz <- liftIO $ scPtrWidthBvNat cctx $ Crucible.memTypeSize ?dl memTy
     let alignment = Crucible.memTypeAlign ?dl memTy
     Setup.currentState . MS.csFreshPointers . at n ?=
       LLVMAllocSpec { _allocSpecMut = Crucible.Mutable
                     , _allocSpecType = memTy
                     , _allocSpecAlign = alignment
                     , _allocSpecBytes = sz
                     , _allocSpecLoc = loc
                     }
     -- TODO: refactor
     case mid of
       Just i -> Setup.currentState . MS.csVarTypeNames.at n ?= i
       Nothing -> return ()
     return (mkAllLLVM (SetupVar n))

crucible_points_to ::
  Bool {- ^ whether to check type compatibility -} ->
  BuiltinContext ->
  Options        ->
  AllLLVM SetupValue     ->
  AllLLVM SetupValue     ->
  LLVMCrucibleSetupM ()
crucible_points_to typed bic opt =
  crucible_points_to_internal bic opt typed Nothing

crucible_conditional_points_to ::
  BuiltinContext ->
  Options ->
  TypedTerm ->
  AllLLVM SetupValue ->
  AllLLVM SetupValue ->
  LLVMCrucibleSetupM ()
crucible_conditional_points_to bic opt cond =
  crucible_points_to_internal bic opt True (Just cond)

crucible_points_to_internal ::
  BuiltinContext ->
  Options ->
  Bool {- ^ whether to check type compatibility -} ->
  Maybe TypedTerm ->
  AllLLVM SetupValue ->
  AllLLVM SetupValue ->
  LLVMCrucibleSetupM ()
crucible_points_to_internal _bic _opt typed cond (getAllLLVM -> ptr) (getAllLLVM -> val) =
  LLVMCrucibleSetupM $
  do cc <- getLLVMCrucibleContext
     loc <- getW4Position "crucible_points_to"
     Crucible.llvmPtrWidth (ccLLVMContext cc) $ \wptr -> Crucible.withPtrWidth wptr $
       do let ?lc = ccTypeCtx cc
          st <- get
          let rs = st ^. Setup.csResolvedState
          if st ^. Setup.csPrePost == PreState && MS.testResolved ptr [] rs
            then throwCrucibleSetup loc "Multiple points-to preconditions on same pointer"
            else Setup.csResolvedState %= MS.markResolved ptr []
          let env = MS.csAllocations (st ^. Setup.csMethodSpec)
              nameEnv = MS.csTypeNames (st ^. Setup.csMethodSpec)
          ptrTy <- typeOfSetupValue cc env nameEnv ptr
          lhsTy <- case ptrTy of
            Crucible.PtrType symTy ->
              case Crucible.asMemType symTy of
                Right lhsTy -> return lhsTy
                Left err -> throwCrucibleSetup loc $ unlines
                  [ "lhs not a valid pointer type: " ++ show ptrTy
                  , "Details:"
                  , err
                  ]

            _ -> throwCrucibleSetup loc $ "lhs not a pointer type: " ++ show ptrTy
          valTy <- typeOfSetupValue cc env nameEnv val
          when typed (checkMemTypeCompatibility loc lhsTy valTy)
          Setup.addPointsTo (LLVMPointsTo loc cond ptr $ ConcreteSizeValue val)

crucible_points_to_array_prefix ::
  BuiltinContext ->
  Options ->
  AllLLVM SetupValue ->
  TypedTerm ->
  TypedTerm ->
  LLVMCrucibleSetupM ()
crucible_points_to_array_prefix _bic _opt (getAllLLVM -> ptr) arr sz =
  LLVMCrucibleSetupM $
  do cc <- getLLVMCrucibleContext
     loc <- getW4Position "crucible_points_to_array_prefix"
     case ttSchema sz of
       Cryptol.Forall [] [] ty
         | Just 64 == asCryptolBVType ty ->
           return ()
       _ -> throwCrucibleSetup loc $ unwords
         [ "crucible_points_to_array_prefix:"
         , "unexpected type of size term, expected [64], found"
         , Cryptol.pretty (ttSchema sz)
         ]
     Crucible.llvmPtrWidth (ccLLVMContext cc) $ \wptr -> Crucible.withPtrWidth wptr $
       do let ?lc = ccTypeCtx cc
          st <- get
          let rs = st ^. Setup.csResolvedState
          if st ^. Setup.csPrePost == PreState && MS.testResolved ptr [] rs
            then throwCrucibleSetup loc "Multiple points-to preconditions on same pointer"
            else Setup.csResolvedState %= MS.markResolved ptr []
          let env = MS.csAllocations (st ^. Setup.csMethodSpec)
              nameEnv = MS.csTypeNames (st ^. Setup.csMethodSpec)
          ptrTy <- typeOfSetupValue cc env nameEnv ptr
          _ <- case ptrTy of
            Crucible.PtrType symTy ->
              case Crucible.asMemType symTy of
                Right lhsTy -> return lhsTy
                Left err -> throwCrucibleSetup loc $ unlines
                  [ "lhs not a valid pointer type: " ++ show ptrTy
                  , "Details:"
                  , err
                  ]

            _ -> throwCrucibleSetup loc $ "lhs not a pointer type: " ++ show ptrTy
          Setup.addPointsTo (LLVMPointsTo loc Nothing ptr $ SymbolicSizeValue arr sz)

crucible_equal ::
  BuiltinContext ->
  Options        ->
  AllLLVM SetupValue ->
  AllLLVM SetupValue ->
  LLVMCrucibleSetupM ()
crucible_equal _bic _opt (getAllLLVM -> val1) (getAllLLVM -> val2) =
  LLVMCrucibleSetupM $
  do cc <- getLLVMCrucibleContext
     loc <- getW4Position "crucible_equal"
     st <- get
     let env = MS.csAllocations (st ^. Setup.csMethodSpec)
         nameEnv = MS.csTypeNames (st ^. Setup.csMethodSpec)
     ty1 <- typeOfSetupValue cc env nameEnv val1
     ty2 <- typeOfSetupValue cc env nameEnv val2

     b <- liftIO $ checkRegisterCompatibility ty1 ty2
     unless b $ throwCrucibleSetup loc $ unlines
       [ "Incompatible types when asserting equality:"
       , show ty1
       , show ty2
       ]
     Setup.addCondition (MS.SetupCond_Equal loc val1 val2)

crucible_declare_ghost_state ::
  BuiltinContext ->
  Options        ->
  String         ->
  TopLevel Value
crucible_declare_ghost_state _bic _opt name =
  do allocator <- getHandleAlloc
     global <- liftIO (Crucible.freshGlobalVar allocator (Text.pack name) knownRepr)
     return (VGhostVar global)

crucible_ghost_value ::
  BuiltinContext ->
  Options ->
  MS.GhostGlobal ->
  TypedTerm ->
  LLVMCrucibleSetupM ()
crucible_ghost_value _bic _opt ghost val = LLVMCrucibleSetupM $
  do loc <- getW4Position "crucible_ghost_value"
     Setup.addCondition (MS.SetupCond_Ghost () loc ghost val)

crucible_spec_solvers :: SomeLLVM (MS.CrucibleMethodSpecIR) -> [String]
crucible_spec_solvers (SomeLLVM mir) =
  Set.toList $ solverStatsSolvers $ (view MS.csSolverStats) $ mir

crucible_spec_size :: SomeLLVM MS.CrucibleMethodSpecIR -> Integer
crucible_spec_size (SomeLLVM mir) =
  solverStatsGoalSize $ mir ^. MS.csSolverStats

crucible_setup_val_to_typed_term ::
  BuiltinContext ->
  Options ->
  AllLLVM SetupValue ->
  TopLevel TypedTerm
crucible_setup_val_to_typed_term bic _opt (getAllLLVM -> sval) =
  do opts <- getOptions
     mtt <- io $ MaybeT.runMaybeT $ MS.setupToTypedTerm opts (biSharedContext bic) sval
     case mtt of
       Nothing -> throwTopLevel $ "Could not convert a setup value to a term: " ++ show sval
       Just tt -> return tt

--------------------------------------------------------------------------------

-- | Sort a list of things and group them into equivalence classes.
groupOn ::
  Ord b =>
  (a -> b) {- ^ equivalence class projection -} ->
  [a] -> [[a]]
groupOn f = groupBy ((==) `on` f) . sortBy (compare `on` f)
