{- |
Module      : SAWCentral.Crucible.LLVM.Builtins
Description : Implementations of Crucible-related SAW-Script primitives.
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module SAWCentral.Crucible.LLVM.Builtins
    ( show_cfg
    , llvm_execute_func
    , llvm_return
    , llvm_precond
    , llvm_postcond
    , llvm_unint
    , llvm_assert
    , llvm_cfg
    , llvm_extract
    , llvm_compositional_extract
    , llvm_verify
    , llvm_refine_spec
    , llvm_array_size_profile
    , llvm_setup_with_tag
    , crucible_setup_val_to_typed_term
    , llvm_spec_size
    , llvm_spec_solvers
    , llvm_ghost_value
    , llvm_equal
    , llvm_points_to
    , llvm_conditional_points_to
    , llvm_points_to_at_type
    , llvm_conditional_points_to_at_type
    , llvm_points_to_internal
    , llvm_points_to_array_prefix
    , llvm_points_to_bitfield
    , llvm_fresh_pointer
    , llvm_unsafe_assume_spec
    , llvm_fresh_var
    , llvm_fresh_cryptol_var
    , llvm_alloc
    , llvm_alloc_aligned
    , llvm_alloc_readonly
    , llvm_alloc_readonly_aligned
    , llvm_alloc_with_size
    , llvm_alloc_sym_init
    , llvm_symbolic_alloc
    , llvm_alloc_global
    , llvm_fresh_expanded_val
    , llvm_sizeof
    , llvm_cast_pointer

    , displayVerifExceptionOpts
    , findDecl
    , findDefMaybeStatic
    , setupLLVMCrucibleContext
    , setupPrestateConditions
    , checkSpecReturnType
    , verifyPrestate
    , verifyPoststate
    , getPoststateObligations
    , withCfgAndBlockId
    , registerOverride
    , lookupMemGlobal
    ) where

import Prelude hiding (fail)

import qualified Control.Exception as X
import           Control.Lens

import           Control.Monad (foldM, forM, replicateM, unless, when)
import           Control.Monad.Fail (MonadFail(..))
import           Control.Monad.IO.Class (MonadIO(..))
import           Control.Monad.Reader (runReaderT)
import           Control.Monad.State (MonadState(..), StateT(..), execStateT, gets)
import           Control.Monad.Trans.Class (MonadTrans(..))
import qualified Data.Bimap as Bimap
import           Data.Char (isDigit)
import           Data.Foldable (for_, toList, fold)
import           Data.Functor (void)
import qualified Data.IntMap as IntMap
import           Data.IORef
import           Data.List (find, nub, partition)
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
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Time.Clock (getCurrentTime, diffUTCTime)
import qualified Data.Vector as V
import           Prettyprinter
import           System.IO
import qualified Text.LLVM.AST as L
import           Text.URI
import qualified Control.Monad.Trans.Maybe as MaybeT

-- parameterized-utils
import           Data.Parameterized.Classes
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as FC

-- cryptol
import qualified Cryptol.TypeCheck.Type as Cryptol
import qualified Cryptol.TypeCheck.PP as Cryptol
import qualified CryptolSAWCore.Cryptol as Cryptol

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
import qualified Lang.Crucible.Backend.Online as Crucible
import qualified Lang.Crucible.CFG.Core as Crucible
import qualified Lang.Crucible.FunctionHandle as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Simulator.Breakpoint as Crucible
import qualified Lang.Crucible.Simulator.GlobalState as Crucible
import qualified Lang.Crucible.Simulator.PathSatisfiability as Crucible

-- crucible-llvm
import qualified Lang.Crucible.LLVM.ArraySizeProfile as Crucible
import qualified Lang.Crucible.LLVM.DataLayout as Crucible
import qualified Lang.Crucible.LLVM.Bytes as Crucible
import qualified Lang.Crucible.LLVM.Functions as Crucible
import qualified Lang.Crucible.LLVM.Intrinsics as Crucible
import qualified Lang.Crucible.LLVM.MemModel as Crucible
import qualified Lang.Crucible.LLVM.MemType as Crucible
import qualified Lang.Crucible.LLVM.PrettyPrint as Crucible
import           Lang.Crucible.LLVM.QQ( llvmOvr )
import qualified Lang.Crucible.LLVM.Translation as Crucible

import qualified SAWCentral.Crucible.LLVM.CrucibleLLVM as Crucible

-- saw-core
import SAWCore.FiniteValue (ppFirstOrderValue)
import SAWCore.Name (VarName(..))
import SAWCore.SharedTerm
import SAWCore.Recognizer
import SAWCore.Term.Pretty (showTerm)
import SAWCore.Term.Raw (closedTerm)

import SAWCoreWhat4.ReturnTrip

-- cryptol-saw-core
import CryptolSAWCore.TypedTerm

-- saw-script
import SAWCentral.AST (tMono, tTerm, Rebindable(ReadOnlyVar))
import SAWCentral.Builtins (ghost_value)
import SAWCentral.Proof
import SAWCentral.Prover.SolverStats
import SAWCentral.Prover.Versions
import SAWCentral.TopLevel
import SAWCentral.Value
import SAWCentral.Position
import SAWCentral.Exceptions
import SAWCentral.Options
import SAWCentral.Utils (neGroupOn, neNubOrd)

import qualified SAWCentral.Crucible.Common as Common
import           SAWCentral.Crucible.Common (Sym, SAWCruciblePersonality)
import           SAWCentral.Crucible.Common.MethodSpec (AllocIndex(..), nextAllocIndex, PrePost(..))
import qualified SAWCentral.Crucible.Common.MethodSpec as MS
import           SAWCentral.Crucible.Common.MethodSpec (SetupValue(..))
import           SAWCentral.Crucible.Common.Override
import qualified SAWCentral.Crucible.Common.Setup.Builtins as Setup
import qualified SAWCentral.Crucible.Common.Setup.Type as Setup
import qualified SAWCentral.Crucible.Common.Vacuity as Vacuity

import SAWCentral.Crucible.LLVM.Override
import SAWCentral.Crucible.LLVM.ResolveSetupValue
import SAWCentral.Crucible.LLVM.Setup.Value(ccUninterp)
import SAWCentral.Crucible.LLVM.MethodSpecIR
import SAWCentral.Panic (panic)

type AssumptionReason = (MS.ConditionMetadata, String)

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
       else "Available function names:" : map (("  " ++) . show . Crucible.ppSymbol) nms
displayVerifExceptionOpts opts (DeclNotFound (L.Symbol nm) nms) =
  unlines $
  [ "Could not find declaration for function named `" ++ nm ++ "`."
  ] ++ if simVerbose opts < 3
       then [ "Run SAW with --sim-verbose=3 to see all function names" ]
       else "Available function names:" : map (("  " ++) . show . Crucible.ppSymbol) nms
displayVerifExceptionOpts _ (SetupError e) =
  "Error during simulation setup: " ++ show (ppSetupError e)

show_cfg :: SAW_CFG -> Text
show_cfg (LLVM_CFG (Crucible.AnyCFG cfg)) = Text.pack $ show cfg
show_cfg (JVM_CFG (Crucible.AnyCFG cfg)) = Text.pack $ show cfg

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

findDefMaybeStatic :: L.Module -> Text -> Either LLVMVerificationException (NE.NonEmpty L.Define)
findDefMaybeStatic llmod nm =
  case NE.nonEmpty (filter (\d -> matchingStatics (L.defName d) nm') (L.modDefines llmod)) of
    Nothing -> Left $ DefNotFound nm' $ map L.defName $ L.modDefines llmod
    Just defs -> Right defs
  where
    nm' = fromString $ Text.unpack nm

findDecl :: L.Module -> Text -> Either LLVMVerificationException L.Declare
findDecl llmod nm =
  case find (\d -> (L.decName d) == nm') (L.modDeclares llmod) of
    Just decl -> Right decl
    Nothing -> Left $ DeclNotFound nm' $ map L.decName $ L.modDeclares llmod
  where
    nm' = fromString $ Text.unpack nm

resolveSpecName :: Text -> TopLevel (Text, Maybe Text)
resolveSpecName nm =
  if Crucible.testBreakpointFunction (Text.unpack nm)
  then
    let (fnName, fnSuffix) = Text.break (== '#') nm
        parentName =
          case Text.uncons fnSuffix of
            Just (_, parentName') -> parentName'
            -- TODO: Give a proper error message here instead of panicking,
            -- and document __breakpoint__ naming requirements. See #2097.
            Nothing -> panic "resolveSpecName" [
                      "__breakpoint__ function not followed by #<parent_name>",
                      "See https://github.com/GaloisInc/saw-script/issues/2097"
                  ]
    in
    return
      ( fnName
      , Just parentName
      )
  else return (nm, Nothing)

llvm_verify ::
  Some LLVMModule        ->
  Text                   ->
  [SomeLLVM MS.ProvedSpec] ->
  Bool                   ->
  LLVMCrucibleSetupM ()      ->
  ProofScript () ->
  TopLevel (SomeLLVM MS.ProvedSpec)
llvm_verify (Some lm) nm lemmas checkSat setup tactic =
  do start <- io getCurrentTime
     lemmas' <- checkModuleCompatibility lm lemmas
     withMethodSpec checkSat lm nm setup $ \cc method_spec ->
       do (stats, vcs, _) <- verifyMethodSpec cc method_spec lemmas' checkSat tactic Nothing
          let lemmaSet = Set.fromList (map (view MS.psSpecIdent) lemmas')
          end <- io getCurrentTime
          let diff = diffUTCTime end start
          ps <- io (MS.mkProvedSpec MS.SpecProved method_spec stats vcs lemmaSet diff)
          returnLLVMProof $ SomeLLVM ps

llvm_refine_spec ::
  Some LLVMModule ->
  Text ->
  [SomeLLVM MS.ProvedSpec] ->
  LLVMCrucibleSetupM () ->
  ProofScript () ->
  TopLevel (SomeLLVM MS.ProvedSpec)
llvm_refine_spec (Some lm) nm lemmas setup tactic =
  do start <- io getCurrentTime
     lemmas' <- checkModuleCompatibility lm lemmas
     withMethodSpec False lm nm setup $ \cc method_spec ->
       do (stats, deps) <- refineMethodSpec cc method_spec lemmas' tactic
          let lemmaSet = Set.fromList (map (view MS.psSpecIdent) lemmas')
          end <- io getCurrentTime
          let diff = diffUTCTime end start
          ps <- io (MS.mkProvedSpec MS.SpecProved method_spec stats deps lemmaSet diff)
          returnLLVMProof $ SomeLLVM ps

llvm_unsafe_assume_spec ::
  Some LLVMModule  ->
  Text                  {- ^ Name of the function -} ->
  LLVMCrucibleSetupM () {- ^ Boundary specification -} ->
  TopLevel (SomeLLVM MS.ProvedSpec)
llvm_unsafe_assume_spec (Some lm) nm setup =
  withMethodSpec False lm nm setup $ \_ method_spec ->
  do printOutLnTop Info $ Text.unpack $
         "Assume override " <> (method_spec ^. csName)
     ps <- io (MS.mkProvedSpec MS.SpecAdmitted method_spec mempty mempty mempty 0)
     returnLLVMProof $ SomeLLVM ps

llvm_array_size_profile ::
  ProofScript () ->
  Some LLVMModule ->
  Text ->
  [SomeLLVM MS.ProvedSpec] ->
  LLVMCrucibleSetupM () ->
  TopLevel [(Text, [Crucible.FunctionProfile])]
llvm_array_size_profile assume (Some lm) nm lemmas setup = do
  cell <- io $ newIORef (Map.empty :: Map Text.Text [Crucible.FunctionProfile])
  lemmas' <- checkModuleCompatibility lm lemmas
  withMethodSpec False lm nm setup $ \cc ms -> do
    void . verifyMethodSpec cc ms lemmas' True assume $ Just cell
    profiles <- io $ readIORef cell
    pure $ Map.toList profiles

llvmURI :: Text -> URI
llvmURI symbol_name =
  fromMaybe (panic "llvmURI" ["Could not create LLVM symbol name " <> symbol_name]) $
  do sch <- mkScheme "llvm"
     p   <- mkPathPiece symbol_name
     pure URI
       { uriScheme = Just sch
       , uriAuthority = Left True -- absolute path
       , uriPath = Just (False, p NE.:| [])
       , uriQuery = []
       , uriFragment = Nothing
       }

llvmNameInfo :: Text -> NameInfo
llvmNameInfo symbol_name = ImportedName (llvmURI symbol_name) [ symbol_name ]

llvm_compositional_extract ::
  Some LLVMModule ->
  Text ->
  Text ->
  [SomeLLVM MS.ProvedSpec] ->
  Bool {- ^ check sat -} ->
  LLVMCrucibleSetupM () ->
  ProofScript () ->
  TopLevel (SomeLLVM MS.ProvedSpec)
llvm_compositional_extract (Some lm) nm func_name lemmas checkSat setup tactic =
  do start <- io getCurrentTime
     lemmas' <- checkModuleCompatibility lm lemmas
     withMethodSpec checkSat lm nm setup $ \cc method_spec ->
       do let value_input_parameters = mapMaybe
                (\(_, setup_value) -> setupValueAsVariable setup_value)
                (Map.elems $ method_spec ^. MS.csArgBindings)
          let reference_input_parameters = mapMaybe
                (\case
                  LLVMPointsTo _ _ _ setup_value -> llvmPointsToValueAsVariable setup_value
                  LLVMPointsToBitfield _ _ _ val -> setupValueAsVariable val)
                (method_spec ^. MS.csPreState ^. MS.csPointsTos)
          let input_parameters = nub $ value_input_parameters ++ reference_input_parameters
          let pre_free_variables = Map.fromList $
                map (\x -> (tvName x, x)) $ method_spec ^. MS.csPreState ^. MS.csFreshVars
          let unsupported_input_parameters = Set.difference
                (Map.keysSet pre_free_variables)
                (Set.fromList (map fst input_parameters))
          when (not $ Set.null unsupported_input_parameters) $
            fail $ unlines
              [ "Unsupported input parameters:"
              , show unsupported_input_parameters
              , "An input parameter must be bound by llvm_execute_func or llvm_points_to."
              ]

          let return_output_parameter =
                case method_spec ^. MS.csRetValue of
                  Just setup_value -> setupValueAsVariable setup_value
                  Nothing -> Nothing
          let reference_output_parameters =
                mapMaybe
                (\case
                  LLVMPointsTo _ _ _ setup_value -> llvmPointsToValueAsVariable setup_value
                  LLVMPointsToBitfield _ _ _ val -> setupValueAsVariable val)
                (method_spec ^. MS.csPostState ^. MS.csPointsTos)
          let output_parameters =
                nub $ filter (isNothing . (Map.!?) pre_free_variables . fst) $
                maybeToList return_output_parameter ++ reference_output_parameters
          let post_free_variables =
                Map.fromList $
                map (\x -> (tvName x, x)) $ method_spec ^. MS.csPostState ^. MS.csFreshVars
          let unsupported_output_parameters =
                Set.difference (Map.keysSet post_free_variables) (Set.fromList (map fst output_parameters))
          when (not $ Set.null unsupported_output_parameters) $
            fail $ unlines
              [ "Unsupported output parameters:"
              , show unsupported_output_parameters
              , "An output parameter must be bound by llvm_return or llvm_points_to."
              ]

          (stats, vcs, post_override_state) <-
            verifyMethodSpec cc method_spec lemmas' checkSat tactic Nothing

          shared_context <- getSharedContext

          let output_values =
                map (((IntMap.!) $ post_override_state ^. termSub) . vnIndex . fst) output_parameters

          extracted_func <-
            io $ scLambdaList shared_context input_parameters
            =<< scTuple shared_context output_values
          when (not (closedTerm extracted_func)) $
            fail "Non-functional simulation summary."

          let nmi = llvmNameInfo func_name

          extracted_func_const <-
            io $ scDefineConstant shared_context nmi extracted_func
            =<< scTypeOf shared_context extracted_func
          input_terms <- io $ scVariables shared_context input_parameters
          applied_extracted_func <- io $ scApplyAll shared_context extracted_func_const input_terms
          applied_extracted_func_selectors <-
            io $ forM [1 .. (length output_parameters)] $ \i ->
            mkTypedTerm shared_context
              =<< scTupleSelector shared_context applied_extracted_func i (length output_parameters)
          let output_parameter_substitution =
                IntMap.fromList $
                zip (map (vnIndex . fst) output_parameters) (map ttTerm applied_extracted_func_selectors)
          let substitute_output_parameters =
                ttTermLens $ scInstantiate shared_context output_parameter_substitution
          let setup_value_substitute_output_parameter setup_value
                | SetupTerm term <- setup_value = SetupTerm <$> substitute_output_parameters term
                | otherwise = return $ setup_value
          let llvm_points_to_value_substitute_output_parameter = \case
                ConcreteSizeValue val -> ConcreteSizeValue <$> setup_value_substitute_output_parameter val
                SymbolicSizeValue arr sz ->
                  SymbolicSizeValue <$> substitute_output_parameters arr <*> substitute_output_parameters sz

          extracted_ret_value <- liftIO $ mapM
            setup_value_substitute_output_parameter
            (method_spec ^. MS.csRetValue)
          extracted_post_state_points_tos <- liftIO $ mapM
            (\case
              LLVMPointsTo x y z value ->
                LLVMPointsTo x y z <$> llvm_points_to_value_substitute_output_parameter value
              LLVMPointsToBitfield x y z value ->
                LLVMPointsToBitfield x y z <$> setup_value_substitute_output_parameter value)
            (method_spec ^. MS.csPostState ^. MS.csPointsTos)
          let extracted_method_spec = method_spec &
                MS.csRetValue .~ extracted_ret_value &
                MS.csPostState . MS.csPointsTos .~ extracted_post_state_points_tos

          -- XXX could have a real position...
          let pos = PosInternal "llvm_compositional_extract"
          typed_extracted_func_const <- io $ mkTypedTerm shared_context extracted_func_const
          extendEnv
              pos
              func_name
              ReadOnlyVar
              (tMono $ tTerm pos)
              Nothing             -- FUTURE: slot for doc string, could put something here
              (VTerm typed_extracted_func_const)

          let lemmaSet = Set.fromList (map (view MS.psSpecIdent) lemmas')

          end <- io getCurrentTime
          let diff = diffUTCTime end start
          ps <- io (MS.mkProvedSpec MS.SpecProved extracted_method_spec stats vcs lemmaSet diff)
          returnLLVMProof (SomeLLVM ps)

setupValueAsVariable :: SetupValue (LLVM arch) -> Maybe (VarName, Term)
setupValueAsVariable =
  \case
    SetupTerm term -> asVariable $ ttTerm term
    _ -> Nothing

llvmPointsToValueAsVariable :: LLVMPointsToValue arch -> Maybe (VarName, Term)
llvmPointsToValueAsVariable =
  \case
    ConcreteSizeValue val -> setupValueAsVariable val
    SymbolicSizeValue arr _sz -> asVariable $ ttTerm arr

-- | Check that all the overrides/lemmas were actually from this module
checkModuleCompatibility ::
  LLVMModule arch ->
  [SomeLLVM MS.ProvedSpec] ->
  TopLevel [MS.ProvedSpec (LLVM arch)]
checkModuleCompatibility llvmModule = foldM step []
  where
    step accum (SomeLLVM lemma) =
      case testEquality (lemma ^. MS.psSpec.MS.csCodebase) llvmModule of
        Nothing -> throwTopLevel $ unlines
          [ "Failed to apply an override that was verified against a"
          , "different LLVM module"
          ]
        Just Refl -> pure (lemma:accum)


-- -- | The real work of 'llvm_verify' and 'llvm_unsafe_assume_spec'.
withMethodSpec ::
  Bool {- ^ path sat -} ->
  LLVMModule arch ->
  Text                  {- ^ Name of the function -} ->
  LLVMCrucibleSetupM () {- ^ Boundary specification -} ->
  (( ?lc :: Crucible.TypeContext
   , ?memOpts::Crucible.MemOptions
   , ?w4EvalTactic :: W4EvalTactic
   , ?checkAllocSymInit :: Bool
   , ?singleOverrideSpecialCase :: Bool
   , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
   , Crucible.HasLLVMAnn Sym
   ) =>
     LLVMCrucibleContext arch ->
     MS.CrucibleMethodSpecIR (LLVM arch) ->
     TopLevel a) ->
  TopLevel a
withMethodSpec pathSat lm nm setup action =
  do (nm', parent) <- resolveSpecName nm
     let edef = findDefMaybeStatic (modAST lm) nm'
     let edecl = findDecl (modAST lm) nm'
     let mtrans = modTrans lm
     opts <- getOptions
     defOrDecls <-
       case (edef, edecl) of
         (Right defs, _) -> return (NE.map Left defs)
         (_, Right decl) -> return (Right decl NE.:| [])
         (Left err, Left _) -> throwTopLevel (displayVerifExceptionOpts opts err)

     let ?lc = mtrans ^. Crucible.transContext . Crucible.llvmTypeCtx

     sosp <- rwSingleOverrideSpecialCase <$> getTopLevelRW
     let ?singleOverrideSpecialCase = sosp

     Crucible.llvmPtrWidth (mtrans ^. Crucible.transContext) $ \_ ->
       fmap NE.head $ forM defOrDecls $ \defOrDecl ->
         setupLLVMCrucibleContext pathSat lm $ \cc ->
           do let sym = cc^.ccSym

              pos <- getPosition
              let setupLoc = toW4Loc "_SAW_LLVM_withMethodSpec" pos

              let est0 =
                    case defOrDecl of
                      Left def -> initialCrucibleSetupState cc def setupLoc parent
                      Right decl -> initialCrucibleSetupStateDecl cc decl setupLoc parent
              st0 <- either (throwTopLevel . show . ppSetupError) return est0

              -- execute commands of the method spec
              io $ W4.setCurrentProgramLoc sym setupLoc

              setupState  <-
                (execStateT
                   (runReaderT (runLLVMCrucibleSetupM setup)
                               (Setup.makeCrucibleSetupRO))
                     st0)
              let methodSpec = setupState ^. Setup.csMethodSpec
                  cc1        = setupState ^. Setup.csCrucibleContext

              -- check for missing llvm_execute_func
              unless (setupState ^. Setup.csPrePost == PostState) $
                io $ throwMethodSpec methodSpec $ Text.unpack $
                "Missing llvm_execute_func specification when verifying " <>
                methodSpec^.csName

              io $ checkSpecArgumentTypes cc1 methodSpec
              io $ checkSpecReturnType cc1 methodSpec

              action cc1 methodSpec

verifyMethodSpec ::
  ( ?lc :: Crucible.TypeContext
  , ?memOpts::Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , ?checkAllocSymInit :: Bool
  , ?singleOverrideSpecialCase :: Bool
  , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
  , Crucible.HasLLVMAnn Sym
  ) =>
  LLVMCrucibleContext arch ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  [MS.ProvedSpec (LLVM arch)] ->
  Bool ->
  ProofScript () ->
  Maybe (IORef (Map Text.Text [Crucible.FunctionProfile])) ->
  TopLevel (SolverStats, [MS.VCStats], OverrideState (LLVM arch))
verifyMethodSpec cc methodSpec lemmas checkSat tactic asp =
  ccWithBackend cc $ \bak ->
  do printOutLnTop Info $ Text.unpack $
         "Verifying " <> (methodSpec ^. csName) <> "..."

     let sym = cc^.ccSym

     profFile <- rwProfilingFile <$> getTopLevelRW
     (writeFinalProfile, pfs) <- io $ Common.setupProfiling sym "llvm_verify" profFile

     -- set up the metadata map for tracking proof obligation metadata
     mdMap <- io $ newIORef mempty

     -- set up the LLVM memory with a pristine heap
     let globals = cc^.ccLLVMGlobals
     let mvar = Crucible.llvmMemVar (ccLLVMContext cc)
     let mem0 = lookupMemGlobal mvar globals
     -- push a memory stack frame if starting from a breakpoint
     let mem = case methodSpec^.csParentName of
               Just parent -> mem0
                 { Crucible.memImplHeap = Crucible.pushStackFrameMem
                   (mconcat [methodSpec ^. csName, "#", parent])
                   (Crucible.memImplHeap mem0)
                 }
               Nothing -> mem0

     let globals1 = Crucible.llvmGlobals mvar mem

     -- construct the initial state for verifications
     opts <- getOptions
     (args, assumes, env, globals2) <-
       io $ verifyPrestate opts cc methodSpec globals1

     when (detectVacuity opts)
       $ Vacuity.checkAssumptionsForContradictions sym methodSpec tactic assumes

     -- save initial path conditions
     frameIdent <- io $ Crucible.pushAssumptionFrame bak

     -- run the symbolic execution
     printOutLnTop Info $ Text.unpack $
         "Simulating " <> (methodSpec ^. csName) <> "..."
     top_loc <- toW4Loc "llvm_verify" <$> getPosition
     (ret, globals3, invSubst) <-
       verifySimulate opts cc pfs methodSpec args assumes top_loc lemmas globals2 checkSat asp mdMap

     -- collect the proof obligations
     (asserts, post_override_state) <-
       verifyPoststate cc
       methodSpec env globals3 ret
       mdMap
       invSubst

     -- restore previous assumption state
     _ <- io $ Crucible.popAssumptionFrame bak frameIdent

     -- attempt to verify the proof obligations
     printOutLnTop Info $ Text.unpack $
         "Checking proof obligations " <> (methodSpec ^. csName) <> "..."
     (stats, vcstats) <- verifyObligations cc methodSpec tactic assumes asserts
     io $ writeFinalProfile

     return ( stats
            , vcstats
            , post_override_state
            )




refineMethodSpec ::
  ( ?lc :: Crucible.TypeContext
  , ?memOpts::Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , ?checkAllocSymInit :: Bool
  , ?singleOverrideSpecialCase :: Bool
  , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
  , Crucible.HasLLVMAnn Sym
  ) =>
  LLVMCrucibleContext arch ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  [MS.ProvedSpec (LLVM arch)] ->
  ProofScript () ->
  TopLevel (SolverStats, [MS.VCStats])
refineMethodSpec cc methodSpec lemmas tactic =
  ccWithBackend cc $ \bak ->
  do let sym = cc^.ccSym

     let fnm = methodSpec ^. MS.csMethod

     let isRelevant lemma_spec =
           lemma_spec ^. MS.csMethod == fnm

     let (relevantLemmas, irrelevantLemmas) =
           partition isRelevant (map (view MS.psSpec) lemmas)

     relevantLemmas' <-
        case relevantLemmas of
          [] -> fail $ unlines $
                  [ "No relevant overrides included in specification refinement for " ++ show (pretty fnm) ] ++
                  (if null irrelevantLemmas then [] else [ "Overrides provided for irrelevant methods:" ]) ++
                  [ " *  " ++ show (pretty nm)
                  | nm <- nubOrd $ map (view MS.csMethod) $ irrelevantLemmas
                  ]
          (x:xs) -> return (x NE.:| xs)

     printOutLnTop Info $ Text.unpack $
         "Refining specification for " <> (methodSpec ^. csName) <> "..."

     unless (null irrelevantLemmas) $ do
         printOutLnTop Warn $ Text.unpack $
             "Irrelevant overrides included in specification refinement for " <>
             ppLLVMMethodId fnm
         mapM_ (printOutLnTop Warn) $
           [ " *  " ++ show (pretty nm)
           | nm <- nubOrd $ map (view MS.csMethod) $ irrelevantLemmas
           ]

     profFile <- rwProfilingFile <$> getTopLevelRW
     (writeFinalProfile, pfs) <- io $ Common.setupProfiling sym "llvm_refine_spec" profFile

     -- set up the metadata map for tracking proof obligation metadata
     mdMap <- io $ newIORef mempty

     -- set up the LLVM memory with a pristine heap
     let globals = cc^.ccLLVMGlobals
     let mvar = Crucible.llvmMemVar (ccLLVMContext cc)
     let mem = lookupMemGlobal mvar globals

     let globals1 = Crucible.llvmGlobals mvar mem

     -- construct the initial state for verifications
     opts <- getOptions
     (args, assumes, env, globals2) <-
       io $ verifyPrestate opts cc methodSpec globals1

     when (detectVacuity opts)
       $ Vacuity.checkAssumptionsForContradictions sym methodSpec tactic assumes

     -- save initial path conditions
     frameIdent <- io $ Crucible.pushAssumptionFrame bak

     -- run the symbolic execution
     top_loc <- toW4Loc "llvm_refine_spec" <$> getPosition

     (ret, globals3) <-
       io $ refineSimulate opts cc pfs methodSpec args assumes top_loc relevantLemmas' globals2 mdMap

     -- collect the proof obligations
     (asserts, _post_override_state) <-
       verifyPoststate cc
       methodSpec env globals3 ret
       mdMap
       MapF.empty

     -- restore previous assumption state
     _ <- io $ Crucible.popAssumptionFrame bak frameIdent

     -- attempt to verify the proof obligations
     printOutLnTop Info $ Text.unpack $
         "Checking proof obligations " <> (methodSpec ^. csName) <> "..."
     (stats, vcstats) <- verifyObligations cc methodSpec tactic assumes asserts
     io $ writeFinalProfile

     return ( stats
            , vcstats
            )


verifyObligations :: LLVMCrucibleContext arch
                  -> MS.CrucibleMethodSpecIR (LLVM arch)
                  -> ProofScript ()
                  -> [Crucible.LabeledPred Term AssumptionReason]
                  -> [(String, MS.ConditionMetadata, Term)]
                  -> TopLevel (SolverStats, [MS.VCStats])
verifyObligations cc mspec tactic assumes asserts =
  do let sym = cc^.ccSym
     st     <- io $ Common.sawCoreState sym
     let sc  = saw_ctx st
     useSequentGoals <- rwSequentGoals <$> getTopLevelRW
     let assumeTerms = toListOf (folded . Crucible.labeledPred) assumes
     assume <- io $ scAndList sc assumeTerms
     let nm  = mspec ^. csName
     outs <-
       forM (zip [(0::Int)..] asserts) $ \(n, (msg, md, assert)) ->
       do let msg' = Text.pack msg
          goal  <- io $ scImplies sc assume assert
          goal' <- io $ boolToProp sc [] goal
          sqt <- if useSequentGoals then
                    io $ booleansToSequent sc assumeTerms [assert]
                 else
                    return (propToSequent goal')
          let ploc = MS.conditionLoc md
          let gloc = (unwords [show (W4.plSourceLoc ploc)
                             ,"in"
                             , show (W4.plFunction ploc)]) ++
                     (if null (MS.conditionContext md) then [] else
                        "\n" ++ MS.conditionContext md)
          let goalname = nm <> " (" <> Text.takeWhile (/= '\n') msg' <> ")"
              proofgoal = ProofGoal
                          { goalNum  = n
                          , goalType = MS.conditionType md
                          , goalName = Text.unpack nm
                          , goalLoc  = gloc
                          , goalDesc = msg
                          , goalSequent = sqt
                          , goalTags = MS.conditionTags md
                          }
          res <- runProofScript tactic goal' proofgoal (Just ploc)
                    (Text.unwords
                      ["LLVM verification condition", Text.pack (show n), goalname])
                    False -- do not record this theorem in the database
                    useSequentGoals
          case res of
            ValidProof stats thm ->
              return (stats, MS.VCStats md stats (thmSummary thm) (thmNonce thm) (thmDepends thm) (thmElapsedTime thm))
            UnfinishedProof pst ->
              do printOutLnTop Info $ Text.unpack $ "Subgoal failed: " <> nm <> " " <> msg'
                 throwTopLevel $ "Proof failed " ++ show (length (psGoals pst)) ++ " goals remaining."
            InvalidProof stats vals _pst ->
              do printOutLnTop Info $ Text.unpack $ "Subgoal failed: " <> nm <> " " <> msg'
                 printOutLnTop Info (show stats)
                 printOutLnTop OnlyCounterExamples "----------Counterexample----------"
                 opts <- rwPPOpts <$> getTopLevelRW
                 if null vals then
                   printOutLnTop OnlyCounterExamples "<<All settings of the symbolic variables constitute a counterexample>>"
                 else
                   let showVar x = Text.unpack (vnName x) in
                   let showAssignment (x, val) = "  " ++ showVar x ++ ": " ++ show (ppFirstOrderValue opts val) in
                   mapM_ (printOutLnTop OnlyCounterExamples . showAssignment) vals
                 printOutLnTop OnlyCounterExamples "----------------------------------"
                 throwTopLevel "Proof failed." -- Mirroring behavior of llvm_verify
     printOutLnTop Info $ Text.unpack $ "Proof succeeded! " <> nm

     let stats = mconcat (map fst outs)
     let vcstats = map snd outs
     return (stats, vcstats)

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
          mt' <- exceptToFail (typeOfSetupValue cc tyenv nameEnv sv)
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
         throwMethodSpec mspec $ Text.unpack $
             "Return value specified, but function " <> mspec ^. csName <>
             " has void return type"
    (Just sv, Just retTy) ->
      do retTy' <- exceptToFail $
           typeOfSetupValue cc
             (MS.csAllocations mspec) -- map allocation indices to allocations
             (mspec ^. MS.csPreState . MS.csVarTypeNames) -- map alloc indices to var names
             sv
         -- This check is too lax, see saw-script#443
         b <- checkRegisterCompatibility retTy retTy'
         unless b $ throwMethodSpec mspec $ Text.unpack $ Text.unlines
           [ "Incompatible types for return value when verifying " <> mspec^.csName
           , "Expected: " <> Text.pack (show retTy)
           , "but given value of type: " <> Text.pack (show retTy')
           ]
    (Nothing, Just retTy) ->
      throwMethodSpec mspec $ Text.unpack $ Text.unlines
      [ "Missing return value specification for function with non-void return type"
      , "Expected: " <> Text.pack (show retTy)
      ]
    (Nothing, Nothing) -> pure ()

-- | Evaluate the precondition part of a Crucible method spec:
--
-- * Allocate heap space for each 'llvm_alloc' statement.
--
-- * Record an equality precondition for each 'llvm_equal'
-- statement.
--
-- * Write to memory for each 'llvm_points_to' statement. (Writes
-- to already-initialized locations are transformed into equality
-- preconditions.)
--
-- * Evaluate the function arguments from the 'llvm_execute_func'
-- statement.
--
-- Returns a tuple of (arguments, preconditions, pointer values,
-- memory).
verifyPrestate ::
  ( ?memOpts :: Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
  , Crucible.HasLLVMAnn Sym
  ) =>
  Options ->
  LLVMCrucibleContext arch ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  Crucible.SymGlobalState Sym ->
  IO ([(Crucible.MemType, LLVMVal)],
      [Crucible.LabeledPred Term AssumptionReason],
      Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)),
      Crucible.SymGlobalState Sym)
verifyPrestate opts cc mspec globals =
  do let ?lc = ccTypeCtx cc
     let sym = cc^.ccSym
     let prestateLoc = W4.mkProgramLoc "_SAW_LLVM_verifyPrestate" W4.InternalPos
     liftIO $ W4.setCurrentProgramLoc sym prestateLoc

     let lvar = Crucible.llvmMemVar (ccLLVMContext cc)
     let mem = lookupMemGlobal lvar globals

     -- Allocate LLVM memory for each 'llvm_alloc'
     (env, mem') <- runStateT
       (Map.traverseWithKey (doAlloc cc) (mspec ^. MS.csPreState . MS.csAllocs))
       mem

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
  (?lc :: Crucible.TypeContext, ?w4EvalTactic :: W4EvalTactic, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
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

-- | For each "llvm_global_alloc" in the method specification, allocate and
-- register the appropriate memory.
setupGlobalAllocs :: forall arch.
  ( ?lc :: Crucible.TypeContext
  , ?memOpts :: Crucible.MemOptions
  , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
  , Crucible.HasLLVMAnn Sym
  ) =>
  LLVMCrucibleContext arch ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  MemImpl ->
  IO MemImpl
setupGlobalAllocs cc mspec mem0 = foldM go mem0 $ mspec ^. MS.csGlobalAllocs
  where
    sym = cc ^. ccSym

    go :: MemImpl -> MS.AllocGlobal (LLVM arch) -> IO MemImpl
    go mem (LLVMAllocGlobal _ symbol@(L.Symbol name)) = do
      let mtrans = ccLLVMModuleTrans cc
          gimap = view Crucible.globalInitMap mtrans
      case Map.lookup symbol gimap of
        Just (g, Right (mt, _)) -> ccWithBackend cc $ \bak ->
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
             (ptr, mem') <- Crucible.doMalloc bak Crucible.GlobalAlloc Crucible.Mutable name mem sz' alignment
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
  ( ?lc :: Crucible.TypeContext
  , ?memOpts :: Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
  , Crucible.HasLLVMAnn Sym
  ) =>
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
         ptr'' <- unpackPtrVal ptr'

         cond' <- mapM (resolveSAWPred cc . ttTerm) cond

         storePointsToValue opts cc env tyenv nameEnv mem cond' ptr'' val Nothing
    go mem (LLVMPointsToBitfield _loc ptr fieldName val) =
      do (bfIndex, ptr') <- resolveSetupValBitfield cc mem env tyenv nameEnv ptr fieldName
         ptr'' <- unpackPtrVal ptr'

         storePointsToBitfieldValue opts cc env tyenv nameEnv mem ptr'' bfIndex val

    unpackPtrVal :: LLVMVal -> IO (LLVMPtr (Crucible.ArchWidth arch))
    unpackPtrVal (Crucible.LLVMValInt blk off)
        | Just Refl <- testEquality (W4.bvWidth off) Crucible.PtrWidth
        = return (Crucible.LLVMPointer blk off)
    unpackPtrVal _ = throwMethodSpec mspec "Non-pointer value found in points-to assertion"

-- | Sets up globals (ghost variable), and collects boolean terms
-- that should be assumed to be true.
setupPrestateConditions ::
  (?lc :: Crucible.TypeContext, ?w4EvalTactic :: W4EvalTactic, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  MS.CrucibleMethodSpecIR (LLVM arch)        ->
  LLVMCrucibleContext arch        ->
  Crucible.MemImpl Sym ->
  Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)) ->
  Crucible.SymGlobalState Sym ->
  [MS.SetupCondition (LLVM arch)]            ->
  IO ( Crucible.SymGlobalState Sym, [Crucible.LabeledPred Term AssumptionReason]
     )
setupPrestateConditions mspec cc mem env = aux []
  where
    tyenv   = MS.csAllocations mspec
    nameEnv = mspec ^. MS.csPreState . MS.csVarTypeNames

    aux acc globals [] = return (globals, acc)

    aux acc globals (MS.SetupCond_Equal md val1 val2 : xs) =
      do val1' <- resolveSetupVal cc mem env tyenv nameEnv val1
         val2' <- resolveSetupVal cc mem env tyenv nameEnv val2
         t     <- assertEqualVals cc val1' val2'
         let lp = Crucible.LabeledPred t (md, "equality precondition")
         aux (lp:acc) globals xs

    aux acc globals (MS.SetupCond_Pred md tm : xs) =
      let lp = Crucible.LabeledPred (ttTerm tm) (md, "precondition") in
      aux (lp:acc) globals xs

    aux acc globals (MS.SetupCond_Ghost _md var val : xs) =
      case val of
        TypedTerm (TypedTermSchema sch) tm ->
          aux acc (Crucible.insertGlobal var (sch,tm) globals) xs
        TypedTerm tp _ ->
          fail $ unlines
            [ "Setup term for global variable expected to have Cryptol schema type, but got"
            , show (ppTypedTermType tp)
            ]

--------------------------------------------------------------------------------

-- | Create a SAWCore formula asserting that two 'LLVMVal's are equal.
assertEqualVals ::
  LLVMCrucibleContext arch ->
  LLVMVal ->
  LLVMVal ->
  IO Term
assertEqualVals cc v1 v2 =
  do let sym = cc^.ccSym
     st <- Common.sawCoreState sym
     toSC sym st =<< equalValsPred cc v1 v2

--------------------------------------------------------------------------------

-- TODO(langston): combine with/move to executeAllocation
doAlloc ::
  ( ?memOpts :: Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
  , Crucible.HasLLVMAnn Sym
  ) =>
  LLVMCrucibleContext arch       ->
  AllocIndex ->
  LLVMAllocSpec ->
  StateT MemImpl IO (LLVMPtr (Crucible.ArchWidth arch))
doAlloc cc i (LLVMAllocSpec mut _memTy alignment sz md fresh initialization)
  | fresh = liftIO $ executeFreshPointer cc i
  | otherwise =
  ccWithBackend cc $ \bak ->
  StateT $ \mem ->
  do sz' <- liftIO $ resolveSAWSymBV cc Crucible.PtrWidth sz
     let l = show (W4.plSourceLoc (MS.conditionLoc md))
     liftIO $ doAllocSymInit bak mem mut alignment sz' l initialization

--------------------------------------------------------------------------------

lookupMemGlobal :: Crucible.GlobalVar tp -> Crucible.SymGlobalState sym -> Crucible.RegValue sym tp
lookupMemGlobal mvar globals =
  fromMaybe
    -- this used to claim it happens in pushFreshReturnAddress from X86.hs,
    -- which seems to be possible but far from the only entry point...
    (panic "lookupMemGlobal" ["LLVM Memory global not found: " <> Text.pack (show $ pretty mvar)])
    (Crucible.lookupGlobal mvar globals)

ppAbortedResult :: LLVMCrucibleContext arch
                -> Crucible.AbortedResult Sym a
                -> Doc ann
ppAbortedResult cc = Common.ppAbortedResult (ppGlobalPair cc)

ppGlobalPair :: LLVMCrucibleContext arch
             -> Crucible.GlobalPair Sym a
             -> Doc ann
ppGlobalPair cc gp =
  let mvar = Crucible.llvmMemVar (ccLLVMContext cc)
      globals = gp ^. Crucible.gpGlobals in
  Crucible.ppMem $ Crucible.memImplHeap $ lookupMemGlobal mvar globals


--------------------------------------------------------------------------------

registerOverride ::
  ( ?lc :: Crucible.TypeContext
  , ?memOpts::Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , ?checkAllocSymInit :: Bool
  , ?singleOverrideSpecialCase :: Bool
  , Crucible.HasPtrWidth wptr
  , wptr ~ Crucible.ArchWidth arch
  , Crucible.HasLLVMAnn Sym
  ) =>
  Options                    ->
  LLVMCrucibleContext arch       ->
  Crucible.SimContext (SAWCruciblePersonality Sym) Sym Crucible.LLVM ->
  W4.ProgramLoc              ->
  IORef MetadataMap ->
  NE.NonEmpty (MS.CrucibleMethodSpecIR (LLVM arch))     ->
  Crucible.OverrideSim (SAWCruciblePersonality Sym) Sym Crucible.LLVM rtp args ret (Crucible.SomeHandle)
registerOverride opts cc sim_ctx _top_loc mdMap cs =
  ccWithBackend cc $ \bak ->
  do let sym = Common.backendGetSym bak
     sc <- saw_ctx <$> liftIO (Common.sawCoreState sym)
     let fstr = (NE.head cs)^.csName
         fsym = L.Symbol (Text.unpack fstr)
         llvmctx = ccLLVMContext cc
         mvar = Crucible.llvmMemVar llvmctx
         halloc = Crucible.simHandleAllocator sim_ctx
         matches dec = matchingStatics (L.decName dec) fsym
     liftIO $
       printOutLn opts Info $ Text.unpack $ "Registering overrides for `" <> fstr <> "`"

     case filter matches (Crucible.allModuleDeclares (ccLLVMModuleAST cc)) of
       [] -> fail $ Text.unpack $ "Couldn't find declaration for `" <> fstr <> "` when registering override for it."
       (d:ds) ->
         Crucible.llvmDeclToFunHandleRepr' d $ \argTypes retType ->
           do let fn_name = W4.functionNameFromText fstr
              h <- liftIO $ Crucible.mkHandle' halloc fn_name argTypes retType
              Crucible.bindFnHandle h
                $ Crucible.UseOverride
                $ Crucible.mkOverride' fn_name retType
                $ methodSpecHandler opts sc cc mdMap cs h
              mem <- Crucible.readGlobal mvar
              let bindPtr m decl =
                    do let declName = L.decName decl
                       printOutLn opts Info $ "  variant `" ++ show declName ++ "`"
                       Crucible.bindLLVMFunPtr bak declName h m
              mem' <- liftIO $ foldM bindPtr mem (d:ds)
              Crucible.writeGlobal mvar mem'
              return (Crucible.SomeHandle h)

registerInvariantOverride ::
  ( ?lc :: Crucible.TypeContext
  , ?memOpts::Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , ?checkAllocSymInit :: Bool
  , ?singleOverrideSpecialCase :: Bool
  , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
  , Crucible.HasLLVMAnn Sym
  ) =>
  Options ->
  LLVMCrucibleContext arch ->
  W4.ProgramLoc ->
  IORef MetadataMap ->
  HashMap Crucible.SomeHandle [Crucible.BreakpointName] ->
  NE.NonEmpty (MS.CrucibleMethodSpecIR (LLVM arch)) ->
  IO (Crucible.ExecutionFeature (SAWCruciblePersonality Sym) Sym Crucible.LLVM rtp)
registerInvariantOverride opts cc top_loc mdMap all_breakpoints cs =
  do sc <- saw_ctx <$> Common.sawCoreState (cc^.ccSym)
     let name = (NE.head cs) ^. csName
     parent <-
       case neNubOrd $ fmap (view csParentName) cs of
         (Just unique_parent NE.:| []) -> return unique_parent
         _ -> fail $ Text.unpack $ "Multiple parent functions for breakpoint: " <> name
     liftIO $ printOutLn opts Info $ Text.unpack $ "Registering breakpoint `" <> name <> "`"
     withBreakpointCfgAndBlockId opts cc (Text.unpack name) (Text.unpack parent) $ \cfg breakpoint_block_id ->
       do let breakpoint_name = Crucible.BreakpointName name
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
            (methodSpecHandler opts sc cc mdMap cs hInvariant)
            all_breakpoints

--------------------------------------------------------------------------------

withCfg ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch), Crucible.HasLLVMAnn Sym) =>
  Options ->
  LLVMCrucibleContext arch ->
  String ->
  (forall blocks init ret . Crucible.CFG Crucible.LLVM blocks init ret -> IO a) ->
  IO a
withCfg opts context name k =
  do let function_id = L.Symbol name
     Crucible.getTranslatedCFG (ccLLVMModuleTrans context) function_id >>= \case
       Just (_, Crucible.AnyCFG cfg, warns) ->
         do mapM_ (handleTranslationWarning opts) warns
            k cfg
       Nothing -> fail $ "Unexpected function name: " ++ name

withCfgAndBlockId ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch), Crucible.HasLLVMAnn Sym) =>
  Options ->
  LLVMCrucibleContext arch ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  (forall blocks init args ret . Crucible.CFG Crucible.LLVM blocks init ret -> Crucible.BlockID blocks args -> IO a) ->
  IO a
withCfgAndBlockId opts context method_spec k =
  case method_spec ^. csParentName of
    Nothing -> withCfg opts context (Text.unpack (method_spec ^. csName)) $ \cfg ->
      k cfg (Crucible.cfgEntryBlockID cfg)
    Just parent -> withBreakpointCfgAndBlockId opts
      context
      (Text.unpack (method_spec ^. csName))
      (Text.unpack parent)
      k

withBreakpointCfgAndBlockId ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch), Crucible.HasLLVMAnn Sym) =>
  Options ->
  LLVMCrucibleContext arch ->
  String ->
  String ->
  (forall blocks init args ret . Crucible.CFG Crucible.LLVM blocks init ret -> Crucible.BlockID blocks args -> IO a) ->
  IO a
withBreakpointCfgAndBlockId opts context name parent k =
  do let breakpoint_name = Crucible.BreakpointName $ Text.pack name
     withCfg opts context parent $ \cfg ->
       case Bimap.lookup breakpoint_name (Crucible.cfgBreakpoints cfg) of
         Just (Some breakpoint_block_id) -> k cfg breakpoint_block_id
         Nothing -> fail $ "Unexpected breakpoint name: " ++ name

-- | Simulate an LLVM function with Crucible as part of a 'llvm_verify' command,
-- making sure to install any overrides that the user supplies.
verifySimulate ::
  ( ?lc :: Crucible.TypeContext
  , ?memOpts::Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , ?checkAllocSymInit :: Bool
  , ?singleOverrideSpecialCase :: Bool
  , Crucible.HasPtrWidth wptr
  , wptr ~ Crucible.ArchWidth arch
  , Crucible.HasLLVMAnn Sym
  ) =>
  Options ->
  LLVMCrucibleContext arch ->
  [Crucible.GenericExecutionFeature Sym] ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  [(Crucible.MemType, LLVMVal)] ->
  [Crucible.LabeledPred Term AssumptionReason] ->
  W4.ProgramLoc ->
  [MS.ProvedSpec (LLVM arch)] ->
  Crucible.SymGlobalState Sym ->
  Bool ->
  Maybe (IORef (Map Text.Text [Crucible.FunctionProfile])) ->
  IORef MetadataMap ->
  TopLevel (Maybe (Crucible.MemType, LLVMVal), Crucible.SymGlobalState Sym, MapF (W4.SymFnWrapper Sym) (W4.SymFnWrapper Sym))
verifySimulate opts cc pfs mspec args assumes top_loc lemmas globals checkSat asp mdMap =
  io $ withCfgAndBlockId opts cc mspec $ \cfg entryId -> ccWithBackend cc $ \bak -> do
     let sym = cc^.ccSym
     let argTys = Crucible.blockInputs $
           Crucible.getBlock entryId $ Crucible.cfgBlockMap cfg
     let retTy = Crucible.handleReturnType $ Crucible.cfgHandle cfg

     args' <- prepareArgs sym argTys (map snd args)
     let simCtx = cc^.ccLLVMSimContext
     psatf <-
       Crucible.pathSatisfiabilityFeature sym
         (Crucible.considerSatisfiability bak)
     let patSatGenExecFeature = if checkSat then [psatf] else []
     when checkSat checkYicesVersion
     let (funcLemmas, invLemmas) =
           partition (isNothing . view csParentName)
                     (map (view MS.psSpec) lemmas)

     breakpoints <-
       forM (neGroupOn (view csParentName) invLemmas) $ \specs ->
       do let parent = fromJust $ (NE.head specs) ^. csParentName
          let breakpoint_names = nubOrd $
                map (Crucible.BreakpointName . view csName) (NE.toList specs)
          withCfg opts cc (Text.unpack parent) $ \parent_cfg ->
            return
              ( Crucible.SomeHandle (Crucible.cfgHandle parent_cfg)
              , breakpoint_names
              )

     invariantExecFeatures <-
       mapM
       (registerInvariantOverride opts cc top_loc mdMap (HashMap.fromList breakpoints))
       (neGroupOn (view csName) invLemmas)

     additionalFeatures <-
       mapM (Crucible.arraySizeProfile (ccLLVMContext cc)) $ maybeToList asp

     let execFeatures =
           invariantExecFeatures ++
           map Crucible.genericToExecutionFeature (patSatGenExecFeature ++ pfs) ++
           additionalFeatures

     let initExecState =
           Crucible.InitialState simCtx globals Crucible.defaultAbortHandler retTy $
           Crucible.runOverrideSim retTy $
           do mapM_ (registerOverride opts cc simCtx top_loc mdMap)
                    (neGroupOn (view csName) funcLemmas)
              liftIO $
                for_ assumes $ \(Crucible.LabeledPred p (md, reason)) ->
                  do expr <- resolveSAWPred cc p
                     let loc = MS.conditionLoc md
                     Crucible.addAssumption bak
                       (Crucible.GenericAssumption loc reason expr)
              Crucible.regValue <$> (Crucible.callBlock cfg entryId args')
     res <- Crucible.executeCrucible execFeatures initExecState
     case res of
       Crucible.FinishedResult _ partialResult ->
         do Crucible.GlobalPair retval globals1 <-
              Common.getGlobalPair opts partialResult
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
            return (retval', globals1, MapF.empty)

       Crucible.TimeoutResult _ -> fail $ "Symbolic execution timed out"

       Crucible.AbortedResult _ ar ->
         do let resultDoc = ppAbortedResult cc ar
            fail $ unlines [ "Symbolic execution failed."
                           , show resultDoc
                           ]


refineSimulate ::
  ( ?lc :: Crucible.TypeContext
  , ?memOpts::Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , ?checkAllocSymInit :: Bool
  , ?singleOverrideSpecialCase :: Bool
  , Crucible.HasPtrWidth wptr
  , wptr ~ Crucible.ArchWidth arch
  , Crucible.HasLLVMAnn Sym
  ) =>
  Options ->
  LLVMCrucibleContext arch ->
  [Crucible.GenericExecutionFeature Sym] ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  [(Crucible.MemType, LLVMVal)] ->
  [Crucible.LabeledPred Term AssumptionReason] ->
  W4.ProgramLoc ->
  NE.NonEmpty (MS.CrucibleMethodSpecIR (LLVM arch)) ->
  Crucible.SymGlobalState Sym ->
  IORef MetadataMap ->
  IO (Maybe (Crucible.MemType, LLVMVal), Crucible.SymGlobalState Sym)
refineSimulate opts cc pfs mspec args assumes top_loc lemmas globals mdMap =
  let fstr = mspec^.csName
      fsym = L.Symbol (Text.unpack fstr)
      matches dec = matchingStatics (L.decName dec) fsym
      simCtx = cc^.ccLLVMSimContext
      sym = cc^.ccSym
  in
  case filter matches (Crucible.allModuleDeclares (ccLLVMModuleAST cc)) of
    [] -> fail $ Text.unpack $ "Couldn't find declaration for `" <> fstr <> "` when attempting specification refinement."
    (decl:_ds) ->
      Crucible.llvmDeclToFunHandleRepr' decl $ \argTys retTy ->
      ccWithBackend cc $ \bak ->
      do args' <- prepareArgs sym argTys (map snd args)

         let execFeatures =
               map Crucible.genericToExecutionFeature pfs

         let initExecState =
               Crucible.InitialState simCtx globals Crucible.defaultAbortHandler retTy $
               Crucible.runOverrideSim retTy $
               do Crucible.SomeHandle h <- registerOverride opts cc simCtx top_loc mdMap lemmas
                  case (testEquality argTys (Crucible.handleArgTypes h),
                        testEquality retTy (Crucible.handleReturnType h)) of
                    (Nothing, _) ->
                        panic "refineSimulate" [
                            "Argument type mismatch when refining specification for " <> fstr,
                            "Argument types: " <> Text.pack (show argTys),
                            "Handle: " <> Text.pack (show h)
                        ]
                    (_, Nothing) ->
                        panic "refineSimulate" [
                            "Return type mismatch when refining specification for " <> fstr,
                            "Return type: " <> Text.pack (show retTy),
                            "Handle: " <> Text.pack (show h)
                        ]
                    (Just Refl, Just Refl) ->
                      do liftIO $
                          for_ assumes $ \(Crucible.LabeledPred p (md, reason)) ->
                           do expr <- resolveSAWPred cc p
                              let loc = MS.conditionLoc md
                              Crucible.addAssumption bak
                                (Crucible.GenericAssumption loc reason expr)
                         Crucible.regValue <$> (Crucible.callFnVal (Crucible.HandleFnVal h) args')

         res <- Crucible.executeCrucible execFeatures initExecState
         case res of
           Crucible.FinishedResult _ partialResult ->
             do Crucible.GlobalPair retval globals1 <-
                  Common.getGlobalPair opts partialResult
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


prepareArgs ::
  Sym ->
  Ctx.Assignment Crucible.TypeRepr xs ->
  [LLVMVal] ->
  IO (Crucible.RegMap Sym xs)
prepareArgs sym ctx x =
  Crucible.RegMap <$>
  Ctx.traverseWithIndex (\idx tr ->
    do v <- Crucible.unpackMemValue sym tr (x !! Ctx.indexVal idx)
       return (Crucible.RegEntry tr v))
  ctx

--------------------------------------------------------------------------------

verifyPoststate ::
  ( ?lc :: Crucible.TypeContext
  , ?memOpts::Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , ?checkAllocSymInit :: Bool
  , Crucible.HasPtrWidth wptr
  , wptr ~ Crucible.ArchWidth arch
  , Crucible.HasLLVMAnn Sym
  ) =>
  LLVMCrucibleContext arch {- ^ crucible context -} ->
  MS.CrucibleMethodSpecIR (LLVM arch) {- ^ specification -} ->
  Map AllocIndex (LLVMPtr wptr) {- ^ allocation substitution -} ->
  Crucible.SymGlobalState Sym {- ^ global variables -} ->
  Maybe (Crucible.MemType, LLVMVal) {- ^ optional return value -} ->
  IORef MetadataMap {- ^ metadata map -} ->
  MapF (W4.SymFnWrapper Sym) (W4.SymFnWrapper Sym) {- ^ invariant substitution -} ->
  TopLevel ([(String, MS.ConditionMetadata, Term)], OverrideState (LLVM arch))
    {- ^ generated labels and verification conditions -}
verifyPoststate cc mspec env0 globals ret mdMap invSubst =
  ccWithBackend cc $ \bak ->
  do poststateLoc <- toW4Loc "_SAW_LLVM_verifyPoststate" <$> getPosition
     sc <- getSharedContext
     opts <- getOptions
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

     let initialFree =
           Set.fromList
           (map (vnIndex . tvName) (view (MS.csPostState . MS.csFreshVars) mspec))
     matchPost <-
       io $
       runOverrideMatcher sym globals env0 terms0 initialFree poststateLoc $
       do matchResult opts sc
          learnCond opts sc cc mspec PostState
            (mspec ^. MS.csGlobalAllocs)
            (mspec ^. MS.csPreState . MS.csAllocs)
            (mspec ^. MS.csPostState)

     st <-
       case matchPost of
         Left err      -> throwTopLevel (show err)
         Right (_, st) -> return st
     io $ for_ (view osAsserts st) $ \(md,W4.LabeledPred p r) ->
       do (ann,p') <- W4.annotateTerm sym p
          modifyIORef mdMap (Map.insert ann md)
          Crucible.addAssertion bak (Crucible.LabeledPred p' r)

     sc_obligations <- io $ getPoststateObligations sc bak mdMap invSubst
     return (sc_obligations, st)

  where
    sym = cc^.ccSym

    matchResult opts sc =
      case (ret, mspec ^. MS.csRetValue) of
        (Just (rty,r), Just expect) ->
          let md = MS.ConditionMetadata
                   { MS.conditionLoc = mspec ^. MS.csLoc
                   , MS.conditionTags = mempty -- TODO? should `llvm_return` track tags?
                   , MS.conditionType = "return value matching"
                   , MS.conditionContext = ""
                   } in
          matchArg opts sc cc mspec PostState md r rty expect
        (Nothing     , Just _ )     ->
          fail "verifyPoststate: unexpected llvm_return specification"
        _ -> return ()

-- | Translate the proof obligations from the Crucible backend into SAWCore
-- terms. For each proof oblication, return a triple consisting of the error
-- message, the metadata, and the SAWCore. For each proof obligation, substitute
-- the uninterpreted invariants with their definitions.
getPoststateObligations ::
  Crucible.IsSymBackend Sym bak =>
  SharedContext ->
  bak ->
  IORef MetadataMap ->
  MapF (W4.SymFnWrapper Sym) (W4.SymFnWrapper Sym) {- ^ invariant substitution -} ->
  IO [(String, MS.ConditionMetadata, Term)]
getPoststateObligations sc bak mdMap invSubst =
  do obligations <- maybe [] Crucible.goalsToList <$> Crucible.getProofObligations bak
     Crucible.clearProofObligations bak

     finalMdMap <- readIORef mdMap
     mapM (verifyObligation finalMdMap) obligations

  where
    sym = Crucible.backendGetSym bak

    verifyObligation finalMdMap (Crucible.ProofGoal hyps (Crucible.LabeledPred concl err@(Crucible.SimError loc _))) =
      do st <- Common.sawCoreState sym
         hypTerm <- toSC sym st =<< W4.substituteSymFns sym invSubst =<< Crucible.assumptionsPred sym hyps
         conclTerm <- toSC sym st =<< W4.substituteSymFns sym invSubst concl
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
         return (show err, md, obligation)

--------------------------------------------------------------------------------

setupLLVMCrucibleContext ::
  Bool {- ^ enable path sat checking -} ->
  LLVMModule arch ->
  ((?lc :: Crucible.TypeContext, ?memOpts::Crucible.MemOptions, ?w4EvalTactic :: W4EvalTactic, ?checkAllocSymInit :: Bool, Crucible.HasPtrWidth (Crucible.ArchWidth arch), Crucible.HasLLVMAnn Sym) =>
   LLVMCrucibleContext arch -> TopLevel a) ->
  TopLevel a
setupLLVMCrucibleContext pathSat lm action =
  do halloc <- getHandleAlloc
     sc <- getSharedContext
     opts <- getOptions
     basic_ss <- getBasicSS
     let llvm_mod = modAST lm
     let mtrans = modTrans lm
     let ctx = mtrans^.Crucible.transContext
     smt_array_memory_model_enabled <- gets rwSMTArrayMemoryModel
     crucible_assert_then_assume_enabled <- gets rwCrucibleAssertThenAssume
     what4HashConsing <- gets rwWhat4HashConsing
     what4PushMuxOps <- gets rwWhat4PushMuxOps
     laxPointerOrdering <- gets rwLaxPointerOrdering
     laxLoadsAndStores <- gets rwLaxLoadsAndStores
     noSatisfyingWriteFreshConstant <- gets rwNoSatisfyingWriteFreshConstant
     pathSatSolver <- gets rwPathSatSolver
     what4Eval <- gets rwWhat4Eval
     allocSymInitCheck <- gets rwAllocSymInitCheck
     crucibleTimeout <- gets rwCrucibleTimeout
     Crucible.llvmPtrWidth ctx $ \wptr ->
       Crucible.withPtrWidth wptr $
       do let ?lc = ctx^.Crucible.llvmTypeCtx
          let ?memOpts = Crucible.defaultMemOptions
                          { Crucible.laxPointerOrdering = laxPointerOrdering
                          , Crucible.laxLoadsAndStores = laxLoadsAndStores
                          , Crucible.noSatisfyingWriteFreshConstant = noSatisfyingWriteFreshConstant
                          }
          let ?intrinsicsOpts = Crucible.defaultIntrinsicsOptions
          let ?recordLLVMAnnotation = \_ _ _ -> return ()
          let ?w4EvalTactic = W4EvalTactic { doW4Eval = what4Eval }
          let ?checkAllocSymInit = allocSymInitCheck
          cc <-
            io $
            do let verbosity = simVerbose opts
               sym <- Common.newSAWCoreExprBuilder sc False
               Common.SomeOnlineBackend bak <-
                 Common.newSAWCoreBackendWithTimeout pathSatSolver sym crucibleTimeout

               let cfg = W4.getConfiguration sym
               verbSetting <- W4.getOptionSetting W4.verbosity cfg
               _ <- W4.setOpt verbSetting (toInteger verbosity)

               cacheTermsSetting <- W4.getOptionSetting W4.cacheTerms cfg
               _ <- W4.setOpt cacheTermsSetting what4HashConsing

               pushMuxOpsSetting <- W4.getOptionSetting W4.pushMuxOpsOption cfg
               _ <- W4.setOpt pushMuxOpsSetting what4PushMuxOps

               -- enable online solver interactions if path sat checking is on
               enableOnlineSetting <- W4.getOptionSetting Crucible.enableOnlineBackend cfg
               _ <- W4.setOpt enableOnlineSetting pathSat

               W4.extendConfig
                 [ W4.opt
                     enableSMTArrayMemoryModel
                     (W4.ConcreteBool smt_array_memory_model_enabled)
                     ("Enable SMT array memory model" :: Text.Text)
                 ]
                 cfg

               crucible_assert_then_assume_option_setting <- W4.getOptionSetting
                 Crucible.assertThenAssumeConfigOption
                 cfg
               _ <- W4.setOpt
                 crucible_assert_then_assume_option_setting
                 crucible_assert_then_assume_enabled

               let bindings = Crucible.fnBindingsFromList []
               let simctx   = Crucible.initSimContext bak
                                 intrinsics halloc stdout
                                 bindings (Crucible.llvmExtensionImpl ?memOpts)
                                 Common.SAWCruciblePersonality
               mem <- Crucible.populateConstGlobals bak (view Crucible.globalInitMap mtrans)
                        =<< Crucible.initializeMemoryConstGlobals bak ctx llvm_mod

               let globals  = Crucible.llvmGlobals (Crucible.llvmMemVar ctx) mem

               let setupMem =
                     do -- register all the functions defined in the LLVM module
                        Crucible.registerLazyModule (handleTranslationWarning opts) mtrans
                        -- register the callable override functions
                        _ <- Crucible.register_llvm_overrides llvm_mod saw_llvm_overrides saw_llvm_overrides ctx

                        pure ()

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
                                     , _ccBackend = Common.SomeOnlineBackend bak
                                     , _ccLLVMSimContext = lsimctx
                                     , _ccLLVMGlobals = lglobals
                                     , _ccBasicSS = basic_ss
                                     , _ccUninterp = mempty
                                     }
          action cc


handleTranslationWarning :: Options -> Crucible.LLVMTranslationWarning -> IO ()
handleTranslationWarning opts (Crucible.LLVMTranslationWarning s p msg) =
  printOutLn opts Warn $ unwords
    [ "LLVM bitcode translation warning"
    , show (Crucible.ppSymbol s)
    , show p
    , Text.unpack msg
    ]

--------------------------------------------------------------------------------

saw_llvm_overrides ::
  ( Crucible.IsSymInterface sym, Crucible.HasLLVMAnn sym, Crucible.HasPtrWidth wptr ) =>
  [Crucible.OverrideTemplate p sym ext arch]
saw_llvm_overrides =
  [ Crucible.basic_llvm_override saw_assert_override
  ]

saw_assert_override ::
  ( Crucible.IsSymInterface sym, Crucible.HasLLVMAnn sym, Crucible.HasPtrWidth wptr ) =>
  Crucible.LLVMOverride p sym ext
    (Crucible.EmptyCtx Crucible.::> Crucible.BVType 32)
    Crucible.UnitType
saw_assert_override =
  [llvmOvr| void @saw_assert( i32 ) |]
  (\_memOps (Ctx.Empty Ctx.:> p) ->
     Crucible.ovrWithBackend $ \bak ->
     do let sym = Crucible.backendGetSym bak
        let msg = Crucible.GenericSimError "saw_assert"
        liftIO $
          do loc <- W4.getCurrentProgramLoc sym
             cond <- W4.bvIsNonzero sym (Crucible.regValue p)
             putStrLn $ unlines ["SAW assert!", show loc, show (W4.printSymExpr cond)]
             Crucible.addDurableAssertion bak (Crucible.LabeledPred cond (Crucible.SimError loc msg))
             Crucible.addAssumption bak (Crucible.GenericAssumption loc "crucible_assume" cond)
  )

-- | Create a fresh argument variable of the appropriate type, suitable for use
-- in an extracted function derived from @llvm_extract@.
setupArg ::
  SharedContext ->
  Sym ->
  IORef (Seq TypedVariable) ->
  Crucible.TypeRepr tp ->
  IO (Crucible.RegEntry Sym tp)
setupArg sc sym ecRef tp = do
  (cty, scTp) <-
    case tp of
      Crucible.LLVMPointerRepr w -> do
        let cty = Cryptol.tWord (Cryptol.tNum (natValue w))
        scTp <- scBitvector sc (natValue w)
        pure (cty, scTp)
      _ -> Common.typeReprToSAWTypes sym sc tp

  ecs <- readIORef ecRef
  vn <- scFreshVarName sc ("arg_" <> Text.pack (show (length ecs)))
  writeIORef ecRef (ecs Seq.|> TypedVariable cty vn scTp)

  t <- scVariable sc vn scTp
  elt <-
    case tp of
      Crucible.LLVMPointerRepr w -> do
        st <- Common.sawCoreState sym
        elt <- bindSAWTerm sym st (Crucible.BaseBVRepr w) t
        Crucible.llvmPointer_bv sym elt
      _ -> Common.termToRegValue sym tp t
  pure $ Crucible.RegEntry tp elt

-- | Create fresh argument variables of the appropriate types, suitable for use
-- in an extracted function derived from @llvm_extract@.
setupArgs ::
  SharedContext ->
  Sym ->
  Crucible.FnHandle init ret ->
  IO (Seq TypedVariable, Crucible.RegMap Sym init)
setupArgs sc sym fn =
  do ecRef  <- newIORef Seq.empty
     regmap <- Crucible.RegMap <$> FC.traverseFC (setupArg sc sym ecRef) (Crucible.handleArgTypes fn)
     ecs    <- readIORef ecRef
     return (ecs, regmap)

--------------------------------------------------------------------------------

extractFromLLVMCFG ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  Options -> SharedContext -> LLVMCrucibleContext arch -> Crucible.AnyCFG Crucible.LLVM -> IO TypedTerm
extractFromLLVMCFG opts sc cc (Crucible.AnyCFG cfg) =
  ccWithBackend cc $ \bak ->
  do let sym = Common.backendGetSym bak
     st <- Common.sawCoreState sym
     let h   = Crucible.cfgHandle cfg
     (ecs, args) <- setupArgs sc sym h
     let simCtx  = cc^.ccLLVMSimContext
     let globals = cc^.ccLLVMGlobals
     res <- Common.runCFG simCtx globals h cfg args
     case res of
       Crucible.FinishedResult _ pr ->
         do gp <- Common.getGlobalPair opts pr
            let regv = gp^.Crucible.gpValue
                rt = Crucible.regType regv
                rv = Crucible.regValue regv
            tt <-
              case rt of
                Crucible.LLVMPointerRepr w ->
                  do bv <- Crucible.projectLLVM_bv bak rv
                     t <- toSC sym st bv
                     let cty = Cryptol.tWord (Cryptol.tNum (natValue w))
                     pure $ TypedTerm (TypedTermSchema (Cryptol.tMono cty)) t
                Crucible.BVRepr w ->
                  do t <- toSC sym st rv
                     let cty = Cryptol.tWord (Cryptol.tNum (natValue w))
                     pure $ TypedTerm (TypedTermSchema (Cryptol.tMono cty)) t
                _ -> fail $ unwords ["Unexpected return type:", show rt]
            tt' <- abstractTypedVars sc (toList ecs) tt
            pure tt'
       Crucible.AbortedResult _ ar ->
         do let resultDoc = ppAbortedResult cc ar
            fail $ unlines [ "Symbolic execution failed."
                           , show resultDoc
                           ]

       Crucible.TimeoutResult _ ->
         fail "Symbolic execution timed out."

--------------------------------------------------------------------------------

llvm_extract ::
  Some LLVMModule ->
  Text ->
  TopLevel TypedTerm
llvm_extract (Some lm) fn_name =
  do let ctx = modTrans lm ^. Crucible.transContext
     let ?lc = ctx^.Crucible.llvmTypeCtx
     let edef = findDefMaybeStatic (modAST lm) fn_name
     sc <- getSharedContext
     opts <- getOptions
     case edef of
       Right defs ->
         do let defTypes =
                  fold $
                  NE.map (map L.typedType . L.defArgs) defs <>
                  NE.map (\d -> [L.defRetType d]) defs
            when (any L.isPointer defTypes) $
              throwTopLevel "Pointer types are not supported by `llvm_extract`."
            when (any L.isAlias defTypes) $
              throwTopLevel "Type aliases are not supported by `llvm_extract`."
       Left err -> throwTopLevel (displayVerifExceptionOpts opts err)
     setupLLVMCrucibleContext False lm $ \cc ->
       io (Crucible.getTranslatedCFG (ccLLVMModuleTrans cc) (fromString $ Text.unpack fn_name)) >>= \case
         Nothing  -> throwTopLevel $ Text.unpack $ "function " <> fn_name <> "not found"
         Just (_,cfg,warns) ->
           do io $ mapM_ (handleTranslationWarning opts) warns
              io $ extractFromLLVMCFG opts sc cc cfg

llvm_cfg ::
  Some LLVMModule ->
  Text ->
  TopLevel SAW_CFG
llvm_cfg (Some lm) fn_name =
  do let ctx = modTrans lm ^. Crucible.transContext
     let ?lc = ctx^.Crucible.llvmTypeCtx
     opts <- getOptions
     setupLLVMCrucibleContext False lm $ \cc ->
       io (Crucible.getTranslatedCFG (ccLLVMModuleTrans cc) (fromString $ Text.unpack fn_name)) >>= \case
         Nothing  -> throwTopLevel $ Text.unpack $ "function " <> fn_name <> " not found"
         Just (_,cfg,warns) ->
           do io $ mapM_ (handleTranslationWarning opts) warns
              return (LLVM_CFG cfg)

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

llvm_assert :: TypedTerm -> LLVMCrucibleSetupM ()
llvm_assert term =
  LLVMCrucibleSetupM $
  do loc <- getW4Position "llvm_assert"
     tags <- view Setup.croTags
     let md = MS.ConditionMetadata
              { MS.conditionLoc = loc
              , MS.conditionTags = tags
              , MS.conditionType = "specification assertion"
              , MS.conditionContext = ""
              }
     Setup.addCondition (MS.SetupCond_Pred md term)

llvm_precond :: TypedTerm -> LLVMCrucibleSetupM ()
llvm_precond term =
  LLVMCrucibleSetupM $
  do loc <- getW4Position "llvm_precond"
     Setup.crucible_precond loc term

llvm_postcond :: TypedTerm -> LLVMCrucibleSetupM ()
llvm_postcond term =
  LLVMCrucibleSetupM $
  do loc <- getW4Position "llvm_postcond"
     Setup.crucible_postcond loc term

llvm_unint :: [Text] -> LLVMCrucibleSetupM ()
llvm_unint term =
  LLVMCrucibleSetupM (Setup.declare_unint "llvm_unint" ccUninterp term)
          

llvm_return ::
  AllLLVM MS.SetupValue ->
  LLVMCrucibleSetupM ()
llvm_return val =
  LLVMCrucibleSetupM $
  do Setup.crucible_return (getAllLLVM val)

llvm_execute_func ::
  [AllLLVM MS.SetupValue] ->
  LLVMCrucibleSetupM ()
llvm_execute_func args =
  LLVMCrucibleSetupM $ Setup.crucible_execute_func (map (\a -> getAllLLVM a) args)

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
      return cryptolPtrType
    Crucible.PtrOpaqueType ->
      return cryptolPtrType
    Crucible.StructType si ->
      do let memtypes = V.toList (Crucible.siFieldTypes si)
         ctys <- traverse (cryptolTypeOfActual dl) memtypes
         case ctys of
           [cty] -> return cty
           _ -> return $ Cryptol.tTuple ctys
    Crucible.X86_FP80Type ->
      Nothing
    Crucible.VecType{} ->
      Nothing
    Crucible.MetadataType ->
      Nothing
  where
    cryptolPtrType :: Cryptol.Type
    cryptolPtrType = Cryptol.tWord (Cryptol.tNum (Crucible.ptrBitwidth dl))

-- | Generate a fresh variable term. The name will be used when
-- pretty-printing the variable in debug output.
llvm_fresh_var ::
  Text                    {- ^ variable name    -} ->
  L.Type                  {- ^ variable type    -} ->
  LLVMCrucibleSetupM TypedTerm {- ^ fresh typed term -}
llvm_fresh_var name lty =
  LLVMCrucibleSetupM $
  do cctx <- getLLVMCrucibleContext
     let ?lc = ccTypeCtx cctx
     loc <- getW4Position "llvm_fresh_var"
     lty' <- memTypeForLLVMType loc lty
     sc <- lift $ lift getSharedContext
     let dl = Crucible.llvmDataLayout (ccTypeCtx cctx)
     case cryptolTypeOfActual dl lty' of
       Nothing -> throwCrucibleSetup loc $ "Unsupported type in llvm_fresh_var: " ++ show (Crucible.ppType lty)
       Just cty -> Setup.freshVariable sc name cty

llvm_fresh_cryptol_var ::
  Text ->
  Cryptol.Schema ->
  LLVMCrucibleSetupM TypedTerm
llvm_fresh_cryptol_var name s =
  LLVMCrucibleSetupM $
  do loc <- getW4Position "llvm_fresh_var"
     case s of
       Cryptol.Forall [] [] ty ->
         do sc <- lift $ lift getSharedContext
            Setup.freshVariable sc name ty
       _ ->
         throwCrucibleSetup loc $ "Unsupported polymorphic Cryptol type schema: " ++ show s

-- | Use the given LLVM type to compute a setup value that
-- covers expands all of the struct, array, and pointer
-- components of the LLVM type. Only the primitive types
-- suitable for import as SAW core terms will be matched
-- against fresh variables.
llvm_fresh_expanded_val ::
  L.Type         {- ^ variable type          -} ->
  LLVMCrucibleSetupM (AllLLVM SetupValue)
                 {- ^ elaborated setup value -}
llvm_fresh_expanded_val lty =
  LLVMCrucibleSetupM $
  do sc <- lift $ lift getSharedContext
     cctx <- getLLVMCrucibleContext
     let ?lc = ccTypeCtx cctx
     loc <- getW4Position "llvm_fresh_expanded_val"
     lty' <- memTypeForLLVMType loc lty
     constructExpandedSetupValue cctx sc loc lty'

-- | See 'llvm_fresh_expanded_val'
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
      pure $ mkAllLLVM $ SetupStruct False $ map (\a -> getAllLLVM a) fields

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
      pure $ mkAllLLVM $ SetupArray () $ map (\a -> getAllLLVM a) elements_

    Crucible.FloatType      -> failUnsupportedType "Float"
    Crucible.DoubleType     -> failUnsupportedType "Double"
    Crucible.MetadataType   -> failUnsupportedType "Metadata"
    Crucible.VecType{}      -> failUnsupportedType "Vec"
    Crucible.X86_FP80Type{} -> failUnsupportedType "X86_FP80"
    -- See https://github.com/GaloisInc/saw-script/issues/1879 for why it is
    -- tricky to support opaque pointers here.
    Crucible.PtrOpaqueType  ->
      panic "constructExpandedSetupValue" [
          "llvm_fresh_expanded_val does not support opaque pointers",
          "Please report this at: https://github.com/GaloisInc/saw-script/issues/1879"
      ]
  where failUnsupportedType tyName = throwCrucibleSetup loc $ unwords
          ["llvm_fresh_expanded_var: " ++ tyName ++ " not supported"]


memTypeForLLVMType ::
  (?lc :: Crucible.TypeContext) =>
  W4.ProgramLoc ->
  L.Type ->
  CrucibleSetup arch Crucible.MemType
memTypeForLLVMType loc lty =
  case Crucible.liftMemType lty of
    Right m -> return m
    Left err -> throwCrucibleSetup loc $ unlines
      [ "unsupported type: " ++ show (Crucible.ppType lty)
      , "Details:"
      , err
      ]

llvm_sizeof ::
  Some LLVMModule ->
  L.Type ->
  TopLevel Integer
llvm_sizeof (Some lm) lty =
  do let mtrans = modTrans lm
     let ?lc = mtrans ^. Crucible.transContext . Crucible.llvmTypeCtx
     let dl = Crucible.llvmDataLayout ?lc
     case Crucible.liftMemType lty of
       Right mty -> pure (Crucible.bytesToInteger (Crucible.memTypeSize dl mty))
       Left err -> fail $ unlines
         [ "llvm_sizeof: Unsupported type: " ++ show (Crucible.ppType lty)
         , "Details:"
         , err
         ]

llvmTypeAlias :: L.Type -> Maybe Crucible.Ident
llvmTypeAlias (L.Alias i) = Just i
llvmTypeAlias _ = Nothing

symTypeAlias :: Crucible.SymType -> Maybe Crucible.Ident
symTypeAlias (Crucible.Alias i) = Just i
symTypeAlias _ = Nothing

-- | Does the hard work for 'llvm_alloc', 'llvm_alloc_with_size',
--   'llvm_alloc_readonly', etc.
llvm_alloc_internal ::
  L.Type  ->
  LLVMAllocSpec  ->
  CrucibleSetup (LLVM arch) (AllLLVM SetupValue)
llvm_alloc_internal lty spec =
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

llvm_alloc_with_mutability_and_size ::
  Crucible.Mutability    ->
  Maybe (Crucible.Bytes) ->
  Maybe Crucible.Alignment ->
  LLVMAllocSpecInit ->
  L.Type           ->
  LLVMCrucibleSetupM (AllLLVM SetupValue)
llvm_alloc_with_mutability_and_size mut sz alignment initialization lty =
  LLVMCrucibleSetupM $
  do cctx <- getLLVMCrucibleContext
     loc <- getW4Position "llvm_alloc"
     memTy <- memTypeForLLVMType loc lty
     opts <- lift $ lift getOptions

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
         Nothing -> pure $! memTyAlign

     tags <- view Setup.croTags
     let md = MS.ConditionMetadata
              { MS.conditionLoc = loc
              , MS.conditionTags = tags
              , MS.conditionType = "fresh allocation"
              , MS.conditionContext = ""
              }
     llvm_alloc_internal lty $
       LLVMAllocSpec
       { _allocSpecMut = mut
       , _allocSpecType = memTy
       , _allocSpecAlign = alignment'
       , _allocSpecBytes = sz''
       , _allocSpecMd = md
       , _allocSpecFresh = False
       , _allocSpecInit = initialization
       }

llvm_alloc ::
  L.Type         ->
  LLVMCrucibleSetupM (AllLLVM SetupValue)
llvm_alloc =
  llvm_alloc_with_mutability_and_size Crucible.Mutable Nothing Nothing LLVMAllocSpecNoInitialization

llvm_alloc_aligned ::
  Int            ->
  L.Type         ->
  LLVMCrucibleSetupM (AllLLVM SetupValue)
llvm_alloc_aligned =
  llvm_alloc_aligned_with_mutability Crucible.Mutable

llvm_alloc_readonly ::
  L.Type         ->
  LLVMCrucibleSetupM (AllLLVM SetupValue)
llvm_alloc_readonly =
  llvm_alloc_with_mutability_and_size Crucible.Immutable Nothing Nothing LLVMAllocSpecNoInitialization

llvm_alloc_readonly_aligned ::
  Int            ->
  L.Type         ->
  LLVMCrucibleSetupM (AllLLVM SetupValue)
llvm_alloc_readonly_aligned =
  llvm_alloc_aligned_with_mutability Crucible.Immutable

llvm_alloc_aligned_with_mutability ::
  Crucible.Mutability ->
  Int ->
  L.Type ->
  LLVMCrucibleSetupM (AllLLVM SetupValue)
llvm_alloc_aligned_with_mutability mut n lty =
  do alignment <- LLVMCrucibleSetupM $ coerceAlignment n
     llvm_alloc_with_mutability_and_size
       mut
       Nothing
       (Just alignment)
       LLVMAllocSpecNoInitialization
       lty

coerceAlignment :: Int -> CrucibleSetup (LLVM arch) Crucible.Alignment
coerceAlignment n =
  case Crucible.toAlignment (Crucible.toBytes n) of
    Nothing ->
      do loc <- getW4Position "llvm_alloc_aligned_with_mutability"
         throwCrucibleSetup loc $ unwords
           [ "llvm_alloc_aligned/llvm_alloc_readonly_aligned:"
           , "invalid non-power-of-2 alignment:"
           , show n
           ]
    Just alignment -> return alignment

llvm_alloc_with_size ::
  Int {-^ allocation size (in bytes) -} ->
  L.Type         ->
  LLVMCrucibleSetupM (AllLLVM SetupValue)
llvm_alloc_with_size sz lty =
  llvm_alloc_with_mutability_and_size
    Crucible.Mutable
    (Just (Crucible.toBytes sz))
    Nothing
    LLVMAllocSpecNoInitialization
    lty

llvm_alloc_sym_init :: L.Type -> LLVMCrucibleSetupM (AllLLVM SetupValue)
llvm_alloc_sym_init =
  llvm_alloc_with_mutability_and_size Crucible.Mutable Nothing Nothing LLVMAllocSpecSymbolicInitialization

llvm_symbolic_alloc ::
  Bool ->
  Int ->
  Term ->
  LLVMCrucibleSetupM (AllLLVM SetupValue)
llvm_symbolic_alloc ro align_bytes sz =
  LLVMCrucibleSetupM $
  do alignment <- coerceAlignment align_bytes
     loc <- getW4Position "llvm_symbolic_alloc"
     sc <- lift $ lift getSharedContext
     sz_ty <- liftIO $ Cryptol.scCryptolType sc =<< scTypeOf sc sz
     case sz_ty of
       Just (Right tp)
         | Just 64 == asCryptolBVType tp -> return ()
         | otherwise -> throwCrucibleSetup loc $ unwords
              [ "llvm_symbolic_alloc:"
              , "unexpected type of size term, expected [64], found"
              , Cryptol.pretty tp
              ]
       _ -> throwCrucibleSetup loc $ unwords
              [ "llvm_symbolic_alloc:"
              , "unexpected term, expected term of type [64], but got"
              , showTerm sz
              ]

     tags <- view Setup.croTags
     let md = MS.ConditionMetadata
              { MS.conditionLoc = loc
              , MS.conditionTags = tags
              , MS.conditionType = "fresh symbolic allocation"
              , MS.conditionContext = ""
              }
     let spec = LLVMAllocSpec
           { _allocSpecMut = if ro then Crucible.Immutable else Crucible.Mutable
           , _allocSpecType = Crucible.i8p
           , _allocSpecAlign = alignment
           , _allocSpecBytes = sz
           , _allocSpecMd = md
           , _allocSpecFresh = False
           , _allocSpecInit = LLVMAllocSpecNoInitialization
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

llvm_alloc_global ::
  Text ->
  LLVMCrucibleSetupM ()
llvm_alloc_global name =
  LLVMCrucibleSetupM $
  do loc <- getW4Position "llvm_alloc_global"
     Setup.addAllocGlobal . LLVMAllocGlobal loc $ L.Symbol (Text.unpack name)

llvm_fresh_pointer ::
  L.Type         ->
  LLVMCrucibleSetupM (AllLLVM SetupValue)
llvm_fresh_pointer lty =
  LLVMCrucibleSetupM $
  do loc <- getW4Position "llvm_fresh_pointer"
     memTy <- memTypeForLLVMType loc lty
     constructFreshPointer (llvmTypeAlias lty) loc memTy

llvm_cast_pointer :: AllLLVM SetupValue -> L.Type -> AllLLVM SetupValue
llvm_cast_pointer ptr lty = mkAllLLVM (SetupCast lty (getAllLLVM ptr))

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
     tags <- view Setup.croTags
     let md = MS.ConditionMetadata
              { MS.conditionLoc = loc
              , MS.conditionTags = tags
              , MS.conditionType = "fresh pointer"
              , MS.conditionContext = ""
              }
     Setup.currentState . MS.csAllocs . at n ?=
       LLVMAllocSpec { _allocSpecMut = Crucible.Mutable
                     , _allocSpecType = memTy
                     , _allocSpecAlign = alignment
                     , _allocSpecBytes = sz
                     , _allocSpecMd = md
                     , _allocSpecFresh = True
                     , _allocSpecInit = LLVMAllocSpecNoInitialization
                     }
     -- TODO: refactor
     case mid of
       Just i -> Setup.currentState . MS.csVarTypeNames.at n ?= i
       Nothing -> return ()
     return (mkAllLLVM (SetupVar n))

llvm_points_to ::
  Bool {- ^ whether to check type compatibility -} ->
  AllLLVM SetupValue     ->
  AllLLVM SetupValue     ->
  LLVMCrucibleSetupM ()
llvm_points_to typed =
  llvm_points_to_internal (shouldCheckAgainstPointerType typed) Nothing

llvm_conditional_points_to ::
  Bool {- ^ whether to check type compatibility -} ->
  TypedTerm ->
  AllLLVM SetupValue ->
  AllLLVM SetupValue ->
  LLVMCrucibleSetupM ()
llvm_conditional_points_to typed cond =
  llvm_points_to_internal (shouldCheckAgainstPointerType typed) (Just cond)

llvm_points_to_at_type ::
  AllLLVM SetupValue ->
  L.Type             ->
  AllLLVM SetupValue ->
  LLVMCrucibleSetupM ()
llvm_points_to_at_type ptr ty val =
  llvm_points_to_internal (Just (Setup.CheckAgainstCastedType ty)) Nothing ptr val

llvm_conditional_points_to_at_type ::
  TypedTerm ->
  AllLLVM SetupValue ->
  L.Type             ->
  AllLLVM SetupValue ->
  LLVMCrucibleSetupM ()
llvm_conditional_points_to_at_type cond ptr ty val =
  llvm_points_to_internal (Just (Setup.CheckAgainstCastedType ty)) (Just cond) ptr val

-- | If the argument is @True@, check the type of the RHS value against the
-- type that the LHS points to (i.e., @'Just' 'CheckAgainstPointerType'@).
-- Otherwise, don't check the type of the RHS value at all (i.e., 'Nothing').
shouldCheckAgainstPointerType :: Bool -> Maybe (Setup.CheckPointsToType ty)
shouldCheckAgainstPointerType b = if b then Just Setup.CheckAgainstPointerType else Nothing

llvm_points_to_internal ::
  Maybe (Setup.CheckPointsToType L.Type)
  {- ^ If 'Just', check the type of the RHS value.
       If 'Nothing', don't check the type of the RHS value at all. -} ->
  Maybe TypedTerm ->
  AllLLVM SetupValue {- ^ lhs pointer -} ->
  AllLLVM SetupValue {- ^ rhs value -} ->
  LLVMCrucibleSetupM ()
llvm_points_to_internal mbCheckType cond (getAllLLVM -> ptr) (getAllLLVM -> val) =
  LLVMCrucibleSetupM $
  do cc <- getLLVMCrucibleContext
     loc <- getW4Position "llvm_points_to"
     Crucible.llvmPtrWidth (ccLLVMContext cc) $ \wptr -> Crucible.withPtrWidth wptr $
       do st <- lift get
          let env = MS.csAllocations (st ^. Setup.csMethodSpec)
              nameEnv = MS.csTypeNames (st ^. Setup.csMethodSpec)

          let path = []
          lhsTy <- llvm_points_to_check_lhs_validity ptr loc path

          valTy <- exceptToFail $ typeOfSetupValue cc env nameEnv val
          case mbCheckType of
            Nothing                                -> pure ()
            Just Setup.CheckAgainstPointerType     -> checkMemTypeCompatibility loc lhsTy valTy
            Just (Setup.CheckAgainstCastedType ty) -> do
              ty' <- memTypeForLLVMType loc ty
              checkMemTypeCompatibility loc ty' valTy

          tags <- view Setup.croTags
          let md = MS.ConditionMetadata
                   { MS.conditionLoc = loc
                   , MS.conditionTags = tags
                   , MS.conditionType = "LLVM points-to"
                   , MS.conditionContext = ""
                   }
          Setup.addPointsTo (LLVMPointsTo md cond ptr $ ConcreteSizeValue val)

-- | Like 'llvm_points_to_internal', but specifically geared towards the needs
-- of fields within bitfields. In particular, rather than checking
-- 'Crucible.MemType' compatibility against the type that that LHS points to,
-- which corresponds to the overall bitfield type, this checks compatibility
-- against the type of the field /within/ the bitfield, which is often a
-- smaller type.
llvm_points_to_bitfield ::
  AllLLVM SetupValue {- ^ lhs pointer -} ->
  Text               {- ^ name of field in bitfield -} ->
  AllLLVM SetupValue {- ^ rhs value -} ->
  LLVMCrucibleSetupM ()
llvm_points_to_bitfield (getAllLLVM -> ptr) fieldName (getAllLLVM -> val) =
  LLVMCrucibleSetupM $
  do cc <- getLLVMCrucibleContext
     loc <- getW4Position "llvm_points_to_bitfield"
     Crucible.llvmPtrWidth (ccLLVMContext cc) $ \wptr -> Crucible.withPtrWidth wptr $
       do let fieldName' = Text.unpack fieldName
          st <- get
          let env = MS.csAllocations (st ^. Setup.csMethodSpec)
              nameEnv = MS.csTypeNames (st ^. Setup.csMethodSpec)

          -- NB: Don't use [] for the path here. It's perfectly acceptable to
          -- have multiple llvm_points_to_bitfield statements on the same
          -- pointer provided that the field names are different, so we use
          -- the field name as the path.
          let path = [ResolvedField fieldName]
          _ <- llvm_points_to_check_lhs_validity ptr loc path

          bfIndex <- exceptToFail $ resolveSetupBitfield cc env nameEnv ptr fieldName'
          let lhsFieldTy = Crucible.IntType $ fromIntegral $ biFieldSize bfIndex
          valTy <- exceptToFail $ typeOfSetupValue cc env nameEnv val
          -- Currently, we require the type of the RHS value to precisely match
          -- the type of the field within the bitfield. One could imagine
          -- having finer-grained control over this (e.g.,
          -- llvm_points_to_bitfield_at_type or llvm_points_to_bitfield_untyped),
          -- but no one has asked for this yet.
          checkMemTypeCompatibility loc lhsFieldTy valTy

          tags <- view Setup.croTags
          let md = MS.ConditionMetadata
                   { MS.conditionLoc = loc
                   , MS.conditionTags = tags
                   , MS.conditionType = "LLVM points-to (bitfield)"
                   , MS.conditionContext = ""
                   }
          Setup.addPointsTo (LLVMPointsToBitfield md ptr fieldName' val)

-- | Perform a set of validity checks that are shared in common between
-- 'llvm_points_to_internal' and 'llvm_points_to_bitfield':
--
-- * Check that there are no dupplicate points-to preconditions on the LHS
--   pointer with the supplied path.
--
-- * Check that the LHS is in fact a valid pointer type.
--
-- Returns the 'Crucible.MemType' that the LHS points to.
llvm_points_to_check_lhs_validity ::
  SetupValue (LLVM arch) {- ^ lhs pointer -} ->
  W4.ProgramLoc {- ^ the location in the program -} ->
  ResolvedPath {- ^ the path from the pointer to the pointee -} ->
  Setup.CrucibleSetupT (LLVM arch) TopLevel Crucible.MemType
llvm_points_to_check_lhs_validity ptr loc path =
  do cc <- getLLVMCrucibleContext
     let ?lc = ccTypeCtx cc
     st <- get
     let rs = st ^. Setup.csResolvedState
     if st ^. Setup.csPrePost == PreState && testResolved ptr path rs
       then throwCrucibleSetup loc "Multiple points-to preconditions on same pointer"
       else Setup.csResolvedState %= markResolved ptr path
     let env = MS.csAllocations (st ^. Setup.csMethodSpec)
         nameEnv = MS.csTypeNames (st ^. Setup.csMethodSpec)
     ptrTy <- exceptToFail $ typeOfSetupValue cc env nameEnv ptr
     case ptrTy of
       Crucible.PtrType symTy ->
         case Crucible.asMemType symTy of
           Right lhsTy -> return lhsTy
           Left err -> throwCrucibleSetup loc $ unlines
             [ "lhs not a valid pointer type: " ++ show ptrTy
             , "Details:"
             , err
             ]

       _ -> throwCrucibleSetup loc $ "lhs not a pointer type: " ++ show ptrTy

llvm_setup_with_tag ::
  Text ->
  LLVMCrucibleSetupM () ->
  LLVMCrucibleSetupM ()
llvm_setup_with_tag tag m =
  LLVMCrucibleSetupM (Setup.setupWithTag tag (runLLVMCrucibleSetupM m))

llvm_points_to_array_prefix ::
  AllLLVM SetupValue ->
  TypedTerm ->
  TypedTerm ->
  LLVMCrucibleSetupM ()
llvm_points_to_array_prefix (getAllLLVM -> ptr) arr sz =
  LLVMCrucibleSetupM $
  do cc <- getLLVMCrucibleContext
     loc <- getW4Position "llvm_points_to_array_prefix"
     case ttType sz of
       TypedTermSchema (Cryptol.Forall [] [] ty)
         | Just 64 == asCryptolBVType ty ->
           return ()
         | otherwise ->
           throwCrucibleSetup loc $ unwords
              [ "llvm_points_to_array_prefix:"
              , "unexpected type of size term, expected [64], found"
              , Cryptol.pretty ty
              ]
       _ -> throwCrucibleSetup loc $ unwords
              [ "llvm_points_to_array_prefix:"
              , "unexpected size term, expected term of type [64], but got"
              , showTerm (ttTerm sz)
              ]

     Crucible.llvmPtrWidth (ccLLVMContext cc) $ \wptr -> Crucible.withPtrWidth wptr $
       do let ?lc = ccTypeCtx cc
          st <- get
          let rs = st ^. Setup.csResolvedState
          if st ^. Setup.csPrePost == PreState && testResolved ptr [] rs
            then throwCrucibleSetup loc "Multiple points-to preconditions on same pointer"
            else Setup.csResolvedState %= markResolved ptr []
          let env = MS.csAllocations (st ^. Setup.csMethodSpec)
              nameEnv = MS.csTypeNames (st ^. Setup.csMethodSpec)
          ptrTy <- exceptToFail $ typeOfSetupValue cc env nameEnv ptr
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
          tags <- view Setup.croTags
          let md = MS.ConditionMetadata
                   { MS.conditionLoc = loc
                   , MS.conditionTags = tags
                   , MS.conditionType = "LLVM points-to (array prefix)"
                   , MS.conditionContext = ""
                   }
          Setup.addPointsTo (LLVMPointsTo md Nothing ptr $ SymbolicSizeValue arr sz)

llvm_equal ::
  AllLLVM SetupValue ->
  AllLLVM SetupValue ->
  LLVMCrucibleSetupM ()
llvm_equal (getAllLLVM -> val1) (getAllLLVM -> val2) =
  LLVMCrucibleSetupM $
  do cc <- getLLVMCrucibleContext
     loc <- getW4Position "llvm_equal"
     st <- get
     let env = MS.csAllocations (st ^. Setup.csMethodSpec)
         nameEnv = MS.csTypeNames (st ^. Setup.csMethodSpec)
     ty1 <- exceptToFail $ typeOfSetupValue cc env nameEnv val1
     ty2 <- exceptToFail $ typeOfSetupValue cc env nameEnv val2

     b <- liftIO $ checkRegisterCompatibility ty1 ty2
     unless b $ throwCrucibleSetup loc $ unlines
       [ "Incompatible types when asserting equality:"
       , show ty1
       , show ty2
       ]
     Setup.crucible_equal loc val1 val2

llvm_ghost_value ::
  MS.GhostGlobal ->
  TypedTerm ->
  LLVMCrucibleSetupM ()
llvm_ghost_value ghost val = LLVMCrucibleSetupM $
  ghost_value ghost val

llvm_spec_solvers :: SomeLLVM MS.ProvedSpec -> [Text]
llvm_spec_solvers (SomeLLVM ps) =
  Set.toList $ solverStatsSolvers $ view MS.psSolverStats $ ps

llvm_spec_size :: SomeLLVM MS.ProvedSpec -> Integer
llvm_spec_size (SomeLLVM mir) =
  solverStatsGoalSize $ mir ^. MS.psSolverStats

crucible_setup_val_to_typed_term ::
  AllLLVM SetupValue ->
  TopLevel TypedTerm
crucible_setup_val_to_typed_term (getAllLLVM -> sval) =
  do opts <- getOptions
     sc <- getSharedContext
     mtt <- io $ MaybeT.runMaybeT $ MS.setupToTypedTerm opts sc sval
     case mtt of
       Nothing -> throwTopLevel $ "Could not convert a setup value to a term: " ++ show sval
       Just tt -> return tt
