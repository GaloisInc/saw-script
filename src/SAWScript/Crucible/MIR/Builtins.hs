{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Implementations of Crucible-related SAWScript primitives for MIR.
module SAWScript.Crucible.MIR.Builtins
  ( -- * Commands
    -- ** Setup
    mir_alloc
  , mir_alloc_mut
  , mir_assert
  , mir_execute_func
  , mir_find_adt
  , mir_fresh_var
  , mir_load_module
  , mir_points_to
  , mir_postcond
  , mir_precond
  , mir_return
  , mir_verify
    -- ** MIR types
  , mir_adt
  , mir_array
  , mir_bool
  , mir_char
  , mir_i8
  , mir_i16
  , mir_i32
  , mir_i64
  , mir_i128
  , mir_isize
  , mir_f32
  , mir_f64
  , mir_ref
  , mir_ref_mut
  , mir_slice
  , mir_str
  , mir_tuple
  , mir_u8
  , mir_u16
  , mir_u32
  , mir_u64
  , mir_u128
  , mir_usize
  ) where

import Control.Lens
import Control.Monad (foldM, forM, forM_, unless, when)
import qualified Control.Monad.Catch as X
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (runReaderT)
import Control.Monad.State (MonadState(..), StateT(..), execStateT, gets)
import Control.Monad.Trans.Class (MonadTrans(..))
import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Foldable as F
import Data.Foldable (for_)
import Data.IORef
import qualified Data.List.Extra as List (find, groupOn)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.NatRepr (knownNat, natValue)
import Data.Parameterized.Some (Some(..))
import qualified Data.Set as Set
import qualified Data.Text as Text
import Data.Text (Text)
import Data.Time.Clock (diffUTCTime, getCurrentTime)
import Data.Type.Equality (TestEquality(..))
import Data.Void (absurd)
import qualified Prettyprinter as PP
import System.IO (stdout)

import qualified Cryptol.TypeCheck.Type as Cryptol

import qualified Lang.Crucible.Analysis.Postdom as Crucible
import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.CFG.Core as Crucible
import qualified Lang.Crucible.FunctionHandle as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Simulator.SimError as Crucible

import qualified Mir.DefId as Mir
import qualified Mir.Mir as Mir
import qualified Mir.Generator as Mir
import Mir.Intrinsics (MIR)
import qualified Mir.Intrinsics as Mir
import qualified Mir.ParseTranslate as Mir
import qualified Mir.Trans as Mir
import Mir.TransCustom (customOps)
import qualified Mir.TransTy as Mir

import qualified What4.Config as W4
import qualified What4.Interface as W4
import qualified What4.ProgramLoc as W4

import Verifier.SAW.FiniteValue (ppFirstOrderValue)
import Verifier.SAW.Name (toShortName)
import Verifier.SAW.SharedTerm
import Verifier.SAW.Simulator.What4.ReturnTrip
import Verifier.SAW.TypedTerm

import SAWScript.Crucible.Common
import qualified SAWScript.Crucible.Common.MethodSpec as MS
import SAWScript.Crucible.Common.Override
import qualified SAWScript.Crucible.Common.Setup.Builtins as Setup
import qualified SAWScript.Crucible.Common.Setup.Type as Setup
import SAWScript.Crucible.MIR.MethodSpecIR
import SAWScript.Crucible.MIR.Override
import SAWScript.Crucible.MIR.ResolveSetupValue
import SAWScript.Crucible.MIR.TypeShape
import SAWScript.Exceptions
import SAWScript.Options
import SAWScript.Panic
import qualified SAWScript.Position as SS
import SAWScript.Proof
import SAWScript.Prover.SolverStats
import SAWScript.Value

type AssumptionReason = (MS.ConditionMetadata, String)
type SetupValue = MS.SetupValue MIR
type Lemma = MS.ProvedSpec MIR
type MethodSpec = MS.CrucibleMethodSpecIR MIR
type SetupCondition = MS.SetupCondition MIR

-- TODO: something useful with the global pair?
ppMIRAbortedResult :: MIRCrucibleContext
                   -> Crucible.AbortedResult Sym a
                   -> PP.Doc ann
ppMIRAbortedResult _cc = ppAbortedResult (\_gp -> mempty)

-----
-- Commands
-----

mir_alloc :: Mir.Ty -> MIRSetupM SetupValue
mir_alloc = mir_alloc_internal Mir.Immut

mir_alloc_mut :: Mir.Ty -> MIRSetupM SetupValue
mir_alloc_mut = mir_alloc_internal Mir.Mut

-- | The workhorse for 'mir_alloc' and 'mir_alloc_mut'.
mir_alloc_internal :: Mir.Mutability -> Mir.Ty -> MIRSetupM SetupValue
mir_alloc_internal mut mty =
  MIRSetupM $
  do st <- get
     let mcc = st ^. Setup.csCrucibleContext
     let col = mcc ^. mccRustModule ^. Mir.rmCS ^. Mir.collection
     Some tpr <- pure $ Mir.tyToRepr col mty
     n <- Setup.csVarCounter <<%= MS.nextAllocIndex
     Setup.currentState . MS.csAllocs . at n ?=
       Some (MirAllocSpec { _maType = tpr
                          , _maMutbl = mut
                          , _maMirType = mty
                          , _maLen = 1
                          })
     return (MS.SetupVar n)

mir_execute_func :: [SetupValue] -> MIRSetupM ()
mir_execute_func args =
  MIRSetupM $
  do st <- get
     let cc = st ^. Setup.csCrucibleContext
     let mspec = st ^. Setup.csMethodSpec
     let env = MS.csAllocations mspec
     let nameEnv = MS.csTypeNames mspec
     let argTys = mspec ^. MS.csArgs
     let
       checkArg i expectedTy val =
         do valTy <- typeOfSetupValue cc env nameEnv val
            unless (checkCompatibleTys expectedTy valTy) $
              X.throwM (MIRArgTypeMismatch i expectedTy valTy)
     let
       checkArgs _ [] [] = pure ()
       checkArgs i [] vals =
         X.throwM (MIRArgNumberWrong i (i + length vals))
       checkArgs i tys [] =
         X.throwM (MIRArgNumberWrong (i + length tys) i)
       checkArgs i (ty : tys) (val : vals) =
         do checkArg i ty val
            checkArgs (i + 1) tys vals
     checkArgs 0 argTys args
     Setup.crucible_execute_func args

-- | Consult the given 'Mir.RustModule' to find an 'Mir.Adt'" with the given
-- 'String' as an identifier and the given 'Mir.Ty's as the types used to
-- instantiate the type parameters. If such a 'Mir.Adt' cannot be found in the
-- 'Mir.RustModule', this will raise an error.
mir_find_adt :: Mir.RustModule -> String -> [Mir.Ty] -> TopLevel Mir.Adt
mir_find_adt rm origName substs = do
  let cs = rm ^. Mir.rmCS
      col = cs ^. Mir.collection
      crateDisambigs = cs ^. Mir.crateHashesMap
  origDid <- findDefId crateDisambigs (Text.pack origName)
  findAdt col origDid (Mir.Substs substs)

-- | Generate a fresh variable term. The name will be used when
-- pretty-printing the variable in debug output.
mir_fresh_var ::
  Text                {- ^ variable name    -} ->
  Mir.Ty              {- ^ variable type    -} ->
  MIRSetupM TypedTerm {- ^ fresh typed term -}
mir_fresh_var name mty =
  MIRSetupM $
  do sc <- lift $ lift getSharedContext
     case cryptolTypeOfActual mty of
       Nothing -> X.throwM $ MIRFreshVarInvalidType mty
       Just cty -> Setup.freshVariable sc name cty

-- | Load a MIR JSON file and return a handle to it.
mir_load_module :: String -> TopLevel Mir.RustModule
mir_load_module inputFile = do
   b <- io $ BSL.readFile inputFile

   opts <- getOptions
   let ?debug = simVerbose opts
   -- For now, we use the same default settings for implicit parameters as in
   -- crux-mir. We may want to add options later that allow configuring these.
   let ?assertFalseOnError = True
   let ?printCrucible = False

   halloc <- getHandleAlloc
   col <- io $ Mir.parseMIR inputFile b
   io $ Mir.translateMIR mempty col halloc

mir_return :: SetupValue -> MIRSetupM ()
mir_return retVal =
  MIRSetupM $
  do st <- get
     let cc = st ^. Setup.csCrucibleContext
     let mspec = st ^. Setup.csMethodSpec
     let env = MS.csAllocations mspec
     let nameEnv = MS.csTypeNames mspec
     valTy <- typeOfSetupValue cc env nameEnv retVal
     case mspec ^. MS.csRet of
       Nothing ->
         X.throwM (MIRReturnUnexpected valTy)
       Just retTy ->
         unless (checkCompatibleTys retTy valTy) $
         X.throwM (MIRReturnTypeMismatch retTy valTy)
     Setup.crucible_return retVal

mir_assert :: TypedTerm -> MIRSetupM ()
mir_assert term = MIRSetupM $ do
  loc <- SS.toW4Loc "mir_assert" <$> lift (lift getPosition)
  tags <- view Setup.croTags
  let md = MS.ConditionMetadata
           { MS.conditionLoc = loc
           , MS.conditionTags = tags
           , MS.conditionType = "specification assertion"
           , MS.conditionContext = ""
           }
  Setup.addCondition (MS.SetupCond_Pred md term)

mir_precond :: TypedTerm -> MIRSetupM ()
mir_precond term = MIRSetupM $ do
  loc <- SS.toW4Loc "mir_precond" <$> lift (lift getPosition)
  Setup.crucible_precond loc term

mir_postcond :: TypedTerm -> MIRSetupM ()
mir_postcond term = MIRSetupM $ do
  loc <- SS.toW4Loc "mir_postcond" <$> lift (lift getPosition)
  Setup.crucible_postcond loc term

mir_points_to ::
  SetupValue {- ^ LHS reference -} ->
  SetupValue {- ^ RHS value -} ->
  MIRSetupM ()
mir_points_to ref val =
  MIRSetupM $
  do cc <- getMIRCrucibleContext
     loc <- getW4Position "mir_points_to"
     st <- lift get
     let env = MS.csAllocations (st ^. Setup.csMethodSpec)
         nameEnv = MS.csTypeNames (st ^. Setup.csMethodSpec)

     allocIdx <-
       case ref of
         MS.SetupVar idx -> pure idx
         _ -> X.throwM $ MIRPointsToNonReference ref

     referentTy <- mir_points_to_check_lhs_validity ref loc
     valTy <- typeOfSetupValue cc env nameEnv val
     unless (checkCompatibleTys referentTy valTy) $
       fail $ unlines
         [ "Referent type incompatible with value in `mir_points_to` statement:"
         , "  Referent type: " ++ show (PP.pretty referentTy)
         , "  Value type:    " ++ show (PP.pretty valTy)
         ]

     tags <- view Setup.croTags
     let md = MS.ConditionMetadata
              { MS.conditionLoc = loc
              , MS.conditionTags = tags
              , MS.conditionType = "MIR points-to"
              , MS.conditionContext = ""
              }
     Setup.addPointsTo (MirPointsTo md allocIdx [val])

-- | Perform a set of validity checks on the LHS reference value in a
-- 'mir_points_to' command. In particular:
--
-- * Check that the LHS is in fact a valid reference type.
--
-- Returns the 'Mir.Ty' that the LHS points to.
mir_points_to_check_lhs_validity ::
  SetupValue {- ^ LHS reference -} ->
  W4.ProgramLoc {- ^ The location in the program -} ->
  Setup.CrucibleSetupT MIR TopLevel Mir.Ty
mir_points_to_check_lhs_validity ref loc =
  do cc <- getMIRCrucibleContext
     st <- get
     let env = MS.csAllocations (st ^. Setup.csMethodSpec)
         nameEnv = MS.csTypeNames (st ^. Setup.csMethodSpec)
     refTy <- typeOfSetupValue cc env nameEnv ref
     case refTy of
       Mir.TyRef referentTy _ -> pure referentTy
       _ -> throwCrucibleSetup loc $ "lhs not a reference type: " ++ show refTy

mir_verify ::
  Mir.RustModule ->
  String {- ^ method name -} ->
  [Lemma] {- ^ overrides -} ->
  Bool {- ^ path sat checking -} ->
  MIRSetupM () ->
  ProofScript () ->
  TopLevel Lemma
mir_verify rm nm lemmas checkSat setup tactic =
  do start <- io getCurrentTime
     opts <- getOptions

     -- set up the metadata map for tracking proof obligation metadata
     mdMap <- io $ newIORef mempty

     cc <- setupCrucibleContext rm
     SomeOnlineBackend bak <- pure (cc^.mccBackend)
     let sym = cc^.mccSym

     pos <- getPosition
     let loc = SS.toW4Loc "_SAW_verify_prestate" pos

     profFile <- rwProfilingFile <$> getTopLevelRW
     (writeFinalProfile, pfs) <- io $ setupProfiling sym "mir_verify" profFile

     let cs = rm ^. Mir.rmCS
         col = cs ^. Mir.collection
         crateDisambigs = cs ^. Mir.crateHashesMap
     did <- findDefId crateDisambigs (Text.pack nm)
     fn <- case Map.lookup did (col ^. Mir.functions) of
         Just x -> return x
         Nothing -> fail $ "Couldn't find MIR function named: " ++ nm
     let st0 = initialCrucibleSetupState cc fn loc

     -- execute commands of the method spec
     io $ W4.setCurrentProgramLoc sym loc
     methodSpec <- view Setup.csMethodSpec <$>
                     execStateT
                       (runReaderT (runMIRSetupM setup) Setup.makeCrucibleSetupRO)
                     st0

     printOutLnTop Info $
       unwords ["Verifying", show (methodSpec ^. MS.csMethod), "..."]

     -- construct the initial state for verifications
     (args, assumes, env, globals1) <- io $ verifyPrestate cc methodSpec Crucible.emptyGlobals

     -- save initial path conditions
     frameIdent <- io $ Crucible.pushAssumptionFrame bak

     -- run the symbolic execution
     printOutLnTop Info $
       unwords ["Simulating", show (methodSpec ^. MS.csMethod), "..."]
     top_loc <- SS.toW4Loc "mir_verify" <$> getPosition
     (ret, globals2) <-
       io $ verifySimulate opts cc pfs methodSpec args assumes top_loc lemmas globals1 checkSat mdMap

     -- collect the proof obligations
     asserts <- verifyPoststate cc
                    methodSpec env globals2 ret mdMap

     -- restore previous assumption state
     _ <- io $ Crucible.popAssumptionFrame bak frameIdent

     -- attempt to verify the proof obligations
     printOutLnTop Info $
       unwords ["Checking proof obligations", show (methodSpec ^. MS.csMethod), "..."]
     (stats,vcstats) <- verifyObligations cc methodSpec tactic assumes asserts
     io $ writeFinalProfile

     let lemmaSet = Set.fromList (map (view MS.psSpecIdent) lemmas)
     end <- io getCurrentTime
     let diff = diffUTCTime end start
     ps <- io (MS.mkProvedSpec MS.SpecProved methodSpec stats vcstats lemmaSet diff)
     returnProof ps

-----
-- Mir.Types
-----

mir_adt :: Mir.Adt -> Mir.Ty
mir_adt = mirAdtToTy

mir_array :: Int -> Mir.Ty -> Mir.Ty
mir_array n t = Mir.TyArray t n

mir_bool :: Mir.Ty
mir_bool = Mir.TyBool

mir_char :: Mir.Ty
mir_char = Mir.TyChar

mir_i8 :: Mir.Ty
mir_i8 = Mir.TyInt Mir.B8

mir_i16 :: Mir.Ty
mir_i16 = Mir.TyInt Mir.B16

mir_i32 :: Mir.Ty
mir_i32 = Mir.TyInt Mir.B32

mir_i64 :: Mir.Ty
mir_i64 = Mir.TyInt Mir.B64

mir_i128 :: Mir.Ty
mir_i128 = Mir.TyInt Mir.B128

mir_isize :: Mir.Ty
mir_isize = Mir.TyInt Mir.USize

mir_f32 :: Mir.Ty
mir_f32 = Mir.TyFloat Mir.F32

mir_f64 :: Mir.Ty
mir_f64 = Mir.TyFloat Mir.F64

mir_ref :: Mir.Ty -> Mir.Ty
mir_ref ty = Mir.TyRef ty Mir.Immut

mir_ref_mut :: Mir.Ty -> Mir.Ty
mir_ref_mut ty = Mir.TyRef ty Mir.Mut

mir_slice :: Mir.Ty -> Mir.Ty
mir_slice = Mir.TySlice

mir_str :: Mir.Ty
mir_str = Mir.TyStr

mir_tuple :: [Mir.Ty] -> Mir.Ty
mir_tuple = Mir.TyTuple

mir_u8 :: Mir.Ty
mir_u8 = Mir.TyUint Mir.B8

mir_u16 :: Mir.Ty
mir_u16 = Mir.TyUint Mir.B16

mir_u32 :: Mir.Ty
mir_u32 = Mir.TyUint Mir.B32

mir_u64 :: Mir.Ty
mir_u64 = Mir.TyUint Mir.B64

mir_u128 :: Mir.Ty
mir_u128 = Mir.TyUint Mir.B128

mir_usize :: Mir.Ty
mir_usize = Mir.TyUint Mir.USize

--------------------------------------------------------------------------------
-- mir_verify
--------------------------------------------------------------------------------

-- | Create a SAWCore formula asserting that two 'MIRVal's are equal.
assertEqualVals ::
  MIRCrucibleContext ->
  MIRVal ->
  MIRVal ->
  IO Term
assertEqualVals cc v1 v2 =
  do let sym = cc^.mccSym
     st <- sawCoreState sym
     toSC sym st =<< equalValsPred cc v1 v2

registerOverride ::
  Options ->
  MIRCrucibleContext ->
  Crucible.SimContext (SAWCruciblePersonality Sym) Sym MIR ->
  W4.ProgramLoc ->
  IORef MetadataMap {- ^ metadata map -} ->
  [MethodSpec] ->
  Crucible.OverrideSim (SAWCruciblePersonality Sym) Sym MIR rtp args ret ()
registerOverride _opts cc _ctx _top_loc _mdMap cs =
  do let c0 = head cs
     let method = c0 ^. MS.csMethod
     let rm = cc^.mccRustModule

     Crucible.AnyCFG cfg <- lookupDefIdCFG rm method
     let h = Crucible.cfgHandle cfg
     let retTy = Crucible.handleReturnType h

     Crucible.bindFnHandle h
       $ Crucible.UseOverride
       $ Crucible.mkOverride'
           (Crucible.handleName h)
           retTy
           (panic "registerOverride.methodSpecHandler" ["not yet implemented"])

resolveArguments ::
  MIRCrucibleContext ->
  MethodSpec ->
  Map MS.AllocIndex (Some (MirPointer Sym)) ->
  IO [(Mir.Ty, MIRVal)]
resolveArguments cc mspec env = mapM resolveArg [0..(nArgs-1)]
  where
    nArgs = toInteger (length (mspec ^. MS.csArgs))
    tyenv = MS.csAllocations mspec
    nameEnv = mspec ^. MS.csPreState . MS.csVarTypeNames
    nm = mspec ^. MS.csMethod

    checkArgTy i mt mt' =
      unless (checkCompatibleTys mt mt') $
           fail $ unlines [ "Type mismatch in argument " ++ show i ++ " when verifying " ++ show nm
                          , "Argument is declared with type: " ++ show mt
                          , "but provided argument has incompatible type: " ++ show mt'
                          , "Note: this may be because the signature of your " ++
                            "function changed during compilation."
                          ]
    resolveArg i =
      case Map.lookup i (mspec ^. MS.csArgBindings) of
        Just (mt, sv) -> do
          mt' <- typeOfSetupValue cc tyenv nameEnv sv
          checkArgTy i mt mt'
          v <- resolveSetupVal cc env tyenv nameEnv sv
          return (mt, v)
        Nothing -> fail $ unwords ["Argument", show i, "unspecified when verifying", show nm]

-- | For each points-to constraint in the pre-state section of the
-- function spec, write the given value to the address of the given
-- pointer.
setupPrePointsTos ::
  MethodSpec ->
  MIRCrucibleContext ->
  Map MS.AllocIndex (Some (MirPointer Sym)) ->
  [MirPointsTo] ->
  Crucible.SymGlobalState Sym ->
  IO (Crucible.SymGlobalState Sym)
setupPrePointsTos mspec cc env pts mem0 = foldM doPointsTo mem0 pts
  where
    tyenv = MS.csAllocations mspec
    nameEnv = mspec ^. MS.csPreState . MS.csVarTypeNames

    doPointsTo ::
         Crucible.SymGlobalState Sym
      -> MirPointsTo
      -> IO (Crucible.SymGlobalState Sym)
    doPointsTo globals (MirPointsTo _ allocIdx referents) =
      mccWithBackend cc $ \bak -> do
        referent <- firstPointsToReferent referents
        MIRVal referentTy referentVal <-
          resolveSetupVal cc env tyenv nameEnv referent
        Some mp <- pure $ lookupAllocIndex env allocIdx
        -- By the time we reach here, we have already checked (in mir_points_to)
        -- that the type of the reference is compatible with the right-hand side
        -- value, so the equality check below should never fail.
        Refl <-
          case W4.testEquality (mp^.mpType) (shapeType referentTy) of
            Just r -> pure r
            Nothing ->
              panic "setupPrePointsTos"
                    [ "Unexpected type mismatch between reference and referent"
                    , "Reference type: " ++ show (mp^.mpType)
                    , "Referent type:  " ++ show (shapeType referentTy)
                    ]
        Mir.writeMirRefIO bak globals Mir.mirIntrinsicTypes (mp^.mpRef) referentVal

-- | Collects boolean terms that should be assumed to be true.
setupPrestateConditions ::
  MethodSpec ->
  MIRCrucibleContext ->
  Map MS.AllocIndex (Some (MirPointer Sym)) ->
  [SetupCondition] ->
  IO [Crucible.LabeledPred Term AssumptionReason]
setupPrestateConditions mspec cc env = aux []
  where
    tyenv   = MS.csAllocations mspec
    nameEnv = mspec ^. MS.csPreState . MS.csVarTypeNames

    aux acc [] = return acc

    aux acc (MS.SetupCond_Equal loc val1 val2 : xs) =
      do val1' <- resolveSetupVal cc env tyenv nameEnv val1
         val2' <- resolveSetupVal cc env tyenv nameEnv val2
         t     <- assertEqualVals cc val1' val2'
         let lp = Crucible.LabeledPred t (loc, "equality precondition")
         aux (lp:acc) xs

    aux acc (MS.SetupCond_Pred loc tm : xs) =
      let lp = Crucible.LabeledPred (ttTerm tm) (loc, "precondition") in
      aux (lp:acc) xs

    aux _ (MS.SetupCond_Ghost empty_ _ _ _ : _) = absurd empty_

verifyObligations ::
  MIRCrucibleContext ->
  MethodSpec ->
  ProofScript () ->
  [Crucible.LabeledPred Term AssumptionReason] ->
  [(String, MS.ConditionMetadata, Term)] ->
  TopLevel (SolverStats, [MS.VCStats])
verifyObligations cc mspec tactic assumes asserts =
  do let sym = cc^.mccSym
     st <- io $ sawCoreState sym
     let sc = saw_ctx st
     assume <- io $ scAndList sc (toListOf (folded . Crucible.labeledPred) assumes)
     let nm = show $ mspec ^. MS.csMethod
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
                 ["MIR verification condition:", Text.pack (show n), Text.pack goalname])
                False -- do not record in the theorem database
                False -- TODO, useSequentGoals...
       case res of
         ValidProof stats thm ->
           return (stats, MS.VCStats md stats (thmSummary thm) (thmNonce thm) (thmDepends thm) (thmElapsedTime thm))
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

     let stats = mconcat (map fst outs)
     let vcstats = map snd outs
     return (stats, vcstats)

verifyPoststate ::
  MIRCrucibleContext                        {- ^ crucible context        -} ->
  MethodSpec                                {- ^ specification           -} ->
  Map MS.AllocIndex (Some (MirPointer Sym)) {- ^ allocation substitution -} ->
  Crucible.SymGlobalState Sym               {- ^ global variables        -} ->
  Maybe (Mir.Ty, MIRVal)                    {- ^ optional return value   -} ->
  IORef MetadataMap                         {- ^ metadata map            -} ->
  TopLevel [(String, MS.ConditionMetadata, Term)] {- ^ generated labels and verification conditions -}
verifyPoststate cc mspec env0 globals ret mdMap =
  mccWithBackend cc $ \bak ->
  do opts <- getOptions
     sc <- getSharedContext
     poststateLoc <- SS.toW4Loc "_SAW_verify_poststate" <$> getPosition
     io $ W4.setCurrentProgramLoc sym poststateLoc

     -- This discards all the obligations generated during
     -- symbolic execution itself, i.e., which are not directly
     -- generated from specification postconditions. This
     -- is, in general, unsound.
     skipSafetyProofs <- gets rwSkipSafetyProofs
     when skipSafetyProofs (io (Crucible.clearProofObligations bak))

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
              learnCond opts sc cc mspec MS.PostState (mspec ^. MS.csPostState)

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
    sym = cc^.mccSym

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
            matchArg opts sc cc mspec MS.PostState md r rty expect
        (Nothing     , Just _ )     -> fail "verifyPoststate: unexpected mir_return specification"
        _ -> return ()

-- | Evaluate the precondition part of a Crucible method spec:
--
-- * Allocate heap space for each 'mir_alloc' statement.
--
-- * Record an equality precondition for each 'mir_equal'
-- statement.
--
-- * Write to memory for each 'mir_points_to' statement. (Writes
-- to already-initialized locations are transformed into equality
-- preconditions.)
--
-- * Evaluate the function arguments from the 'mir_execute_func'
-- statement.
--
-- Returns a tuple of (arguments, preconditions, pointer values,
-- memory).
verifyPrestate ::
  MIRCrucibleContext ->
  MS.CrucibleMethodSpecIR MIR ->
  Crucible.SymGlobalState Sym ->
  IO ([(Mir.Ty, MIRVal)],
      [Crucible.LabeledPred Term AssumptionReason],
      Map MS.AllocIndex (Some (MirPointer Sym)),
      Crucible.SymGlobalState Sym)
verifyPrestate cc mspec globals0 =
  do let sym = cc^.mccSym
     let tyenv = MS.csAllocations mspec
     let nameEnv = mspec ^. MS.csPreState . MS.csVarTypeNames

     let prestateLoc = W4.mkProgramLoc "_SAW_verify_prestate" W4.InternalPos
     liftIO $ W4.setCurrentProgramLoc sym prestateLoc

     (env, globals1) <- runStateT
       (traverse (doAlloc cc) (mspec ^. MS.csPreState . MS.csAllocs))
       globals0

     globals2 <- setupPrePointsTos mspec cc env (mspec ^. MS.csPreState . MS.csPointsTos) globals1
     cs <- setupPrestateConditions mspec cc env (mspec ^. MS.csPreState . MS.csConditions)
     args <- resolveArguments cc mspec env

     -- Check the type of the return setup value
     let methodStr = show (mspec ^. MS.csMethod)
     case (mspec ^. MS.csRetValue, mspec ^. MS.csRet) of
       (Just _, Nothing) ->
            fail $ unlines
              [ "Return value specified, but method " ++ methodStr ++
                " has void return type"
              ]
       (Just sv, Just retTy) ->
         do retTy' <- typeOfSetupValue cc tyenv nameEnv sv
            unless (checkCompatibleTys retTy retTy') $
              fail $ unlines
              [ "Incompatible types for return value when verifying " ++ methodStr
              , "Expected: " ++ show retTy
              , "but given value of type: " ++ show retTy'
              ]
       (Nothing, _) -> return ()

     return (args, cs, env, globals2)

-- | Simulate a MIR function with Crucible as part of a 'mir_verify' command,
-- making sure to install any overrides that the user supplies.
verifySimulate ::
  Options ->
  MIRCrucibleContext ->
  [Crucible.GenericExecutionFeature Sym] ->
  MethodSpec ->
  [(a, MIRVal)] ->
  [Crucible.LabeledPred Term AssumptionReason] ->
  W4.ProgramLoc ->
  [Lemma] ->
  Crucible.SymGlobalState Sym ->
  Bool {- ^ path sat checking -} ->
  IORef MetadataMap {- ^ metadata map -} ->
  IO (Maybe (Mir.Ty, MIRVal), Crucible.SymGlobalState Sym)
verifySimulate opts cc pfs mspec args assumes top_loc lemmas globals _checkSat mdMap =
  mccWithBackend cc $ \bak ->
  do let rm = cc^.mccRustModule
     let cfgMap = rm ^. Mir.rmCFGs
     let cs = rm ^. Mir.rmCS
     let col = cs ^. Mir.collection
     let method = mspec ^. MS.csMethod
     let verbosity = simVerbose opts
     let halloc = cc^.mccHandleAllocator

     when (verbosity > 2) $
          putStrLn "starting executeCrucibleMIR"

     -- Translate the static initializer function
     let ?debug = simVerbose opts
     -- For now, we use the same default settings for implicit parameters as in
     -- crux-mir. We may want to add options later that allow configuring these.
     let ?assertFalseOnError = True
     let ?customOps          = customOps
     Crucible.AnyCFG staticInitCfg <- Mir.transStatics cs halloc
     let staticInitHndl = Crucible.cfgHandle staticInitCfg
     Refl <- case testEquality (Crucible.handleArgTypes staticInitHndl) Ctx.Empty of
       Just e -> pure e
       Nothing -> fail "mir_verify: static initializer should not require arguments"

     -- Find and run the target function
     Crucible.AnyCFG methodCfg <- lookupDefIdCFG rm method
     let methodHndl = Crucible.cfgHandle methodCfg
     let methodArgTys = Crucible.handleArgTypes methodHndl
     let methodRetTy = Crucible.handleReturnType methodHndl

     regmap <- prepareArgs methodArgTys (map snd args)
     res <-
       do let feats = pfs
          let simctx = Crucible.initSimContext bak Mir.mirIntrinsicTypes halloc stdout
                         (Crucible.FnBindings Crucible.emptyHandleMap) Mir.mirExtImpl
                         SAWCruciblePersonality
          let simSt = Crucible.InitialState simctx globals Crucible.defaultAbortHandler methodRetTy
          let fnCall = Crucible.regValue <$> Crucible.callCFG methodCfg regmap
          let overrideSim =
                do forM_ cfgMap $ \(Crucible.AnyCFG cfg) ->
                     Crucible.bindFnHandle (Crucible.cfgHandle cfg) $
                     Crucible.UseCFG cfg (Crucible.postdomInfo cfg)
                   _ <- Crucible.callCFG staticInitCfg Crucible.emptyRegMap

                   mapM_ (registerOverride opts cc simctx top_loc mdMap)
                           (List.groupOn (view MS.csMethod) (map (view MS.psSpec) lemmas))
                   liftIO $
                     for_ assumes $ \(Crucible.LabeledPred p (md, reason)) ->
                       do expr <- resolveSAWPred cc p
                          let loc = MS.conditionLoc md
                          Crucible.addAssumption bak (Crucible.GenericAssumption loc reason expr)
                   fnCall
          Crucible.executeCrucible (map Crucible.genericToExecutionFeature feats)
            (simSt (Crucible.runOverrideSim methodRetTy overrideSim))

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
                      case decodeMIRVal col ret_mt (Crucible.AnyValue ty val) of
                        Nothing -> error $ "FIXME: Unsupported return type: " ++ show ret_ty
                        Just v -> return (Just (ret_mt, v))
            return (retval', globals1)

       Crucible.AbortedResult _ ar ->
         do let resultDoc = ppMIRAbortedResult cc ar
            fail $ unlines [ "Symbolic execution failed."
                           , show resultDoc
                           ]

       Crucible.TimeoutResult _cxt -> fail "Symbolic execution timed out."

  where
    prepareArg :: forall tp. Crucible.TypeRepr tp -> MIRVal -> IO (Crucible.RegValue Sym tp)
    prepareArg ty (MIRVal vTy vVal) =
      case testEquality ty (shapeType vTy) of
        Just Refl -> pure vVal
        Nothing   -> fail $ unlines
          [ "argument type mismatch"
          , show ty
          , show (shapeType vTy)
          ]

    prepareArgs ::
      forall xs.
      Ctx.Assignment Crucible.TypeRepr xs ->
      [MIRVal] ->
      IO (Crucible.RegMap Sym xs)
    prepareArgs ctx xs | length xs /= Ctx.sizeInt (Ctx.size ctx) =
      fail $ "Wrong number of arguments: found " ++ show (length xs) ++ ", expected " ++ show (Ctx.sizeInt (Ctx.size ctx))
    prepareArgs ctx xs =
      Crucible.RegMap <$>
      Ctx.traverseWithIndex (\idx tr ->
        do v <- prepareArg tr (xs !! Ctx.indexVal idx)
           return (Crucible.RegEntry tr v))
      ctx

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- | Returns the Cryptol type of a MIR type, returning 'Nothing' if it is not
-- easily expressible in Cryptol's type system or if it is not currently
-- supported.
cryptolTypeOfActual :: Mir.Ty -> Maybe Cryptol.Type
cryptolTypeOfActual mty =
  case mty of
    Mir.TyBool      -> Just Cryptol.tBit
    Mir.TyChar      -> Just $ Cryptol.tWord $ Cryptol.tNum (32 :: Integer)
    Mir.TyUint bs   -> baseSizeType bs
    Mir.TyInt  bs   -> baseSizeType bs
    Mir.TyArray t n -> Cryptol.tSeq (Cryptol.tNum n) <$> cryptolTypeOfActual t
    Mir.TyTuple tys -> Cryptol.tTuple <$> traverse cryptolTypeOfActual tys

    Mir.TyFloat _      -> Nothing
    Mir.TyStr          -> Nothing
    Mir.TyAdt _ _ _    -> Nothing
    Mir.TyRef _ _      -> Nothing
    Mir.TyFnDef _      -> Nothing
    Mir.TyFnPtr _      -> Nothing
    Mir.TyRawPtr _ _   -> Nothing
    Mir.TyClosure _    -> Nothing
    Mir.TySlice _      -> Nothing
    Mir.TyDowncast _ _ -> Nothing
    Mir.TyNever        -> Nothing
    Mir.TyForeign      -> Nothing
    Mir.TyLifetime     -> Nothing
    Mir.TyConst        -> Nothing
    Mir.TyErased       -> Nothing
    Mir.TyInterned _   -> Nothing
    Mir.TyDynamic _    -> Nothing
  where
    baseSizeType :: Mir.BaseSize -> Maybe Cryptol.Type
    baseSizeType Mir.B8    = Just $ Cryptol.tWord $ Cryptol.tNum (8 :: Integer)
    baseSizeType Mir.B16   = Just $ Cryptol.tWord $ Cryptol.tNum (16 :: Integer)
    baseSizeType Mir.B32   = Just $ Cryptol.tWord $ Cryptol.tNum (32 :: Integer)
    baseSizeType Mir.B64   = Just $ Cryptol.tWord $ Cryptol.tNum (64 :: Integer)
    baseSizeType Mir.B128  = Just $ Cryptol.tWord $ Cryptol.tNum (128 :: Integer)
    baseSizeType Mir.USize = Just $ Cryptol.tWord $ Cryptol.tNum $ natValue $ knownNat @Mir.SizeBits

-- | Allocate memory for each 'mir_alloc' or 'mir_alloc_mut'.
doAlloc ::
     MIRCrucibleContext
  -> Some MirAllocSpec
  -> StateT (Crucible.SymGlobalState Sym) IO (Some (MirPointer Sym))
doAlloc cc (Some ma) =
  mccWithBackend cc $ \bak ->
  do let col = cc ^. mccRustModule ^. Mir.rmCS ^. Mir.collection
     let halloc = cc^.mccHandleAllocator
     let sym = backendGetSym bak
     let iTypes = Mir.mirIntrinsicTypes
     Some tpr <- pure $ Mir.tyToRepr col (ma^.maMirType)

     -- Create an uninitialized `MirVector_PartialVector` of length 1 and
     -- return a pointer to its element.
     ref <- liftIO $
       Mir.newMirRefIO sym halloc (Mir.MirVectorRepr tpr)

     globals <- get
     globals' <- liftIO $ do
       one <- W4.bvLit sym W4.knownRepr $ BV.mkBV W4.knownRepr 1
       vec <- Mir.mirVector_uninitIO bak one
       Mir.writeMirRefIO bak globals iTypes ref vec
     put globals'

     ptr <- liftIO $ do
       zero <- W4.bvLit sym W4.knownRepr $ BV.mkBV W4.knownRepr 0
       Mir.subindexMirRefIO bak iTypes tpr ref zero
     pure $ Some MirPointer
       { _mpType = tpr
       , _mpMutbl = ma^.maMutbl
       , _mpMirType = ma^.maMirType
       , _mpRef = ptr
       }

-- Find the ADT definition that is monomorphized from `origName` with `substs`.
-- This should only be used on types that are known to be present in the crate
-- after dead code elimination - for example, because the type appears in the
-- signature of a function that's being translated.
findAdt :: Mir.Collection -> Mir.DefId -> Mir.Substs -> TopLevel Mir.Adt
findAdt col origName substs =
    case List.find (\adt -> adt ^. Mir.adtOrigSubsts == substs) insts of
        Just x -> return x
        Nothing -> fail $ "Unknown ADT: " ++ show (origName, substs)
  where
    insts = col ^. Mir.adtsOrig . at origName . to (fromMaybe [])

-- | Given a function name @fnName@, attempt to look up its corresponding
-- 'Mir.DefId'. Currently, the following types of function names are permittd:
--
-- * @<crate_name>/<disambiguator>::<function_name>: A fully disambiguated name.
--
-- * @<crate_name>::<function_name>: A name without a disambiguator. In this
--   case, SAW will attempt to look up a disambiguator from the @crateDisambigs@
--   map. If none can be found, or if there are multiple disambiguators for the
--   given @<crate_name>@, then this will fail.
findDefId :: Map Text (NonEmpty Text) -> Text -> TopLevel Mir.DefId
findDefId crateDisambigs fnName = do
    (crate, path) <-
      case edid of
        crate:path -> pure (crate, path)
        [] -> fail $ unlines
                [ "The function `" ++ fnNameStr ++ "` lacks a crate."
                , "Consider providing one, e.g., `<crate_name>::" ++ fnNameStr ++ "`."
                ]
    let crateStr = Text.unpack crate
    case Text.splitOn "/" crate of
      [crateNoDisambig, disambig] ->
        pure $ Mir.textId $ Text.intercalate "::"
             $ (crateNoDisambig <> "/" <> disambig) : path
      [_] ->
        case Map.lookup crate crateDisambigs of
            Just allDisambigs@(disambig :| otherDisambigs)
              |  F.null otherDisambigs
              -> pure $ Mir.textId $ Text.intercalate "::"
                      $ (crate <> "/" <> disambig) : path
              |  otherwise
              -> fail $ unlines $
                   [ "ambiguous crate " ++ crateStr
                   , "crate disambiguators:"
                   ] ++ F.toList (Text.unpack <$> allDisambigs)
            Nothing -> fail $ "unknown crate " ++ crateStr
      _ -> fail $ "Malformed crate name: " ++ show crateStr
  where
    fnNameStr = Text.unpack fnName
    edid = Text.splitOn "::" fnName

getMIRCrucibleContext :: CrucibleSetup MIR MIRCrucibleContext
getMIRCrucibleContext = view Setup.csCrucibleContext <$> get

-- | Look up the control-flow graph (CFG) for a 'Mir.DefId', failing if a CFG
-- cannot be found.
lookupDefIdCFG ::
     MonadFail m
  => Mir.RustModule
  -> Mir.DefId
  -> m (Crucible.AnyCFG MIR)
lookupDefIdCFG rm method =
  case Map.lookup (Mir.idText method) (rm ^. Mir.rmCFGs) of
    Just x -> return x
    Nothing -> fail $ "Couldn't find CFG for MIR function: " ++ show method

setupCrucibleContext :: Mir.RustModule -> TopLevel MIRCrucibleContext
setupCrucibleContext rm =
  do halloc <- getHandleAlloc
     sc <- getSharedContext
     pathSatSolver <- gets rwPathSatSolver
     sym <- io $ newSAWCoreExprBuilder sc
     bak <- io $ newSAWCoreBackend pathSatSolver sym
     opts <- getOptions
     io $ do let cfg = W4.getConfiguration sym
             verbSetting <- W4.getOptionSetting W4.verbosity cfg
             _ <- W4.setOpt verbSetting $ toInteger $ simVerbose opts
             return ()

     -- TODO! there's a lot of options setup we need to replicate
     --  from SAWScript.Crucible.LLVM.Builtins

     return MIRCrucibleContext { _mccRustModule = rm
                               , _mccBackend = bak
                               , _mccHandleAllocator = halloc
                               }

--------------------------------------------------------------------------------
-- Errors
--------------------------------------------------------------------------------

data MIRSetupError
  = MIRFreshVarInvalidType Mir.Ty
  | MIRPointsToNonReference SetupValue
  | MIRArgTypeMismatch Int Mir.Ty Mir.Ty -- argument position, expected, found
  | MIRArgNumberWrong Int Int -- number expected, number found
  | MIRReturnUnexpected Mir.Ty -- found
  | MIRReturnTypeMismatch Mir.Ty Mir.Ty -- expected, found

instance X.Exception MIRSetupError where
  toException = topLevelExceptionToException
  fromException = topLevelExceptionFromException

instance Show MIRSetupError where
  show err =
    case err of
      MIRFreshVarInvalidType jty ->
        "mir_fresh_var: Invalid type: " ++ show jty
      MIRPointsToNonReference ptr ->
        unlines
        [ "mir_points_to: Left-hand side is not a valid reference"
        , show (MS.ppSetupValue ptr)
        ]
      MIRArgTypeMismatch i expected found ->
        unlines
        [ "mir_execute_func: Argument type mismatch"
        , "Argument position: " ++ show i
        , "Expected type: " ++ show expected
        , "Given type: " ++ show found
        ]
      MIRArgNumberWrong expected found ->
        unlines
        [ "mir_execute_func: Wrong number of arguments"
        , "Expected: " ++ show expected
        , "Given: " ++ show found
        ]
      MIRReturnUnexpected found ->
        unlines
        [ "mir_return: Unexpected return value for void method"
        , "Given type: " ++ show found
        ]
      MIRReturnTypeMismatch expected found ->
        unlines
        [ "mir_return: Return type mismatch"
        , "Expected type: " ++ show expected
        , "Given type: " ++ show found
        ]
