{- |
Module      : SAWCentral.Crucible.JVM.Override
Description : Override matching and application for JVM
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wno-orphans #-} -- Pretty JVMVal

module SAWCentral.Crucible.JVM.Override
  ( OverrideMatcher
  , OverrideMatcher'(..)
  , runOverrideMatcher

  , setupValueSub
  , osAsserts
  , termSub

  , learnCond
  , matchArg
  , methodSpecHandler
  , valueToSC
  , injectJVMVal
  , decodeJVMVal

  , doEntireArrayStore
  , destVecTypedTerm
  ) where

import           Control.Lens (_2)
import           Control.Lens.At
import           Control.Lens.Each
import           Control.Lens.Fold
import           Control.Lens.Getter
import           Control.Lens.Lens
import           Control.Lens.Setter
import           Control.Exception as X
import           Control.Monad.IO.Class (liftIO)
import           Control.Monad
import           Data.Either (partitionEithers)
import           Data.Foldable (for_, traverse_)
import           Data.IORef
import           Data.List (tails)
import           Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.Void (absurd)
import qualified Prettyprinter as PP

-- cryptol
import qualified Cryptol.TypeCheck.AST as Cryptol
import qualified Cryptol.Eval.Type as Cryptol (TValue(..), evalType, evalValType)

-- what4
import qualified What4.BaseTypes as W4
import qualified What4.Interface as W4
import qualified What4.ProgramLoc as W4
import           What4.LabeledPred (labeledPred)

-- crucible
import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.CFG.Core as Crucible ( TypeRepr(UnitRepr) )
import qualified Lang.Crucible.FunctionHandle as Crucible
import qualified Lang.Crucible.Simulator as Crucible

-- crucible-jvm
import qualified Lang.Crucible.JVM as CJ

-- parameterized-utils
import           Data.Parameterized.Classes ((:~:)(..), testEquality)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(Some))

-- saw-core
import           Verifier.SAW.SharedTerm
import           CryptolSAWCore.TypedTerm

import           SAWCoreWhat4.ReturnTrip (toSC)

-- cryptol-saw-core
import qualified CryptolSAWCore.Cryptol as Cryptol

import           SAWCentral.Crucible.Common
import           SAWCentral.Crucible.Common.MethodSpec (AllocIndex(..), PrePost(..))
import           SAWCentral.Crucible.Common.Override hiding (getSymInterface)
import qualified SAWCentral.Crucible.Common.Override as Ov (getSymInterface)

import qualified SAWCentral.Crucible.Common.MethodSpec as MS
import           SAWCentral.Crucible.JVM.MethodSpecIR
import           SAWCentral.Crucible.JVM.ResolveSetupValue
import           SAWCentral.Crucible.JVM.Setup.Value ()
import           SAWCentral.Options
import           SAWCentral.Panic
import           SAWCentral.Utils (handleException)

-- jvm-parser
import qualified Language.JVM.Parser as J

-- A few convenient synonyms
type SetupValue = MS.SetupValue CJ.JVM
type CrucibleMethodSpecIR = MS.CrucibleMethodSpecIR CJ.JVM
type StateSpec = MS.StateSpec CJ.JVM
type SetupCondition = MS.SetupCondition CJ.JVM

-- TODO: Improve?
ppJVMVal :: JVMVal -> PP.Doc ann
ppJVMVal = PP.viaShow

instance PP.Pretty JVMVal where
  pretty = ppJVMVal


-- | Try to translate the spec\'s 'SetupValue' into an 'LLVMVal', pretty-print
--   the 'LLVMVal'.
mkStructuralMismatch ::
  Options              {- ^ output/verbosity options -} ->
  JVMCrucibleContext ->
  SharedContext {- ^ context for constructing SAW terms -} ->
  CrucibleMethodSpecIR {- ^ for name and typing environments -} ->
  JVMVal {- ^ the value from the simulator -} ->
  SetupValue {- ^ the value from the spec -} ->
  J.Type     {- ^ the expected type -} ->
  OverrideMatcher CJ.JVM w (OverrideFailureReason CJ.JVM)
mkStructuralMismatch opts cc sc spec jvmval setupval jty = do
  setupTy <- typeOfSetupValueJVM cc spec setupval
  setupJVal <- resolveSetupValueJVM opts cc sc spec setupval
  pure $ StructuralMismatch
            (ppJVMVal jvmval)
            (ppJVMVal setupJVal)
            (Just setupTy)
            jty


------------------------------------------------------------------------

-- | This function is responsible for implementing the \"override\" behavior
--   of method specifications.  The main work done in this function to manage
--   the process of selecting between several possible different override
--   specifications that could apply.  We want a proof to succeed if /any/
--   choice of method spec allows the proof to go through, which is a slightly
--   awkward thing to fit into the symbolic simulation framework.
--
--   The main work of determining the preconditions, postconditions, memory
--   updates and return value for a single specification is done by
--   the @methodSpecHandler_prestate@ and @methodSpecHandler_poststate@ functions.
--
--   In a first phase, we attempt to apply the precondition portion of each of
--   the given method specifications.  Each of them that might apply generate
--   a substitution for the setup variables and a collection of preconditions
--   that guard the specification.  We use these preconditions to compute
--   a multiway symbolic branch, one for each override which might apply.
--
--   In the body of each of the individual branches, we compute the postcondition
--   actions of the corresponding method specification.  This will update memory
--   and compute function return values, in addition to assuming postcondition
--   predicates.
methodSpecHandler ::
  forall rtp args ret.
  Options                  {- ^ output/verbosity options                     -} ->
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  JVMCrucibleContext          {- ^ context for interacting with Crucible        -} ->
  W4.ProgramLoc            {- ^ Location of the call site for error reporting-} ->
  IORef MetadataMap {- ^ metadata map -} ->
  NonEmpty CrucibleMethodSpecIR {- ^ specification for current function override  -} ->
  Crucible.FnHandle args ret {- ^ a handle for the function -} ->
  Crucible.OverrideSim (SAWCruciblePersonality Sym) Sym CJ.JVM rtp args ret
     (Crucible.RegValue Sym ret)
methodSpecHandler opts sc cc top_loc _mdMap css h =
  -- TODO, special case for single-override situations,
  --  and use the mdMap to keep track of obligations arising
  --  from override preconditions.

  jccWithBackend cc $ \bak -> do
  let sym = backendGetSym bak
  Crucible.RegMap args <- Crucible.getOverrideArgs

  -- First, run the precondition matcher phase.  Collect together a list of the results.
  -- For each override, this will either be an error message, or a matcher state and
  -- a method spec.
  prestates <-
    do g0 <- Crucible.readGlobals
       forM css $ \cs -> liftIO $
         let initialFree =
               Set.fromList (cs ^.. MS.csPreState. MS.csFreshVars . each . to tecExt . to ecVarIndex)
          in runOverrideMatcher sym g0 Map.empty Map.empty initialFree (view MS.csLoc cs)
                      (do methodSpecHandler_prestate opts sc cc args cs
                          return cs)

  -- Print a failure message if all overrides failed to match.  Otherwise, collect
  -- all the override states that might apply, and compute the conjunction of all
  -- the preconditions.  We'll use these to perform symbolic branches between the
  -- various overrides.
  branches <- case partitionEithers (NE.toList prestates) of
                (e, []) ->
                  fail $ show $
                  PP.vcat
                  [ "All overrides failed during structural matching:"
                  , PP.vcat (map (\x -> "*" <> PP.indent 2 (ppOverrideFailure x)) e)
                  ]
                (_, ss) -> liftIO $
                  forM ss $ \(cs,st) ->
                    do precond <- W4.andAllOf sym (folded._2.labeledPred) (st^.osAsserts)
                       return ( precond, cs, st )

  -- Now use crucible's symbolic branching machinery to select between the branches.
  -- Essentially, we are doing an n-way if statement on the precondition predicates
  -- for each override, and selecting the first one whose preconditions hold.
  --
  -- Then, in the body of the branch, we run the poststate handler to update the
  -- memory state, compute return values and compute postcondition predicates.
  --
  -- For each override branch that doesn't fail outright, we assume the relevant
  -- postconditions, update the crucible global variable state, and return the
  -- computed return value.
  --
  -- We add a final default branch that simply fails unless some previous override
  -- branch has already succeeded.
  let retTy = Crucible.handleReturnType h
  Crucible.regValue <$> Crucible.callOverride h
     (Crucible.mkOverride' "overrideBranches" retTy
       (Crucible.symbolicBranches Crucible.emptyRegMap $
         [ ( precond
           , do g <- Crucible.readGlobals
                res <- liftIO $ runOverrideMatcher sym g
                   (st^.setupValueSub)
                   (st^.termSub)
                   (st^.osFree)
                   (st^.osLocation)
                   (methodSpecHandler_poststate opts sc cc retTy cs)
                case res of
                  Left (OF loc rsn)  ->
                    -- TODO, better pretty printing for reasons
                    liftIO
                      $ Crucible.abortExecBecause
                      $ Crucible.AssertionFailure
                      $ Crucible.SimError loc
                      $ Crucible.AssertFailureSimError "assumed false" (show rsn)
                  Right (ret,st') ->
                    do liftIO $ forM_ (st'^.osAssumes) $ \(_md,asum) ->
                         Crucible.addAssumption bak
                          $ Crucible.GenericAssumption (st^.osLocation) "override postcondition" asum
                       Crucible.writeGlobals (st'^.overrideGlobals)
                       Crucible.overrideReturn' (Crucible.RegEntry retTy ret)
           , Just (W4.plSourceLoc (cs ^. MS.csLoc))
           )
         | (precond, cs, st) <- branches
         ] ++
        [

            let fnName = case branches of
                           (_, cs, _) : _  -> cs ^. MS.csMethod . jvmMethodName
                           _               -> "unknown function"
            in
            ( W4.truePred sym
            , liftIO $ Crucible.addFailedAssertion bak (Crucible.GenericSimError $ "no override specification applies for " ++ fnName)
            , Just (W4.plSourceLoc top_loc)
            )
        ]
       ))
     (Crucible.RegMap args)

------------------------------------------------------------------------

-- | Use a method spec to override the behavior of a function.
--   This function computes the pre-state portion of the override,
--   which involves reading values from arguments and memory and computing
--   substitutions for the setup value variables, and computing precondition
--   predicates.
methodSpecHandler_prestate ::
  forall ctx w.
  Options                  {- ^ output/verbosity options                     -} ->
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  JVMCrucibleContext          {- ^ context for interacting with Crucible        -} ->
  Ctx.Assignment (Crucible.RegEntry Sym) ctx
                           {- ^ the arguments to the function -} ->
  CrucibleMethodSpecIR     {- ^ specification for current function override  -} ->
  OverrideMatcher CJ.JVM w ()
methodSpecHandler_prestate opts sc cc args cs =
  do let expectedArgTypes = Map.elems (cs ^. MS.csArgBindings)
     let aux ::
           (J.Type, SetupValue) -> Crucible.AnyValue Sym ->
           IO (JVMVal, J.Type, SetupValue)
         aux (argTy, setupVal) val =
           case decodeJVMVal argTy val of
             Just val' -> return (val', argTy, setupVal)
             Nothing -> fail "unexpected type"

     -- todo: fail if list lengths mismatch
     xs <- liftIO (zipWithM aux expectedArgTypes (assignmentToList args))

     let md = MS.ConditionMetadata
              { MS.conditionLoc = cs ^. MS.csLoc
              , MS.conditionTags = mempty
              , MS.conditionType = "formal argument matching"
              , MS.conditionContext = ""
              }

     sequence_ [ matchArg opts sc cc cs PreState md x y z | (x, y, z) <- xs]

     learnCond opts sc cc cs PreState (cs ^. MS.csPreState)


-- | Use a method spec to override the behavior of a function.
--   This function computes the post-state portion of the override,
--   which involves writing values into memory, computing the return value,
--   and computing postcondition predicates.
methodSpecHandler_poststate ::
  forall ret.
  Options                  {- ^ output/verbosity options                     -} ->
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  JVMCrucibleContext          {- ^ context for interacting with Crucible        -} ->
  Crucible.TypeRepr ret    {- ^ type representation of function return value -} ->
  CrucibleMethodSpecIR     {- ^ specification for current function override  -} ->
  OverrideMatcher CJ.JVM RW (Crucible.RegValue Sym ret)
methodSpecHandler_poststate opts sc cc retTy cs =
  do executeCond opts sc cc cs (cs ^. MS.csPostState)
     computeReturnValue opts cc sc cs retTy (cs ^. MS.csRetValue)

-- learn pre/post condition
learnCond ::
  Options ->
  SharedContext ->
  JVMCrucibleContext ->
  CrucibleMethodSpecIR ->
  PrePost ->
  StateSpec ->
  OverrideMatcher CJ.JVM w ()
learnCond opts sc cc cs prepost ss =
  do let loc = cs ^. MS.csLoc
     matchPointsTos opts sc cc cs prepost (ss ^. MS.csPointsTos)
     traverse_ (learnSetupCondition opts sc cc cs prepost) (ss ^. MS.csConditions)
     assertTermEqualities sc cc
     enforceDisjointness cc loc ss
     enforceCompleteSubstitution loc ss


assertTermEqualities ::
  SharedContext ->
  JVMCrucibleContext ->
  OverrideMatcher CJ.JVM md ()
assertTermEqualities sc cc = do
  let sym = cc ^. jccSym
  let assertTermEquality (cond, t, md, e) = do
        p <- instantiateExtResolveSAWPred sc cc t
        p' <- liftIO $ W4.impliesPred sym cond p
        addAssert p' md e
  traverse_ assertTermEquality =<< OM (use termEqs)


-- execute a pre/post condition
executeCond ::
  Options ->
  SharedContext ->
  JVMCrucibleContext ->
  CrucibleMethodSpecIR ->
  StateSpec ->
  OverrideMatcher CJ.JVM RW ()
executeCond opts sc cc cs ss =
  do refreshTerms sc ss
     traverse_ (executeAllocation opts cc) (Map.assocs (ss ^. MS.csAllocs))
     traverse_ (executePointsTo opts sc cc cs) (ss ^. MS.csPointsTos)
     traverse_ (executeSetupCondition opts sc cc cs) (ss ^. MS.csConditions)


------------------------------------------------------------------------

-- | Generate assertions that all of the memory allocations matched by
-- an override's precondition are disjoint.
enforceDisjointness ::
  JVMCrucibleContext -> W4.ProgramLoc -> StateSpec -> OverrideMatcher CJ.JVM w ()
enforceDisjointness cc loc ss =
  do let sym = cc^.jccSym
     sub <- OM (use setupValueSub)
     let mems = Map.elems $ Map.intersectionWith (,) (view MS.csAllocs ss) sub

     let md = MS.ConditionMetadata
              { MS.conditionLoc = loc
              , MS.conditionTags = mempty
              , MS.conditionType = "memory region disjointness"
              , MS.conditionContext = ""
              }
     -- Ensure that all regions are disjoint from each other.
     sequence_
        [ do c <- liftIO $ W4.notPred sym =<< CJ.refIsEqual sym p q
             addAssert c md a

        | let a = Crucible.SimError loc $
                    Crucible.AssertFailureSimError "Memory regions not disjoint" ""
        , ((_ploc, _pty), p) : ps <- tails mems
        , ((_qloc, _qty), q)      <- ps
        ]

------------------------------------------------------------------------

-- | For each points-to statement read the memory value through the
-- given pointer (lhs) and match the value against the given pattern
-- (rhs).  Statements are processed in dependency order: a points-to
-- statement cannot be executed until bindings for any/all lhs
-- variables exist.
matchPointsTos ::
  Options          {- ^ saw script print out opts -} ->
  SharedContext    {- ^ term construction context -} ->
  JVMCrucibleContext  {- ^ simulator context     -}     ->
  CrucibleMethodSpecIR                               ->
  PrePost                                            ->
  [JVMPointsTo]       {- ^ points-tos                -} ->
  OverrideMatcher CJ.JVM w ()
matchPointsTos opts sc cc spec prepost = go False []
  where
    go ::
      Bool       {- progress indicator -} ->
      [JVMPointsTo] {- delayed conditions -} ->
      [JVMPointsTo] {- queued conditions  -} ->
      OverrideMatcher CJ.JVM w ()

    -- all conditions processed, success
    go _ [] [] = return ()

    -- not all conditions processed, no progress, failure
    go False delayed [] = failure (spec ^. MS.csLoc) (AmbiguousPointsTos delayed)

    -- not all conditions processed, progress made, resume delayed conditions
    go True delayed [] = go False [] delayed

    -- progress the next points-to in the work queue
    go progress delayed (c:cs) =
      do ready <- checkPointsTo c
         if ready then
           do learnPointsTo opts sc cc spec prepost c
              go True delayed cs
         else
           do go progress (c:delayed) cs

    -- determine if a precondition is ready to be checked
    checkPointsTo :: JVMPointsTo -> OverrideMatcher CJ.JVM w Bool
    checkPointsTo (JVMPointsToField _loc p _ _) = checkAllocIndex p
    checkPointsTo (JVMPointsToStatic _loc _ _) = pure True
    checkPointsTo (JVMPointsToElem _loc p _ _) = checkAllocIndex p
    checkPointsTo (JVMPointsToArray _loc p _) = checkAllocIndex p

    checkAllocIndex :: AllocIndex -> OverrideMatcher CJ.JVM w Bool
    checkAllocIndex i =
      do m <- OM (use setupValueSub)
         return (Map.member i m)


------------------------------------------------------------------------

computeReturnValue ::
  Options               {- ^ saw script debug and print options     -} ->
  JVMCrucibleContext       {- ^ context of the crucible simulation     -} ->
  SharedContext         {- ^ context for generating saw terms       -} ->
  CrucibleMethodSpecIR  {- ^ method specification                   -} ->
  Crucible.TypeRepr ret {- ^ representation of function return type -} ->
  Maybe SetupValue      {- ^ optional symbolic return value         -} ->
  OverrideMatcher CJ.JVM w (Crucible.RegValue Sym ret)
                        {- ^ concrete return value                  -}

computeReturnValue _opts _cc _sc spec ty Nothing =
  case ty of
    Crucible.UnitRepr -> return ()
    _ -> failure (spec ^. MS.csLoc) (BadReturnSpecification (Some ty))

computeReturnValue opts cc sc spec ty (Just val) =
  do val' <- resolveSetupValueJVM opts cc sc spec val
     let fail_ = failure (spec ^. MS.csLoc) (BadReturnSpecification (Some ty))
     case val' of
       IVal i ->
         case testEquality ty CJ.intRepr of
           Just Refl -> return i
           Nothing -> fail_
       LVal l ->
         case testEquality ty CJ.longRepr of
           Just Refl -> return l
           Nothing -> fail_
       RVal r ->
         case testEquality ty CJ.refRepr of
           Just Refl -> return r
           Nothing -> fail_


------------------------------------------------------------------------

-- | Assign the given pointer value to the given allocation index in
-- the current substitution. If there is already a binding for this
-- index, then add a pointer-equality constraint.
assignVar ::
  JVMCrucibleContext {- ^ context for interacting with Crucible -} ->
  MS.ConditionMetadata ->
  AllocIndex {- ^ variable index -} ->
  JVMRefVal  {- ^ concrete value -} ->
  OverrideMatcher CJ.JVM w ()

assignVar cc md var ref =
  do old <- OM (setupValueSub . at var <<.= Just ref)
     let loc = MS.conditionLoc md
     let sym = cc ^. jccSym
     for_ old $ \ref' ->
       do p <- liftIO (CJ.refIsEqual sym ref ref')
          addAssert p md (Crucible.SimError loc (Crucible.AssertFailureSimError "equality of aliased pointers" ""))

------------------------------------------------------------------------

-- | Match the value of a function argument with a symbolic 'SetupValue'.
matchArg ::
  Options          {- ^ saw script print out opts -} ->
  SharedContext      {- ^ context for constructing SAW terms    -} ->
  JVMCrucibleContext    {- ^ context for interacting with Crucible -} ->
  CrucibleMethodSpecIR {- ^ specification for current function override  -} ->
  PrePost                                                          ->
  MS.ConditionMetadata ->
  JVMVal             {- ^ concrete simulation value             -} ->
  J.Type             {- ^ expected memory type                  -} ->
  SetupValue         {- ^ expected specification value          -} ->
  OverrideMatcher CJ.JVM w ()

matchArg opts sc cc cs prepost md actual expectedTy expected@(MS.SetupTerm expectedTT)
  | TypedTermSchema (Cryptol.Forall [] [] tyexpr) <- ttType expectedTT
  , Right tval <- Cryptol.evalType mempty tyexpr
  = do sym <- Ov.getSymInterface
       failMsg  <- mkStructuralMismatch opts cc sc cs actual expected expectedTy
       realTerm <- valueToSC sym md failMsg tval actual
       matchTerm sc md prepost realTerm (ttTerm expectedTT)

matchArg opts sc cc cs prepost md actual@(RVal ref) expectedTy setupval =
  case setupval of
    MS.SetupVar var ->
      do assignVar cc md var ref

    MS.SetupNull () ->
      do sym <- Ov.getSymInterface
         p   <- liftIO (CJ.refIsNull sym ref)
         addAssert p md (Crucible.SimError (cs ^. MS.csLoc) (Crucible.AssertFailureSimError ("null-equality " ++ MS.stateCond prepost) ""))

    MS.SetupGlobal empty _ -> absurd empty
    MS.SetupEnum   empty   -> absurd empty
    MS.SetupTuple  empty _ -> absurd empty
    MS.SetupSlice  empty   -> absurd empty

    _ -> failure (cs ^. MS.csLoc) =<<
           mkStructuralMismatch opts cc sc cs actual setupval expectedTy

matchArg opts sc cc cs _prepost md actual expectedTy expected =
  failure (MS.conditionLoc md) =<<
    mkStructuralMismatch opts cc sc cs actual expected expectedTy

------------------------------------------------------------------------

valueToSC ::
  Sym ->
  MS.ConditionMetadata ->
  OverrideFailureReason CJ.JVM ->
  Cryptol.TValue ->
  JVMVal ->
  OverrideMatcher CJ.JVM w Term
valueToSC sym _ _ Cryptol.TVBit (IVal x) =
  do b <- liftIO $ W4.bvIsNonzero sym x
      -- TODO: assert that x is 0 or 1
     st <- liftIO (sawCoreState sym)
     liftIO (toSC sym st b)

valueToSC sym _ _ (Cryptol.TVSeq 8 Cryptol.TVBit) (IVal x) =
  do st <- liftIO (sawCoreState sym)
     liftIO (toSC sym st =<< W4.bvTrunc sym (W4.knownNat @8) x)

valueToSC sym _ _ (Cryptol.TVSeq 16 Cryptol.TVBit) (IVal x) =
  do st <- liftIO (sawCoreState sym)
     liftIO (toSC sym st =<< W4.bvTrunc sym (W4.knownNat @16) x)

valueToSC sym _ _ (Cryptol.TVSeq 32 Cryptol.TVBit) (IVal x) =
  do st <- liftIO (sawCoreState sym)
     liftIO (toSC sym st x)

valueToSC sym _ _ (Cryptol.TVSeq 64 Cryptol.TVBit) (LVal x) =
  do st <- liftIO (sawCoreState sym)
     liftIO (toSC sym st x)

valueToSC _sym md failMsg _tval _val =
  failure (MS.conditionLoc md) failMsg

------------------------------------------------------------------------

-- | Use the current state to learn about variable assignments based on
-- preconditions for a procedure specification.
learnSetupCondition ::
  Options                    ->
  SharedContext              ->
  JVMCrucibleContext            ->
  CrucibleMethodSpecIR       ->
  PrePost                    ->
  SetupCondition             ->
  OverrideMatcher CJ.JVM w ()
learnSetupCondition opts sc cc spec prepost cond =
  case cond of
    MS.SetupCond_Equal md val1 val2 -> learnEqual opts sc cc spec md prepost val1 val2
    MS.SetupCond_Pred md tm         -> learnPred sc cc md prepost (ttTerm tm)
    MS.SetupCond_Ghost md var val   -> learnGhost sc md prepost var val

------------------------------------------------------------------------

-- | Process a "points_to" statement from the precondition section of
-- the CrucibleSetup block. First, load the value from the address
-- indicated by 'ptr', and then match it against the pattern 'val'.
learnPointsTo ::
  Options                    ->
  SharedContext              ->
  JVMCrucibleContext            ->
  CrucibleMethodSpecIR       ->
  PrePost                    ->
  JVMPointsTo                   ->
  OverrideMatcher CJ.JVM w ()
learnPointsTo opts sc cc spec prepost pt =
  jccWithBackend cc $ \bak -> do
  let sym = backendGetSym bak
  let tyenv = MS.csAllocations spec
  let nameEnv = MS.csTypeNames spec
  let jc = cc ^. jccJVMContext
  globals <- OM (use overrideGlobals)
  case pt of

    JVMPointsToField md ptr fid (Just val) ->
      do ty <- typeOfSetupValue cc tyenv nameEnv val
         rval <- resolveAllocIndexJVM ptr
         dyn <- liftIO $ CJ.doFieldLoad bak globals rval fid
         v <- liftIO $ projectJVMVal bak ty ("field load " ++ J.fieldIdName fid ++ ", " ++ show (MS.conditionLoc md)) dyn
         matchArg opts sc cc spec prepost md v ty val

    JVMPointsToStatic md fid (Just val) ->
      do ty <- typeOfSetupValue cc tyenv nameEnv val
         dyn <- liftIO $ CJ.doStaticFieldLoad bak jc globals fid
         v <- liftIO $ projectJVMVal bak ty ("static field load " ++ J.fieldIdName fid ++ ", " ++ show (MS.conditionLoc md)) dyn
         matchArg opts sc cc spec prepost md v ty val

    JVMPointsToElem md ptr idx (Just val) ->
      do ty <- typeOfSetupValue cc tyenv nameEnv val
         rval <- resolveAllocIndexJVM ptr
         dyn <- liftIO $ CJ.doArrayLoad bak globals rval idx
         v <- liftIO $ projectJVMVal bak ty ("array load " ++ show idx ++ ", " ++ show (MS.conditionLoc md)) dyn
         matchArg opts sc cc spec prepost md v ty val

    JVMPointsToArray md ptr (Just tt) ->
      do (len, ety) <-
           case ttIsMono (ttType tt) of
             Nothing -> fail "jvm_array_is: invalid polymorphic value"
             Just cty ->
               case Cryptol.tIsSeq cty of
                 Nothing -> fail "jvm_array_is: expected array type"
                 Just (lty, ety) ->
                   case Cryptol.tIsNum lty of
                     Nothing -> fail "jvm_array_is: expected finite-sized array"
                     Just len -> pure (len, ety)
         jty <-
           case toJVMType (Cryptol.evalValType mempty ety) of
             Nothing -> fail "jvm_array_is: invalid element type"
             Just jty -> pure jty
         rval <- resolveAllocIndexJVM ptr
         let tval = Cryptol.evalValType mempty ety
         let
           load idx =
             do dyn <- liftIO $ CJ.doArrayLoad bak globals rval idx
                let msg = "array load " ++ show idx ++ ", " ++ show (MS.conditionLoc md)
                jval <- liftIO $ projectJVMVal bak jty msg dyn
                let failMsg = StructuralMismatch (ppJVMVal jval) mempty (Just jty) jty -- REVISIT
                valueToSC sym md failMsg tval jval

         when (len > toInteger (maxBound :: Int)) $ fail "jvm_array_is: array length too long"
         ety_tm <- liftIO $ Cryptol.importType sc Cryptol.emptyEnv ety
         ts <- traverse load [0 .. fromInteger len - 1]
         realTerm <- liftIO $ scVector sc ety_tm ts
         matchTerm sc md prepost realTerm (ttTerm tt)

    -- If the right-hand-side is 'Nothing', this is indicates a "modifies" declaration,
    -- which should probably not appear in the pre-state section, and has no effect.
    _ -> pure ()

------------------------------------------------------------------------

-- | Process a "crucible_equal" statement from the precondition
-- section of the CrucibleSetup block.
learnEqual ::
  Options                                          ->
  SharedContext                                    ->
  JVMCrucibleContext                                  ->
  CrucibleMethodSpecIR                             ->
  MS.ConditionMetadata                             ->
  PrePost                                          ->
  SetupValue       {- ^ first value to compare  -} ->
  SetupValue       {- ^ second value to compare -} ->
  OverrideMatcher CJ.JVM w ()
learnEqual opts sc cc spec md prepost v1 v2 =
  do val1 <- resolveSetupValueJVM opts cc sc spec v1
     val2 <- resolveSetupValueJVM opts cc sc spec v2
     p <- liftIO (equalValsPred cc val1 val2)
     let name = "equality " ++ MS.stateCond prepost
     let loc = MS.conditionLoc md
     addAssert p md (Crucible.SimError loc (Crucible.AssertFailureSimError name ""))

-- | Process a "crucible_precond" statement from the precondition
-- section of the CrucibleSetup block.
learnPred ::
  SharedContext                                                       ->
  JVMCrucibleContext                                                     ->
  MS.ConditionMetadata                                                ->
  PrePost                                                             ->
  Term             {- ^ the precondition to learn                  -} ->
  OverrideMatcher CJ.JVM w ()
learnPred sc cc md prepost t =
  do s <- OM (use termSub)
     u <- liftIO $ scInstantiateExt sc s t
     p <- liftIO $ resolveBoolTerm (cc ^. jccSym) u
     let loc = MS.conditionLoc md
     addAssert p md (Crucible.SimError loc (Crucible.AssertFailureSimError (MS.stateCond prepost) ""))

instantiateExtResolveSAWPred ::
  SharedContext ->
  JVMCrucibleContext ->
  Term ->
  OverrideMatcher CJ.JVM md (W4.Pred Sym)
instantiateExtResolveSAWPred sc cc cond = do
  sub <- OM (use termSub)
  liftIO $ resolveSAWPred cc =<< scInstantiateExt sc sub cond

------------------------------------------------------------------------

-- TODO: replace (W4.ProgramLoc, J.Type) by some allocation datatype
-- that includes constructors for object allocations and array
-- allocations (with length).

-- | Perform an allocation as indicated by a 'crucible_alloc'
-- statement from the postcondition section.
executeAllocation ::
  Options                        ->
  JVMCrucibleContext                ->
  (AllocIndex, (MS.ConditionMetadata, Allocation)) ->
  OverrideMatcher CJ.JVM w ()
executeAllocation opts cc (var, (md, alloc)) =
  jccWithBackend cc $ \bak ->
  do liftIO $ printOutLn opts Debug $ unwords ["executeAllocation:", show var, show alloc]
     let jc = cc^.jccJVMContext
     let halloc = cc^.jccHandleAllocator
     globals <- OM (use overrideGlobals)
     let mut = True -- allocate objects/arrays from post-state as mutable
     (ptr, globals') <-
       case alloc of
         AllocObject cname ->
           liftIO $ CJ.doAllocateObject bak halloc jc cname (const mut) globals
         AllocArray len elemTy ->
           liftIO $ CJ.doAllocateArray bak halloc jc len elemTy (const mut) globals
     OM (overrideGlobals .= globals')
     assignVar cc md var ptr

------------------------------------------------------------------------

-- | Update the simulator state based on the postconditions from the
-- procedure specification.
executeSetupCondition ::
  Options                    ->
  SharedContext              ->
  JVMCrucibleContext            ->
  CrucibleMethodSpecIR       ->
  SetupCondition             ->
  OverrideMatcher CJ.JVM RW ()
executeSetupCondition opts sc cc spec =
  \case
    MS.SetupCond_Equal md val1 val2 ->
      executeEqual opts sc cc spec md val1 val2
    MS.SetupCond_Pred md tm -> executePred sc cc md tm
    MS.SetupCond_Ghost md var val -> executeGhost sc md var val

------------------------------------------------------------------------

-- | Process a "points_to" statement from the postcondition section of
-- the CrucibleSetup block. First we compute the value indicated by
-- 'val', and then write it to the address indicated by 'ptr'.
executePointsTo ::
  Options                    ->
  SharedContext              ->
  JVMCrucibleContext            ->
  CrucibleMethodSpecIR       ->
  JVMPointsTo                   ->
  OverrideMatcher CJ.JVM w ()
executePointsTo opts sc cc spec pt =
  jccWithBackend cc $ \bak -> do
  let sym = backendGetSym bak
  globals <- OM (use overrideGlobals)
  let jc = cc ^. jccJVMContext
  case pt of

    JVMPointsToField _loc ptr fid val ->
      do dyn <- maybe (pure CJ.unassignedJVMValue) (injectSetupValueJVM sym opts cc sc spec) val
         rval <- resolveAllocIndexJVM ptr
         globals' <- liftIO $ CJ.doFieldStore bak globals rval fid dyn
         OM (overrideGlobals .= globals')

    JVMPointsToStatic _loc fid val ->
      do dyn <- maybe (pure CJ.unassignedJVMValue) (injectSetupValueJVM sym opts cc sc spec) val
         globals' <- liftIO $ CJ.doStaticFieldStore bak jc globals fid dyn
         OM (overrideGlobals .= globals')

    JVMPointsToElem _loc ptr idx val ->
      do dyn <- maybe (pure CJ.unassignedJVMValue) (injectSetupValueJVM sym opts cc sc spec) val
         rval <- resolveAllocIndexJVM ptr
         globals' <- liftIO $ CJ.doArrayStore bak globals rval idx dyn
         OM (overrideGlobals .= globals')

    JVMPointsToArray _loc ptr (Just tt) ->
      do (_ety, tts) <-
           liftIO (destVecTypedTerm sc tt) >>=
           \case
             Nothing -> fail "jvm_array_is: not a monomorphic sequence type"
             Just x -> pure x
         rval <- resolveAllocIndexJVM ptr
         vs <- traverse (injectSetupValueJVM sym opts cc sc spec . MS.SetupTerm) tts
         globals' <- liftIO $ doEntireArrayStore bak globals rval vs
         OM (overrideGlobals .= globals')

    JVMPointsToArray _loc ptr Nothing ->
      case Map.lookup ptr (MS.csAllocations spec) of
        Just (_, AllocArray len _) ->
          do let vs = replicate len CJ.unassignedJVMValue
             rval <- resolveAllocIndexJVM ptr
             globals' <- liftIO $ doEntireArrayStore bak globals rval vs
             OM (overrideGlobals .= globals')
        _ -> panic "JVMSetup" ["executePointsTo", "expected array allocation"]

injectSetupValueJVM ::
  Sym                  ->
  Options              ->
  JVMCrucibleContext   ->
  SharedContext        ->
  CrucibleMethodSpecIR ->
  SetupValue           ->
  OverrideMatcher CJ.JVM w (Crucible.RegValue Sym CJ.JVMValueType)
injectSetupValueJVM sym opts cc sc spec val =
  injectJVMVal sym <$> resolveSetupValueJVM opts cc sc spec val

doEntireArrayStore ::
  (Crucible.IsSymBackend sym bak) =>
  bak ->
  Crucible.SymGlobalState sym ->
  Crucible.RegValue sym CJ.JVMRefType ->
  [Crucible.RegValue sym CJ.JVMValueType] ->
  IO (Crucible.SymGlobalState sym)
doEntireArrayStore bak glob ref vs = foldM store glob (zip [0..] vs)
  where store g (i, v) = CJ.doArrayStore bak g ref i v

-- | Given a 'TypedTerm' with a vector type, return the element type
-- along with a list of its projected components. Return 'Nothing' if
-- the 'TypedTerm' does not have a vector type.
destVecTypedTerm :: SharedContext -> TypedTerm -> IO (Maybe (Cryptol.Type, [TypedTerm]))
destVecTypedTerm sc (TypedTerm ttp t) =
  case asVec of
    Nothing -> pure Nothing
    Just (len, ety) ->
      do len_tm <- scNat sc (fromInteger len)
         ty_tm <- Cryptol.importType sc Cryptol.emptyEnv ety
         idxs <- traverse (scNat sc) (map fromInteger [0 .. len-1])
         ts <- traverse (scAt sc len_tm ty_tm t) idxs
         pure $ Just (ety, map (TypedTerm (TypedTermSchema (Cryptol.tMono ety))) ts)
  where
    asVec =
      do ty <- ttIsMono ttp
         (n, a) <- Cryptol.tIsSeq ty
         n' <- Cryptol.tIsNum n
         Just (n', a)

------------------------------------------------------------------------


-- | Process a "crucible_equal" statement from the postcondition
-- section of the CrucibleSetup block.
executeEqual ::
  Options                                          ->
  SharedContext                                    ->
  JVMCrucibleContext                                  ->
  CrucibleMethodSpecIR                             ->
  MS.ConditionMetadata ->
  SetupValue       {- ^ first value to compare  -} ->
  SetupValue       {- ^ second value to compare -} ->
  OverrideMatcher CJ.JVM w ()
executeEqual opts sc cc spec md v1 v2 =
  do val1 <- resolveSetupValueJVM opts cc sc spec v1
     val2 <- resolveSetupValueJVM opts cc sc spec v2
     p <- liftIO (equalValsPred cc val1 val2)
     addAssume p md

-- | Process a "crucible_postcond" statement from the postcondition
-- section of the CrucibleSetup block.
executePred ::
  SharedContext   ->
  JVMCrucibleContext ->
  MS.ConditionMetadata ->
  TypedTerm        {- ^ the term to assert as a postcondition -} ->
  OverrideMatcher CJ.JVM w ()
executePred sc cc md tt =
  do s <- OM (use termSub)
     t <- liftIO $ scInstantiateExt sc s (ttTerm tt)
     p <- liftIO $ resolveBoolTerm (cc ^. jccSym) t
     addAssume p md

------------------------------------------------------------------------

-- | Map the given substitution over all 'SetupTerm' constructors in
-- the given 'SetupValue'.
instantiateSetupValue ::
  SharedContext     ->
  Map VarIndex Term ->
  SetupValue        ->
  IO SetupValue
instantiateSetupValue sc s v =
  case v of
    MS.SetupVar _                     -> return v
    MS.SetupTerm tt                   -> MS.SetupTerm <$> doTerm tt
    MS.SetupNull ()                   -> return v
    MS.SetupGlobal empty _            -> absurd empty
    MS.SetupStruct empty _            -> absurd empty
    MS.SetupEnum empty                -> absurd empty
    MS.SetupTuple empty _             -> absurd empty
    MS.SetupSlice empty               -> absurd empty
    MS.SetupArray empty _             -> absurd empty
    MS.SetupElem empty _ _            -> absurd empty
    MS.SetupField empty _ _           -> absurd empty
    MS.SetupCast empty _              -> absurd empty
    MS.SetupUnion empty _ _           -> absurd empty
    MS.SetupGlobalInitializer empty _ -> absurd empty
    MS.SetupMux empty _ _ _           -> absurd empty
  where
    doTerm (TypedTerm schema t) = TypedTerm schema <$> scInstantiateExt sc s t

------------------------------------------------------------------------

resolveAllocIndexJVM :: AllocIndex -> OverrideMatcher CJ.JVM w JVMRefVal
resolveAllocIndexJVM i =
  do m <- OM (use setupValueSub)
     case Map.lookup i m of
       Just rval -> pure rval
       Nothing ->
         panic "JVMSetup" ["resolveAllocIndexJVM", "Unresolved prestate variable:" ++ show i]

resolveSetupValueJVM ::
  Options              ->
  JVMCrucibleContext   ->
  SharedContext        ->
  CrucibleMethodSpecIR ->
  SetupValue           ->
  OverrideMatcher CJ.JVM w JVMVal
resolveSetupValueJVM opts cc sc spec sval =
  do m <- OM (use setupValueSub)
     s <- OM (use termSub)
     let tyenv = MS.csAllocations spec
         nameEnv = MS.csTypeNames spec
     sval' <- liftIO $ instantiateSetupValue sc s sval
     liftIO $ resolveSetupVal cc m tyenv nameEnv sval' `X.catch` handleException opts

typeOfSetupValueJVM ::
  JVMCrucibleContext   ->
  CrucibleMethodSpecIR ->
  SetupValue           ->
  OverrideMatcher CJ.JVM w J.Type
typeOfSetupValueJVM cc spec sval =
  do let tyenv = MS.csAllocations spec
         nameEnv = MS.csTypeNames spec
     liftIO $ typeOfSetupValue cc tyenv nameEnv sval

injectJVMVal :: Sym -> JVMVal -> Crucible.RegValue Sym CJ.JVMValueType
injectJVMVal sym jv =
  case jv of
    RVal x -> Crucible.injectVariant sym W4.knownRepr CJ.tagR x
    IVal x -> Crucible.injectVariant sym W4.knownRepr CJ.tagI x
    LVal x -> Crucible.injectVariant sym W4.knownRepr CJ.tagL x

projectJVMVal :: OnlineSolver solver =>
  Backend solver -> J.Type -> String -> Crucible.RegValue Sym CJ.JVMValueType -> IO JVMVal
projectJVMVal bak ty msg' v =
  case ty of
    J.BooleanType -> IVal <$> proj v CJ.tagI
    J.ByteType    -> IVal <$> proj v CJ.tagI
    J.CharType    -> IVal <$> proj v CJ.tagI
    J.ShortType   -> IVal <$> proj v CJ.tagI
    J.IntType     -> IVal <$> proj v CJ.tagI
    J.LongType    -> LVal <$> proj v CJ.tagL
    J.FloatType   -> err -- FIXME
    J.DoubleType  -> err -- FIXME
    J.ArrayType{} -> RVal <$> proj v CJ.tagR
    J.ClassType{} -> RVal <$> proj v CJ.tagR
  where
    proj ::
      forall tp.
      Crucible.RegValue Sym CJ.JVMValueType ->
      Ctx.Index CJ.JVMValueCtx tp ->
      IO (Crucible.RegValue Sym tp)
    proj val idx = Crucible.readPartExpr bak (Crucible.unVB (val Ctx.! idx)) msg

    msg = Crucible.GenericSimError $ "Ill-formed value for type " ++ show ty ++ " (" ++ msg' ++ ")"
    err = Crucible.addFailedAssertion bak msg

decodeJVMVal :: J.Type -> Crucible.AnyValue Sym -> Maybe JVMVal
decodeJVMVal ty v =
  case ty of
    J.BooleanType -> go v CJ.intRepr IVal
    J.ByteType    -> go v CJ.intRepr IVal
    J.CharType    -> go v CJ.intRepr IVal
    J.ShortType   -> go v CJ.intRepr IVal
    J.IntType     -> go @CJ.JVMIntType v CJ.intRepr IVal
    J.LongType    -> go @CJ.JVMLongType v CJ.longRepr LVal
    J.FloatType   -> Nothing -- FIXME
    J.DoubleType  -> Nothing -- FIXME
    J.ArrayType{} -> go @CJ.JVMRefType v CJ.refRepr RVal
    J.ClassType{} -> go @CJ.JVMRefType v CJ.refRepr RVal
  where
    go ::
      forall t.
      Crucible.AnyValue Sym ->
      Crucible.TypeRepr t ->
      (Crucible.RegValue Sym t -> JVMVal) ->
      Maybe JVMVal
    go (Crucible.AnyValue repr rv) repr' k =
      case testEquality repr repr' of
        Just Refl -> Just (k rv)
        Nothing   -> Nothing
