{- |
Module      : SAWScript.Crucible.JVM.Override
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

module SAWScript.Crucible.JVM.Override
  ( OverrideMatcher(..)
  , runOverrideMatcher

  , setupValueSub
  , osAsserts
  , termSub

  , learnCond
  , matchArg
  , methodSpecHandler
  , valueToSC
  , termId
  , injectJVMVal
  , decodeJVMVal
  ) where

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
import           Data.List (tails)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Void (absurd)
import qualified Text.PrettyPrint.ANSI.Leijen as PPL

-- cryptol
import qualified Cryptol.TypeCheck.AST as Cryptol (Schema(..))
import qualified Cryptol.Eval.Type as Cryptol (TValue(..), evalType)

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

-- crucible-saw
import qualified Lang.Crucible.Backend.SAWCore as CrucibleSAW

-- crucible-jvm
import qualified Lang.Crucible.JVM as CJ

-- parameterized-utils
import           Data.Parameterized.Classes ((:~:)(..), testEquality)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(Some))

-- saw-core
import           Verifier.SAW.SharedTerm
import           Verifier.SAW.Prelude (scEq)
import           Verifier.SAW.TypedAST
import           Verifier.SAW.Recognizer
import           Verifier.SAW.TypedTerm

import           SAWScript.Crucible.Common (Sym)
import           SAWScript.Crucible.Common.MethodSpec (AllocIndex(..), PrePost(..))
import           SAWScript.Crucible.Common.Override hiding (getSymInterface)
import qualified SAWScript.Crucible.Common.Override as Ov (getSymInterface)

--import           SAWScript.JavaExpr (JavaType(..))
import qualified SAWScript.Crucible.Common.MethodSpec as MS
import           SAWScript.Crucible.JVM.MethodSpecIR
import           SAWScript.Crucible.JVM.ResolveSetupValue
import           SAWScript.Options
import           SAWScript.Utils (handleException)

-- jvm-parser
import qualified Language.JVM.Parser as J

-- A few convenient synonyms
type SetupValue = MS.SetupValue CJ.JVM
type CrucibleMethodSpecIR = MS.CrucibleMethodSpecIR CJ.JVM
type StateSpec = MS.StateSpec CJ.JVM
type SetupCondition = MS.SetupCondition CJ.JVM
type instance Pointer CJ.JVM = JVMRefVal

-- TODO: Improve?
ppJVMVal :: JVMVal -> PPL.Doc
ppJVMVal = PPL.text . show

instance PPL.Pretty JVMVal where
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
  (setupTy, setupJVal) <- resolveSetupValueJVM opts cc sc spec setupval
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
  [CrucibleMethodSpecIR]   {- ^ specification for current function override  -} ->
  Crucible.FnHandle args ret {- ^ a handle for the function -} ->
  Crucible.OverrideSim (CrucibleSAW.SAWCruciblePersonality Sym) Sym CJ.JVM rtp args ret
     (Crucible.RegValue Sym ret)
methodSpecHandler opts sc cc top_loc css h = do
  sym <- Crucible.getSymInterface
  Crucible.RegMap args <- Crucible.getOverrideArgs

  -- First, run the precondition matcher phase.  Collect together a list of the results.
  -- For each override, this will either be an error message, or a matcher state and
  -- a method spec.
  prestates <-
    do g0 <- Crucible.readGlobals
       forM css $ \cs -> liftIO $
         let initialFree =
               Set.fromList (cs ^.. MS.csPreState. MS.csFreshVars . each . to ttTerm . to termId)
          in runOverrideMatcher sym g0 Map.empty Map.empty initialFree (view MS.csLoc cs)
                      (do methodSpecHandler_prestate opts sc cc args cs
                          return cs)

  -- Print a failure message if all overrides failed to match.  Otherwise, collect
  -- all the override states that might apply, and compute the conjunction of all
  -- the preconditions.  We'll use these to perform symbolic branches between the
  -- various overrides.
  branches <- case partitionEithers prestates of
                (e, []) ->
                  fail $ show $
                    PPL.text "All overrides failed during structural matching:" PPL.<$$>
                    PPL.vcat (map (\x -> PPL.text "*" PPL.<> PPL.indent 2 (ppOverrideFailure x)) e)
                (_, ss) -> liftIO $
                  forM ss $ \(cs,st) ->
                    do precond <- W4.andAllOf sym (folded.labeledPred) (st^.osAsserts)
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
                    liftIO $ Crucible.abortExecBecause
                      (Crucible.AssumedFalse (Crucible.AssumptionReason loc (show rsn)))
                  Right (ret,st') ->
                    do liftIO $ forM_ (st'^.osAssumes) $ \asum ->
                         Crucible.addAssumption (cc ^. jccBackend)
                            (Crucible.LabeledPred asum
                              (Crucible.AssumptionReason (st^.osLocation) "override postcondition"))
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
            , liftIO $ Crucible.addFailedAssertion sym (Crucible.GenericSimError $ "no override specification applies for " ++ fnName)
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

     sequence_ [ matchArg opts sc cc cs PreState x y z | (x, y, z) <- xs]

     learnCond opts sc cc cs PreState (cs ^. MS.csPreState)


-- | Use a method spec to override the behavior of a function.
--   This function computes the post-state portion of the override,
--   which involves writing values into memory, computing the return value,
--   and computing postcondition predicates.
methodSpecHandler_poststate ::
  forall ret w.
  Options                  {- ^ output/verbosity options                     -} ->
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  JVMCrucibleContext          {- ^ context for interacting with Crucible        -} ->
  Crucible.TypeRepr ret    {- ^ type representation of function return value -} ->
  CrucibleMethodSpecIR     {- ^ specification for current function override  -} ->
  OverrideMatcher CJ.JVM w (Crucible.RegValue Sym ret)
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
     enforceDisjointness cc loc ss
     enforceCompleteSubstitution loc ss


-- | Verify that all of the fresh variables for the given
-- state spec have been "learned". If not, throws
-- 'AmbiguousVars' exception.
enforceCompleteSubstitution :: W4.ProgramLoc -> StateSpec -> OverrideMatcher CJ.JVM w ()
enforceCompleteSubstitution loc ss =

  do sub <- OM (use termSub)

     let -- predicate matches terms that are not covered by the computed
         -- term substitution
         isMissing tt = termId (ttTerm tt) `Map.notMember` sub

         -- list of all terms not covered by substitution
         missing = filter isMissing (view MS.csFreshVars ss)

     unless (null missing) (failure loc (AmbiguousVars missing))


-- | Given a 'Term' that must be an external constant, extract the 'VarIndex'.
termId :: Term -> VarIndex
termId t =
  case asExtCns t of
    Just ec -> ecVarIndex ec
    _       -> error "termId expected a variable"


-- execute a pre/post condition
executeCond ::
  Options ->
  SharedContext ->
  JVMCrucibleContext ->
  CrucibleMethodSpecIR ->
  StateSpec ->
  OverrideMatcher CJ.JVM w ()
executeCond opts sc cc cs ss =
  do refreshTerms sc ss
     traverse_ (executeAllocation opts cc) (Map.assocs (ss ^. MS.csAllocs))
     traverse_ (executePointsTo opts sc cc cs) (ss ^. MS.csPointsTos)
     traverse_ (executeSetupCondition opts sc cc cs) (ss ^. MS.csConditions)


-- | Allocate fresh variables for all of the "fresh" vars
-- used in this phase and add them to the term substitution.
refreshTerms ::
  SharedContext {- ^ shared context -} ->
  StateSpec     {- ^ current phase spec -} ->
  OverrideMatcher CJ.JVM w ()
refreshTerms sc ss =
  do extension <- Map.fromList <$> traverse freshenTerm (view MS.csFreshVars ss)
     OM (termSub %= Map.union extension)
  where
    freshenTerm tt =
      case asExtCns (ttTerm tt) of
        Just ec -> do new <- liftIO (scFreshGlobal sc (ecName ec) (ecType ec))
                      return (termId (ttTerm tt), new)
        Nothing -> error "refreshTerms: not a variable"

------------------------------------------------------------------------

-- | Generate assertions that all of the memory allocations matched by
-- an override's precondition are disjoint.
enforceDisjointness ::
  JVMCrucibleContext -> W4.ProgramLoc -> StateSpec -> OverrideMatcher CJ.JVM w ()
enforceDisjointness _cc loc ss =
  do sym <- Ov.getSymInterface
     sub <- OM (use setupValueSub)
     let mems = Map.elems $ Map.intersectionWith (,) (view MS.csAllocs ss) sub

     -- Ensure that all regions are disjoint from each other.
     sequence_
        [ do c <- liftIO $ W4.notPred sym =<< CJ.refIsEqual sym p q
             addAssert c a

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
    checkPointsTo (JVMPointsToField _loc p _ _) = checkSetupValue p
    checkPointsTo (JVMPointsToElem _loc p _ _) = checkSetupValue p

    checkSetupValue :: SetupValue -> OverrideMatcher CJ.JVM w Bool
    checkSetupValue v =
      do m <- OM (use setupValueSub)
         return (all (`Map.member` m) (setupVars v))

    -- Compute the set of variable identifiers in a 'SetupValue'
    setupVars :: SetupValue -> Set AllocIndex
    setupVars v =
      case v of
        MS.SetupVar i                     -> Set.singleton i
        MS.SetupTerm _                    -> Set.empty
        MS.SetupNull ()                   -> Set.empty
        MS.SetupGlobal () _               -> Set.empty
        MS.SetupStruct empty _ _          -> absurd empty
        MS.SetupArray empty _             -> absurd empty
        MS.SetupElem empty _ _            -> absurd empty
        MS.SetupField empty _ _           -> absurd empty
        MS.SetupGlobalInitializer empty _ -> absurd empty


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
  do (_memTy, val') <- resolveSetupValueJVM opts cc sc spec val
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
  W4.ProgramLoc ->
  AllocIndex {- ^ variable index -} ->
  JVMRefVal  {- ^ concrete value -} ->
  OverrideMatcher CJ.JVM w ()

assignVar cc loc var ref =
  do old <- OM (setupValueSub . at var <<.= Just ref)
     let sym = cc ^. jccBackend
     for_ old $ \ref' ->
       do p <- liftIO (CJ.refIsEqual sym ref ref')
          addAssert p (Crucible.SimError loc (Crucible.AssertFailureSimError "equality of aliased pointers" ""))

------------------------------------------------------------------------


assignTerm ::
  SharedContext      {- ^ context for constructing SAW terms    -} ->
  JVMCrucibleContext    {- ^ context for interacting with Crucible -} ->
  W4.ProgramLoc ->
  PrePost                                                          ->
  VarIndex {- ^ external constant index -} ->
  Term     {- ^ value                   -} ->
  OverrideMatcher CJ.JVM w ()

assignTerm sc cc loc prepost var val =
  do mb <- OM (use (termSub . at var))
     case mb of
       Nothing -> OM (termSub . at var ?= val)
       Just old ->
         matchTerm sc cc loc prepost val old


------------------------------------------------------------------------

-- | Match the value of a function argument with a symbolic 'SetupValue'.
matchArg ::
  Options          {- ^ saw script print out opts -} ->
  SharedContext      {- ^ context for constructing SAW terms    -} ->
  JVMCrucibleContext    {- ^ context for interacting with Crucible -} ->
  CrucibleMethodSpecIR {- ^ specification for current function override  -} ->
  PrePost                                                          ->
  JVMVal             {- ^ concrete simulation value             -} ->
  J.Type             {- ^ expected memory type                  -} ->
  SetupValue         {- ^ expected specification value          -} ->
  OverrideMatcher CJ.JVM w ()

matchArg opts sc cc cs prepost actual expectedTy expected@(MS.SetupTerm expectedTT)
  | Cryptol.Forall [] [] tyexpr <- ttSchema expectedTT
  , Right tval <- Cryptol.evalType mempty tyexpr
  = do sym <- Ov.getSymInterface
       failMsg  <- mkStructuralMismatch opts cc sc cs actual expected expectedTy
       realTerm <- valueToSC sym (cs ^. MS.csLoc) failMsg tval actual
       matchTerm sc cc (cs ^. MS.csLoc) prepost realTerm (ttTerm expectedTT)

matchArg opts sc cc cs prepost actual@(RVal ref) expectedTy setupval =
  case setupval of
    MS.SetupVar var ->
      do assignVar cc (cs ^. MS.csLoc) var ref

    MS.SetupNull () ->
      do sym <- Ov.getSymInterface
         p   <- liftIO (CJ.refIsNull sym ref)
         addAssert p (Crucible.SimError (cs ^. MS.csLoc) (Crucible.AssertFailureSimError ("null-equality " ++ stateCond prepost) ""))

    MS.SetupGlobal () name ->
      do let mem = () -- FIXME cc^.ccLLVMEmptyMem
         sym  <- Ov.getSymInterface
         ref' <- liftIO $ doResolveGlobal sym mem name

         p  <- liftIO (CJ.refIsEqual sym ref ref')
         addAssert p (Crucible.SimError (cs ^. MS.csLoc) (Crucible.AssertFailureSimError ("global-equality " ++ stateCond prepost) ""))

    _ -> failure (cs ^. MS.csLoc) =<<
           mkStructuralMismatch opts cc sc cs actual setupval expectedTy

matchArg opts sc cc cs _prepost actual expectedTy expected =
  failure (cs ^. MS.csLoc) =<<
    mkStructuralMismatch opts cc sc cs actual expected expectedTy

------------------------------------------------------------------------

valueToSC ::
  Sym ->
  W4.ProgramLoc ->
  OverrideFailureReason CJ.JVM ->
  Cryptol.TValue ->
  JVMVal ->
  OverrideMatcher CJ.JVM w Term
valueToSC sym _ _ Cryptol.TVBit (IVal x) =
  do b <- liftIO $ W4.bvIsNonzero sym x
      -- TODO: assert that x is 0 or 1
     liftIO (CrucibleSAW.toSC sym b)

valueToSC sym _ _ (Cryptol.TVSeq _n Cryptol.TVBit) (IVal x) =
  liftIO (CrucibleSAW.toSC sym x)

valueToSC sym _ _ (Cryptol.TVSeq _n Cryptol.TVBit) (LVal x) =
  liftIO (CrucibleSAW.toSC sym x)

valueToSC _sym loc failMsg _tval _val =
  failure loc failMsg
-- TODO: check sizes on bitvectors, support bool, char, and short types

------------------------------------------------------------------------

-- | NOTE: The two 'Term' arguments must have the same type.
matchTerm ::
  SharedContext   {- ^ context for constructing SAW terms    -} ->
  JVMCrucibleContext {- ^ context for interacting with Crucible -} ->
  W4.ProgramLoc ->
  PrePost                                                       ->
  Term            {- ^ exported concrete term                -} ->
  Term            {- ^ expected specification term           -} ->
  OverrideMatcher CJ.JVM w ()

matchTerm _ _ _ _ real expect | real == expect = return ()
matchTerm sc cc loc prepost real expect =
  do free <- OM (use osFree)
     case unwrapTermF expect of
       FTermF (ExtCns ec)
         | Set.member (ecVarIndex ec) free ->
         do assignTerm sc cc loc prepost (ecVarIndex ec) real

       _ ->
         do t <- liftIO $ scEq sc real expect
            p <- liftIO $ resolveBoolTerm (cc ^. jccBackend) t
            addAssert p (Crucible.SimError loc (Crucible.AssertFailureSimError ("literal equality " ++ stateCond prepost) ""))

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
learnSetupCondition opts sc cc spec prepost (MS.SetupCond_Equal loc val1 val2)  = learnEqual opts sc cc spec loc prepost val1 val2
learnSetupCondition _opts sc cc _    prepost (MS.SetupCond_Pred loc tm)         = learnPred sc cc loc prepost (ttTerm tm)
learnSetupCondition _opts _ _ _ _ (MS.SetupCond_Ghost empty _ _ _) = absurd empty

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
learnPointsTo opts sc cc spec prepost pt = do
  let tyenv = MS.csAllocations spec
  let nameEnv = MS.csTypeNames spec
  sym <- Ov.getSymInterface
  globals <- OM (use overrideGlobals)
  case pt of

    JVMPointsToField loc ptr fname val ->
      do ty <- typeOfSetupValue cc tyenv nameEnv val
         (_, ptr') <- resolveSetupValueJVM opts cc sc spec ptr
         rval <- asRVal loc ptr'
         dyn <- liftIO $ CJ.doFieldLoad sym globals rval fname
         v <- liftIO $ projectJVMVal sym ty ("field load " ++ fname ++ ", " ++ show loc) dyn
         matchArg opts sc cc spec prepost v ty val

    JVMPointsToElem loc ptr idx val ->
      do ty <- typeOfSetupValue cc tyenv nameEnv val
         (_, ptr') <- resolveSetupValueJVM opts cc sc spec ptr
         rval <- asRVal loc ptr'
         dyn <- liftIO $ CJ.doArrayLoad sym globals rval idx
         v <- liftIO $ projectJVMVal sym ty ("array load " ++ show idx ++ ", " ++ show loc) dyn
         matchArg opts sc cc spec prepost v ty val


------------------------------------------------------------------------

stateCond :: PrePost -> String
stateCond PreState = "precondition"
stateCond PostState = "postcondition"

-- | Process a "crucible_equal" statement from the precondition
-- section of the CrucibleSetup block.
learnEqual ::
  Options                                          ->
  SharedContext                                    ->
  JVMCrucibleContext                                  ->
  CrucibleMethodSpecIR                             ->
  W4.ProgramLoc                                    ->
  PrePost                                          ->
  SetupValue       {- ^ first value to compare  -} ->
  SetupValue       {- ^ second value to compare -} ->
  OverrideMatcher CJ.JVM w ()
learnEqual opts sc cc spec loc prepost v1 v2 =
  do (_, val1) <- resolveSetupValueJVM opts cc sc spec v1
     (_, val2) <- resolveSetupValueJVM opts cc sc spec v2
     p         <- liftIO (equalValsPred cc val1 val2)
     let name = "equality " ++ stateCond prepost
     addAssert p (Crucible.SimError loc (Crucible.AssertFailureSimError name ""))

-- | Process a "crucible_precond" statement from the precondition
-- section of the CrucibleSetup block.
learnPred ::
  SharedContext                                                       ->
  JVMCrucibleContext                                                     ->
  W4.ProgramLoc                                                       ->
  PrePost                                                             ->
  Term             {- ^ the precondition to learn                  -} ->
  OverrideMatcher CJ.JVM w ()
learnPred sc cc loc prepost t =
  do s <- OM (use termSub)
     u <- liftIO $ scInstantiateExt sc s t
     p <- liftIO $ resolveBoolTerm (cc ^. jccBackend) u
     addAssert p (Crucible.SimError loc (Crucible.AssertFailureSimError (stateCond prepost) ""))

------------------------------------------------------------------------

-- TODO: replace (W4.ProgramLoc, J.Type) by some allocation datatype
-- that includes constructors for object allocations and array
-- allocations (with length).

-- | Perform an allocation as indicated by a 'crucible_alloc'
-- statement from the postcondition section.
executeAllocation ::
  Options                        ->
  JVMCrucibleContext                ->
  (AllocIndex, (W4.ProgramLoc, Allocation)) ->
  OverrideMatcher CJ.JVM w ()
executeAllocation opts cc (var, (loc, alloc)) =
  do liftIO $ printOutLn opts Debug $ unwords ["executeAllocation:", show var, show alloc]
     let jc = cc^.jccJVMContext
     let halloc = cc^.jccHandleAllocator
     sym <- Ov.getSymInterface
     globals <- OM (use overrideGlobals)
     (ptr, globals') <-
       case alloc of
         AllocObject cname -> liftIO $ CJ.doAllocateObject sym halloc jc cname globals
         AllocArray len elemTy -> liftIO $ CJ.doAllocateArray sym halloc jc len elemTy globals
     OM (overrideGlobals .= globals')
     assignVar cc loc var ptr

------------------------------------------------------------------------

-- | Update the simulator state based on the postconditions from the
-- procedure specification.
executeSetupCondition ::
  Options                    ->
  SharedContext              ->
  JVMCrucibleContext            ->
  CrucibleMethodSpecIR       ->
  SetupCondition             ->
  OverrideMatcher CJ.JVM w ()
executeSetupCondition opts sc cc spec (MS.SetupCond_Equal _loc val1 val2) = executeEqual opts sc cc spec val1 val2
executeSetupCondition _opts sc cc _    (MS.SetupCond_Pred _loc tm)        = executePred sc cc tm
executeSetupCondition _ _ _ _    (MS.SetupCond_Ghost empty _ _ _)        = absurd empty

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
executePointsTo opts sc cc spec pt = do
  sym <- Ov.getSymInterface
  globals <- OM (use overrideGlobals)
  case pt of

    JVMPointsToField loc ptr fname val ->
      do (_, val') <- resolveSetupValueJVM opts cc sc spec val
         (_, ptr') <- resolveSetupValueJVM opts cc sc spec ptr
         rval <- asRVal loc ptr'
         let dyn = injectJVMVal sym val'
         globals' <- liftIO $ CJ.doFieldStore sym globals rval fname dyn
         OM (overrideGlobals .= globals')

    JVMPointsToElem loc ptr idx val ->
      do (_, val') <- resolveSetupValueJVM opts cc sc spec val
         (_, ptr') <- resolveSetupValueJVM opts cc sc spec ptr
         rval <- asRVal loc ptr'
         let dyn = injectJVMVal sym val'
         globals' <- liftIO $ CJ.doArrayStore sym globals rval idx dyn
         OM (overrideGlobals .= globals')

------------------------------------------------------------------------


-- | Process a "crucible_equal" statement from the postcondition
-- section of the CrucibleSetup block.
executeEqual ::
  Options                                          ->
  SharedContext                                    ->
  JVMCrucibleContext                                  ->
  CrucibleMethodSpecIR                             ->
  SetupValue       {- ^ first value to compare  -} ->
  SetupValue       {- ^ second value to compare -} ->
  OverrideMatcher CJ.JVM w ()
executeEqual opts sc cc spec v1 v2 =
  do (_, val1) <- resolveSetupValueJVM opts cc sc spec v1
     (_, val2) <- resolveSetupValueJVM opts cc sc spec v2
     p         <- liftIO (equalValsPred cc val1 val2)
     addAssume p

-- | Process a "crucible_postcond" statement from the postcondition
-- section of the CrucibleSetup block.
executePred ::
  SharedContext   ->
  JVMCrucibleContext ->
  TypedTerm        {- ^ the term to assert as a postcondition -} ->
  OverrideMatcher CJ.JVM w ()
executePred sc cc tt =
  do s <- OM (use termSub)
     t <- liftIO $ scInstantiateExt sc s (ttTerm tt)
     p <- liftIO $ resolveBoolTerm (cc ^. jccBackend) t
     addAssume p

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
    MS.SetupGlobal () _               -> return v
    MS.SetupStruct empty _ _          -> absurd empty
    MS.SetupArray empty _             -> absurd empty
    MS.SetupElem empty _ _            -> absurd empty
    MS.SetupField empty _ _           -> absurd empty
    MS.SetupGlobalInitializer empty _ -> absurd empty
  where
    doTerm (TypedTerm schema t) = TypedTerm schema <$> scInstantiateExt sc s t

------------------------------------------------------------------------

resolveSetupValueJVM ::
  Options              ->
  JVMCrucibleContext      ->
  SharedContext        ->
  CrucibleMethodSpecIR ->
  SetupValue           ->
  OverrideMatcher CJ.JVM w (J.Type, JVMVal)
resolveSetupValueJVM opts cc sc spec sval =
  do m <- OM (use setupValueSub)
     s <- OM (use termSub)
     let tyenv = MS.csAllocations spec
         nameEnv = MS.csTypeNames spec
     memTy <- liftIO $ typeOfSetupValue cc tyenv nameEnv sval
     sval' <- liftIO $ instantiateSetupValue sc s sval
     lval  <- liftIO $ resolveSetupVal cc m tyenv nameEnv sval' `X.catch` handleException opts
     return (memTy, lval)

injectJVMVal :: Sym -> JVMVal -> Crucible.RegValue Sym CJ.JVMValueType
injectJVMVal sym jv =
  case jv of
    RVal x -> Crucible.injectVariant sym W4.knownRepr CJ.tagR x
    IVal x -> Crucible.injectVariant sym W4.knownRepr CJ.tagI x
    LVal x -> Crucible.injectVariant sym W4.knownRepr CJ.tagL x

projectJVMVal :: Sym -> J.Type -> String -> Crucible.RegValue Sym CJ.JVMValueType -> IO JVMVal
projectJVMVal sym ty msg' v =
  case ty of
    J.BooleanType -> err -- FIXME
    J.ByteType    -> err -- FIXME
    J.CharType    -> err -- FIXME
    J.ShortType   -> err -- FIXME
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
    proj val idx = Crucible.readPartExpr sym (Crucible.unVB (val Ctx.! idx)) msg

    msg = Crucible.GenericSimError $ "Ill-formed value for type " ++ show ty ++ " (" ++ msg' ++ ")"
    err = Crucible.addFailedAssertion sym msg

decodeJVMVal :: J.Type -> Crucible.AnyValue Sym -> Maybe JVMVal
decodeJVMVal ty v =
  case ty of
    J.BooleanType -> go v CJ.intRepr IVal
    J.ByteType    -> Nothing -- FIXME
    J.CharType    -> Nothing -- FIXME
    J.ShortType   -> Nothing -- FIXME
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

------------------------------------------------------------------------

asRVal :: W4.ProgramLoc -> JVMVal -> OverrideMatcher CJ.JVM w JVMRefVal
asRVal _ (RVal ptr) = return ptr
asRVal loc _ = failure loc BadPointerCast

doResolveGlobal :: Sym -> () -> String -> IO JVMRefVal
doResolveGlobal _sym _mem _name = fail "doResolveGlobal: FIXME"
-- FIXME: replace () with whatever type we need to look up global/static references
