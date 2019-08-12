{- |
Module      : SAWScript.Crucible.LLVM.Override
Description : Override matching and application for LLVM
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module SAWScript.Crucible.LLVM.Override
  ( OverrideMatcher(..)
  , runOverrideMatcher

  , setupValueSub
  , executeFreshPointer
  , omAsserts
  , omArgAsserts
  , termSub

  , doAlloc
  , learnCond
  , matchArg
  , methodSpecHandler
  , valueToSC
  , termId
  , storePointsToValue

  , enableSMTArrayMemoryModel
  ) where

import           Control.Lens
import           Control.Exception as X
import           Control.Monad.IO.Class (liftIO)
import           Control.Monad
import           Data.Either (partitionEithers)
import           Data.Foldable (for_, traverse_)
import           Data.List (tails)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe, catMaybes)
import           Data.Proxy
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as V
import           GHC.Generics (Generic)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import qualified Text.LLVM.AST as L

import qualified Cryptol.TypeCheck.AST as Cryptol (Schema(..))
import qualified Cryptol.Eval.Type as Cryptol (TValue(..), evalType)

import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Backend.SAWCore as Crucible
import qualified Lang.Crucible.Backend.SAWCore as CrucibleSAW
import qualified Lang.Crucible.Backend.Online as Crucible
import qualified Lang.Crucible.CFG.Core as Crucible (TypeRepr(UnitRepr))
import qualified Lang.Crucible.CFG.Extension.Safety as Crucible
import qualified Lang.Crucible.LLVM.MemModel as Crucible
import qualified Lang.Crucible.Simulator.OverrideSim as Crucible
import qualified Lang.Crucible.Simulator.RegMap as Crucible
import qualified Lang.Crucible.Simulator.SimError as Crucible

import qualified What4.BaseTypes as W4
import qualified What4.Config as W4
import qualified What4.Expr.Builder as W4
import qualified What4.Interface as W4
import qualified What4.LabeledPred as W4
import qualified What4.Partial as W4
import qualified What4.ProgramLoc as W4
import qualified What4.Symbol as W4

import qualified SAWScript.Crucible.LLVM.CrucibleLLVM as Crucible
import           SAWScript.Crucible.LLVM.CrucibleLLVM (LLVM)

import           Data.Parameterized.Classes ((:~:)(..), testEquality)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(..))

import           Verifier.SAW.SharedTerm
import           Verifier.SAW.Recognizer
import           Verifier.SAW.TypedTerm

import           SAWScript.Crucible.Common (Sym, LabeledPred)
import           SAWScript.Crucible.Common.MethodSpec (SetupValue(..), PointsTo)
import qualified SAWScript.Crucible.Common.MethodSpec as MS
import           SAWScript.Crucible.Common.MethodSpec (AllocIndex(..), PrePost(..))
import           SAWScript.Crucible.Common.Override
import           SAWScript.Crucible.LLVM.MethodSpecIR
import           SAWScript.Crucible.LLVM.ResolveSetupValue
import           SAWScript.Options
import           SAWScript.Utils (bullets, handleException)

type instance Pointer (LLVM arch) = LLVMPtr (Crucible.ArchWidth arch)

-- | An override packaged together with its preconditions, labeled with some
--   human-readable info about each condition.
data OverrideWithPreconditions arch =
  OverrideWithPreconditions
    { _owpPreconditions :: [LabeledPred Sym] -- ^ c.f. '_omAsserts'
    , _owpMethodSpec :: MS.CrucibleMethodSpecIR (LLVM arch)
    , owpState :: OverrideMatcherRW (LLVM arch)
    }
  deriving (Generic)

makeLenses ''OverrideWithPreconditions

------------------------------------------------------------------------
-- Translating SAW values to Crucible values for good error messages

ppLLVMVal ::
  LLVMCrucibleContext arch ->
  LLVMVal ->
  OverrideMatcher (LLVM arch) w PP.Doc
ppLLVMVal cc val = do
  sym <- getSymInterface
  mem <- readGlobal (Crucible.llvmMemVar (cc^.ccLLVMContext))
  liftIO $ Crucible.ppLLVMValWithGlobals sym (Crucible.memImplGlobalMap mem) val

-- | Resolve a 'SetupValue' into a 'LLVMVal' and pretty-print it
ppSetupValueAsLLVMVal ::
  (Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options              {- ^ output/verbosity options -} ->
  LLVMCrucibleContext arch ->
  SharedContext {- ^ context for constructing SAW terms -} ->
  MS.CrucibleMethodSpecIR (LLVM arch) {- ^ for name and typing environments -} ->
  SetupValue (Crucible.LLVM arch) ->
  OverrideMatcher (LLVM arch) w PP.Doc
ppSetupValueAsLLVMVal opts cc sc spec setupval = do
  (_memTy, llvmval) <- resolveSetupValueLLVM opts cc sc spec setupval
  ppLLVMVal cc llvmval

-- | Try to translate the spec\'s 'SetupValue' into an 'LLVMVal', pretty-print
--   the 'LLVMVal'.
mkStructuralMismatch ::
  (Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options              {- ^ output/verbosity options -} ->
  LLVMCrucibleContext arch ->
  SharedContext {- ^ context for constructing SAW terms -} ->
  MS.CrucibleMethodSpecIR (LLVM arch) {- ^ for name and typing environments -} ->
  Crucible.LLVMVal Sym {- ^ the value from the simulator -} ->
  SetupValue (Crucible.LLVM arch)           {- ^ the value from the spec -} ->
  Crucible.MemType     {- ^ the expected type -} ->
  OverrideMatcher (LLVM arch) w (OverrideFailureReason (LLVM arch))
mkStructuralMismatch _opts cc _sc spec llvmval setupval memTy =
  let tyEnv = MS.csAllocations spec
      nameEnv = MS.csTypeNames spec
      maybeTy = typeOfSetupValue cc tyEnv nameEnv setupval
  in pure $ StructuralMismatch
              (PP.pretty llvmval)
              (MS.ppSetupValue setupval)
              maybeTy
              memTy

-- | Instead of using 'ppPointsTo', which prints 'SetupValue', translate
--   expressions to 'LLVMVal'.
ppPointsToAsLLVMVal ::
  (Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options              {- ^ output/verbosity options -} ->
  LLVMCrucibleContext arch ->
  SharedContext {- ^ context for constructing SAW terms -} ->
  MS.CrucibleMethodSpecIR (LLVM arch) {- ^ for name and typing environments -} ->
  PointsTo (LLVM arch) ->
  OverrideMatcher (LLVM arch) w PP.Doc
ppPointsToAsLLVMVal opts cc sc spec (LLVMPointsTo loc setupVal1 setupVal2) = do
  pretty1 <- ppSetupValueAsLLVMVal opts cc sc spec setupVal1
  pretty2 <- ppSetupValueAsLLVMVal opts cc sc spec setupVal2
  pure $ PP.vcat [ PP.text "Pointer:" PP.<+> pretty1
                 , PP.text "Pointee:" PP.<+> pretty2
                 , PP.text "Assertion made at:" PP.<+>
                   PP.pretty (W4.plSourceLoc loc)
                 ]

-- | Create an error stating that the 'LLVMVal' was not equal to the 'SetupValue'
notEqual ::
  (Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  PrePost ->
  Options              {- ^ output/verbosity options -} ->
  W4.ProgramLoc        {- ^ where is the assertion from? -} ->
  LLVMCrucibleContext arch ->
  SharedContext {- ^ context for constructing SAW terms -} ->
  MS.CrucibleMethodSpecIR (LLVM arch) {- ^ for name and typing environments -} ->
  SetupValue (Crucible.LLVM arch)           {- ^ the value from the spec -} ->
  Crucible.LLVMVal Sym {- ^ the value from the simulator -} ->
  OverrideMatcher (LLVM arch) w Crucible.SimError
notEqual cond opts loc cc sc spec expected actual = do
  prettyLLVMVal      <- ppLLVMVal cc actual
  prettySetupLLVMVal <- ppSetupValueAsLLVMVal opts cc sc spec expected
  pure $
    Crucible.SimError loc $ Crucible.AssertFailureSimError $ unlines $
      [ "Equality " ++ stateCond cond
      , "Expected value (as a SAW value): "
      , show (MS.ppSetupValue expected)
      , "Expected value (as a Crucible value): "
      , show prettySetupLLVMVal
      , "Actual value: "
      , show prettyLLVMVal
      ]

------------------------------------------------------------------------

-- | Partition into three groups:
--   * Preconditions concretely succeed
--   * Preconditions concretely fail
--   * Preconditions are symbolic
partitionOWPsConcrete :: forall arch.
  Sym ->
  [OverrideWithPreconditions arch] ->
  IO ([OverrideWithPreconditions arch], [OverrideWithPreconditions arch], [OverrideWithPreconditions arch])
partitionOWPsConcrete sym =
  let traversal = owpPreconditions . each . W4.labeledPred
  in W4.partitionByPredsM (Just sym) $
       foldlMOf traversal (W4.andPred sym) (W4.truePred sym)

-- | Like 'W4.partitionByPreds', but partitions on solver responses, not just
--   concretized values.
partitionBySymbolicPreds ::
  (Foldable t) =>
  Sym {- ^ solver connection -} ->
  (a -> W4.Pred Sym) {- ^ how to extract predicates -} ->
  t a ->
  IO (Map Crucible.BranchResult [a])
partitionBySymbolicPreds sym getPred =
  let step mp a =
        CrucibleSAW.considerSatisfiability sym Nothing (getPred a) <&> \k ->
          Map.insertWith (++) k [a] mp
  in foldM step Map.empty

-- | Find individual preconditions that are symbolically false
--
-- We should probably be using unsat cores for this.
findFalsePreconditions ::
  Sym ->
  OverrideWithPreconditions arch ->
  IO [LabeledPred Sym]
findFalsePreconditions sym owp =
  fromMaybe [] . Map.lookup (Crucible.NoBranch False) <$>
    partitionBySymbolicPreds sym (view W4.labeledPred) (owp ^. owpPreconditions)

-- | Is this group of predicates collectively unsatisfiable?
unsatPreconditions ::
  Sym {- ^ solver connection -} ->
  Fold s (W4.Pred Sym) {- ^ how to extract predicates -} ->
  s {- ^ a container full of predicates -}->
  IO Bool
unsatPreconditions sym container getPreds = do
  conj <- W4.andAllOf sym container getPreds
  CrucibleSAW.considerSatisfiability sym Nothing conj >>=
    \case
      Crucible.NoBranch False -> pure True
      _ -> pure False

-- | Print a message about failure of an override's preconditions
ppFailure ::
  OverrideWithPreconditions arch ->
  [LabeledPred Sym] ->
  PP.Doc
ppFailure owp false =
  MS.ppMethodSpec (owp ^. owpMethodSpec)
     PP.<$$> bullets '*' (map Crucible.ppSimError
                              (false ^.. traverse . W4.labeledPredMsg))

-- | Print a message about concrete failure of an override's preconditions
--
-- Assumes that the override it's being passed does have concretely failing
-- preconditions. Otherwise, the error won't make much sense.
ppConcreteFailure :: OverrideWithPreconditions arch -> PP.Doc
ppConcreteFailure owp =
  let (_, false, _) =
        W4.partitionLabeledPreds (Proxy :: Proxy Sym) (owp ^. owpPreconditions)
  in ppFailure owp false

-- | Print a message about symbolic failure of an override's preconditions
--
-- TODO: Needs additional testing. Are these messages useful?
{-
ppSymbolicFailure ::
  (OverrideWithPreconditions arch, [LabeledPred Sym]) ->
  PP.Doc
ppSymbolicFailure = uncurry ppFailure
-}

-- | This function is responsible for implementing the \"override\" behavior
--   of method specifications.  The main work done in this function to manage
--   the process of selecting between several possible different override
--   specifications that could apply.  We want a proof to succeed if _any_
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
  forall arch rtp args ret.
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options                  {- ^ output/verbosity options                     -} ->
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  LLVMCrucibleContext arch     {- ^ context for interacting with Crucible        -} ->
  W4.ProgramLoc            {- ^ Location of the call site for error reporting-} ->
  [MS.CrucibleMethodSpecIR (LLVM arch)]   {- ^ specification for current function override  -} ->
  Crucible.TypeRepr ret    {- ^ type representation of function return value -} ->
  Crucible.OverrideSim (Crucible.SAWCruciblePersonality Sym) Sym (Crucible.LLVM arch) rtp args ret
     (Crucible.RegValue Sym ret)
methodSpecHandler opts sc cc top_loc css retTy = do
  liftIO $ printOutLn opts Info $ unwords
    [ "Matching"
    , show (length css)
    , "overrides of "
    , ((head css)^.csName)
    , "..."
    ]
  sym <- Crucible.getSymInterface
  Crucible.RegMap args <- Crucible.getOverrideArgs

  -- First, run the precondition matcher phase.  Collect together a list of the results.
  -- For each override, this will either be an error message, or a matcher state and
  -- a method spec.
  prestates <-
    do g0 <- Crucible.readGlobals
       forM css $ \cs -> liftIO $
         let initialFree = Set.fromList (map (termId . ttTerm)
                                           (view (MS.csPreState . MS.csFreshVars) cs))
          in runOverrideMatcher sym g0 Map.empty Map.empty initialFree (view MS.csLoc cs)
                      (do methodSpecHandler_prestate opts sc cc args cs
                          return cs)

  -- Print a failure message if all overrides failed to match.  Otherwise, collect
  -- all the override states that might apply, and compute the conjunction of all
  -- the preconditions.  We'll use these to perform symbolic branches between the
  -- various overrides.
  branches <-
    let prettyError methodSpec failureReason =
          MS.ppMethodSpec methodSpec PP.<$$> ppOverrideFailure failureReason
    in
      case partitionEithers prestates of
        (errs, []) ->
          fail $ show $
            PP.text "All overrides failed during structural matching:"
            PP.<$$>
              PP.vcat
                (map (\(cs, err) ->
                        PP.text "*" PP.<> PP.indent 2 (prettyError cs err))
                    (zip css errs))
            PP.<$$> PP.text "Actual function return type: " PP.<>
                      PP.text (show (retTy))
        (_, ss) -> liftIO $
          forM ss $ \(cs, omrw) ->
            return (OverrideWithPreconditions (omrw ^. omAsserts) cs omrw)

  -- Now we do a second phase of simple compatibility checking: we check to see
  -- if any of the preconditions of the various overrides are concretely false.
  -- If so, there's no use in branching on them with @symbolicBranches@.
  (true, false, unknown) <- liftIO $ partitionOWPsConcrete sym branches

  -- Collapse the preconditions to a single predicate
  branches' <- liftIO $ forM (true ++ unknown) $
    \(OverrideWithPreconditions preconds cs omrw) ->
      W4.andAllOf sym (folded . W4.labeledPred) preconds <&>
        \precond -> (precond, cs, omrw)

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
  liftIO $ printOutLn opts Info $ unwords
    [ "Branching on"
    , show (length branches')
    , "override variants of"
    , ((head css)^.csName)
    , "..."
    ]
  res <- Crucible.regValue <$> Crucible.callOverride
     (Crucible.mkOverride' "overrideBranches" retTy
       (Crucible.symbolicBranches Crucible.emptyRegMap $
         [ ( precond
           , do g <- Crucible.readGlobals
                res <- liftIO $ runOverrideMatcher sym g
                   (omrw^.setupValueSub)
                   (omrw^.termSub)
                   (omrw^.omFree)
                   top_loc
                   (methodSpecHandler_poststate opts sc cc retTy cs)
                case res of
                  Left (OF loc rsn)  ->
                    -- TODO, better pretty printing for reasons
                    liftIO $ Crucible.abortExecBecause
                      (Crucible.AssumedFalse (Crucible.AssumptionReason loc (show rsn)))
                  Right (ret,omrw') ->
                    do liftIO $ forM_ (omrw'^.omAssumes) $ \asum ->
                         Crucible.addAssumption (cc^.ccBackend)
                            (Crucible.LabeledPred asum
                              (Crucible.AssumptionReason top_loc "override postcondition"))
                       Crucible.writeGlobals (omrw'^.omGlobals)
                       Crucible.overrideReturn' (Crucible.RegEntry retTy ret)
           , Just (W4.plSourceLoc top_loc)
           )
         | (precond, cs, omrw) <- branches'
         ] ++
         [ let fnName = case branches of
                         owp : _  -> owp ^. owpMethodSpec . MS.csMethod . llvmMethodName
                         _        -> "<unknown function>"

               e symFalse unsat = show $ PP.vcat $ concat
                 [ [ PP.text $
                     "No override specification applies for " ++ fnName ++ "."
                   ]
                 , if | not (null false) ->
                        [ PP.text (unwords
                            [ "The following overrides had some preconditions"
                            , "that failed concretely:"
                            ]) PP.<$$> bullets '-' (map ppConcreteFailure false)
                        ]
                      -- See comment on ppSymbolicFailure: this needs more
                      -- examination to see if it's useful.
                      -- - | not (null symFalse) ->
                      --   [ PP.text (unwords
                      --       [ "The following overrides had some preconditions "
                      --       , "that failed symbolically:"
                      --       ]) PP.<$$> bullets '-' (map ppSymbolicFailure symFalse)
                      --   ]

                      -- Note that we only print these in case no override had
                      -- individually (concretely or symbolically) false
                      -- preconditions.
                      | not (null unsat) && null false && null symFalse ->
                        [ PP.text (unwords
                          [ "The conjunction of these overrides' preconditions"
                          , "was unsatisfiable, meaning your override can never"
                          , "apply. You probably have unintentionally specified"
                          , "mutually exclusive/inconsistent preconditions."
                          ]) PP.<$$>
                          bullets '-' (unsat ^.. each . owpMethodSpec . to MS.ppMethodSpec)
                        ]
                      | null false && null symFalse ->
                        [ PP.text (unwords
                            [ "No overrides had any single concretely or"
                            , "symbolically failing preconditions."
                            ])
                        ]
                      | otherwise -> []
                 , if | simVerbose opts < 3 ->
                        [ PP.text $ unwords
                          [ "Run SAW with --sim-verbose=3 to see a description"
                          , "of each override."
                          ]
                        ]
                      | otherwise ->
                        [ PP.text "Here are the descriptions of each override:"
                          PP.<$$>
                          bullets '-'
                            (branches ^.. each . owpMethodSpec . to MS.ppMethodSpec)
                        ]
                 ]
           in ( W4.truePred sym
              , liftIO $ do
                  -- Now that we're failing, do the additional work of figuring out
                  -- if any overrides had symbolically false preconditions
                  symFalse <- catMaybes <$> (forM unknown $ \owp ->
                    findFalsePreconditions sym owp <&>
                      \case
                        [] -> Nothing
                        ps -> Just (owp, ps))

                  unsat <-
                    filterM
                      (unsatPreconditions sym (owpPreconditions . each . W4.labeledPred))
                      branches

                  Crucible.addFailedAssertion sym
                    (Crucible.GenericSimError (e symFalse unsat))
              , Just (W4.plSourceLoc top_loc)
              )
         ]))
     (Crucible.RegMap args)
  liftIO $ printOutLn opts Info $
    unwords ["Applied override!", ((head css)^.csName)]
  return res

------------------------------------------------------------------------

-- | Use a method spec to override the behavior of a function.
--   This function computes the pre-state portion of the override,
--   which involves reading values from arguments and memory and computing
--   substitutions for the setup value variables, and computing precondition
--   predicates.
methodSpecHandler_prestate ::
  forall arch ctx.
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options                  {- ^ output/verbosity options                     -} ->
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  LLVMCrucibleContext arch     {- ^ context for interacting with Crucible        -} ->
  Ctx.Assignment (Crucible.RegEntry Sym) ctx
                           {- ^ the arguments to the function -} ->
  MS.CrucibleMethodSpecIR (LLVM arch) {- ^ specification for current function override  -} ->
  OverrideMatcher (LLVM arch) RO ()
methodSpecHandler_prestate opts sc cc args cs =
    do let expectedArgTypes = Map.elems (cs ^. MS.csArgBindings)

       sym <- getSymInterface

       let aux (memTy, setupVal) (Crucible.AnyValue tyrep val) =
             do storTy <- Crucible.toStorableType memTy
                pmv <- Crucible.packMemValue sym storTy tyrep val
                return (pmv, memTy, setupVal)

       -- todo: fail if list lengths mismatch
       xs <- liftIO (zipWithM aux expectedArgTypes (assignmentToList args))

       sequence_ [ matchArg opts sc cc cs PreState x y z | (x, y, z) <- xs]

       learnCond opts sc cc cs PreState (cs ^. MS.csPreState)


-- | Use a method spec to override the behavior of a function.
--   This function computes the post-state portion of the override,
--   which involves writing values into memory, computing the return value,
--   and computing postcondition predicates.
methodSpecHandler_poststate ::
  forall arch ret.
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options                  {- ^ output/verbosity options                     -} ->
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  LLVMCrucibleContext arch     {- ^ context for interacting with Crucible        -} ->
  Crucible.TypeRepr ret    {- ^ type representation of function return value -} ->
  MS.CrucibleMethodSpecIR (LLVM arch)     {- ^ specification for current function override  -} ->
  OverrideMatcher (LLVM arch) RW (Crucible.RegValue Sym ret)
methodSpecHandler_poststate opts sc cc retTy cs =
  do executeCond opts sc cc cs (cs ^. MS.csPostState)
     computeReturnValue opts cc sc cs retTy (cs ^. MS.csRetValue)

-- learn pre/post condition
learnCond :: (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch))
          => Options
          -> SharedContext
          -> LLVMCrucibleContext arch
          -> MS.CrucibleMethodSpecIR (LLVM arch)
          -> PrePost
          -> MS.StateSpec (LLVM arch)
          -> OverrideMatcher (LLVM arch) md ()
learnCond opts sc cc cs prepost ss = do
  let loc = cs ^. MS.csLoc
  matchPointsTos opts sc cc cs prepost (ss ^. MS.csPointsTos)
  traverse_ (learnSetupCondition opts sc cc cs prepost) (ss ^. MS.csConditions)
  enforceDisjointness loc ss
  enforceCompleteSubstitution loc ss


-- | Verify that all of the fresh variables for the given
-- state spec have been "learned". If not, throws
-- 'AmbiguousVars' exception.
enforceCompleteSubstitution ::
  W4.ProgramLoc ->
  MS.StateSpec (LLVM arch) ->
  OverrideMatcher (LLVM arch) md ()
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
executeCond :: (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch))
            => Options
            -> SharedContext
            -> LLVMCrucibleContext arch
            -> MS.CrucibleMethodSpecIR (LLVM arch)
            -> MS.StateSpec (LLVM arch)
            -> OverrideMatcher (LLVM arch) RW ()
executeCond opts sc cc cs ss = do
  refreshTerms sc ss

  ptrs <- liftIO $ Map.traverseWithKey
            (\k _memty -> executeFreshPointer cc k)
            (ss ^. MS.csFreshPointers)
  OM (setupValueSub %= Map.union ptrs)

  traverse_ (executeAllocation opts cc) (Map.assocs (ss ^. MS.csAllocs))
  traverse_ (executePointsTo opts sc cc cs) (ss ^. MS.csPointsTos)
  traverse_ (executeSetupCondition opts sc cc cs) (ss ^. MS.csConditions)


-- | Allocate fresh variables for all of the "fresh" vars
-- used in this phase and add them to the term substitution.
refreshTerms ::
  SharedContext {- ^ shared context -} ->
  MS.StateSpec (LLVM arch)    {- ^ current phase spec -} ->
  OverrideMatcher (LLVM arch) md ()
refreshTerms sc ss =
  do extension <- Map.fromList <$> traverse freshenTerm (view MS.csFreshVars ss)
     OM (termSub %= Map.union extension)
  where
    freshenTerm tt =
      case asExtCns (ttTerm tt) of
        Just ec -> do new <- liftIO (mkTypedTerm sc =<< scFreshGlobal sc (ecName ec) (ecType ec))
                      return (termId (ttTerm tt), ttTerm new)
        Nothing -> error "refreshTerms: not a variable"

------------------------------------------------------------------------

-- | Generate assertions that all of the memory allocations matched by
-- an override's precondition are disjoint. Read-only allocations are
-- allowed to alias other read-only allocations, however.
enforceDisjointness ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  W4.ProgramLoc ->
  MS.StateSpec (LLVM arch) ->
  OverrideMatcher (LLVM arch) md ()
enforceDisjointness loc ss =
  do sym <- getSymInterface
     sub <- OM (use setupValueSub)
     let (allocsRW, allocsRO) = Map.partition (view isMut) (view MS.csAllocs ss)
         memsRW = Map.elems $ Map.intersectionWith (,) allocsRW sub
         memsRO = Map.elems $ Map.intersectionWith (,) allocsRO sub

     -- Ensure that all RW regions are disjoint from each other, and
     -- that all RW regions are disjoint from all RO regions.
     sequence_
        [ do c <- liftIO $
               do W4.setCurrentProgramLoc sym ploc
                  psz' <- W4.bvLit sym Crucible.PtrWidth $ Crucible.bytesToInteger psz
                  W4.setCurrentProgramLoc sym qloc
                  qsz' <- W4.bvLit sym Crucible.PtrWidth $ Crucible.bytesToInteger qsz
                  W4.setCurrentProgramLoc sym loc
                  Crucible.buildDisjointRegionsAssertion
                    sym Crucible.PtrWidth
                    p psz'
                    q qsz'
             addAssert c $ Crucible.SimError loc $
               Crucible.AssertFailureSimError $
                 "Memory regions not disjoint: "
                   ++ "(base=" ++ show (Crucible.ppPtr p) ++ ", size=" ++ show psz ++ ")"
                   ++ " and "
                   ++ "(base=" ++ show (Crucible.ppPtr q) ++ ", size=" ++ show qsz ++ ")"

        | (LLVMAllocSpec _mut _pty psz ploc, p) : ps <- tails memsRW
        , (LLVMAllocSpec _mut _qty qsz qloc, q) <- ps ++ memsRO
        ]

------------------------------------------------------------------------

-- | For each points-to statement read the memory value through the
-- given pointer (lhs) and match the value against the given pattern
-- (rhs).  Statements are processed in dependency order: a points-to
-- statement cannot be executed until bindings for any/all lhs
-- variables exist.
matchPointsTos :: forall arch md.
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options          {- ^ saw script print out opts -} ->
  SharedContext    {- ^ term construction context -} ->
  LLVMCrucibleContext arch {- ^ simulator context     -} ->
  MS.CrucibleMethodSpecIR (LLVM arch)                               ->
  PrePost                                            ->
  [PointsTo (LLVM arch)]       {- ^ points-tos                -} ->
  OverrideMatcher (LLVM arch) md ()
matchPointsTos opts sc cc spec prepost = go False []
  where
    go ::
      Bool       {- progress indicator -} ->
      [PointsTo (LLVM arch)] {- delayed conditions -} ->
      [PointsTo (LLVM arch)] {- queued conditions  -} ->
      OverrideMatcher (LLVM arch) md ()

    -- all conditions processed, success
    go _ [] [] = return ()

    -- not all conditions processed, no progress, failure
    go False delayed [] = failure (spec ^. MS.csLoc) (AmbiguousPointsTos delayed)

    -- not all conditions processed, progress made, resume delayed conditions
    go True delayed [] = go False [] delayed

    -- progress the next points-to in the work queue
    go progress delayed (c@(LLVMPointsTo loc _ _):cs) =
      do ready <- checkPointsTo c
         if ready then
           do err <- learnPointsTo opts sc cc spec prepost c
              case err of
                Just msg -> do
                  doc <- ppPointsToAsLLVMVal opts cc sc spec c
                  failure loc (BadPointerLoad (Right doc) msg)
                Nothing  -> go True delayed cs
         else
           do go progress (c:delayed) cs

    -- determine if a precondition is ready to be checked
    checkPointsTo :: PointsTo (LLVM arch) -> OverrideMatcher (LLVM arch) md Bool
    checkPointsTo (LLVMPointsTo _loc p _) = checkSetupValue p

    checkSetupValue :: SetupValue (Crucible.LLVM arch) -> OverrideMatcher (LLVM arch) md Bool
    checkSetupValue v =
      do m <- OM (use setupValueSub)
         return (all (`Map.member` m) (setupVars v))

    -- Compute the set of variable identifiers in a 'SetupValue'
    setupVars :: SetupValue (Crucible.LLVM arch) -> Set AllocIndex
    setupVars v =
      case v of
        SetupVar i                 -> Set.singleton i
        SetupStruct _ _ xs         -> foldMap setupVars xs
        SetupArray _ xs            -> foldMap setupVars xs
        SetupElem _ x _            -> setupVars x
        SetupField _ x _           -> setupVars x
        SetupTerm _                -> Set.empty
        SetupNull _                -> Set.empty
        SetupGlobal _ _            -> Set.empty
        SetupGlobalInitializer _ _ -> Set.empty


------------------------------------------------------------------------

computeReturnValue ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options               {- ^ saw script debug and print options     -} ->
  LLVMCrucibleContext arch  {- ^ context of the crucible simulation     -} ->
  SharedContext         {- ^ context for generating saw terms       -} ->
  MS.CrucibleMethodSpecIR (LLVM arch)  {- ^ method specification                   -} ->
  Crucible.TypeRepr ret {- ^ representation of function return type -} ->
  Maybe (SetupValue (LLVM arch)) {- ^ optional symbolic return value -} ->
  OverrideMatcher (LLVM arch) md (Crucible.RegValue Sym ret)
                        {- ^ concrete return value                  -}

computeReturnValue _opts _cc _sc spec ty Nothing =
  case ty of
    Crucible.UnitRepr -> return ()
    _ -> failure (spec ^. MS.csLoc) (BadReturnSpecification (Some ty))

computeReturnValue opts cc sc spec ty (Just val) =
  do (_memTy, xval) <- resolveSetupValue opts cc sc spec ty val
     return xval


------------------------------------------------------------------------

-- | Assign the given pointer value to the given allocation index in
-- the current substitution. If there is already a binding for this
-- index, then add a pointer-equality constraint.
assignVar ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  LLVMCrucibleContext arch {- ^ context for interacting with Crucible -} ->
  W4.ProgramLoc ->
  AllocIndex      {- ^ variable index -} ->
  LLVMPtr (Crucible.ArchWidth arch) {- ^ concrete value -} ->
  OverrideMatcher (LLVM arch) md ()

assignVar cc loc var val =
  do old <- OM (setupValueSub . at var <<.= Just val)
     for_ old $ \val' ->
       do p <- liftIO (equalValsPred cc (Crucible.ptrToPtrVal val') (Crucible.ptrToPtrVal val))
          addAssert p $ Crucible.SimError loc $ Crucible.AssertFailureSimError $ unlines
            [ "The following pointers had to alias, but they didn't:"
            , "  " ++ show (Crucible.ppPtr val)
            , "  " ++ show (Crucible.ppPtr val')
            ]

------------------------------------------------------------------------

-- | Match the value of a function argument with a symbolic 'SetupValue'.
matchArg ::
  Options          {- ^ saw script print out opts -} ->
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  SharedContext      {- ^ context for constructing SAW terms    -} ->
  LLVMCrucibleContext arch {- ^ context for interacting with Crucible -} ->
  MS.CrucibleMethodSpecIR (LLVM arch) {- ^ specification for current function override  -} ->
  PrePost                                                          ->
  Crucible.LLVMVal Sym
                     {- ^ concrete simulation value             -} ->
  Crucible.MemType   {- ^ expected memory type                  -} ->
  SetupValue (Crucible.LLVM arch)         {- ^ expected specification value          -} ->
  OverrideMatcher (LLVM arch) md ()

matchArg opts sc cc cs prepost actual expectedTy expected =
  case (actual, expectedTy, expected) of
    (_, _, SetupTerm expectedTT)
      | Cryptol.Forall [] [] tyexpr <- ttSchema expectedTT
      , Right tval <- Cryptol.evalType mempty tyexpr
        -> do sym      <- getSymInterface
              failMsg  <- mkStructuralMismatch opts cc sc cs actual expected expectedTy
              realTerm <- valueToSC sym (cs ^. MS.csLoc) failMsg tval actual
              matchTerm sc (cc ^. ccBackend) (cs ^. MS.csLoc) prepost realTerm (ttTerm expectedTT)

    -- match the fields of struct point-wise
    (Crucible.LLVMValStruct xs, Crucible.StructType fields, SetupStruct () _ zs) ->
      sequence_
        [ matchArg opts sc cc cs prepost x y z
        | ((_,x),y,z) <- zip3 (V.toList xs)
                              (V.toList (Crucible.fiType <$> Crucible.siFields fields))
                              zs ]

    (_, Crucible.PtrType _, SetupElem () _ _) -> resolveAndMatch
    (_, Crucible.PtrType _, SetupField () _ _) -> resolveAndMatch
    (_, _, SetupGlobalInitializer () _) -> resolveAndMatch

    (Crucible.LLVMValInt blk off, _, _) ->
      case expected of
        SetupVar var | Just Refl <- testEquality (W4.bvWidth off) Crucible.PtrWidth ->
          do assignVar cc (cs ^. MS.csLoc) var (Crucible.LLVMPointer blk off)

        SetupNull () | Just Refl <- testEquality (W4.bvWidth off) Crucible.PtrWidth ->
          do sym <- getSymInterface
             p   <- liftIO (Crucible.ptrIsNull sym Crucible.PtrWidth (Crucible.LLVMPointer blk off))
             addAssert p =<<
               notEqual prepost opts (cs ^. MS.csLoc) cc sc cs expected actual

        SetupGlobal () name | Just Refl <- testEquality (W4.bvWidth off) Crucible.PtrWidth ->
          do let mem = cc^.ccLLVMEmptyMem
             sym  <- getSymInterface
             ptr2 <- liftIO $ Crucible.doResolveGlobal sym mem (L.Symbol name)
             pred_ <- liftIO $
               Crucible.ptrEq sym Crucible.PtrWidth (Crucible.LLVMPointer blk off) ptr2
             addAssert pred_ =<<
               notEqual prepost opts (cs ^. MS.csLoc) cc sc cs expected actual

        _ -> failure (cs ^. MS.csLoc) =<<
              mkStructuralMismatch opts cc sc cs actual expected expectedTy

    _ -> failure (cs ^. MS.csLoc) =<<
           mkStructuralMismatch opts cc sc cs actual expected expectedTy

  where
    resolveAndMatch = do
      (ty, val) <- resolveSetupValueLLVM opts cc sc cs expected
      sym  <- getSymInterface
      if expectedTy /= ty
      then failure (cs ^. MS.csLoc) =<<
            mkStructuralMismatch opts cc sc cs actual expected expectedTy
      else liftIO (Crucible.testEqual sym val actual) >>=
        \case
          Nothing -> failure (cs ^. MS.csLoc) BadEqualityComparison
          Just pred_ ->
            addAssert pred_ =<<
              notEqual prepost opts (cs ^. MS.csLoc) cc sc cs expected actual

------------------------------------------------------------------------

zeroValueSC :: SharedContext -> Crucible.StorageType -> IO Term
zeroValueSC sc tp = case Crucible.storageTypeF tp of
  Crucible.Float -> fail "zeroValueSC: float unsupported"
  Crucible.Double -> fail "zeroValueSC: double unsupported"
  Crucible.X86_FP80 -> fail "zeroValueSC: X86_FP80 unsupported"
  Crucible.Bitvector bs ->
    do n <- scNat sc (Crucible.bytesToBits bs)
       z <- scNat sc 0
       scBvNat sc n z
  Crucible.Array n tp' ->
    do sctp <- typeToSC sc tp'
       v <- zeroValueSC sc tp'
       scVector sc sctp (replicate (fromIntegral n) v)
  Crucible.Struct fs ->
    do tms <- mapM (zeroValueSC sc . view Crucible.fieldVal) (V.toList fs)
       scTuple sc tms

valueToSC ::
  Sym ->
  W4.ProgramLoc ->
  OverrideFailureReason (LLVM arch) ->
  Cryptol.TValue ->
  Crucible.LLVMVal Sym  ->
  OverrideMatcher (LLVM arch) md Term
valueToSC sym _loc _failMsg _ts (Crucible.LLVMValZero gtp)
  = liftIO $
     do sc <- Crucible.sawBackendSharedContext sym
        zeroValueSC sc gtp

valueToSC sym loc failMsg (Cryptol.TVTuple tys) (Crucible.LLVMValStruct vals)
  | length tys == length vals
  = do terms <- traverse (\(ty, tm) -> valueToSC sym loc failMsg ty (snd tm)) (zip tys (V.toList vals))
       sc <- liftIO $ Crucible.sawBackendSharedContext sym
       liftIO (scTupleReduced sc terms)

valueToSC sym loc failMsg (Cryptol.TVSeq _n Cryptol.TVBit) (Crucible.LLVMValInt base off) =
  do baseZero <- liftIO (W4.natEq sym base =<< W4.natLit sym 0)
     offTm    <- liftIO (Crucible.toSC sym off)
     case W4.asConstantPred baseZero of
       Just True  -> return offTm
       Just False -> failure loc failMsg
       _ -> do addAssert baseZero (Crucible.SimError loc (Crucible.GenericSimError "Expected bitvector value, but found pointer"))
               return offTm

-- This is a case for pointers, when we opaque types in Cryptol to represent them...
-- valueToSC sym _tval (Crucible.LLVMValInt base off) =
--   do base' <- Crucible.toSC sym base
--      off'  <- Crucible.toSC sym off
--      sc    <- Crucible.saw_ctx <$> readIORef (Crucible.sbStateManager sym)
--      Just <$> scTuple sc [base', off']

valueToSC sym loc failMsg (Cryptol.TVSeq n cryty) (Crucible.LLVMValArray ty vals)
  | toInteger (length vals) == n
  = do terms <- V.toList <$> traverse (valueToSC sym loc failMsg cryty) vals
       sc <- liftIO $ Crucible.sawBackendSharedContext sym
       t <- liftIO (typeToSC sc ty)
       liftIO (scVectorReduced sc t terms)

valueToSC _ _ _ _ Crucible.LLVMValFloat{} =
  fail  "valueToSC: Real not supported"

valueToSC _sym loc failMsg _tval _val =
  failure loc failMsg

------------------------------------------------------------------------

typeToSC :: SharedContext -> Crucible.StorageType -> IO Term
typeToSC sc t =
  case Crucible.storageTypeF t of
    Crucible.Bitvector sz -> scBitvector sc (Crucible.bytesToBits sz)
    Crucible.Float -> fail "typeToSC: float not supported"
    Crucible.Double -> fail "typeToSC: double not supported"
    Crucible.X86_FP80 -> fail "typeToSC: X86_FP80 not supported"
    Crucible.Array sz ty ->
      do n <- scNat sc (fromIntegral sz)
         ty' <- typeToSC sc ty
         scVecType sc n ty'
    Crucible.Struct fields ->
      do fields' <- V.toList <$> traverse (typeToSC sc . view Crucible.fieldVal) fields
         scTuple sc fields'

------------------------------------------------------------------------

-- | Use the current state to learn about variable assignments based on
-- preconditions for a procedure specification.
learnSetupCondition ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options                    ->
  SharedContext              ->
  LLVMCrucibleContext arch       ->
  MS.CrucibleMethodSpecIR (LLVM arch)       ->
  PrePost                    ->
  MS.SetupCondition (LLVM arch) ->
  OverrideMatcher (LLVM arch) md ()
learnSetupCondition opts sc cc spec prepost (MS.SetupCond_Equal loc val1 val2)  = learnEqual opts sc cc spec loc prepost val1 val2
learnSetupCondition _opts sc cc _    prepost (MS.SetupCond_Pred loc tm)         = learnPred sc cc loc prepost (ttTerm tm)
learnSetupCondition _opts sc cc _    prepost (MS.SetupCond_Ghost () loc var val)   = learnGhost sc cc loc prepost var val


------------------------------------------------------------------------

-- TODO(lb): make this language-independent!
learnGhost ::
  SharedContext                                          ->
  LLVMCrucibleContext arch                                  ->
  W4.ProgramLoc                                          ->
  PrePost                                                ->
  MS.GhostGlobal                                            ->
  TypedTerm                                              ->
  OverrideMatcher (LLVM arch) md ()
learnGhost sc cc loc prepost var expected =
  do actual <- readGlobal var
     matchTerm sc (cc ^. ccBackend) loc prepost (ttTerm actual) (ttTerm expected)

------------------------------------------------------------------------

-- | Process a "points_to" statement from the precondition section of
-- the CrucibleSetup block. First, load the value from the address
-- indicated by 'ptr', and then match it against the pattern 'val'.
--
-- Returns a string on failure describing a concrete memory load failure.
learnPointsTo ::
  forall arch md .
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options                    ->
  SharedContext              ->
  LLVMCrucibleContext arch      ->
  MS.CrucibleMethodSpecIR (LLVM arch)       ->
  PrePost                    ->
  PointsTo (LLVM arch)       ->
  OverrideMatcher (LLVM arch) md (Maybe PP.Doc)
learnPointsTo opts sc cc spec prepost (LLVMPointsTo loc ptr val) =
  do let tyenv = MS.csAllocations spec
         nameEnv = MS.csTypeNames spec
     memTy <- liftIO $ typeOfSetupValue cc tyenv nameEnv val
     (_memTy, ptr1) <- resolveSetupValue opts cc sc spec Crucible.PtrRepr ptr

     -- In case the types are different (from crucible_points_to_untyped)
     -- then the load type should be determined by the rhs.
     storTy <- Crucible.toStorableType memTy
     sym    <- getSymInterface

     mem    <- readGlobal $ Crucible.llvmMemVar
                          $ (cc^.ccLLVMContext)

     let ?lc = cc^.ccTypeCtx
     let alignment = Crucible.memTypeAlign (Crucible.llvmDataLayout ?lc) memTy
     res <- liftIO $ Crucible.loadRaw sym mem ptr1 storTy alignment
     let summarizeBadLoad =
          let dataLayout = Crucible.llvmDataLayout (cc^.ccTypeCtx)
              sz = Crucible.memTypeSize dataLayout memTy
          in map (PP.text . unwords)
             [ [ "When reading through pointer:", show (Crucible.ppPtr ptr1) ]
             , [ "in the ", stateCond prepost, "of an override" ]
             , [ "Tried to read something of size:"
               , show (Crucible.bytesToInteger sz)
               ]
             , [ "And type:", show (Crucible.ppMemType memTy) ]
             ]
     case res of
       Crucible.PartLLVMVal assertion_tree res_val -> do
         pred_ <- Crucible.treeToPredicate
           (Proxy @(Crucible.LLVM arch))
           sym
           assertion_tree
         addAssert pred_ $ Crucible.SimError loc $
           Crucible.AssertFailureSimError $ show $ PP.vcat $ summarizeBadLoad
         pure Nothing <* matchArg opts sc cc spec prepost res_val memTy val
       W4.Err _err -> do
         -- When we have a concrete failure, we do a little more computation to
         -- try and find out why.
         let (blk, _offset) = Crucible.llvmPointerView ptr1
         pure $ Just $ PP.vcat . (summarizeBadLoad ++) $
           case W4.asNat blk of
             Nothing -> [PP.text "<Read from unknown allocation>"]
             Just blk' ->
               let possibleAllocs =
                     Crucible.possibleAllocs blk' (Crucible.memImplHeap mem)
               in [ PP.text $ unwords
                    [ "Found"
                    , show (length possibleAllocs)
                    , "possibly matching allocation(s):"
                    ]
                  , bullets '-' (map Crucible.ppSomeAlloc possibleAllocs)
                  ]
               -- This information tends to be overwhelming, but might be useful?
               -- We should brainstorm about better ways of presenting it.
               -- PP.<$$> PP.text (unwords [ "Here are the details on why reading"
               --                          , "from each matching write failed"
               --                          ])
               -- PP.<$$> PP.text (show err)

------------------------------------------------------------------------

-- | Process a "crucible_equal" statement from the precondition
-- section of the CrucibleSetup block.
learnEqual ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  Options                                          ->
  SharedContext                                    ->
  LLVMCrucibleContext arch                            ->
  MS.CrucibleMethodSpecIR (LLVM arch)                             ->
  W4.ProgramLoc                                    ->
  PrePost                                          ->
  SetupValue (Crucible.LLVM arch)       {- ^ first value to compare  -} ->
  SetupValue (Crucible.LLVM arch)       {- ^ second value to compare -} ->
  OverrideMatcher (LLVM arch) md ()
learnEqual opts sc cc spec loc prepost v1 v2 = do
  (_, val1) <- resolveSetupValueLLVM opts cc sc spec v1
  (_, val2) <- resolveSetupValueLLVM opts cc sc spec v2
  p         <- liftIO (equalValsPred cc val1 val2)
  let name = "equality " ++ stateCond prepost
  addAssert p (Crucible.SimError loc (Crucible.AssertFailureSimError name))

-- | Process a "crucible_precond" statement from the precondition
-- section of the CrucibleSetup block.
learnPred ::
  SharedContext                                                       ->
  LLVMCrucibleContext arch                                               ->
  W4.ProgramLoc                                                       ->
  PrePost                                                             ->
  Term             {- ^ the precondition to learn                  -} ->
  OverrideMatcher (LLVM arch) md ()
learnPred sc cc loc prepost t =
  do s <- OM (use termSub)
     u <- liftIO $ scInstantiateExt sc s t
     p <- liftIO $ resolveSAWPred (cc ^. ccBackend) u
     addAssert p (Crucible.SimError loc (Crucible.AssertFailureSimError (stateCond prepost)))

------------------------------------------------------------------------

-- | Perform an allocation as indicated by a 'crucible_alloc' statement
doAlloc ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  LLVMCrucibleContext arch       ->
  LLVMAllocSpec ->
  Crucible.MemImpl Sym ->
  IO (LLVMPtr (Crucible.ArchWidth arch), Crucible.MemImpl Sym)
doAlloc cc (LLVMAllocSpec mut memTy sz loc) mem =
  do let sym = cc^.ccBackend
     sz' <- W4.bvLit sym Crucible.PtrWidth $ Crucible.bytesToInteger sz
     let alignment = Crucible.memTypeAlign (Crucible.llvmDataLayout ?lc) memTy
     let l = show (W4.plSourceLoc loc)
     Crucible.doMalloc sym Crucible.HeapAlloc mut l mem sz' alignment

-- | Perform an allocation as indicated by a 'crucible_alloc' statement
executeAllocation ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options                        ->
  LLVMCrucibleContext arch          ->
  (AllocIndex, LLVMAllocSpec) ->
  OverrideMatcher (LLVM arch) RW ()
executeAllocation opts cc (var, spec@(LLVMAllocSpec _mut memTy _sz loc)) =
  do liftIO $ printOutLn opts Debug $ unwords ["executeAllocation:", show var, show memTy]
     let memVar = Crucible.llvmMemVar $ (cc^.ccLLVMContext)
     mem <- readGlobal memVar
     (ptr, mem') <- liftIO $ doAlloc cc spec mem
     writeGlobal memVar mem'
     assignVar cc loc var ptr

------------------------------------------------------------------------

-- | Update the simulator state based on the postconditions from the
-- procedure specification.
executeSetupCondition ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options                    ->
  SharedContext              ->
  LLVMCrucibleContext arch     ->
  MS.CrucibleMethodSpecIR (LLVM arch)       ->
  MS.SetupCondition (LLVM arch) ->
  OverrideMatcher (LLVM arch) RW ()
executeSetupCondition opts sc cc spec =
  \case
    MS.SetupCond_Equal _loc val1 val2 ->
      executeEqual opts sc cc spec val1 val2
    MS.SetupCond_Pred _loc tm -> executePred sc cc tm
    MS.SetupCond_Ghost () _loc var val -> executeGhost sc var val

------------------------------------------------------------------------

-- TODO(lb): make this language independent!
executeGhost ::
  SharedContext ->
  MS.GhostGlobal ->
  TypedTerm ->
  OverrideMatcher (LLVM arch) RW ()
executeGhost sc var val =
  do s <- OM (use termSub)
     t <- liftIO (ttTermLens (scInstantiateExt sc s) val)
     writeGlobal var t

------------------------------------------------------------------------

-- | Process a "points_to" statement from the postcondition section of
-- the CrucibleSetup block. First we compute the value indicated by
-- 'val', and then write it to the address indicated by 'ptr'.
executePointsTo ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options                    ->
  SharedContext              ->
  LLVMCrucibleContext arch     ->
  MS.CrucibleMethodSpecIR (LLVM arch)       ->
  PointsTo (LLVM arch)       ->
  OverrideMatcher (LLVM arch) RW ()
executePointsTo opts sc cc spec (LLVMPointsTo _loc ptr val) =
  do (_, ptr') <- resolveSetupValue opts cc sc spec Crucible.PtrRepr ptr
     let memVar = Crucible.llvmMemVar $ (cc^.ccLLVMContext)
     mem <- readGlobal memVar

     -- In case the types are different (from crucible_points_to_untyped)
     -- then the load type should be determined by the rhs.
     m <- OM (use setupValueSub)
     s <- OM (use termSub)
     let tyenv = MS.csAllocations spec
     let nameEnv = MS.csTypeNames spec
     val' <- liftIO $ instantiateSetupValue sc s val

     mem' <- liftIO $ storePointsToValue opts cc m tyenv nameEnv mem ptr' val'
     writeGlobal memVar mem'

storePointsToValue ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  Options ->
  LLVMCrucibleContext arch ->
  Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)) ->
  Map AllocIndex (MS.AllocSpec (LLVM arch)) ->
  Map AllocIndex (MS.TypeName (LLVM arch)) ->
  Crucible.MemImpl Sym ->
  LLVMPtr (Crucible.ArchWidth arch) ->
  SetupValue (Crucible.LLVM arch) ->
  IO (Crucible.MemImpl Sym)
storePointsToValue opts cc env tyenv nameEnv mem ptr val = do
  let sym = cc ^. ccBackend

  memTy <- typeOfSetupValue cc tyenv nameEnv val
  storTy <- Crucible.toStorableType memTy
  let ?lc = cc^.ccTypeCtx
  let alignment = Crucible.memTypeAlign (Crucible.llvmDataLayout ?lc) memTy

  smt_array_memory_model_enabled <- W4.getOpt
    =<< W4.getOptionSetting enableSMTArrayMemoryModel (W4.getConfiguration sym)

  case val of
    SetupTerm tm
      | Crucible.storageTypeSize storTy > 16
      , smt_array_memory_model_enabled -> do
        arr_tm <- memArrayToSawCoreTerm cc (Crucible.memEndian mem) tm
        arr <- Crucible.bindSAWTerm
          sym
          (W4.BaseArrayRepr
            (Ctx.singleton $ W4.BaseBVRepr ?ptrWidth)
            (W4.BaseBVRepr (W4.knownNat @8)))
          arr_tm
        sz <- W4.bvLit
          sym
          ?ptrWidth
          (fromIntegral $ Crucible.storageTypeSize storTy)
        Crucible.doArrayConstStore sym mem ptr alignment arr sz
    _ -> do
      val' <- X.handle (handleException opts) $
        resolveSetupVal cc env tyenv nameEnv val
      Crucible.storeConstRaw sym mem ptr storTy alignment val'


------------------------------------------------------------------------


-- | Process a "crucible_equal" statement from the postcondition
-- section of the CrucibleSetup block.
executeEqual ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  Options                                          ->
  SharedContext                                    ->
  LLVMCrucibleContext arch                           ->
  MS.CrucibleMethodSpecIR (LLVM arch)                             ->
  SetupValue (Crucible.LLVM arch)       {- ^ first value to compare  -} ->
  SetupValue (Crucible.LLVM arch)       {- ^ second value to compare -} ->
  OverrideMatcher (LLVM arch) md ()
executeEqual opts sc cc spec v1 v2 = do
  (_, val1) <- resolveSetupValueLLVM opts cc sc spec v1
  (_, val2) <- resolveSetupValueLLVM opts cc sc spec v2
  p         <- liftIO (equalValsPred cc val1 val2)
  addAssume p

-- | Process a "crucible_postcond" statement from the postcondition
-- section of the CrucibleSetup block.
executePred ::
  SharedContext ->
  LLVMCrucibleContext arch ->
  TypedTerm {- ^ the term to assert as a postcondition -} ->
  OverrideMatcher (LLVM arch) md ()
executePred sc cc tt =
  do s <- OM (use termSub)
     t <- liftIO $ scInstantiateExt sc s (ttTerm tt)
     p <- liftIO $ resolveSAWPred (cc ^. ccBackend) t
     addAssume p

------------------------------------------------------------------------

-- | Construct a completely symbolic pointer. This pointer could point to anything, or it could
-- be NULL.
executeFreshPointer ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  LLVMCrucibleContext arch {-  Cruible context       -} ->
  AllocIndex      {- ^ SetupVar allocation ID -} ->
  IO (LLVMPtr (Crucible.ArchWidth arch)) {- ^ Symbolic pointer value -}
executeFreshPointer cc (AllocIndex i) =
  do let mkName base = W4.systemSymbol (base ++ show i ++ "!")
         sym         = cc^.ccBackend
     blk <- W4.freshConstant sym (mkName "blk") W4.BaseNatRepr
     off <- W4.freshConstant sym (mkName "off") (W4.BaseBVRepr Crucible.PtrWidth)
     return (Crucible.LLVMPointer blk off)

------------------------------------------------------------------------

resolveSetupValueLLVM ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  Options              ->
  LLVMCrucibleContext arch ->
  SharedContext        ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  SetupValue (LLVM arch)           ->
  OverrideMatcher (LLVM arch) md (Crucible.MemType, LLVMVal)
resolveSetupValueLLVM opts cc sc spec sval =
  do m <- OM (use setupValueSub)
     s <- OM (use termSub)
     let tyenv = MS.csAllocations spec
         nameEnv = MS.csTypeNames spec
     memTy <- liftIO $ typeOfSetupValue cc tyenv nameEnv sval
     sval' <- liftIO $ instantiateSetupValue sc s sval
     lval  <- liftIO $ resolveSetupVal cc m tyenv nameEnv sval' `X.catch` handleException opts
     return (memTy, lval)

resolveSetupValue ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  Options              ->
  LLVMCrucibleContext arch ->
  SharedContext        ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  Crucible.TypeRepr tp ->
  SetupValue (Crucible.LLVM arch)           ->
  OverrideMatcher (LLVM arch) md (Crucible.MemType, Crucible.RegValue Sym tp)
resolveSetupValue opts cc sc spec tp sval =
  do (memTy, lval) <- resolveSetupValueLLVM opts cc sc spec sval
     sym <- getSymInterface
     val <- liftIO $ Crucible.unpackMemValue sym tp lval
     return (memTy, val)

enableSMTArrayMemoryModel :: W4.ConfigOption W4.BaseBoolType
enableSMTArrayMemoryModel = (W4.configOption W4.knownRepr "smt-array-memory-model")
