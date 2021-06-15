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
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module SAWScript.Crucible.LLVM.Override
  ( OverrideMatcher
  , OverrideMatcher'(..)
  , runOverrideMatcher

  , setupValueSub
  , executeFreshPointer
  , osAsserts
  , termSub

  , learnCond
  , learnSetupCondition
  , executeSetupCondition
  , matchArg
  , assertTermEqualities
  , methodSpecHandler
  , valueToSC
  , storePointsToValue

  , diffMemTypes

  , enableSMTArrayMemoryModel
  ) where

import           Control.Lens.At
import           Control.Lens.Each
import           Control.Lens.Fold
import           Control.Lens.Getter
import           Control.Lens.Lens
import           Control.Lens.Setter
import           Control.Lens.TH
import           Control.Exception as X
import           Control.Monad.IO.Class (liftIO)
import           Control.Monad
import           Data.Either (partitionEithers)
import           Data.Foldable (for_, traverse_, toList)
import           Data.List
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Proxy
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text, pack)
import qualified Data.Vector as V
import           GHC.Generics (Generic)
import           Numeric.Natural
import qualified Prettyprinter as PP

import qualified Text.LLVM.AST as L

import qualified Cryptol.TypeCheck.AST as Cryptol (Schema(..))
import qualified Cryptol.Eval.Type as Cryptol (TValue(..), evalType)
import qualified Cryptol.Utils.PP as Cryptol (pp)

import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Backend.Online as Crucible
import qualified Lang.Crucible.CFG.Core as Crucible (TypeRepr(UnitRepr))
import qualified Lang.Crucible.FunctionHandle as Crucible
import qualified Lang.Crucible.LLVM.Bytes as Crucible
import qualified Lang.Crucible.LLVM.MemModel as Crucible
import qualified Lang.Crucible.LLVM.Translation as Crucible
import qualified Lang.Crucible.Simulator.GlobalState as Crucible
import qualified Lang.Crucible.Simulator.OverrideSim as Crucible
import qualified Lang.Crucible.Simulator.RegMap as Crucible
import qualified Lang.Crucible.Simulator.SimError as Crucible

import qualified What4.BaseTypes as W4
import qualified What4.Config as W4
import qualified What4.Expr.Builder as W4
import qualified What4.Interface as W4
import qualified What4.LabeledPred as W4
import qualified What4.ProgramLoc as W4
import qualified What4.Symbol as W4

import qualified SAWScript.Crucible.LLVM.CrucibleLLVM as Crucible

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some (Some(..))
import qualified Data.BitVector.Sized as BV

import           Verifier.SAW.Prelude (scEq)
import           Verifier.SAW.SharedTerm
import           Verifier.SAW.TypedAST
import           Verifier.SAW.Recognizer
import           Verifier.SAW.TypedTerm
import           Verifier.SAW.Simulator.What4.ReturnTrip (SAWCoreState(..), toSC, bindSAWTerm)

import           SAWScript.Crucible.Common
import           SAWScript.Crucible.Common.MethodSpec (SetupValue(..), PointsTo)
import qualified SAWScript.Crucible.Common.MethodSpec as MS
import           SAWScript.Crucible.Common.MethodSpec (AllocIndex(..), PrePost(..))
import           SAWScript.Crucible.Common.Override hiding (getSymInterface)
import qualified SAWScript.Crucible.Common.Override as Ov (getSymInterface)
import           SAWScript.Crucible.LLVM.MethodSpecIR
import           SAWScript.Crucible.LLVM.ResolveSetupValue
import           SAWScript.Options
import           SAWScript.Utils (bullets, handleException)

type LabeledPred sym = W4.LabeledPred (W4.Pred sym) Crucible.SimError

type instance Pointer' (LLVM arch) Sym = LLVMPtr (Crucible.ArchWidth arch)

-- | An override packaged together with its preconditions, labeled with some
--   human-readable info about each condition.
data OverrideWithPreconditions arch =
  OverrideWithPreconditions
    { _owpPreconditions :: [LabeledPred Sym] -- ^ c.f. '_osAsserts'
    , _owpMethodSpec :: MS.CrucibleMethodSpecIR (LLVM arch)
    , owpState :: OverrideState (LLVM arch)
    }
  deriving (Generic)

makeLenses ''OverrideWithPreconditions

------------------------------------------------------------------------
-- Translating SAW values to Crucible values for good error messages

ppLLVMVal ::
  LLVMCrucibleContext arch ->
  LLVMVal ->
  OverrideMatcher (LLVM arch) w (PP.Doc ann)
ppLLVMVal cc val = do
  sym <- Ov.getSymInterface
  mem <- readGlobal (Crucible.llvmMemVar (ccLLVMContext cc))
  -- TODO: remove viaShow when crucible switches to prettyprinter
  pure $ PP.viaShow $ Crucible.ppLLVMValWithGlobals sym (Crucible.memImplSymbolMap mem) val

-- | Resolve a 'SetupValue' into a 'LLVMVal' and pretty-print it
ppSetupValueAsLLVMVal ::
  (Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options              {- ^ output/verbosity options -} ->
  LLVMCrucibleContext arch ->
  SharedContext {- ^ context for constructing SAW terms -} ->
  MS.CrucibleMethodSpecIR (LLVM arch) {- ^ for name and typing environments -} ->
  SetupValue (LLVM arch) ->
  OverrideMatcher (LLVM arch) w (PP.Doc ann)
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
  SetupValue (LLVM arch)           {- ^ the value from the spec -} ->
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
  OverrideMatcher (LLVM arch) w (PP.Doc ann)
ppPointsToAsLLVMVal opts cc sc spec (LLVMPointsTo loc cond ptr val) = do
  pretty1 <- ppSetupValueAsLLVMVal opts cc sc spec ptr
  let pretty2 = PP.pretty val
  pure $ PP.vcat [ "Pointer:" PP.<+> pretty1
                 , "Pointee:" PP.<+> pretty2
                 , maybe PP.emptyDoc (\tt -> "Condition:" PP.<+> MS.ppTypedTerm tt) cond
                 , "Assertion made at:" PP.<+>
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
  SetupValue (LLVM arch)           {- ^ the value from the spec -} ->
  Crucible.LLVMVal Sym {- ^ the value from the simulator -} ->
  OverrideMatcher (LLVM arch) w Crucible.SimError
notEqual cond opts loc cc sc spec expected actual = do
  prettyLLVMVal      <- ppLLVMVal cc actual
  prettySetupLLVMVal <- ppSetupValueAsLLVMVal opts cc sc spec expected
  let msg = unlines
        [ "Equality " ++ stateCond cond
        , "Expected value (as a SAW value): "
        , show (MS.ppSetupValue expected)
        , "Expected value (as a Crucible value): "
        , show prettySetupLLVMVal
        , "Actual value: "
        , show prettyLLVMVal
        ]
  pure $ Crucible.SimError loc $ Crucible.AssertFailureSimError msg ""

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
        Crucible.considerSatisfiability sym Nothing (getPred a) <&> \k ->
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
  Crucible.considerSatisfiability sym Nothing conj >>=
    \case
      Crucible.NoBranch False -> pure True
      _ -> pure False

-- | Print a message about failure of an override's preconditions
ppFailure ::
  OverrideWithPreconditions arch ->
  [LabeledPred Sym] ->
  PP.Doc ann
ppFailure owp false =
  PP.vcat
  [ MS.ppMethodSpec (owp ^. owpMethodSpec)
    -- TODO: remove viaShow when crucible switches to prettyprinter
  , bullets '*' (map (PP.viaShow . Crucible.ppSimError)
                  (false ^.. traverse . W4.labeledPredMsg))
  ]

-- | Print a message about concrete failure of an override's preconditions
--
-- Assumes that the override it's being passed does have concretely failing
-- preconditions. Otherwise, the error won't make much sense.
ppConcreteFailure :: OverrideWithPreconditions arch -> PP.Doc ann
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

-- | Pretty-print the arguments passed to an override
ppArgs ::
  forall arch args ann.
  (Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Sym ->
  LLVMCrucibleContext arch            {- ^ context for interacting with Crucible        -} ->
  MS.CrucibleMethodSpecIR (LLVM arch) {- ^ specification for current function override  -} ->
  Crucible.RegMap Sym args            {- ^ arguments from the simulator -} ->
  IO [PP.Doc ann]
ppArgs sym cc cs (Crucible.RegMap args) = do
  let expectedArgTypes = map fst (Map.elems (cs ^. MS.csArgBindings))
  let aux memTy (Crucible.AnyValue tyrep val) =
        do storTy <- Crucible.toStorableType memTy
           llvmval <- Crucible.packMemValue sym storTy tyrep val
           return (llvmval, memTy)
  case Crucible.lookupGlobal (Crucible.llvmMemVar (ccLLVMContext cc)) (cc^.ccLLVMGlobals) of
    Nothing -> fail "Internal error: Couldn't find LLVM memory variable"
    Just mem -> do
      -- TODO: remove viaShow when crucible switches to prettyprinter
      map (PP.viaShow . Crucible.ppLLVMValWithGlobals sym (Crucible.memImplSymbolMap mem) . fst) <$>
        liftIO (zipWithM aux expectedArgTypes (assignmentToList args))

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
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch), Crucible.HasLLVMAnn Sym) =>
  Options                  {- ^ output/verbosity options                     -} ->
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  LLVMCrucibleContext arch     {- ^ context for interacting with Crucible        -} ->
  W4.ProgramLoc            {- ^ Location of the call site for error reporting-} ->
  [MS.CrucibleMethodSpecIR (LLVM arch)]
    {- ^ specification for current function override  -} ->
  Crucible.FnHandle args ret {- ^ the handle for this function -} ->
  Crucible.OverrideSim (SAWCruciblePersonality Sym) Sym Crucible.LLVM rtp args ret
     (Crucible.RegValue Sym ret)
methodSpecHandler opts sc cc top_loc css h = do
  let fnName = head css ^. csName
  liftIO $ printOutLn opts Info $ unwords
    [ "Matching"
    , show (length css)
    , "overrides of "
    , fnName
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
         let initialFree = Set.fromList (map (ecVarIndex . tecExt)
                                           (view (MS.csPreState . MS.csFreshVars) cs))
          in runOverrideMatcher sym g0 Map.empty Map.empty initialFree (view MS.csLoc cs)
                      (do methodSpecHandler_prestate opts sc cc args cs
                          return cs)

  -- Print a failure message if all overrides failed to match.  Otherwise, collect
  -- all the override states that might apply, and compute the conjunction of all
  -- the preconditions.  We'll use these to perform symbolic branches between the
  -- various overrides.
  branches <-
    let prettyError methodSpec failureReason = do
          prettyArgs <- liftIO $ ppArgs sym cc methodSpec (Crucible.RegMap args)
          pure $
            PP.vcat
            [ MS.ppMethodSpec methodSpec
            , "Arguments:"
            , bullets '-' prettyArgs
            , ppOverrideFailure failureReason
            ]
    in
      case partitionEithers (toList prestates) of
          (errs, []) -> do
            msgs <-
              mapM (\(cs, err) ->
                      ("*" PP.<>) . PP.indent 2 <$> prettyError cs err)
                   (zip (toList css) errs)
            fail $ show $
              PP.vcat ["All overrides failed during structural matching:", PP.vcat msgs]
          (_, ss) -> liftIO $
            forM ss $ \(cs,st) ->
              return (OverrideWithPreconditions (st^.osAsserts) cs st)

  -- Now we do a second phase of simple compatibility checking: we check to see
  -- if any of the preconditions of the various overrides are concretely false.
  -- If so, there's no use in branching on them with @symbolicBranches@.
  (true, false, unknown) <- liftIO $ partitionOWPsConcrete sym branches

  -- Collapse the preconditions to a single predicate
  branches' <- liftIO $ forM (true ++ unknown) $
    \(OverrideWithPreconditions preconds cs st) ->
      W4.andAllOf sym (folded . W4.labeledPred) preconds <&>
        \precond -> (precond, cs, st)

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
    , fnName
    , "..."
    ]
  let retTy = Crucible.handleReturnType h
  res <- Crucible.regValue <$> Crucible.callOverride h
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
                         Crucible.addAssumption (cc^.ccBackend)
                            (Crucible.LabeledPred asum
                              (Crucible.AssumptionReason (st^.osLocation) "override postcondition"))
                       Crucible.writeGlobals (st'^.overrideGlobals)
                       Crucible.overrideReturn' (Crucible.RegEntry retTy ret)
           , Just (W4.plSourceLoc (cs ^. MS.csLoc))
           )
         | (precond, cs, st) <- branches'
         ] ++
         [ let e prettyArgs symFalse unsat = show $ PP.vcat $ concat
                 [ [ PP.pretty $
                     "No override specification applies for " ++ fnName ++ "."
                   ]
                 , [ "Arguments:"
                   , bullets '-' prettyArgs
                   ]
                 , if | not (null false) ->
                        [ PP.vcat
                          [ PP.pretty (unwords
                              [ "The following overrides had some preconditions"
                              , "that failed concretely:"
                              ])
                          , bullets '-' (map ppConcreteFailure false)
                          ]
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
                        [ PP.vcat
                          [ PP.pretty (unwords
                            [ "The conjunction of these overrides' preconditions"
                            , "was unsatisfiable, meaning your override can never"
                            , "apply. You probably have unintentionally specified"
                            , "mutually exclusive/inconsistent preconditions."
                            ])
                          , bullets '-' (unsat ^.. each . owpMethodSpec . to MS.ppMethodSpec)
                          ]
                        ]
                      | null false && null symFalse ->
                        [ PP.pretty (unwords
                            [ "No overrides had any single concretely or"
                            , "symbolically failing preconditions."
                            ])
                        ]
                      | otherwise -> []
                 , if | simVerbose opts < 3 ->
                        [ PP.pretty $ unwords
                          [ "Run SAW with --sim-verbose=3 to see a description"
                          , "of each override."
                          ]
                        ]
                      | otherwise ->
                        [ PP.vcat
                          [ "Here are the descriptions of each override:"
                          , bullets '-'
                            (branches ^.. each . owpMethodSpec . to MS.ppMethodSpec)
                          ]
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

                  prettyArgs <-
                    ppArgs sym cc (head css) (Crucible.RegMap args)

                  unsat <-
                    filterM
                      (unsatPreconditions sym (owpPreconditions . each . W4.labeledPred))
                      branches

                  Crucible.addFailedAssertion sym
                    (Crucible.GenericSimError (e prettyArgs symFalse unsat))
              , Just (W4.plSourceLoc top_loc)
              )
         ]))
     (Crucible.RegMap args)
  liftIO $ printOutLn opts Info $ unwords ["Applied override!", fnName]
  return res

------------------------------------------------------------------------

-- | Use a method spec to override the behavior of a function.
--   This function computes the pre-state portion of the override,
--   which involves reading values from arguments and memory and computing
--   substitutions for the setup value variables, and computing precondition
--   predicates.
methodSpecHandler_prestate ::
  forall arch ctx.
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch), Crucible.HasLLVMAnn Sym) =>
  Options                  {- ^ output/verbosity options                     -} ->
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  LLVMCrucibleContext arch     {- ^ context for interacting with Crucible        -} ->
  Ctx.Assignment (Crucible.RegEntry Sym) ctx
                           {- ^ the arguments to the function -} ->
  MS.CrucibleMethodSpecIR (LLVM arch) {- ^ specification for current function override  -} ->
  OverrideMatcher (LLVM arch) RO ()
methodSpecHandler_prestate opts sc cc args cs =
    do let expectedArgTypes = Map.elems (cs ^. MS.csArgBindings)

       sym <- Ov.getSymInterface

       let aux (memTy, setupVal) (Crucible.AnyValue tyrep val) =
             do storTy <- Crucible.toStorableType memTy
                pmv <- Crucible.packMemValue sym storTy tyrep val
                return (pmv, memTy, setupVal)

       -- todo: fail if list lengths mismatch
       xs <- liftIO (zipWithM aux expectedArgTypes (assignmentToList args))

       sequence_ [ matchArg opts sc cc cs PreState x y z | (x, y, z) <- xs]

       learnCond opts sc cc cs PreState (cs ^. MS.csGlobalAllocs) Map.empty (cs ^. MS.csPreState)


-- | Use a method spec to override the behavior of a function.
--   This function computes the post-state portion of the override,
--   which involves writing values into memory, computing the return value,
--   and computing postcondition predicates.
methodSpecHandler_poststate ::
  forall arch ret.
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch), Crucible.HasLLVMAnn Sym) =>
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
learnCond :: (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch), Crucible.HasLLVMAnn Sym)
          => Options
          -> SharedContext
          -> LLVMCrucibleContext arch
          -> MS.CrucibleMethodSpecIR (LLVM arch)
          -> PrePost
          -> [MS.AllocGlobal (LLVM arch)]
          -> Map AllocIndex (MS.AllocSpec (LLVM arch))
          -> MS.StateSpec (LLVM arch)
          -> OverrideMatcher (LLVM arch) md ()
learnCond opts sc cc cs prepost globals extras ss =
  do let loc = cs ^. MS.csLoc
     matchPointsTos opts sc cc cs prepost (ss ^. MS.csPointsTos)
     traverse_ (learnSetupCondition opts sc cc cs prepost) (ss ^. MS.csConditions)
     assertTermEqualities sc cc
     enforcePointerValidity sc cc loc ss
     enforceDisjointness sc cc loc globals extras ss
     enforceCompleteSubstitution loc ss


assertTermEqualities ::
  SharedContext ->
  LLVMCrucibleContext arch ->
  OverrideMatcher (LLVM arch) md ()
assertTermEqualities sc cc = do
  let assertTermEquality (t, e) = do
        p <- instantiateExtResolveSAWPred sc cc t
        addAssert p e
  traverse_ assertTermEquality =<< OM (use termEqs)


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
         isMissing tt = ecVarIndex (tecExt tt) `Map.notMember` sub

         -- list of all terms not covered by substitution
         missing = filter isMissing (view MS.csFreshVars ss)

     unless (null missing) (failure loc (AmbiguousVars missing))


-- execute a pre/post condition
executeCond :: (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch), Crucible.HasLLVMAnn Sym)
            => Options
            -> SharedContext
            -> LLVMCrucibleContext arch
            -> MS.CrucibleMethodSpecIR (LLVM arch)
            -> MS.StateSpec (LLVM arch)
            -> OverrideMatcher (LLVM arch) RW ()
executeCond opts sc cc cs ss = do
  refreshTerms sc ss

  traverse_ (executeAllocation opts sc cc) (Map.assocs (ss ^. MS.csAllocs))
  overwritten_allocs <- invalidateMutableAllocs opts sc cc cs
  traverse_
    (executePointsTo opts sc cc cs overwritten_allocs)
    (ss ^. MS.csPointsTos)
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
    freshenTerm (TypedExtCns _cty ec) =
      do ec' <- liftIO $ scFreshEC sc (toShortName (ecName ec)) (ecType ec)
         new <- liftIO $ scExtCns sc ec'
         return (ecVarIndex ec, new)

------------------------------------------------------------------------

-- | Generate assertions that all of the memory regions matched by an
-- override's precondition are allocated, and meet the appropriate
-- requirements for alignment and mutability.
enforcePointerValidity ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  SharedContext ->
  LLVMCrucibleContext arch ->
  W4.ProgramLoc ->
  MS.StateSpec (LLVM arch) ->
  OverrideMatcher (LLVM arch) md ()
enforcePointerValidity sc cc loc ss =
  do sym <- Ov.getSymInterface
     sub <- OM (use setupValueSub) -- Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch))
     let allocs = view MS.csAllocs ss -- Map AllocIndex LLVMAllocSpec
     let mems = Map.elems $ Map.intersectionWith (,) allocs sub
     let w = Crucible.PtrWidth
     let memVar = Crucible.llvmMemVar (ccLLVMContext cc)
     mem <- readGlobal memVar

     sequence_
       [ do psz' <- instantiateExtResolveSAWSymBV sc cc Crucible.PtrWidth psz
            c <-
              liftIO $
              Crucible.isAllocatedAlignedPointer sym w alignment mut ptr (Just psz') mem
            let msg =
                  "Pointer not valid:"
                  ++ "\n  base = " ++ show (Crucible.ppPtr ptr)
                  ++ "\n  size = " ++ showTerm psz
                  ++ "\n  required alignment = " ++ show (Crucible.fromAlignment alignment) ++ "-byte"
                  ++ "\n  required mutability = " ++ show mut
            addAssert c $ Crucible.SimError loc $
              Crucible.AssertFailureSimError msg ""

       | (LLVMAllocSpec mut _pty alignment psz _ploc fresh, ptr) <- mems
       , not fresh -- Fresh symbolic pointers are not assumed to be valid; don't check them
       ]

------------------------------------------------------------------------

-- | Generate assertions that all of the memory allocations matched by
-- an override's precondition are disjoint. Read-only allocations are
-- allowed to alias other read-only allocations, however.
enforceDisjointness ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  SharedContext ->
  LLVMCrucibleContext arch ->
  W4.ProgramLoc ->
  [MS.AllocGlobal (LLVM arch)] ->
  -- | Additional allocations to check disjointness from (from prestate)
  (Map AllocIndex (MS.AllocSpec (LLVM arch))) ->
  MS.StateSpec (LLVM arch) ->
  OverrideMatcher (LLVM arch) md ()
enforceDisjointness sc cc loc globals extras ss =
  do sym <- Ov.getSymInterface
     sub <- OM (use setupValueSub)
     mem <- readGlobal $ Crucible.llvmMemVar $ ccLLVMContext cc
     -- every csAllocs entry should be present in sub
     let mems = Map.elems $ Map.intersectionWith (,) (view MS.csAllocs ss) sub
     let mems2 = Map.elems $ Map.intersectionWith (,) extras sub

     -- Ensure that all RW regions are disjoint from each other, and
     -- that all RW regions are disjoint from all RO regions.
     sequence_
        [ enforceDisjointAllocSpec sc cc sym loc p q
        | p : ps <- tails mems
        , q <- ps ++ mems2
        ]

     -- Ensure that all RW and RO regions are disjoint from mutable
     -- global regions.
     let resolveAllocGlobal g@(LLVMAllocGlobal _ nm) =
           do ptr <- liftIO $ Crucible.doResolveGlobal sym mem nm
              pure (g, ptr)
     globals' <- traverse resolveAllocGlobal globals
     sequence_
       [ enforceDisjointAllocGlobal sym loc p q
       | p <- mems
       , q <- globals'
       ]

-- | Assert that two LLVM allocations are disjoint from each other, if
-- they need to be. If both allocations are read-only, then they need
-- not be disjoint. Similarly, fresh pointers need not be checked for
-- disjointness.
enforceDisjointAllocSpec ::
  (Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  SharedContext ->
  LLVMCrucibleContext arch ->
  Sym -> W4.ProgramLoc ->
  (LLVMAllocSpec, LLVMPtr (Crucible.ArchWidth arch)) ->
  (LLVMAllocSpec, LLVMPtr (Crucible.ArchWidth arch)) ->
  OverrideMatcher (LLVM arch) md ()
enforceDisjointAllocSpec sc cc sym loc
  (LLVMAllocSpec pmut _pty _palign psz ploc pfresh, p)
  (LLVMAllocSpec qmut _qty _qalign qsz qloc qfresh, q)
  | (pmut, qmut) == (Crucible.Immutable, Crucible.Immutable) =
    pure () -- Read-only allocations may alias each other
  | pfresh || qfresh =
    pure () -- Fresh pointers need not be disjoint
  | otherwise =
  do liftIO $ W4.setCurrentProgramLoc sym ploc
     psz' <- instantiateExtResolveSAWSymBV sc cc Crucible.PtrWidth psz
     liftIO $ W4.setCurrentProgramLoc sym qloc
     qsz' <- instantiateExtResolveSAWSymBV sc cc Crucible.PtrWidth qsz
     liftIO $ W4.setCurrentProgramLoc sym loc
     c <- liftIO $ Crucible.buildDisjointRegionsAssertion
       sym Crucible.PtrWidth
       p psz'
       q qsz'
     let msg =
           "Memory regions not disjoint:"
           ++ "\n  (base=" ++ show (Crucible.ppPtr p) ++ ", size=" ++ showTerm psz ++ ")"
           ++ "\n  from " ++ ppProgramLoc ploc
           ++ "\n  and "
           ++ "\n  (base=" ++ show (Crucible.ppPtr q) ++ ", size=" ++ showTerm qsz ++ ")"
           ++ "\n  from " ++ ppProgramLoc qloc
     addAssert c $ Crucible.SimError loc $
       Crucible.AssertFailureSimError msg ""

-- | Assert that an LLVM allocation is disjoint from a global region.
enforceDisjointAllocGlobal ::
  Sym -> W4.ProgramLoc ->
  (LLVMAllocSpec, LLVMPtr (Crucible.ArchWidth arch)) ->
  (LLVMAllocGlobal arch, LLVMPtr (Crucible.ArchWidth arch)) ->
  OverrideMatcher (LLVM arch) md ()
enforceDisjointAllocGlobal sym loc
  (LLVMAllocSpec _pmut _pty _palign psz ploc _pfresh, p)
  (LLVMAllocGlobal qloc (L.Symbol qname), q) =
  do let Crucible.LLVMPointer pblk _ = p
     let Crucible.LLVMPointer qblk _ = q
     c <- liftIO $ W4.notPred sym =<< W4.natEq sym pblk qblk
     let msg =
           "Memory regions not disjoint:"
           ++ "\n  (base=" ++ show (Crucible.ppPtr p) ++ ", size=" ++ showTerm psz ++ ")"
           ++ "\n  from " ++ ppProgramLoc ploc
           ++ "\n  and "
           ++ "\n  global " ++ show qname ++ " (base=" ++ show (Crucible.ppPtr q) ++ ")"
           ++ "\n  from " ++ ppProgramLoc qloc
     addAssert c $ Crucible.SimError loc $
       Crucible.AssertFailureSimError msg ""

ppProgramLoc :: W4.ProgramLoc -> String
ppProgramLoc loc =
  show (W4.plFunction loc) ++ " (" ++ show (W4.plSourceLoc loc) ++ ")"

------------------------------------------------------------------------

-- | For each points-to statement read the memory value through the
-- given pointer (lhs) and match the value against the given pattern
-- (rhs).  Statements are processed in dependency order: a points-to
-- statement cannot be executed until bindings for any/all lhs
-- variables exist.
matchPointsTos :: forall arch md.
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch), Crucible.HasLLVMAnn Sym) =>
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
    go progress delayed (c@(LLVMPointsTo loc _ _ _):cs) =
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
    checkPointsTo (LLVMPointsTo _loc _ p _) = checkSetupValue p

    checkSetupValue :: SetupValue (LLVM arch) -> OverrideMatcher (LLVM arch) md Bool
    checkSetupValue v =
      do m <- OM (use setupValueSub)
         return (all (`Map.member` m) (setupVars v))

    -- Compute the set of variable identifiers in a 'SetupValue'
    setupVars :: SetupValue (LLVM arch) -> Set AllocIndex
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
          let msg = unlines
                [ "The following pointers had to alias, but they didn't:"
                , "  " ++ show (Crucible.ppPtr val)
                , "  " ++ show (Crucible.ppPtr val')
                ]
          addAssert p $ Crucible.SimError loc $ Crucible.AssertFailureSimError msg ""

------------------------------------------------------------------------


assignTerm ::
  SharedContext      {- ^ context for constructing SAW terms    -} ->
  LLVMCrucibleContext arch   {- ^ context for interacting with Crucible -} ->
  W4.ProgramLoc ->
  PrePost                                                          ->
  VarIndex {- ^ external constant index -} ->
  Term     {- ^ value                   -} ->
  OverrideMatcher (LLVM arch) md ()

assignTerm sc cc loc prepost var val =
  do mb <- OM (use (termSub . at var))
     case mb of
       Nothing -> OM (termSub . at var ?= val)
       Just old ->
         matchTerm sc cc loc prepost val old

--          do t <- liftIO $ scEq sc old val
--             p <- liftIO $ resolveSAWPred cc t
--             addAssert p (Crucible.AssertFailureSimError ("literal equality " ++ stateCond prepost))

------------------------------------------------------------------------

diffMemTypes ::
  Crucible.HasPtrWidth wptr =>
  Crucible.MemType ->
  Crucible.MemType ->
  [([Maybe Int], Crucible.MemType, Crucible.MemType)]
diffMemTypes x0 y0 =
  let wptr :: Natural = fromIntegral (W4.natValue ?ptrWidth) in
  case (x0, y0) of
    -- Special case; consider a one-element struct to be compatible with
    -- the type of its field
    (Crucible.StructType x, _)
      | V.length (Crucible.siFields x) == 1 -> diffMemTypes (Crucible.fiType (V.head (Crucible.siFields x))) y0
    (_, Crucible.StructType y)
      | V.length (Crucible.siFields y) == 1 -> diffMemTypes x0 (Crucible.fiType (V.head (Crucible.siFields y)))

    (Crucible.IntType x, Crucible.IntType y) | x == y -> []
    (Crucible.FloatType, Crucible.FloatType) -> []
    (Crucible.DoubleType, Crucible.DoubleType) -> []
    (Crucible.PtrType{}, Crucible.PtrType{}) -> []
    (Crucible.IntType w, Crucible.PtrType{}) | w == wptr -> []
    (Crucible.PtrType{}, Crucible.IntType w) | w == wptr -> []
    (Crucible.ArrayType xn xt, Crucible.ArrayType yn yt)
      | xn == yn ->
        [ (Nothing : path, l , r) | (path, l, r) <- diffMemTypes xt yt ]
    (Crucible.VecType xn xt, Crucible.VecType yn yt)
      | xn == yn ->
        [ (Nothing : path, l , r) | (path, l, r) <- diffMemTypes xt yt ]
    (Crucible.StructType x, Crucible.StructType y)
      | V.map Crucible.fiOffset (Crucible.siFields x) ==
        V.map Crucible.fiOffset (Crucible.siFields y) ->
          let xts = Crucible.siFieldTypes x
              yts = Crucible.siFieldTypes y
          in diffMemTypesList 1 (V.toList (V.zip xts yts))
    _ -> [([], x0, y0)]

diffMemTypesList ::
  Crucible.HasPtrWidth arch =>
  Int ->
  [(Crucible.MemType, Crucible.MemType)] ->
  [([Maybe Int], Crucible.MemType, Crucible.MemType)]
diffMemTypesList _ [] = []
diffMemTypesList i ((x, y) : ts) =
  [ (Just i : path, l , r) | (path, l, r) <- diffMemTypes x y ]
  ++ diffMemTypesList (i+1) ts


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
  SetupValue (LLVM arch)         {- ^ expected specification value          -} ->
  OverrideMatcher (LLVM arch) md ()

matchArg opts sc cc cs prepost actual expectedTy expected = do
  let mvar = Crucible.llvmMemVar (ccLLVMContext cc)
  mem <- case Crucible.lookupGlobal mvar $ cc ^. ccLLVMGlobals of
    Nothing -> fail "internal error: LLVM Memory global not found"
    Just mem -> pure mem
  case (actual, expectedTy, expected) of
    (_, _, SetupTerm expectedTT)
      | TypedTermSchema (Cryptol.Forall [] [] tyexpr) <- ttType expectedTT
      , Right tval <- Cryptol.evalType mempty tyexpr
        -> do sym      <- Ov.getSymInterface
              failMsg  <- mkStructuralMismatch opts cc sc cs actual expected expectedTy
              realTerm <- valueToSC sym (cs ^. MS.csLoc) failMsg tval actual
              instantiateExtMatchTerm sc cc (cs ^. MS.csLoc) prepost realTerm (ttTerm expectedTT)

    -- match arrays point-wise
    (Crucible.LLVMValArray _ xs, Crucible.ArrayType _len y, SetupArray () zs)
      | V.length xs >= length zs ->
        sequence_
          [ matchArg opts sc cc cs prepost x y z
          | (x, z) <- zip (V.toList xs) zs ]

    -- match the fields of struct point-wise
    (Crucible.LLVMValStruct xs, Crucible.StructType fields, SetupStruct () _ zs) ->
      sequence_
        [ matchArg opts sc cc cs prepost x y z
        | ((_,x),y,z) <- zip3 (V.toList xs)
                              (V.toList (Crucible.fiType <$> Crucible.siFields fields))
                              zs ]

    (Crucible.LLVMValInt blk off, Crucible.PtrType _, SetupElem () v i) ->
      do let tyenv = MS.csAllocations cs
             nameEnv = MS.csTypeNames cs
             sym = cc^.ccBackend
         i' <- resolveSetupElemIndexOrFail cc tyenv nameEnv v i
         off' <- liftIO $ W4.bvSub sym off
           =<< W4.bvLit sym (W4.bvWidth off) (Crucible.bytesToBV (W4.bvWidth off) i')
         matchArg opts sc cc cs prepost (Crucible.LLVMValInt blk off') expectedTy v
    (_, Crucible.PtrType _, SetupField () v n) ->
      do let tyenv = MS.csAllocations cs
             nameEnv = MS.csTypeNames cs
         i <- resolveSetupFieldIndexOrFail cc tyenv nameEnv v n
         matchArg opts sc cc cs prepost actual expectedTy (SetupElem () v i)
    (_, _, SetupGlobalInitializer () _) -> resolveAndMatch

    (Crucible.LLVMValInt blk off, _, _) ->
      case expected of
        SetupVar var | Just Refl <- testEquality (W4.bvWidth off) Crucible.PtrWidth ->
          do assignVar cc (cs ^. MS.csLoc) var (Crucible.LLVMPointer blk off)

        SetupNull () | Just Refl <- testEquality (W4.bvWidth off) Crucible.PtrWidth ->
          do sym <- Ov.getSymInterface
             p   <- liftIO (Crucible.ptrIsNull sym Crucible.PtrWidth (Crucible.LLVMPointer blk off))
             addAssert p =<<
               notEqual prepost opts (cs ^. MS.csLoc) cc sc cs expected actual

        SetupGlobal () name | Just Refl <- testEquality (W4.bvWidth off) Crucible.PtrWidth ->
          do sym  <- Ov.getSymInterface
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
      sym  <- Ov.getSymInterface
      if diffMemTypes expectedTy ty /= []
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
     do st <- liftIO (sawCoreState sym)
        let sc = saw_ctx st
        zeroValueSC sc gtp

valueToSC sym loc failMsg (Cryptol.TVTuple tys) (Crucible.LLVMValStruct vals)
  | length tys == length vals
  = do terms <- traverse (\(ty, tm) -> valueToSC sym loc failMsg ty (snd tm)) (zip tys (V.toList vals))
       st <- liftIO (sawCoreState sym)
       let sc = saw_ctx st
       liftIO (scTupleReduced sc terms)

valueToSC sym loc failMsg (Cryptol.TVSeq _n Cryptol.TVBit) (Crucible.LLVMValInt base off) =
  do baseZero <- liftIO (W4.natEq sym base =<< W4.natLit sym 0)
     st <- liftIO (sawCoreState sym)
     offTm <- liftIO (toSC sym st off)
     case W4.asConstantPred baseZero of
       Just True  -> return offTm
       Just False -> failure loc failMsg
       _ -> do addAssert baseZero (Crucible.SimError loc (Crucible.GenericSimError "Expected bitvector value, but found pointer"))
               return offTm

-- This is a case for pointers, when we opaque types in Cryptol to represent them...
-- valueToSC sym _tval (Crucible.LLVMValInt base off) =
--   do base' <- Crucible.toSC sym base
--      off'  <- Crucible.toSC sym off
--      sc    <- Crucible.saw_ctx <$> sawCoreState sym
--      Just <$> scTuple sc [base', off']

valueToSC sym loc failMsg (Cryptol.TVSeq n cryty) (Crucible.LLVMValArray ty vals)
  | toInteger (length vals) == n
  = do terms <- V.toList <$> traverse (valueToSC sym loc failMsg cryty) vals
       st <- liftIO (sawCoreState sym)
       let sc = saw_ctx st
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
         scTupleType sc fields'

------------------------------------------------------------------------

-- | NOTE: The two 'Term' arguments must have the same type.
instantiateExtMatchTerm ::
  SharedContext   {- ^ context for constructing SAW terms    -} ->
  LLVMCrucibleContext arch {- ^ context for interacting with Crucible -} ->
  W4.ProgramLoc ->
  PrePost                                                       ->
  Term            {- ^ exported concrete term                -} ->
  Term            {- ^ expected specification term           -} ->
  OverrideMatcher (LLVM arch) md ()
instantiateExtMatchTerm sc cc loc prepost actual expected = do
  sub <- OM (use termSub)
  matchTerm sc cc loc prepost actual =<< liftIO (scInstantiateExt sc sub expected)

matchTerm ::
  SharedContext   {- ^ context for constructing SAW terms    -} ->
  LLVMCrucibleContext arch {- ^ context for interacting with Crucible -} ->
  W4.ProgramLoc ->
  PrePost                                                       ->
  Term            {- ^ exported concrete term                -} ->
  Term            {- ^ expected specification term           -} ->
  OverrideMatcher (LLVM arch) md ()

matchTerm _ _ _ _ real expect | real == expect = return ()
matchTerm sc cc loc prepost real expect =
  do free <- OM (use osFree)
     case unwrapTermF expect of
       FTermF (ExtCns ec)
         | Set.member (ecVarIndex ec) free ->
         do assignTerm sc cc loc prepost (ecVarIndex ec) real

       _ ->
         do t <- liftIO $ scEq sc real expect
            let msg = unlines $
                  [ "Literal equality " ++ stateCond prepost
                  , "Expected term: " ++ prettyTerm expect
                  , "Actual term:   " ++ prettyTerm real
                  ]
            addTermEq t $ Crucible.SimError loc $ Crucible.AssertFailureSimError msg ""
  where prettyTerm = show . ppTermDepth 20


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
learnSetupCondition opts sc cc spec prepost cond =
  case cond of
    MS.SetupCond_Equal loc val1 val2  -> learnEqual opts sc cc spec loc prepost val1 val2
    MS.SetupCond_Pred loc tm          -> learnPred sc cc loc prepost (ttTerm tm)
    MS.SetupCond_Ghost () loc var val -> learnGhost sc cc loc prepost var val


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
learnGhost sc cc loc prepost var (TypedTerm (TypedTermSchema schEx) tmEx) =
  do (sch,tm) <- readGlobal var
     when (sch /= schEx) $ fail $ unlines $
       [ "Ghost variable had the wrong type:"
       , "- Expected: " ++ show (Cryptol.pp schEx)
       , "- Actual:   " ++ show (Cryptol.pp sch)
       ]
     instantiateExtMatchTerm sc cc loc prepost tm tmEx
learnGhost _sc _cc _loc _prepost _var (TypedTerm tp _)
  = fail $ unlines
      [ "Ghost variable expected value has improper type"
      , "expected Cryptol schema type, but got"
      , show (MS.ppTypedTermType tp)
      ]

------------------------------------------------------------------------

-- | Process a "points_to" statement from the precondition section of
-- the CrucibleSetup block. First, load the value from the address
-- indicated by 'ptr', and then match it against the pattern 'val'.
--
-- Returns a string on failure describing a concrete memory load failure.
learnPointsTo ::
  forall arch md ann.
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch), Crucible.HasLLVMAnn Sym) =>
  Options                    ->
  SharedContext              ->
  LLVMCrucibleContext arch      ->
  MS.CrucibleMethodSpecIR (LLVM arch)       ->
  PrePost                    ->
  PointsTo (LLVM arch)       ->
  OverrideMatcher (LLVM arch) md (Maybe (PP.Doc ann))
learnPointsTo opts sc cc spec prepost (LLVMPointsTo loc maybe_cond ptr val) =
  do let tyenv = MS.csAllocations spec
         nameEnv = MS.csTypeNames spec
     sym    <- Ov.getSymInterface

     mem    <- readGlobal $ Crucible.llvmMemVar
                          $ ccLLVMContext cc

     (_memTy, ptr1) <- resolveSetupValue opts cc sc spec Crucible.PtrRepr ptr

     let alignment = Crucible.noAlignment -- default to byte alignment (FIXME)

     case val of
       ConcreteSizeValue val' ->
         do memTy <- liftIO $ typeOfSetupValue cc tyenv nameEnv val'
            -- In case the types are different (from llvm_points_to_untyped)
            -- then the load type should be determined by the rhs.
            storTy <- Crucible.toStorableType memTy
            res <- liftIO $ Crucible.loadRaw sym mem ptr1 storTy alignment
            let summarizeBadLoad =
                 let dataLayout = Crucible.llvmDataLayout (ccTypeCtx cc)
                     sz = Crucible.memTypeSize dataLayout memTy
                 in map (PP.pretty . unwords)
                    [ [ "When reading through pointer:", show (Crucible.ppPtr ptr1) ]
                    , [ "in the ", stateCond prepost, "of an override" ]
                    , [ "Tried to read something of size:"
                      , show (Crucible.bytesToInteger sz)
                      ]
                    , [ "And type:", show (Crucible.ppMemType memTy) ]
                    ]
            case res of
              Crucible.NoErr pred_ res_val -> do
                pred_' <- case maybe_cond of
                  Just cond -> do
                    cond' <- instantiateExtResolveSAWPred sc cc (ttTerm cond)
                    liftIO $ W4.impliesPred sym cond' pred_
                  Nothing -> return pred_
                addAssert pred_' $ Crucible.SimError loc $
                  Crucible.AssertFailureSimError (show $ PP.vcat $ summarizeBadLoad) ""
                pure Nothing <* matchArg opts sc cc spec prepost res_val memTy val'
              _ -> do
                -- When we have a concrete failure, we do a little more computation to
                -- try and find out why.
                let (blk, _offset) = Crucible.llvmPointerView ptr1
                pure $ Just $ PP.vcat . (summarizeBadLoad ++) $
                  case W4.asNat blk of
                    Nothing -> ["<Read from unknown allocation>"]
                    Just blk' ->
                      let possibleAllocs =
                            Crucible.possibleAllocs blk' (Crucible.memImplHeap mem)
                      in [ PP.pretty $ unwords
                           [ "Found"
                           , show (length possibleAllocs)
                           , "possibly matching allocation(s):"
                           ]
                         , bullets '-' (map (PP.viaShow . Crucible.ppSomeAlloc) possibleAllocs)
                           -- TODO: remove 'viaShow' when crucible switches to prettyprinter
                         ]
                      -- This information tends to be overwhelming, but might be useful?
                      -- We should brainstorm about better ways of presenting it.
                      -- PP.<$$> PP.text (unwords [ "Here are the details on why reading"
                      --                          , "from each matching write failed"
                      --                          ])
                      -- PP.<$$> PP.text (show err)

       SymbolicSizeValue expected_arr_tm expected_sz_tm ->
         do maybe_allocation_array <- liftIO $
              Crucible.asMemAllocationArrayStore sym Crucible.PtrWidth ptr1 (Crucible.memImplHeap mem)
            let errMsg = PP.vcat $ map (PP.pretty . unwords)
                  [ [ "When reading through pointer:", show (Crucible.ppPtr ptr1) ]
                  , [ "in the ", stateCond prepost, "of an override" ]
                  , [ "Tried to read an array prefix of size:", show (MS.ppTypedTerm expected_sz_tm) ]
                  ]
            case maybe_allocation_array of
              Just (ok, arr, sz)
                | Crucible.LLVMPointer _ off <- ptr1
                , Just 0 <- BV.asUnsigned <$> W4.asBV off ->
                do addAssert ok $ Crucible.SimError loc $ Crucible.GenericSimError $ show errMsg
                   st <- liftIO (sawCoreState sym)
                   arr_tm <- liftIO $ toSC sym st arr
                   instantiateExtMatchTerm sc cc (spec ^. MS.csLoc) prepost arr_tm (ttTerm expected_arr_tm)
                   sz_tm <- liftIO $ toSC sym st sz
                   instantiateExtMatchTerm sc cc (spec ^. MS.csLoc) prepost sz_tm (ttTerm expected_sz_tm)
                   return Nothing

              _ -> return $ Just errMsg

------------------------------------------------------------------------

stateCond :: PrePost -> String
stateCond PreState = "precondition"
stateCond PostState = "postcondition"

-- | Process an @llvm_equal@ statement from the precondition
-- section of the CrucibleSetup block.
learnEqual ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  Options                                          ->
  SharedContext                                    ->
  LLVMCrucibleContext arch                            ->
  MS.CrucibleMethodSpecIR (LLVM arch)                             ->
  W4.ProgramLoc                                    ->
  PrePost                                          ->
  SetupValue (LLVM arch)       {- ^ first value to compare  -} ->
  SetupValue (LLVM arch)       {- ^ second value to compare -} ->
  OverrideMatcher (LLVM arch) md ()
learnEqual opts sc cc spec loc prepost v1 v2 = do
  (_, val1) <- resolveSetupValueLLVM opts cc sc spec v1
  (_, val2) <- resolveSetupValueLLVM opts cc sc spec v2
  p         <- liftIO (equalValsPred cc val1 val2)
  let name = "equality " ++ stateCond prepost
  addAssert p (Crucible.SimError loc (Crucible.AssertFailureSimError name ""))

-- | Process an @llvm_precond@ statement from the precondition
-- section of the CrucibleSetup block.
learnPred ::
  SharedContext                                                       ->
  LLVMCrucibleContext arch                                               ->
  W4.ProgramLoc                                                       ->
  PrePost                                                             ->
  Term             {- ^ the precondition to learn                  -} ->
  OverrideMatcher (LLVM arch) md ()
learnPred sc cc loc prepost t =
  do p <- instantiateExtResolveSAWPred sc cc t
     addAssert p (Crucible.SimError loc (Crucible.AssertFailureSimError (stateCond prepost) ""))

instantiateExtResolveSAWPred ::
  SharedContext ->
  LLVMCrucibleContext arch ->
  Term ->
  OverrideMatcher (LLVM arch) md (W4.Pred Sym)
instantiateExtResolveSAWPred sc cc cond = do
  sub <- OM (use termSub)
  liftIO $ resolveSAWPred cc =<< scInstantiateExt sc sub cond

instantiateExtResolveSAWSymBV ::
  (1 <= w) =>
  SharedContext ->
  LLVMCrucibleContext arch ->
  NatRepr w ->
  Term ->
  OverrideMatcher (LLVM arch) md (W4.SymBV Sym w)
instantiateExtResolveSAWSymBV sc cc w tm = do
  sub <- OM (use termSub)
  liftIO $ resolveSAWSymBV cc w =<< scInstantiateExt sc sub tm

------------------------------------------------------------------------

-- | Invalidate all mutable memory that was allocated in the method spec
-- precondition, either through explicit calls to @llvm_alloc@ or to
-- @llvm_alloc_global@. As an optimization, a memory allocation that
-- is overwritten by a postcondition memory write is not invalidated.
-- Return a map containing the overwritten memory allocations.
invalidateMutableAllocs ::
  ( ?lc :: Crucible.TypeContext
  , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
  , Crucible.HasLLVMAnn Sym
  ) =>
  Options ->
  SharedContext ->
  LLVMCrucibleContext arch ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  OverrideMatcher (LLVM arch) RW (Map (W4.SymNat Sym) Text)
invalidateMutableAllocs opts sc cc cs = do
  sym <- use syminterface
  mem <- readGlobal . Crucible.llvmMemVar $ ccLLVMContext cc
  sub <- use setupValueSub

  let mutableAllocs =
        Map.filter (view isMut) $
        Map.filter (not . view allocSpecFresh) $
        cs ^. MS.csPreState . MS.csAllocs
      allocPtrs = catMaybes $ map
        (\case
          (ptr, spec)
            | Just sz <- asUnsignedConcreteBv (_allocSpecBytes spec) ->
              Just
                ( ptr
                , fromIntegral sz
                , mconcat
                  [ "state of memory allocated in precondition (at "
                  , pack . show . W4.plSourceLoc $ spec ^. allocSpecLoc
                  , ") not described in postcondition"
                  ]
                )
            | otherwise -> Nothing)
        (Map.elems (Map.intersectionWith (,) sub mutableAllocs))
      mtrans = ccLLVMModuleTrans cc
      gimap = Crucible.globalInitMap mtrans
      mutableGlobals = cs ^. MS.csGlobalAllocs

  globalPtrs <- liftIO . fmap catMaybes . forM mutableGlobals $ \(LLVMAllocGlobal loc s@(L.Symbol st)) ->
    case Map.lookup s gimap of
      Just (_, Right (mt, _)) -> do
        ptr <- Crucible.doResolveGlobal sym mem s
        pure $ Just
          ( ptr
          , Crucible.memTypeSize (Crucible.llvmDataLayout ?lc) mt
          , mconcat
            [ "state of mutable global variable \""
            , pack st
            , "\" (allocated at "
            , pack . show $ W4.plSourceLoc loc
            , ") not described in postcondition"
            ]
          )
      _ -> pure Nothing

  -- set of (concrete base pointer, size) for each postcondition memory write
  postPtrs <- Set.fromList <$> catMaybes <$> mapM
    (\(LLVMPointsTo _loc _cond ptr val) -> case val of
      ConcreteSizeValue val' -> do
        (_, Crucible.LLVMPointer blk _) <- resolveSetupValue opts cc sc cs Crucible.PtrRepr ptr
        sz <- (return . Crucible.storageTypeSize)
          =<< Crucible.toStorableType
          =<< typeOfSetupValue cc (MS.csAllocations cs) (MS.csTypeNames cs) val'
        return $ Just (W4.asNat blk, sz)
      SymbolicSizeValue{} -> return Nothing)
    (cs ^. MS.csPostState ^. MS.csPointsTos)

  -- partition allocations into those overwritten by a postcondition write
  -- and those not overwritten
  let (overwritten_ptrs, danglingPtrs) = partition
        (\((Crucible.LLVMPointer blk _), sz, _) ->
          Set.member (W4.asNat blk, sz) postPtrs)
        (allocPtrs ++ globalPtrs)

  let overwritten_allocs = Map.fromList $ map
        (\((Crucible.LLVMPointer blk _), _, msg) -> (blk, msg))
        overwritten_ptrs

  -- invalidate each allocation that is not overwritten by a postcondition write
  mem' <- foldM (\m (ptr, sz, msg) ->
                    liftIO $ Crucible.doInvalidate sym ?ptrWidth m ptr msg
                      =<< W4.bvLit sym ?ptrWidth (Crucible.bytesToBV ?ptrWidth sz)
                ) mem danglingPtrs

  writeGlobal (Crucible.llvmMemVar $ ccLLVMContext cc) mem'

  return overwritten_allocs

------------------------------------------------------------------------

-- | Perform an allocation as indicated by an @llvm_alloc@ or
-- @llvm_fresh_pointer@ statement from the postcondition section.
executeAllocation ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options                        ->
  SharedContext ->
  LLVMCrucibleContext arch          ->
  (AllocIndex, LLVMAllocSpec) ->
  OverrideMatcher (LLVM arch) RW ()
executeAllocation opts sc cc (var, LLVMAllocSpec mut memTy alignment sz loc fresh)
  | fresh =
  do ptr <- liftIO $ executeFreshPointer cc var
     OM (setupValueSub %= Map.insert var ptr)
  | otherwise =
  do let sym = cc^.ccBackend
     {-
     memTy <- case Crucible.asMemType symTy of
                Just memTy -> return memTy
                Nothing    -> fail "executAllocation: failed to resolve type"
                -}
     liftIO $ printOutLn opts Debug $ unwords ["executeAllocation:", show var, show memTy]
     let memVar = Crucible.llvmMemVar (ccLLVMContext cc)
     mem <- readGlobal memVar
     sz' <- instantiateExtResolveSAWSymBV sc cc Crucible.PtrWidth sz
     let l = show (W4.plSourceLoc loc) ++ " (Poststate)"
     (ptr, mem') <- liftIO $
       Crucible.doMalloc sym Crucible.HeapAlloc mut l mem sz' alignment
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
executeGhost sc var (TypedTerm (TypedTermSchema sch) tm) =
  do s <- OM (use termSub)
     tm' <- liftIO (scInstantiateExt sc s tm)
     writeGlobal var (sch,tm')
executeGhost _sc _var (TypedTerm tp _) =
  fail $ unlines
    [ "executeGhost: improper value type"
    , "expected Cryptol schema type, but got"
    , show (MS.ppTypedTermType tp)
    ]

------------------------------------------------------------------------

-- | Process a "points_to" statement from the postcondition section of
-- the CrucibleSetup block. First we compute the value indicated by
-- 'val', and then write it to the address indicated by 'ptr'.
executePointsTo ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch), Crucible.HasLLVMAnn Sym) =>
  Options                    ->
  SharedContext              ->
  LLVMCrucibleContext arch     ->
  MS.CrucibleMethodSpecIR (LLVM arch)       ->
  Map (W4.SymNat Sym) Text ->
  PointsTo (LLVM arch)       ->
  OverrideMatcher (LLVM arch) RW ()
executePointsTo opts sc cc spec overwritten_allocs (LLVMPointsTo _loc cond ptr val) =
  do (_, ptr') <- resolveSetupValue opts cc sc spec Crucible.PtrRepr ptr
     let memVar = Crucible.llvmMemVar (ccLLVMContext cc)
     mem <- readGlobal memVar

     -- In case the types are different (from llvm_points_to_untyped)
     -- then the load type should be determined by the rhs.
     m <- OM (use setupValueSub)
     s <- OM (use termSub)
     let tyenv = MS.csAllocations spec
     let nameEnv = MS.csTypeNames spec
     val' <- liftIO $ case val of
       ConcreteSizeValue val'' -> ConcreteSizeValue <$> instantiateSetupValue sc s val''
       SymbolicSizeValue arr sz ->
         SymbolicSizeValue <$> ttTermLens (scInstantiateExt sc s) arr <*> ttTermLens (scInstantiateExt sc s) sz
     cond' <- mapM (instantiateExtResolveSAWPred sc cc . ttTerm) cond
     let Crucible.LLVMPointer blk _ = ptr'
     let invalidate_msg = Map.lookup blk overwritten_allocs

     mem' <- liftIO $ storePointsToValue opts cc m tyenv nameEnv mem cond' ptr' val' invalidate_msg
     writeGlobal memVar mem'

storePointsToValue ::
  (Crucible.HasPtrWidth (Crucible.ArchWidth arch), Crucible.HasLLVMAnn Sym) =>
  Options ->
  LLVMCrucibleContext arch ->
  Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)) ->
  Map AllocIndex (MS.AllocSpec (LLVM arch)) ->
  Map AllocIndex (MS.TypeName (LLVM arch)) ->
  Crucible.MemImpl Sym ->
  Maybe (W4.Pred Sym) ->
  LLVMPtr (Crucible.ArchWidth arch) ->
  LLVMPointsToValue arch ->
  Maybe Text ->
  IO (Crucible.MemImpl Sym)
storePointsToValue opts cc env tyenv nameEnv base_mem maybe_cond ptr val maybe_invalidate_msg = do
  let sym = cc ^. ccBackend

  let alignment = Crucible.noAlignment -- default to byte alignment (FIXME)

  smt_array_memory_model_enabled <- W4.getOpt
    =<< W4.getOptionSetting enableSMTArrayMemoryModel (W4.getConfiguration sym)

  let store_op = \mem -> case val of
        ConcreteSizeValue val' -> do
          memTy <- typeOfSetupValue cc tyenv nameEnv val'
          storTy <- Crucible.toStorableType memTy
          case val' of
            SetupTerm tm
              | Crucible.storageTypeSize storTy > 16
              , smt_array_memory_model_enabled -> do
                arr_tm <- memArrayToSawCoreTerm cc (Crucible.memEndian mem) tm
                st <- sawCoreState sym
                arr <- bindSAWTerm
                  sym st
                  (W4.BaseArrayRepr
                    (Ctx.singleton $ W4.BaseBVRepr ?ptrWidth)
                    (W4.BaseBVRepr (W4.knownNat @8)))
                  arr_tm
                sz <- W4.bvLit
                  sym
                  ?ptrWidth
                  (Crucible.bytesToBV ?ptrWidth $ Crucible.storageTypeSize storTy)
                Crucible.doArrayConstStore sym mem ptr alignment arr sz
            _ -> do
              val'' <- X.handle (handleException opts) $
                resolveSetupVal cc mem env tyenv nameEnv val'
              Crucible.storeConstRaw sym mem ptr storTy alignment val''
        SymbolicSizeValue arr_tm sz_tm -> do
          st <- sawCoreState sym
          arr <- bindSAWTerm
            sym st
            (W4.BaseArrayRepr
              (Ctx.singleton $ W4.BaseBVRepr ?ptrWidth)
              (W4.BaseBVRepr (W4.knownNat @8)))
            (ttTerm arr_tm)
          sz <- resolveSAWSymBV cc ?ptrWidth $ ttTerm sz_tm
          Crucible.doArrayConstStore sym mem ptr alignment arr sz

  case maybe_cond of
    Just cond -> case maybe_invalidate_msg of
      Just invalidate_msg -> do
        let invalidate_op = \mem -> do
              sz <- case val of
                ConcreteSizeValue val' -> do
                  memTy <- typeOfSetupValue cc tyenv nameEnv val'
                  storTy <- Crucible.toStorableType memTy
                  W4.bvLit
                    sym
                    ?ptrWidth
                    (Crucible.bytesToBV ?ptrWidth $ Crucible.storageTypeSize storTy)
                SymbolicSizeValue{} -> fail $ unwords
                  [ "internal error:"
                  , "unsupported conditional invalidation of symbolic size points-to value"
                  , show (PP.pretty val)
                  ]
              Crucible.doInvalidate sym ?ptrWidth mem ptr invalidate_msg sz
        Crucible.mergeWriteOperations sym base_mem cond store_op invalidate_op
      Nothing ->
        Crucible.doConditionalWriteOperation sym base_mem cond store_op
    Nothing -> store_op base_mem


------------------------------------------------------------------------


-- | Process an @llvm_equal@ statement from the postcondition
-- section of the CrucibleSetup block.
executeEqual ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  Options                                          ->
  SharedContext                                    ->
  LLVMCrucibleContext arch                           ->
  MS.CrucibleMethodSpecIR (LLVM arch)                             ->
  SetupValue (LLVM arch)       {- ^ first value to compare  -} ->
  SetupValue (LLVM arch)       {- ^ second value to compare -} ->
  OverrideMatcher (LLVM arch) md ()
executeEqual opts sc cc spec v1 v2 = do
  (_, val1) <- resolveSetupValueLLVM opts cc sc spec v1
  (_, val2) <- resolveSetupValueLLVM opts cc sc spec v2
  p         <- liftIO (equalValsPred cc val1 val2)
  addAssume p

-- | Process an @llvm_postcond@ statement from the postcondition
-- section of the CrucibleSetup block.
executePred ::
  SharedContext ->
  LLVMCrucibleContext arch ->
  TypedTerm {- ^ the term to assert as a postcondition -} ->
  OverrideMatcher (LLVM arch) md ()
executePred sc cc tt =
  addAssume =<< instantiateExtResolveSAWPred sc cc (ttTerm tt)

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
     blk <- W4.freshNat sym (mkName "blk")
     off <- W4.freshConstant sym (mkName "off") (W4.BaseBVRepr Crucible.PtrWidth)
     return (Crucible.LLVMPointer blk off)

------------------------------------------------------------------------

-- | Map the given substitution over all 'SetupTerm' constructors in
-- the given 'SetupValue'.
instantiateSetupValue ::
  SharedContext     ->
  Map VarIndex Term ->
  SetupValue (LLVM arch)        ->
  IO (SetupValue (LLVM arch))
instantiateSetupValue sc s v =
  case v of
    SetupVar{}               -> return v
    SetupTerm tt             -> SetupTerm        <$> doTerm tt
    SetupStruct () p vs      -> SetupStruct () p <$> mapM (instantiateSetupValue sc s) vs
    SetupArray () vs         -> SetupArray ()    <$> mapM (instantiateSetupValue sc s) vs
    SetupElem{}              -> return v
    SetupField{}             -> return v
    SetupNull{}              -> return v
    SetupGlobal{}            -> return v
    SetupGlobalInitializer{} -> return v
  where
    doTerm (TypedTerm schema t) = TypedTerm schema <$> scInstantiateExt sc s t

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
     mem <- readGlobal (Crucible.llvmMemVar (ccLLVMContext cc))
     let tyenv = MS.csAllocations spec
         nameEnv = MS.csTypeNames spec
     memTy <- liftIO $ typeOfSetupValue cc tyenv nameEnv sval
     sval' <- liftIO $ instantiateSetupValue sc s sval
     lval  <- liftIO $ resolveSetupVal cc mem m tyenv nameEnv sval' `X.catch` handleException opts
     return (memTy, lval)

resolveSetupValue ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  Options              ->
  LLVMCrucibleContext arch ->
  SharedContext        ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  Crucible.TypeRepr tp ->
  SetupValue (LLVM arch)           ->
  OverrideMatcher (LLVM arch) md (Crucible.MemType, Crucible.RegValue Sym tp)
resolveSetupValue opts cc sc spec tp sval =
  do (memTy, lval) <- resolveSetupValueLLVM opts cc sc spec sval
     sym <- Ov.getSymInterface
     val <- liftIO $ Crucible.unpackMemValue sym tp lval
     return (memTy, val)

enableSMTArrayMemoryModel :: W4.ConfigOption W4.BaseBoolType
enableSMTArrayMemoryModel = (W4.configOption W4.knownRepr "smt-array-memory-model")
