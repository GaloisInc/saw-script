{- |
Module      : SAWCentral.Crucible.LLVM.Override
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
{-# OPTIONS_GHC -Wno-orphans #-}

module SAWCentral.Crucible.LLVM.Override
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
  , matchPointsToValue
  , matchPointsToBitfieldValue
  , assertTermEqualities
  , methodSpecHandler
  , valueToSC
  , storePointsToValue
  , storePointsToBitfieldValue
  , doAllocSymInit

  , diffMemTypes
  , ppPointsToAsLLVMVal

  , enableSMTArrayMemoryModel
  ) where

import           Control.Lens ( _2 )
import           Control.Lens.At
import           Control.Lens.Each
import           Control.Lens.Fold
import           Control.Lens.Getter
import           Control.Lens.Lens
import           Control.Lens.Setter
import           Control.Exception as X
import           Control.Monad (filterM, foldM, forM, forM_, zipWithM)
import           Control.Monad.Except (runExcept)
import           Control.Monad.IO.Class (MonadIO(..))
import qualified Data.ByteString as BS
import           Data.Either (partitionEithers)
import           Data.Foldable (for_, traverse_, toList)
import           Data.List (partition, tails)
import qualified Data.List.NonEmpty as NE
import           Data.IORef (IORef, modifyIORef)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text, pack)
import qualified Data.Vector as V
import           Data.Void (absurd)
import           Numeric.Natural
import qualified Prettyprinter as PP

import qualified Text.LLVM.AST as L

import qualified Cryptol.TypeCheck.AST as Cryptol (Schema(..))
import qualified Cryptol.Eval.Type as Cryptol (TValue(..), evalType)

import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.CFG.Core as Crucible (TypeRepr(UnitRepr))
import qualified Lang.Crucible.FunctionHandle as Crucible
import qualified Lang.Crucible.LLVM.Bytes as Crucible
import qualified Lang.Crucible.LLVM.DataLayout as Crucible
import qualified Lang.Crucible.LLVM.MemModel as Crucible
import qualified Lang.Crucible.LLVM.MemType as Crucible
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

import qualified SAWCentral.Crucible.LLVM.CrucibleLLVM as Crucible

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some (Some(..))
import qualified Data.BitVector.Sized as BV

import           SAWCore.SharedTerm
import           SAWCore.Recognizer
import           SAWCore.Term.Pretty (showTerm)
import           CryptolSAWCore.TypedTerm
import           SAWCore.Simulator.TermModel
import           SAWCoreWhat4.ReturnTrip (SAWCoreState(..), toSC, bindSAWTerm)

import           SAWCentral.Crucible.Common
import           SAWCentral.Crucible.Common.MethodSpec (SetupValue(..), PointsTo)
import qualified SAWCentral.Crucible.Common.MethodSpec as MS
import           SAWCentral.Crucible.Common.MethodSpec (AllocIndex(..), PrePost(..))
import           SAWCentral.Crucible.Common.Override hiding (getSymInterface)
import qualified SAWCentral.Crucible.Common.Override as Ov (getSymInterface)
import           SAWCentral.Crucible.LLVM.MethodSpecIR
import           SAWCentral.Crucible.LLVM.ResolveSetupValue
import           SAWCentral.Crucible.LLVM.Setup.Value ()
import           SAWCentral.Options
import           SAWCentral.Panic
import           SAWCentral.Utils (bullets, handleException)

type instance Pointer' (LLVM arch) Sym = LLVMPtr (Crucible.ArchWidth arch)

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
  (?w4EvalTactic :: W4EvalTactic, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
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
      maybeMsgTy = either (const Nothing) Just $ runExcept (typeOfSetupValue cc tyEnv nameEnv setupval)
  in pure $ StructuralMismatch
              (PP.pretty llvmval)
              (MS.ppSetupValue setupval)
              maybeMsgTy
              memTy

-- | Instead of using 'ppPointsTo', which prints 'SetupValue', translate
--   expressions to 'LLVMVal'.
ppPointsToAsLLVMVal ::
  (?w4EvalTactic :: W4EvalTactic, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options              {- ^ output/verbosity options -} ->
  LLVMCrucibleContext arch ->
  SharedContext {- ^ context for constructing SAW terms -} ->
  MS.CrucibleMethodSpecIR (LLVM arch) {- ^ for name and typing environments -} ->
  PointsTo (LLVM arch) ->
  OverrideMatcher (LLVM arch) w (PP.Doc ann)
ppPointsToAsLLVMVal opts cc sc spec (LLVMPointsTo md cond ptr val) = do
  pretty1 <- ppSetupValueAsLLVMVal opts cc sc spec ptr
  let pretty2 = PP.pretty val
  pure $ PP.vcat [ "Pointer:" PP.<+> pretty1
                 , "Pointee:" PP.<+> pretty2
                 , maybe PP.emptyDoc (\tt -> "Condition:" PP.<+> MS.ppTypedTerm tt) cond
                 , "Assertion made at:" PP.<+>
                   PP.pretty (W4.plSourceLoc (MS.conditionLoc md))
                 ]
ppPointsToAsLLVMVal opts cc sc spec (LLVMPointsToBitfield md ptr fieldName val) = do
  pretty1 <- ppSetupValueAsLLVMVal opts cc sc spec ptr
  let pretty2 = MS.ppSetupValue val
  pure $ PP.vcat [ "Pointer (bitfield):" PP.<+> pretty1 <> PP.pretty ("." ++ fieldName)
                 , "Pointee:" PP.<+> pretty2
                 , "Assertion made at:" PP.<+>
                   PP.pretty (W4.plSourceLoc (MS.conditionLoc md))
                 ]

-- | Create an error stating that the 'LLVMVal' was not equal to the 'SetupValue'
notEqual ::
  (?w4EvalTactic :: W4EvalTactic, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
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
        [ "Equality " ++ MS.stateCond cond
        , "Expected value (as a SAW value): "
        , show (MS.ppSetupValue expected)
        , "Expected value (as a Crucible value): "
        , show prettySetupLLVMVal
        , "Actual value: "
        , show prettyLLVMVal
        ]
  pure $ Crucible.SimError loc $ Crucible.AssertFailureSimError msg ""

------------------------------------------------------------------------

-- | Print a message about symbolic failure of an override's preconditions
--
-- TODO: Needs additional testing. Are these messages useful?
{-
ppSymbolicFailure ::
  (OverrideWithPreconditions (LLVM arch), [LabeledPred Sym]) ->
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
  ( ?lc :: Crucible.TypeContext
  , ?memOpts::Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , ?checkAllocSymInit :: Bool
  , ?singleOverrideSpecialCase :: Bool
  , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
  , Crucible.HasLLVMAnn Sym
  ) =>
  Options                  {- ^ output/verbosity options                     -} ->
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  LLVMCrucibleContext arch     {- ^ context for interacting with Crucible        -} ->
  IORef MetadataMap ->
  NE.NonEmpty (MS.CrucibleMethodSpecIR (LLVM arch))
    {- ^ specification for current function override  -} ->
  Crucible.FnHandle args ret {- ^ the handle for this function -} ->
  Crucible.OverrideSim (SAWCruciblePersonality Sym) Sym Crucible.LLVM rtp args ret
     (Crucible.RegValue Sym ret)
methodSpecHandler opts sc cc mdMap css h =
  ccWithBackend cc $ \bak -> do
  let sym = backendGetSym bak
  let fnName = NE.head css ^. csName
  call_loc <- liftIO $ W4.getCurrentProgramLoc sym
  liftIO $ printOutLn opts Info $ unwords
    [ "Matching"
    , show (length css)
    , "overrides of "
    , fnName
    , "..."
    ]
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

  -- Check if there is only a single override branch that might apply at this
  -- point.  If so, commit to it and handle that case specially. If there is
  -- more than one (or zero) branches that might apply, go to the general case.
  case true ++ unknown of
    [singleBranch] | ?singleOverrideSpecialCase ->
         handleSingleOverrideBranch opts sc cc call_loc mdMap h singleBranch
    _ -> handleOverrideBranches opts sc cc call_loc css h branches (true, false, unknown)

handleSingleOverrideBranch :: forall arch rtp args ret.
  ( ?lc :: Crucible.TypeContext
  , ?memOpts::Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , ?checkAllocSymInit :: Bool
  , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
  , Crucible.HasLLVMAnn Sym
  ) =>
  Options                  {- ^ output/verbosity options                     -} ->
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  LLVMCrucibleContext arch     {- ^ context for interacting with Crucible        -} ->
  W4.ProgramLoc            {- ^ Location of the call site for error reporting-} ->
  IORef MetadataMap ->
  Crucible.FnHandle args ret {- ^ the handle for this function -} ->
  OverrideWithPreconditions (LLVM arch) ->
  Crucible.OverrideSim (SAWCruciblePersonality Sym) Sym Crucible.LLVM rtp args ret
     (Crucible.RegValue Sym ret)
handleSingleOverrideBranch opts sc cc call_loc mdMap h (OverrideWithPreconditions preconds cs st) =
  ccWithBackend cc $ \bak -> do
  let sym = backendGetSym bak
  let fnName = cs ^. csName
  let retTy = Crucible.handleReturnType h

  liftIO $ printOutLn opts Info $ unwords
    [ "Found a single potential override for"
    , fnName
    ]

  -- First assert the override preconditions
  liftIO $ forM_ preconds $ \(md,W4.LabeledPred p r) ->
    do (ann,p') <- W4.annotateTerm sym p
       let caller = unwords ["Override called from:", show (W4.plSourceLoc call_loc)]
       let md' = md{ MS.conditionContext = MS.conditionContext md ++ caller }
       modifyIORef mdMap (Map.insert ann md')
       Crucible.addAssertion bak (Crucible.LabeledPred p' r)

  g <- Crucible.readGlobals
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

handleOverrideBranches :: forall arch rtp args ret.
  ( ?lc :: Crucible.TypeContext
  , ?memOpts::Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , ?checkAllocSymInit :: Bool
  , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
  , Crucible.HasLLVMAnn Sym
  ) =>
  Options                  {- ^ output/verbosity options                     -} ->
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  LLVMCrucibleContext arch     {- ^ context for interacting with Crucible        -} ->
  W4.ProgramLoc            {- ^ Location of the call site for error reporting-} ->
  NE.NonEmpty (MS.CrucibleMethodSpecIR (LLVM arch))
    {- ^ specification for current function override  -} ->
  Crucible.FnHandle args ret {- ^ the handle for this function -} ->
  [OverrideWithPreconditions (LLVM arch)] ->
  ([OverrideWithPreconditions (LLVM arch)],[OverrideWithPreconditions (LLVM arch)],[OverrideWithPreconditions (LLVM arch)]) ->
  Crucible.OverrideSim (SAWCruciblePersonality Sym) Sym Crucible.LLVM rtp args ret
     (Crucible.RegValue Sym ret)

handleOverrideBranches opts sc cc call_loc css h branches (true, false, unknown) =
  ccWithBackend cc $ \bak -> do
  let sym = backendGetSym bak
  let fnName = NE.head css ^. csName
  Crucible.RegMap args <- Crucible.getOverrideArgs

  -- Collapse the preconditions to a single predicate
  branches' <- liftIO $ forM (true ++ unknown) $
    \(OverrideWithPreconditions preconds cs st) ->
      W4.andAllOf sym (folded . _2 . W4.labeledPred) preconds <&>
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
                    findFalsePreconditions bak owp <&>
                      \case
                        [] -> Nothing
                        ps -> Just (owp, ps))

                  prettyArgs <-
                    ppArgs sym cc (NE.head css) (Crucible.RegMap args)

                  unsat <-
                    filterM
                      (unsatPreconditions bak (owpPreconditions . each . _2 . W4.labeledPred))
                      branches

                  Crucible.addFailedAssertion bak
                    (Crucible.GenericSimError (e prettyArgs symFalse unsat))
              , Just (W4.plSourceLoc call_loc)
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
  ( ?lc :: Crucible.TypeContext
  , ?memOpts::Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , ?checkAllocSymInit :: Bool
  , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
  , Crucible.HasLLVMAnn Sym
  ) =>
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

       let md = MS.ConditionMetadata
                { MS.conditionLoc  = cs ^. MS.csLoc
                , MS.conditionTags = mempty -- TODO? should `execute_func` track tags?
                , MS.conditionType = "formal argument matching"
                , MS.conditionContext = ""
                }
       sequence_ [ matchArg opts sc cc cs PreState md x y z | (x, y, z) <- xs]

       learnCond opts sc cc cs PreState (cs ^. MS.csGlobalAllocs) Map.empty (cs ^. MS.csPreState)


-- | Use a method spec to override the behavior of a function.
--   This function computes the post-state portion of the override,
--   which involves writing values into memory, computing the return value,
--   and computing postcondition predicates.
methodSpecHandler_poststate ::
  forall arch ret.
  ( ?lc :: Crucible.TypeContext
  , ?memOpts :: Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
  , Crucible.HasLLVMAnn Sym
  ) =>
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
learnCond ::
  ( ?lc :: Crucible.TypeContext
  , ?memOpts::Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , ?checkAllocSymInit :: Bool
  , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
  , Crucible.HasLLVMAnn Sym
  ) =>
  Options ->
  SharedContext ->
  LLVMCrucibleContext arch ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  PrePost ->
  [MS.AllocGlobal (LLVM arch)] ->
  Map AllocIndex (MS.AllocSpec (LLVM arch)) ->
  MS.StateSpec (LLVM arch) ->
  OverrideMatcher (LLVM arch) md ()
learnCond opts sc cc cs prepost globals extras ss =
  do let loc = cs ^. MS.csLoc
     matchPointsTos opts sc cc cs prepost (ss ^. MS.csPointsTos)
     traverse_ (learnSetupCondition opts sc cc cs prepost) (ss ^. MS.csConditions)
     assertTermEqualities sc cc
     enforcePointerValidity sc cc ss
     enforceDisjointness sc cc loc globals extras ss
     enforceCompleteSubstitution loc ss


assertTermEqualities ::
  (?w4EvalTactic :: W4EvalTactic) =>
  SharedContext ->
  LLVMCrucibleContext arch ->
  OverrideMatcher (LLVM arch) md ()
assertTermEqualities sc cc = do
  let sym = cc ^. ccSym
  let assertTermEquality (cond, t, md, e) = do
        p <- instantiateExtResolveSAWPred sc cc t
        p' <- liftIO $ W4.impliesPred sym cond p
        addAssert p' md e
  traverse_ assertTermEquality =<< OM (use termEqs)


-- execute a pre/post condition
executeCond :: ( ?lc :: Crucible.TypeContext
               , ?memOpts :: Crucible.MemOptions
               , ?w4EvalTactic :: W4EvalTactic
               , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
               , Crucible.HasLLVMAnn Sym
               )
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

------------------------------------------------------------------------

-- | Generate assertions that all of the memory regions matched by an
-- override's precondition are allocated, and meet the appropriate
-- requirements for alignment and mutability.
enforcePointerValidity ::
  (?lc :: Crucible.TypeContext, ?memOpts::Crucible.MemOptions, ?w4EvalTactic :: W4EvalTactic, ?checkAllocSymInit :: Bool, Crucible.HasPtrWidth (Crucible.ArchWidth arch), Crucible.HasLLVMAnn Sym) =>
  SharedContext ->
  LLVMCrucibleContext arch ->
  MS.StateSpec (LLVM arch) ->
  OverrideMatcher (LLVM arch) md ()
enforcePointerValidity sc cc ss =
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
            let ploc = MS.conditionLoc allocMd

            let msg =
                  "Pointer not valid:"
                  ++ "\n  base = " ++ show (Crucible.ppPtr ptr)
                  ++ "\n  size = " ++ showTerm psz
                  ++ "\n  required alignment = " ++ show (Crucible.fromAlignment alignment) ++ "-byte"
                  ++ "\n  required mutability = " ++ show mut
            addAssert c allocMd $ Crucible.SimError ploc $
              Crucible.AssertFailureSimError msg ""

            case initialization of
              LLVMAllocSpecSymbolicInitialization
                | ?checkAllocSymInit ->
                  do maybeOk <- liftIO $ checkMemLoad sym mem ptr psz' alignment
                     let msg' = PP.vcat $ map (PP.pretty . unwords)
                           [ [ "Memory region not initialized:" ]
                           , [ "  pointer =", show (Crucible.ppPtr ptr) ]
                           , [ "  size =", showTerm psz ]
                           ]
                     case maybeOk of
                       Just ok ->
                         addAssert ok allocMd $ Crucible.SimError (MS.conditionLoc allocMd) $
                           Crucible.AssertFailureSimError (show msg') ""
                       Nothing -> failure ploc (BadPointerLoad (Right msg') "")
              _ -> return ()

       | (LLVMAllocSpec mut _pty alignment psz allocMd fresh initialization, ptr) <- mems
       , not fresh -- Fresh symbolic pointers are not assumed to be valid; don't check them
       ]

checkMemLoad ::
  (?memOpts::Crucible.MemOptions, Crucible.IsSymInterface sym, Crucible.HasPtrWidth wptr, Crucible.HasLLVMAnn sym) =>
  sym ->
  Crucible.MemImpl sym ->
  Crucible.LLVMPtr sym wptr ->
  W4.SymBV sym wptr ->
  Crucible.Alignment ->
  IO (Maybe (W4.Pred sym))
checkMemLoad sym mem ptr sz align =
  case BV.asNatural <$> W4.asBV sz of
    Just n -> do
      res <- Crucible.loadRaw sym mem ptr (Crucible.arrayType n $ Crucible.bitvectorType 1) align
      case res of
        Crucible.NoErr pred_ _val -> do
          return $ Just pred_
        _ -> return Nothing
    Nothing -> do
      maybe_allocation_array <- Crucible.asMemAllocationArrayStore sym Crucible.PtrWidth ptr (Crucible.memImplHeap mem)
      case maybe_allocation_array of
        Just (ok, _arr, _sz) -> return $ Just ok
        Nothing -> return Nothing

------------------------------------------------------------------------

-- | Generate assertions that all of the memory allocations matched by
-- an override's precondition are disjoint. Read-only allocations are
-- allowed to alias other read-only allocations, however.
enforceDisjointness ::
  (?lc :: Crucible.TypeContext, ?w4EvalTactic :: W4EvalTactic, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  SharedContext ->
  LLVMCrucibleContext arch ->
  W4.ProgramLoc ->
  [MS.AllocGlobal (LLVM arch)] ->
  -- | Additional allocations to check disjointness from (from prestate)
  (Map AllocIndex (MS.AllocSpec (LLVM arch))) ->
  MS.StateSpec (LLVM arch) ->
  OverrideMatcher (LLVM arch) md ()
enforceDisjointness sc cc loc globals extras ss =
  ccWithBackend cc $ \bak ->
  do let sym = backendGetSym bak
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
           do ptr <- liftIO $ Crucible.doResolveGlobal bak mem nm
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
  (?w4EvalTactic :: W4EvalTactic, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  SharedContext ->
  LLVMCrucibleContext arch ->
  Sym ->
  W4.ProgramLoc ->
  (LLVMAllocSpec, LLVMPtr (Crucible.ArchWidth arch)) ->
  (LLVMAllocSpec, LLVMPtr (Crucible.ArchWidth arch)) ->
  OverrideMatcher (LLVM arch) md ()
enforceDisjointAllocSpec sc cc sym loc
  (LLVMAllocSpec pmut _pty _palign psz pMd pfresh _p_sym_init, p)
  (LLVMAllocSpec qmut _qty _qalign qsz qMd qfresh _q_sym_init, q)
  | (pmut, qmut) == (Crucible.Immutable, Crucible.Immutable) =
    pure () -- Read-only allocations may alias each other
  | pfresh || qfresh =
    pure () -- Fresh pointers need not be disjoint
  | otherwise =
  do liftIO $ W4.setCurrentProgramLoc sym (MS.conditionLoc pMd)
     psz' <- instantiateExtResolveSAWSymBV sc cc Crucible.PtrWidth psz
     liftIO $ W4.setCurrentProgramLoc sym (MS.conditionLoc qMd)
     qsz' <- instantiateExtResolveSAWSymBV sc cc Crucible.PtrWidth qsz
     liftIO $ W4.setCurrentProgramLoc sym loc
     c <- liftIO $ Crucible.buildDisjointRegionsAssertion
       sym Crucible.PtrWidth
       p psz'
       q qsz'
     let md = MS.ConditionMetadata
              { MS.conditionLoc = loc
              , MS.conditionTags = mempty
              , MS.conditionType = "memory disjointness"
              , MS.conditionContext = ""
              }
     let msg =
           "Memory regions not disjoint:"
           ++ "\n  (base=" ++ show (Crucible.ppPtr p) ++ ", size=" ++ showTerm psz ++ ")"
           ++ "\n  from " ++ ppProgramLoc (MS.conditionLoc pMd)
           ++ "\n  and "
           ++ "\n  (base=" ++ show (Crucible.ppPtr q) ++ ", size=" ++ showTerm qsz ++ ")"
           ++ "\n  from " ++ ppProgramLoc (MS.conditionLoc qMd)
     addAssert c md $ Crucible.SimError loc $
       Crucible.AssertFailureSimError msg ""

-- | Assert that an LLVM allocation is disjoint from a global region.
enforceDisjointAllocGlobal ::
  Sym -> W4.ProgramLoc ->
  (LLVMAllocSpec, LLVMPtr (Crucible.ArchWidth arch)) ->
  (LLVMAllocGlobal arch, LLVMPtr (Crucible.ArchWidth arch)) ->
  OverrideMatcher (LLVM arch) md ()
enforceDisjointAllocGlobal sym loc
  (LLVMAllocSpec _pmut _pty _palign psz pMd pfresh _p_sym_init, p)
  (LLVMAllocGlobal qloc (L.Symbol qname), q)
  | pfresh =
    pure () -- Fresh pointers need not be disjoint
  | otherwise =
  do let Crucible.LLVMPointer pblk _ = p
     let Crucible.LLVMPointer qblk _ = q
     c <- liftIO $ W4.notPred sym =<< W4.natEq sym pblk qblk
     let msg =
           "Memory regions not disjoint:"
           ++ "\n  (base=" ++ show (Crucible.ppPtr p) ++ ", size=" ++ showTerm psz ++ ")"
           ++ "\n  from " ++ ppProgramLoc (MS.conditionLoc pMd)
           ++ "\n  and "
           ++ "\n  global " ++ show qname ++ " (base=" ++ show (Crucible.ppPtr q) ++ ")"
           ++ "\n  from " ++ ppProgramLoc qloc
     let md = MS.ConditionMetadata
              { MS.conditionLoc  = loc
              , MS.conditionTags = mempty
              , MS.conditionType = "global region disjointness"
              , MS.conditionContext = ""
              }
     addAssert c md $ Crucible.SimError loc $
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
  ( ?lc :: Crucible.TypeContext
  , ?memOpts :: Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
  , Crucible.HasLLVMAnn Sym
  ) =>
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
    go progress delayed (c:cs) =
      do ready <- checkPointsTo c
         if ready then
           do err <- learnPointsTo opts sc cc spec prepost c
              case err of
                Just msg -> do
                  doc <- ppPointsToAsLLVMVal opts cc sc spec c
                  failure (llvmPointsToProgramLoc c) (BadPointerLoad (Right doc) msg)
                Nothing  -> go True delayed cs
         else
           do go progress (c:delayed) cs

    -- determine if a precondition is ready to be checked
    checkPointsTo :: PointsTo (LLVM arch) -> OverrideMatcher (LLVM arch) md Bool
    checkPointsTo (LLVMPointsTo _loc _ p _) = checkSetupValue p
    checkPointsTo (LLVMPointsToBitfield _loc p _ _) = checkSetupValue p

    checkSetupValue :: SetupValue (LLVM arch) -> OverrideMatcher (LLVM arch) md Bool
    checkSetupValue v =
      do m <- OM (use setupValueSub)
         return (all (`Map.member` m) (setupVars v))

    -- Compute the set of variable identifiers in a 'SetupValue'
    setupVars :: SetupValue (LLVM arch) -> Set AllocIndex
    setupVars v =
      case v of
        SetupVar i                 -> Set.singleton i
        SetupStruct _ xs           -> foldMap setupVars xs
        SetupEnum  empty           -> absurd empty
        SetupTuple empty _         -> absurd empty
        SetupSlice empty           -> absurd empty
        SetupArray _ xs            -> foldMap setupVars xs
        SetupElem _ x _            -> setupVars x
        SetupField _ x _           -> setupVars x
        SetupCast _ x              -> setupVars x
        SetupUnion _ x _           -> setupVars x
        SetupTerm _                -> Set.empty
        SetupNull _                -> Set.empty
        SetupGlobal _ _            -> Set.empty
        SetupGlobalInitializer _ _ -> Set.empty
        SetupMux empty _ _ _       -> absurd empty


------------------------------------------------------------------------

computeReturnValue ::
  (?lc :: Crucible.TypeContext, ?w4EvalTactic :: W4EvalTactic, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
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
  MS.ConditionMetadata ->
  AllocIndex      {- ^ variable index -} ->
  LLVMPtr (Crucible.ArchWidth arch) {- ^ concrete value -} ->
  OverrideMatcher (LLVM arch) md ()

assignVar cc md var val =
  do let loc = MS.conditionLoc md
     old <- OM (setupValueSub . at var <<.= Just val)
     for_ old $ \val' ->
       do p <- liftIO (equalValsPred cc (Crucible.ptrToPtrVal val') (Crucible.ptrToPtrVal val))
          let msg = unlines
                [ "The following pointers had to alias, but they didn't:"
                , "  " ++ show (Crucible.ppPtr val)
                , "  " ++ show (Crucible.ppPtr val')
                ]
          addAssert p md $ Crucible.SimError loc $ Crucible.AssertFailureSimError msg ""

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
    (_, _)
      | Crucible.isPointerMemType x0 && Crucible.isPointerMemType y0 ->
          []
    (Crucible.IntType w, _)
      | Crucible.isPointerMemType y0 && w == wptr ->
          []
    (_, Crucible.IntType w)
      | Crucible.isPointerMemType x0 && w == wptr ->
          []
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
  (?w4EvalTactic :: W4EvalTactic) =>
  Options          {- ^ saw script print out opts -} ->
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  SharedContext      {- ^ context for constructing SAW terms    -} ->
  LLVMCrucibleContext arch {- ^ context for interacting with Crucible -} ->
  MS.CrucibleMethodSpecIR (LLVM arch) {- ^ specification for current function override  -} ->
  PrePost                                                          ->
  MS.ConditionMetadata ->
  Crucible.LLVMVal Sym
                     {- ^ concrete simulation value             -} ->
  Crucible.MemType   {- ^ expected memory type                  -} ->
  SetupValue (LLVM arch)         {- ^ expected specification value          -} ->
  OverrideMatcher (LLVM arch) md ()

matchArg opts sc cc cs prepost md actual expectedTy expected =
  ccWithBackend cc $ \bak -> do
  let sym = backendGetSym bak
  mem <- readGlobal $ Crucible.llvmMemVar $ ccLLVMContext cc
  case (actual, expectedTy, expected) of
    (_, _, SetupTerm expectedTT)
      | TypedTermSchema (Cryptol.Forall [] [] tyexpr) <- ttType expectedTT
      , Right tval <- Cryptol.evalType mempty tyexpr
        -> do failMsg  <- mkStructuralMismatch opts cc sc cs actual expected expectedTy
              realTerm <- valueToSC sym md failMsg tval actual
              instantiateExtMatchTerm sc md prepost realTerm (ttTerm expectedTT)

    -- match arrays point-wise
    (Crucible.LLVMValArray _ xs, Crucible.ArrayType _len y, SetupArray () zs)
      | V.length xs >= length zs ->
        sequence_
          [ matchArg opts sc cc cs prepost md x y z
          | (x, z) <- zip (V.toList xs) zs ]

    -- LLVM string literals are syntactic shorthand for [<N> x i8] arrays,
    -- so we defer to the LLVMValArray case above.
    (Crucible.LLVMValString xs, Crucible.ArrayType _len (Crucible.IntType 8), SetupArray () zs)
      | BS.length xs >= length zs ->
        do explodedActual <- liftIO $ Crucible.explodeStringValue sym xs
           matchArg opts sc cc cs prepost md explodedActual expectedTy expected

    -- match the fields of struct point-wise
    (Crucible.LLVMValStruct xs, Crucible.StructType fields, SetupStruct _ zs) ->
      sequence_
        [ matchArg opts sc cc cs prepost md x y z
        | ((_,x),y,z) <- zip3 (V.toList xs)
                              (V.toList (Crucible.fiType <$> Crucible.siFields fields))
                              zs ]

    (_, _, SetupEnum empty) ->
      absurd empty
    (_, _, SetupTuple empty _) ->
      absurd empty
    (_, _, SetupSlice empty) ->
      absurd empty

    (Crucible.LLVMValInt blk off, _, SetupElem () v i) | Crucible.isPointerMemType expectedTy ->
      do let tyenv = MS.csAllocations cs
             nameEnv = MS.csTypeNames cs
         delta <- exceptToFail $ resolveSetupElemOffset cc tyenv nameEnv v i
         off' <- liftIO $ W4.bvSub sym off
           =<< W4.bvLit sym (W4.bvWidth off) (Crucible.bytesToBV (W4.bvWidth off) delta)
         matchArg opts sc cc cs prepost md (Crucible.LLVMValInt blk off') expectedTy v

    (Crucible.LLVMValInt blk off, _, SetupField () v n) | Crucible.isPointerMemType expectedTy ->
      do let tyenv = MS.csAllocations cs
             nameEnv = MS.csTypeNames cs
         fld <- exceptToFail $
                  do info <- resolveSetupValueInfo cc tyenv nameEnv v
                     recoverStructFieldInfo cc tyenv nameEnv v info n
         let delta = fromIntegral $ Crucible.fiOffset fld
         off' <- liftIO $ W4.bvSub sym off
                    =<< W4.bvLit sym (W4.bvWidth off) (Crucible.bytesToBV (W4.bvWidth off) delta)
         matchArg opts sc cc cs prepost md (Crucible.LLVMValInt blk off') expectedTy v

    (_, _, SetupGlobalInitializer () _) -> resolveAndMatch
    (_, _, SetupMux empty _ _ _)        -> absurd empty

    (Crucible.LLVMValInt blk off, _, _) ->
      case expected of
        SetupVar var | Just Refl <- testEquality (W4.bvWidth off) Crucible.PtrWidth ->
          do assignVar cc md var (Crucible.LLVMPointer blk off)

        SetupNull () | Just Refl <- testEquality (W4.bvWidth off) Crucible.PtrWidth ->
          do p   <- liftIO (Crucible.ptrIsNull sym Crucible.PtrWidth (Crucible.LLVMPointer blk off))
             addAssert p md =<<
               notEqual prepost opts loc cc sc cs expected actual

        SetupGlobal () name | Just Refl <- testEquality (W4.bvWidth off) Crucible.PtrWidth ->
          do ptr2 <- liftIO $ Crucible.doResolveGlobal bak mem (L.Symbol name)
             pred_ <- liftIO $
               Crucible.ptrEq sym Crucible.PtrWidth (Crucible.LLVMPointer blk off) ptr2
             addAssert pred_ md =<<
               notEqual prepost opts loc cc sc cs expected actual

        _ -> failure loc =<<
              mkStructuralMismatch opts cc sc cs actual expected expectedTy

    _ -> failure loc =<<
           mkStructuralMismatch opts cc sc cs actual expected expectedTy

  where
    loc = MS.conditionLoc md

    resolveAndMatch = do
      (ty, val) <- resolveSetupValueLLVM opts cc sc cs expected
      sym  <- Ov.getSymInterface
      if diffMemTypes expectedTy ty /= []
      then failure loc =<<
            mkStructuralMismatch opts cc sc cs actual expected expectedTy
      else liftIO (Crucible.testEqual sym val actual) >>=
        \case
          Nothing -> failure loc BadEqualityComparison
          Just pred_ ->
            addAssert pred_ md =<<
              notEqual prepost opts loc cc sc cs expected actual

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
  MS.ConditionMetadata ->
  OverrideFailureReason (LLVM arch) ->
  Cryptol.TValue ->
  Crucible.LLVMVal Sym  ->
  OverrideMatcher (LLVM arch) md Term
valueToSC sym _md _failMsg _ts (Crucible.LLVMValZero gtp)
  = liftIO $
     do st <- liftIO (sawCoreState sym)
        let sc = saw_ctx st
        zeroValueSC sc gtp

valueToSC sym md failMsg (Cryptol.TVTuple tys) (Crucible.LLVMValStruct vals)
  | length tys == length vals
  = do terms <- traverse (\(ty, tm) -> valueToSC sym md failMsg ty (snd tm)) (zip tys (V.toList vals))
       st <- liftIO (sawCoreState sym)
       let sc = saw_ctx st
       liftIO (scTupleReduced sc terms)

valueToSC sym md failMsg (Cryptol.TVSeq _n Cryptol.TVBit) (Crucible.LLVMValInt base off) =
  do let loc = MS.conditionLoc md
     baseZero <- liftIO (W4.natEq sym base =<< W4.natLit sym 0)
     st <- liftIO (sawCoreState sym)
     offTm <- liftIO (toSC sym st off)
     case W4.asConstantPred baseZero of
       Just True  -> return offTm
       Just False -> failure loc failMsg
       _ -> do addAssert baseZero md (Crucible.SimError loc (Crucible.GenericSimError "Expected bitvector value, but found pointer"))
               return offTm

-- This is a case for pointers, when we opaque types in Cryptol to represent them...
-- valueToSC sym _tval (Crucible.LLVMValInt base off) =
--   do base' <- Crucible.toSC sym base
--      off'  <- Crucible.toSC sym off
--      sc    <- Crucible.saw_ctx <$> sawCoreState sym
--      Just <$> scTuple sc [base', off']

valueToSC sym md failMsg (Cryptol.TVSeq n cryty) (Crucible.LLVMValArray ty vals)
  | toInteger (length vals) == n
  = do terms <- V.toList <$> traverse (valueToSC sym md failMsg cryty) vals
       st <- liftIO (sawCoreState sym)
       let sc = saw_ctx st
       t <- liftIO (typeToSC sc ty)
       liftIO (scVectorReduced sc t terms)

-- LLVM string literals are syntactic shorthand for [<N> x i8] arrays, so we
-- defer to the LLVMValArray case above.
valueToSC sym md failMsg tval@(Cryptol.TVSeq n (Cryptol.TVSeq 8 Cryptol.TVBit)) (Crucible.LLVMValString str)
  | toInteger (BS.length str) == n
  = do explodedVal <- liftIO $ Crucible.explodeStringValue sym str
       valueToSC sym md failMsg tval explodedVal

valueToSC _ _ _ _ Crucible.LLVMValFloat{} =
  fail  "valueToSC: Real not supported"

valueToSC _sym md failMsg _tval _val =
  failure (MS.conditionLoc md) failMsg

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

-- | Use the current state to learn about variable assignments based on
-- preconditions for a procedure specification.
learnSetupCondition ::
  (?lc :: Crucible.TypeContext, ?w4EvalTactic :: W4EvalTactic, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options                    ->
  SharedContext              ->
  LLVMCrucibleContext arch       ->
  MS.CrucibleMethodSpecIR (LLVM arch)       ->
  PrePost                    ->
  MS.SetupCondition (LLVM arch) ->
  OverrideMatcher (LLVM arch) md ()
learnSetupCondition opts sc cc spec prepost cond =
  case cond of
    MS.SetupCond_Equal md val1 val2 -> learnEqual opts sc cc spec md prepost val1 val2
    MS.SetupCond_Pred md tm         -> learnPred sc cc md prepost (ttTerm tm)
    MS.SetupCond_Ghost md var val   -> learnGhost sc md prepost var val


------------------------------------------------------------------------

-- | Process a "points_to" statement from the precondition section of
-- the CrucibleSetup block. First, load the value from the address
-- indicated by 'ptr', and then match it against the pattern 'val'.
--
-- Returns a string on failure describing a concrete memory load failure.
learnPointsTo ::
  forall arch md ann.
  ( ?lc :: Crucible.TypeContext
  , ?memOpts :: Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
  , Crucible.HasLLVMAnn Sym
  ) =>
  Options ->
  SharedContext ->
  LLVMCrucibleContext arch ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  PrePost ->
  PointsTo (LLVM arch) ->
  OverrideMatcher (LLVM arch) md (Maybe (PP.Doc ann))
learnPointsTo opts sc cc spec prepost (LLVMPointsTo md maybe_cond ptr val) =
  do (_memTy, ptr1) <- resolveSetupValue opts cc sc spec Crucible.PtrRepr ptr
     matchPointsToValue opts sc cc spec prepost md maybe_cond ptr1 val
learnPointsTo opts sc cc spec prepost (LLVMPointsToBitfield md ptr fieldName val) =
  do (bfIndex, ptr1) <- resolveSetupValueBitfield opts cc sc spec ptr fieldName
     matchPointsToBitfieldValue opts sc cc spec prepost md ptr1 bfIndex val

matchPointsToValue ::
  forall arch md ann.
  ( ?lc :: Crucible.TypeContext
  , ?memOpts :: Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
  , Crucible.HasLLVMAnn Sym
  ) =>
  Options ->
  SharedContext ->
  LLVMCrucibleContext arch ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  PrePost ->
  MS.ConditionMetadata ->
  Maybe TypedTerm ->
  LLVMPtr (Crucible.ArchWidth arch) ->
  LLVMPointsToValue arch ->
  OverrideMatcher (LLVM arch) md (Maybe (PP.Doc ann))
matchPointsToValue opts sc cc spec prepost md maybe_cond ptr val =
  do let tyenv = MS.csAllocations spec
         nameEnv = MS.csTypeNames spec
         loc = MS.conditionLoc md
     sym    <- Ov.getSymInterface

     mem    <- readGlobal $ Crucible.llvmMemVar
                          $ ccLLVMContext cc

     let alignment = Crucible.noAlignment -- default to byte alignment (FIXME, see #338)

     case val of
       ConcreteSizeValue val' ->
         do memTy <- exceptToFail $ typeOfSetupValue cc tyenv nameEnv val'
            -- In case the types are different (from llvm_points_to_untyped)
            -- then the load type should be determined by the rhs.
            storTy <- Crucible.toStorableType memTy
            res <- liftIO $ Crucible.loadRaw sym mem ptr storTy alignment
            let badLoadSummary = summarizeBadLoad cc memTy prepost ptr
            case res of
              Crucible.NoErr pred_ res_val -> do
                -- If dealing with an `llvm_conditional_points_to` statement,
                -- convert the condition to a `Pred`. If dealing with an
                -- ordinary `llvm_points_to` statement, this condition will
                -- simply be `True`.
                cond' <- case maybe_cond of
                  Just cond ->
                    instantiateExtResolveSAWPred sc cc (ttTerm cond)
                  Nothing ->
                    pure $ W4.truePred sym
                -- Next, construct an implication involving the condition and
                -- assert it.
                pred_' <- liftIO $ W4.impliesPred sym cond' pred_
                addAssert pred_' md $ Crucible.SimError loc $
                  Crucible.AssertFailureSimError (show $ PP.vcat badLoadSummary) ""

                -- Finally, match the value that the pointer points to against
                -- the right-hand side value in the points_to statement. Make
                -- sure to execute this match with an extended path condition
                -- that takes the condition above into account. See also
                -- Note [oeConditionalPred] in SAWCentral.Crucible.Common.Override.
                withConditionalPred cond' $
                  pure Nothing <* matchArg opts sc cc spec prepost md res_val memTy val'
              _ -> do
                pure $ Just $ describeConcreteMemoryLoadFailure mem badLoadSummary ptr

       SymbolicSizeValue expected_arr_tm expected_sz_tm ->
         do maybe_allocation_array <- liftIO $
              Crucible.asMemAllocationArrayStore sym Crucible.PtrWidth ptr (Crucible.memImplHeap mem)
            let errMsg = PP.vcat $ map (PP.pretty . unwords)
                  [ [ "When reading through pointer:", show (Crucible.ppPtr ptr) ]
                  , [ "in the ", MS.stateCond prepost, "of an override" ]
                  , [ "Tried to read an array prefix of size:", show (MS.ppTypedTerm expected_sz_tm) ]
                  ]
            case maybe_allocation_array of
              Just (ok, arr, sz)
                | Crucible.LLVMPointer _ off <- ptr ->
                do addAssert ok md $ Crucible.SimError loc $ Crucible.GenericSimError $ show errMsg
                   sub <- OM (use termSub)
                   st <- liftIO (sawCoreState sym)

                   ptr_width_tm <- liftIO $ scNat sc $ natValue ?ptrWidth
                   off_type_tm <- liftIO $ scBitvector sc $ natValue ?ptrWidth
                   off_tm <- liftIO $ toSC sym st off
                   alloc_arr_tm <- liftIO $ toSC sym st arr

                   arr_tm <- liftIO $ case BV.asUnsigned <$> W4.asBV off of
                     Just 0 -> return alloc_arr_tm
                     _ ->
                       do byte_width_tm <- scNat sc 8
                          byte_type_tm <- scBitvector sc 8

                          zero_off_tm <- scBvNat sc ptr_width_tm =<< scNat sc 0
                          zero_byte_tm <- scBvNat sc byte_width_tm =<< scNat sc 0
                          zero_arr_const_tm <- scArrayConstant sc off_type_tm byte_type_tm zero_byte_tm

                          instantiated_expected_sz_tm <- scInstantiateExt sc sub $ ttTerm expected_sz_tm
                          scArrayCopy sc ptr_width_tm byte_type_tm
                            zero_arr_const_tm -- dest array
                            zero_off_tm -- dest offset
                            alloc_arr_tm -- src array
                            off_tm -- src offset
                            instantiated_expected_sz_tm -- length

                   instantiateExtMatchTerm sc md prepost arr_tm $ ttTerm expected_arr_tm

                   sz_tm <- liftIO $ toSC sym st sz
                   expected_end_off_tm <- liftIO $ scBvAdd sc ptr_width_tm off_tm $ ttTerm expected_sz_tm
                   inbounds_check_tm <- liftIO $ scBvULe sc ptr_width_tm expected_end_off_tm sz_tm
                   learnPred sc cc md prepost inbounds_check_tm

                   return Nothing

              _ ->
                do sub <- OM (use termSub)
                   modmap <- liftIO $ scGetModuleMap sc
                   instantiated_expected_sz_tm <- liftIO $ scInstantiateExt sc sub $ ttTerm expected_sz_tm
                   normalized_expected_sz_tm <- liftIO $
                     normalizeSharedTerm sc modmap mempty mempty mempty instantiated_expected_sz_tm
                   case asUnsignedConcreteBv normalized_expected_sz_tm of
                     Just sz_nat ->
                       do sz_bv <- liftIO $
                            W4.bvLit sym Crucible.PtrWidth $ BV.mkBV Crucible.PtrWidth $ fromIntegral sz_nat
                          maybe_matching_array <- liftIO $
                            Crucible.asMemMatchingArrayStore sym Crucible.PtrWidth ptr sz_bv (Crucible.memImplHeap mem)
                          res <- case maybe_matching_array of
                            Just (ok, arr) -> return $ Right (ok, arr)
                            Nothing -> liftIO $ Crucible.loadArrayConcreteSizeRaw sym mem ptr sz_nat alignment

                          case res of
                            Right (ok, arr) ->
                              do addAssert ok md $ Crucible.SimError loc $ Crucible.GenericSimError $ show errMsg
                                 st <- liftIO (sawCoreState sym)
                                 arr_tm <- liftIO $ toSC sym st arr
                                 instantiateExtMatchTerm sc md prepost arr_tm $ ttTerm expected_arr_tm
                                 return Nothing

                            Left{} -> return $ Just errMsg

                     Nothing -> return $ Just errMsg


-- | Like 'matchPointsToValue', but specifically geared towards the needs
-- of fields within bitfields. In particular, this performs all of the
-- necessary bit-twiddling on the LHS (a bitfield) to extract the necessary
-- field and match it against the RHS.
matchPointsToBitfieldValue ::
  forall arch md ann.
  ( ?memOpts :: Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
  , Crucible.HasLLVMAnn Sym
  ) =>
  Options ->
  SharedContext ->
  LLVMCrucibleContext arch ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  PrePost ->
  MS.ConditionMetadata ->
  LLVMPtr (Crucible.ArchWidth arch) ->
  BitfieldIndex ->
  SetupValue (LLVM arch) ->
  OverrideMatcher (LLVM arch) md (Maybe (PP.Doc ann))
matchPointsToBitfieldValue opts sc cc spec prepost md ptr bfIndex val =
  do let loc = MS.conditionLoc md
     sym    <- Ov.getSymInterface

     mem    <- readGlobal $ Crucible.llvmMemVar
                          $ ccLLVMContext cc

     let alignment = Crucible.noAlignment -- default to byte alignment (FIXME, see #338)

     -- Unlike in matchPointsToValue, we compute the MemTy/StorageType not from
     -- the RHS value, but from the BitfieldIndex. This is because we need to
     -- load the entire bitfield, which can be larger than the size of the RHS
     -- value.
     let memTy = biBitfieldType bfIndex
     storTy <- Crucible.toStorableType memTy
     res <- liftIO $ Crucible.loadRaw sym mem ptr storTy alignment
     let badLoadSummary = summarizeBadLoad cc memTy prepost ptr
     case res of
       Crucible.NoErr pred_ res_val -> do
         addAssert pred_ md $ Crucible.SimError loc $
           Crucible.AssertFailureSimError (show $ PP.vcat badLoadSummary) ""
         case res_val of
           -- This will only work if:
           --
           -- * The bitfield is in fact a bitvector, and
           -- * The width of the RHS type is less than the width of the
           --   bitfield type.
           --
           -- We check these criteria in this case.
           Crucible.LLVMValInt bfBlk bfBV
             |  let bfWidth = W4.bvWidth bfBV
             ,  Some rhsWidth <- mkNatRepr $ fromIntegral $ biFieldSize bfIndex
             -> case (testLeq (knownNat @1) rhsWidth, testLeq (incNat rhsWidth) bfWidth) of
                  (Just LeqProof, Just LeqProof) ->
                    do -- Here is where we perform the bit-twiddling needed
                       -- to match the RHS value against the field within the
                       -- bitfield. We will use this as a running example:
                       --
                       --   struct s {
                       --     int32_t w;
                       --     uint8_t x1:1;
                       --     uint8_t x2:2;
                       --     uint8_t y:1;
                       --     int32_t z;
                       --   };
                       --
                       -- Let us imagine that we are matching against the
                       -- `y` field. The bitfield (bfBV) will look something
                       -- like 0b????Y???, where `Y` denotes the value of the
                       -- `y` bit. Here, `bfWidth` (the width of the entire
                       -- bitfield in bits) is 8, and `rhsWidth` (the width of
                       -- the `y` field in bits) is 1.

                       -- The offset (in bits) of the field within the
                       -- bitfield. For `y`, this is 3 (x1's offset is 0 and
                       -- `x2`'s offset is 1).
                       Some bfOffset <- pure $ mkNatRepr $ fromIntegral
                                             $ biFieldOffset bfIndex

                       -- Next, convince the typechecker that
                       -- (bfOffset + rhsWidth) <= bfWidth. This should always
                       -- be the case if the BitfieldIndex is constructed
                       -- correctly.
                       LeqProof <- case testLeq (addNat bfOffset rhsWidth) bfWidth of
                         Just prf -> pure prf
                         Nothing ->
                           panic "llvm_points_to_bitfield (in matchPointsToBitfieldValue)" [
                               "Unexpected bitfield field offset",
                               "Field offset: " <> pack (show bfOffset),
                               "RHS value width: " <> pack (show rhsWidth),
                               "Bitvector width: " <> pack (show bfWidth)
                           ]

                       -- Finally, select the subsequence of bits from the
                       -- bitfield corresponding to the field. In the `y`
                       -- example, the means selecting `0bY` from `0b????Y???`.
                       bfFieldBV <- liftIO $ W4.bvSelect sym bfOffset rhsWidth bfBV

                       -- Match the selected field against the RHS value.
                       let field_val = Crucible.LLVMValInt bfBlk bfFieldBV
                       pure Nothing <* matchArg opts sc cc spec prepost md field_val memTy val
                  _ ->
                    fail $ unlines
                      [ "llvm_points_to_bitfield: RHS value's size must be less then or equal to bitfield's size"
                      , "Bitvector width: " ++ show bfWidth
                      , "RHS value width: " ++ show rhsWidth
                      ]
           _ -> fail $ unlines
                  [ "llvm_points_to_bitfield: The bitfield must be a bitvector"
                  , "Bitfield value: " ++ show (Crucible.ppTermExpr res_val)
                  ]
       _ ->
         -- When we have a concrete failure, we do a little more computation to
         -- try and find out why.
         pure $ Just $ describeConcreteMemoryLoadFailure mem badLoadSummary ptr

-- | Give a general summary of why a call to 'Crucible.loadRaw' in
-- @matchPointsTo{Bitfield}Value@ failed. This is used for error-message
-- purposes.
summarizeBadLoad ::
  LLVMCrucibleContext arch ->
  Crucible.MemType ->
  PrePost ->
  LLVMPtr wptr ->
  [PP.Doc ann]
summarizeBadLoad cc memTy prepost ptr =
 let dataLayout = Crucible.llvmDataLayout (ccTypeCtx cc)
     sz = Crucible.memTypeSize dataLayout memTy
 in map (PP.pretty . unwords)
    [ [ "When reading through pointer:", show (Crucible.ppPtr ptr) ]
    , [ "in the ", MS.stateCond prepost, "of an override" ]
    , [ "Tried to read something of size:"
      , show (Crucible.bytesToInteger sz)
      ]
    , [ "And type:", show (Crucible.ppMemType memTy) ]
    ]

-- | Give a summary of why a call to 'Crucible.loadRaw' in
-- @matchPointsTo{Bitfield}Value@ concretely failed. This is used for
-- error-message purposes.
describeConcreteMemoryLoadFailure ::
  Crucible.MemImpl Sym ->
  [PP.Doc ann] {- A summary of why the load failed -} ->
  LLVMPtr w ->
  PP.Doc ann
describeConcreteMemoryLoadFailure mem badLoadSummary ptr = do
  let (blk, _offset) = Crucible.llvmPointerView ptr
  PP.vcat . (badLoadSummary ++) $
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

------------------------------------------------------------------------

-- | Process an @llvm_equal@ statement from the precondition
-- section of the CrucibleSetup block.
learnEqual ::
  (?w4EvalTactic :: W4EvalTactic, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options                                          ->
  SharedContext                                    ->
  LLVMCrucibleContext arch                            ->
  MS.CrucibleMethodSpecIR (LLVM arch)                             ->
  MS.ConditionMetadata                             ->
  PrePost                                          ->
  SetupValue (LLVM arch)       {- ^ first value to compare  -} ->
  SetupValue (LLVM arch)       {- ^ second value to compare -} ->
  OverrideMatcher (LLVM arch) md ()
learnEqual opts sc cc spec md prepost v1 v2 = do
  (_, val1) <- resolveSetupValueLLVM opts cc sc spec v1
  (_, val2) <- resolveSetupValueLLVM opts cc sc spec v2
  p         <- liftIO (equalValsPred cc val1 val2)
  let name = "equality " ++ MS.stateCond prepost
  let loc = MS.conditionLoc md
  addAssert p md (Crucible.SimError loc (Crucible.AssertFailureSimError name ""))

-- | Process an @llvm_precond@ statement from the precondition
-- section of the CrucibleSetup block.
learnPred ::
  (?w4EvalTactic :: W4EvalTactic) =>
  SharedContext                                                       ->
  LLVMCrucibleContext arch                                               ->
  MS.ConditionMetadata                                                ->
  PrePost                                                             ->
  Term             {- ^ the precondition to learn                  -} ->
  OverrideMatcher (LLVM arch) md ()
learnPred sc cc md prepost t =
  do p <- instantiateExtResolveSAWPred sc cc t
     let loc = MS.conditionLoc md
     addAssert p md (Crucible.SimError loc (Crucible.AssertFailureSimError (MS.stateCond prepost) ""))

instantiateExtResolveSAWPred ::
  (?w4EvalTactic :: W4EvalTactic) =>
  SharedContext ->
  LLVMCrucibleContext arch ->
  Term ->
  OverrideMatcher (LLVM arch) md (W4.Pred Sym)
instantiateExtResolveSAWPred sc cc cond = do
  sub <- OM (use termSub)
  liftIO $ resolveSAWPred cc =<< scInstantiateExt sc sub cond

instantiateExtResolveSAWSymBV ::
  (?w4EvalTactic :: W4EvalTactic, 1 <= w) =>
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
  , ?memOpts :: Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
  , Crucible.HasLLVMAnn Sym
  ) =>
  Options ->
  SharedContext ->
  LLVMCrucibleContext arch ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  OverrideMatcher (LLVM arch) RW (Map (W4.SymNat Sym) Text)
invalidateMutableAllocs opts sc cc cs =
  ccWithBackend cc $ \bak -> do
  let sym = backendGetSym bak
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
                  , pack . show . W4.plSourceLoc . MS.conditionLoc
                      $ spec ^. allocSpecMd
                  , ") not described in postcondition"
                  ]
                )
            | otherwise -> Nothing)
        (Map.elems (Map.intersectionWith (,) sub mutableAllocs))
      mtrans = ccLLVMModuleTrans cc
      gimap = view Crucible.globalInitMap mtrans
      mutableGlobals = cs ^. MS.csGlobalAllocs

  globalPtrs <- liftIO . fmap catMaybes . forM mutableGlobals $ \(LLVMAllocGlobal loc s@(L.Symbol st)) ->
    case Map.lookup s gimap of
      Just (_, Right (mt, _)) -> do
        ptr <- Crucible.doResolveGlobal bak mem s
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
  postPtrs <- Set.fromList <$> catMaybes <$> traverse
    (\case
      LLVMPointsTo _loc _cond ptr val -> case val of
        ConcreteSizeValue val' -> do
          (_, Crucible.LLVMPointer blk _) <- resolveSetupValue opts cc sc cs Crucible.PtrRepr ptr
          memTy <- exceptToFail $
                     typeOfSetupValue cc (MS.csAllocations cs) (MS.csTypeNames cs) val'
          sz <- Crucible.storageTypeSize <$> Crucible.toStorableType memTy
          return $ Just (W4.asNat blk, sz)
        SymbolicSizeValue{} -> return Nothing
      LLVMPointsToBitfield _loc ptr fieldName _val -> do
        (bfIndex, Crucible.LLVMPointer blk _) <-
          resolveSetupValueBitfield opts cc sc cs ptr fieldName
        let memTy = biBitfieldType bfIndex
        storTy <- Crucible.toStorableType memTy
        let sz = Crucible.storageTypeSize storTy
        pure $ Just (W4.asNat blk, sz))
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
                    liftIO $ Crucible.doInvalidate bak ?ptrWidth m ptr msg
                      =<< W4.bvLit sym ?ptrWidth (Crucible.bytesToBV ?ptrWidth sz)
                ) mem danglingPtrs

  writeGlobal (Crucible.llvmMemVar $ ccLLVMContext cc) mem'

  return overwritten_allocs

------------------------------------------------------------------------

-- | Perform an allocation as indicated by an @llvm_alloc@ or
-- @llvm_fresh_pointer@ statement from the postcondition section.
executeAllocation ::
  ( ?lc :: Crucible.TypeContext
  , ?memOpts :: Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
  , Crucible.HasLLVMAnn Sym
  ) =>
  Options                        ->
  SharedContext ->
  LLVMCrucibleContext arch          ->
  (AllocIndex, LLVMAllocSpec) ->
  OverrideMatcher (LLVM arch) RW ()
executeAllocation opts sc cc (var, LLVMAllocSpec mut memTy alignment sz md fresh initialization)
  | fresh =
  do ptr <- liftIO $ executeFreshPointer cc var
     OM (setupValueSub %= Map.insert var ptr)
  | otherwise =
  ccWithBackend cc $ \bak -> do
     {-
     memTy <- case Crucible.asMemType symTy of
                Just memTy -> return memTy
                Nothing    -> fail "executAllocation: failed to resolve type"
                -}
     liftIO $ printOutLn opts Debug $ unwords ["executeAllocation:", show var, show memTy]
     let memVar = Crucible.llvmMemVar (ccLLVMContext cc)
     mem <- readGlobal memVar
     sz' <- instantiateExtResolveSAWSymBV sc cc Crucible.PtrWidth sz
     let loc = MS.conditionLoc md
     let l = show (W4.plSourceLoc loc) ++ " (Poststate)"
     (ptr, mem') <- liftIO $ doAllocSymInit bak mem mut alignment sz' l initialization
     writeGlobal memVar mem'
     assignVar cc md var ptr

doAllocSymInit ::
  ( ?memOpts :: Crucible.MemOptions
  , Crucible.IsSymInterface sym
  , Crucible.HasPtrWidth wptr
  , Crucible.HasLLVMAnn sym
  , IsSymBackend sym bak
  ) =>
  bak ->
  Crucible.MemImpl sym ->
  Crucible.Mutability ->
  Crucible.Alignment ->
  W4.SymBV sym wptr {- ^ allocation size -} ->
  String {- ^ source location for use in error messages -} ->
  LLVMAllocSpecInit {- ^ allocation initialization policy -} ->
  IO (Crucible.LLVMPtr sym wptr, Crucible.MemImpl sym)
doAllocSymInit bak mem mut alignment sz loc initialization  = do
  (ptr, mem') <- Crucible.doMalloc bak Crucible.HeapAlloc mut loc mem sz alignment
  mem'' <- case initialization of
    LLVMAllocSpecSymbolicInitialization -> do
      arr <- W4.freshConstant
        (backendGetSym bak)
        (W4.systemSymbol "arr!")
        (W4.BaseArrayRepr (Ctx.singleton $ W4.BaseBVRepr ?ptrWidth) (W4.BaseBVRepr (W4.knownNat @8)))
      Crucible.doArrayConstStore bak mem' ptr alignment arr sz
    LLVMAllocSpecNoInitialization -> return mem'
  return (ptr, mem'')

------------------------------------------------------------------------

-- | Update the simulator state based on the postconditions from the
-- procedure specification.
executeSetupCondition ::
  (?lc :: Crucible.TypeContext, ?w4EvalTactic :: W4EvalTactic, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options                    ->
  SharedContext              ->
  LLVMCrucibleContext arch     ->
  MS.CrucibleMethodSpecIR (LLVM arch)       ->
  MS.SetupCondition (LLVM arch) ->
  OverrideMatcher (LLVM arch) RW ()
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
  ( ?lc :: Crucible.TypeContext
  , ?memOpts :: Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
  , Crucible.HasLLVMAnn Sym
  ) =>
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
executePointsTo opts sc cc spec _overwritten_allocs (LLVMPointsToBitfield _loc ptr fieldName val) =
  do (bfIndex, ptr') <- resolveSetupValueBitfield opts cc sc spec ptr fieldName
     let memVar = Crucible.llvmMemVar (ccLLVMContext cc)
     mem <- readGlobal memVar

     m <- OM (use setupValueSub)
     s <- OM (use termSub)
     let tyenv = MS.csAllocations spec
     let nameEnv = MS.csTypeNames spec
     val' <- liftIO $ instantiateSetupValue sc s val

     mem' <- liftIO $ storePointsToBitfieldValue opts cc m tyenv nameEnv mem ptr' bfIndex val'
     writeGlobal memVar mem'

storePointsToValue ::
  ( ?memOpts :: Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
  , Crucible.HasLLVMAnn Sym
  ) =>
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
storePointsToValue opts cc env tyenv nameEnv base_mem maybe_cond ptr val maybe_invalidate_msg =
  ccWithBackend cc $ \bak -> do
  let sym = backendGetSym bak

  let alignment = Crucible.noAlignment -- default to byte alignment (FIXME, see #338)

  smt_array_memory_model_enabled <- W4.getOpt
    =<< W4.getOptionSetting enableSMTArrayMemoryModel (W4.getConfiguration sym)

  let store_op = \mem -> case val of
        ConcreteSizeValue val' -> do
          memTy <- exceptToFail $ typeOfSetupValue cc tyenv nameEnv val'
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
                Crucible.doArrayConstStore bak mem ptr alignment arr sz
            _ -> do
              val'' <- X.handle (handleException opts) $
                resolveSetupVal cc mem env tyenv nameEnv val'
              Crucible.storeConstRaw bak mem ptr storTy alignment val''
        SymbolicSizeValue arr_tm sz_tm -> do
          st <- sawCoreState sym
          arr <- bindSAWTerm
            sym st
            (W4.BaseArrayRepr
              (Ctx.singleton $ W4.BaseBVRepr ?ptrWidth)
              (W4.BaseBVRepr (W4.knownNat @8)))
            (ttTerm arr_tm)
          sz <- resolveSAWSymBV cc ?ptrWidth $ ttTerm sz_tm
          Crucible.doArrayConstStore bak mem ptr alignment arr sz

  case maybe_cond of
    Just cond -> case maybe_invalidate_msg of
      Just invalidate_msg -> do
        let invalidate_op = \mem -> do
              sz <- case val of
                ConcreteSizeValue val' -> do
                  memTy <- exceptToFail $ typeOfSetupValue cc tyenv nameEnv val'
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
              Crucible.doInvalidate bak ?ptrWidth mem ptr invalidate_msg sz
        Crucible.mergeWriteOperations bak base_mem cond store_op invalidate_op
      Nothing ->
        Crucible.doConditionalWriteOperation bak base_mem cond store_op
    Nothing -> store_op base_mem

-- | Like 'storePointsToValue', but specifically geared towards the needs
-- of fields within bitfields. In particular, this performs all of the
-- necessary bit-twiddling on the LHS (a bitfield) to store the RHS value in
-- the right place in the bitfield.
storePointsToBitfieldValue ::
  ( ?memOpts :: Crucible.MemOptions
  , ?w4EvalTactic :: W4EvalTactic
  , Crucible.HasPtrWidth (Crucible.ArchWidth arch)
  , Crucible.HasLLVMAnn Sym
  ) =>
  Options ->
  LLVMCrucibleContext arch ->
  Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)) ->
  Map AllocIndex (MS.AllocSpec (LLVM arch)) ->
  Map AllocIndex (MS.TypeName (LLVM arch)) ->
  Crucible.MemImpl Sym ->
  LLVMPtr (Crucible.ArchWidth arch) ->
  BitfieldIndex ->
  SetupValue (LLVM arch) ->
  IO (Crucible.MemImpl Sym)
storePointsToBitfieldValue opts cc env tyenv nameEnv base_mem ptr bfIndex val =
  ccWithBackend cc $ \bak -> do
  let sym = backendGetSym bak

  let alignment = Crucible.noAlignment -- default to byte alignment (FIXME, see #338)

  smt_array_memory_model_enabled <- W4.getOpt
    =<< W4.getOptionSetting enableSMTArrayMemoryModel (W4.getConfiguration sym)

  -- Unlike in storePointsToValue, we compute the MemTy/StorageType not from
  -- the RHS value, but from the BitfieldIndex. This is because we need to
  -- load the entire bitfield, which can be larger than the size of the RHS
  -- value.
  let memTy = biBitfieldType bfIndex
  storTy <- Crucible.toStorableType memTy

  case val of
    SetupTerm _tm
      | smt_array_memory_model_enabled ->
        -- See #1540.
        fail $ unlines
          [ "llvm_points_to_bitfield currently does not work in"
          , "combination with the enable_smt_array_memory_model option."
          ]
    _ -> do
      -- Resolve the RHS value as an LLVMVal.
      rhsVal <- X.handle (handleException opts) $
        resolveSetupVal cc base_mem env tyenv nameEnv val

      -- Load the bitfield that `ptr` points to.
      bfLoadedVal <- Crucible.loadRaw sym base_mem ptr storTy alignment

      -- Assert that the bitfield was loaded successfully. If not, abort.
      let badLoadSummary = summarizeBadLoad cc memTy PreState ptr
      bfVal <- case bfLoadedVal of
        Crucible.NoErr p res_val -> do
          let rsn = Crucible.AssertFailureSimError "Error loading bitvector" $
                    show badLoadSummary
          Crucible.assert bak p rsn
          pure res_val
        Crucible.Err _p ->
          fail $ show $ describeConcreteMemoryLoadFailure base_mem badLoadSummary ptr

      case (bfVal, rhsVal) of
        -- This will only work if:
        --
        -- * Both the bitfield and the RHS value are bitvectors, and
        -- * The width of the RHS type is less than or equal to the width
        --   of the bitfield type.
        --
        -- We check these criteria in this case.
        (Crucible.LLVMValInt bfBlk bfBV, Crucible.LLVMValInt _rhsBlk rhsBV)
          -> let bfWidth = W4.bvWidth bfBV
                 rhsWidth = W4.bvWidth rhsBV in
             case testLeq (incNat rhsWidth) bfWidth of
               Nothing ->
                 fail $ unlines
                   [ "llvm_points_to_bitfield: RHS value's size must be less then or equal to bitfield's size"
                   , "Bitvector width: " ++ show bfWidth
                   , "RHS value width: " ++ show rhsWidth
                   ]
               Just LeqProof ->
                 do -- Here is where we perform the bit-twiddling needed
                    -- to store the RHS value in the bitfield. We will use
                    -- this as a running example:
                    --
                    --   struct s {
                    --     int32_t w;
                    --     uint8_t x1:1;
                    --     uint8_t x2:2;
                    --     uint8_t y:1;
                    --     int32_t z;
                    --   };
                    --
                    -- Let us imagine that we are setting the `y` field to
                    -- be 1.
                    let -- The offset (in bits) of the field within the
                        -- bitfield. For `y`, this is 3 (x1's offset is 0
                        -- and `x2`'s offset is 1).
                        bfOffset   = biFieldOffset bfIndex
                        bfOffsetBV = BV.mkBV bfWidth $ fromIntegral bfOffset

                        -- A bitmask with the nth bit (zero-indexed) is
                        -- set, where n equals the size of the field
                        -- (in bits) within the bitfield. Since `y` is
                        -- 1-bit, this would make `fieldBitsBV` be
                        -- 0b00000010, or 2.
                        fieldBitsBV = BV.bit' bfWidth $
                                      fromIntegral $ biFieldSize bfIndex

                        -- A bitmask with the (n-1) least significant bits
                        -- set to 1, where n equals the value of
                        -- `fieldBitsBV`. For `y`, `leastBitsBV` would be
                        -- equal to 0b00000001, or 1.
                        leastBitsBV = BV.sub bfWidth fieldBitsBV (BV.one bfWidth)

                        -- A bitmask with the bits corresponding to the
                        -- field within the bitfield set to 1, and all
                        -- other bits are set to 0. For `y`, `bitmaskBV`
                        -- would be equal to 0b00001000, or 8.
                        bitmaskBV = BV.shl bfWidth leastBitsBV $ fromIntegral bfOffset

                        -- A bitmask with the bits corresponding to the
                        -- field within the bitfield set to 0, and all
                        -- other bits are set to 1. For `y`, `compBitmaskBV`
                        -- would be equal to 0b11110111, or 247.
                        compBitmaskBV = BV.complement bfWidth bitmaskBV
                    compBitmaskSymBV <- W4.bvLit sym bfWidth compBitmaskBV

                    -- Clear all of the bits in the bitfield
                    -- corresponding to the field, leaving all other bits
                    -- unchanged. If the original bitvector was 0b????????,
                    -- then `bfBV'` is 0b????0???.
                    bfBV' <- W4.bvAndBits sym bfBV compBitmaskSymBV

                    -- Zero-extend the RHS value to be the same width as
                    -- the bitfield. In our running example, we
                    -- zero-extend 0b1 (1) to 0b00000001.
                    rhsBV' <- W4.bvZext sym bfWidth rhsBV

                    -- Left-shift the zero-extended RHS value such that
                    -- its contents are in the same position as the field
                    -- in the bitfield. In our running example, `rhsBV''`
                    -- is 0b00001000, or 8.
                    rhsBV'' <- W4.bvShl sym rhsBV' =<< W4.bvLit sym bfWidth bfOffsetBV

                    -- Finally, set the bits in the bitfield to the RHS
                    -- value with a bitwise-XOR operation. (We could just as
                    -- well use bitwise-OR, but bitwise-XOR plays nicer with
                    -- how What4 represents bitvectors). In our running
                    -- example, `bfBV''` is 0b????1???.
                    bfBV'' <- W4.bvXorBits sym bfBV' rhsBV''

                    -- Store the bitfield's value back to memory.
                    --
                    -- Bear in mind that this whole process is repeated once per
                    -- field, even if the fields all reside within the same
                    -- bitfield. See #1541 for an alternative approach that
                    -- would optimize this further.
                    let bfVal' = Crucible.LLVMValInt bfBlk bfBV''
                    Crucible.storeConstRaw bak base_mem ptr storTy alignment bfVal'
        _ -> fail $ unlines
               [ "llvm_points_to_bitfield: Both the bitfield and RHS value must be bitvectors"
               , "Bitfield value: " ++ show (Crucible.ppTermExpr bfVal)
               , "RHS value: " ++ show (MS.ppSetupValue val)
               ]


------------------------------------------------------------------------


-- | Process an @llvm_equal@ statement from the postcondition
-- section of the CrucibleSetup block.
executeEqual ::
  (?w4EvalTactic :: W4EvalTactic, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options                                          ->
  SharedContext                                    ->
  LLVMCrucibleContext arch                           ->
  MS.CrucibleMethodSpecIR (LLVM arch)                             ->
  MS.ConditionMetadata ->
  SetupValue (LLVM arch)       {- ^ first value to compare  -} ->
  SetupValue (LLVM arch)       {- ^ second value to compare -} ->
  OverrideMatcher (LLVM arch) md ()
executeEqual opts sc cc spec md v1 v2 = do
  (_, val1) <- resolveSetupValueLLVM opts cc sc spec v1
  (_, val2) <- resolveSetupValueLLVM opts cc sc spec v2
  p         <- liftIO (equalValsPred cc val1 val2)
  addAssume p md

-- | Process an @llvm_postcond@ statement from the postcondition
-- section of the CrucibleSetup block.
executePred ::
  (?w4EvalTactic :: W4EvalTactic) =>
  SharedContext ->
  LLVMCrucibleContext arch ->
  MS.ConditionMetadata ->
  TypedTerm {- ^ the term to assert as a postcondition -} ->
  OverrideMatcher (LLVM arch) md ()
executePred sc cc md tt =
  do p <- instantiateExtResolveSAWPred sc cc (ttTerm tt)
     addAssume p md

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
         sym         = cc^.ccSym
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
    SetupTerm tt             -> SetupTerm     <$> doTerm tt
    SetupStruct p vs         -> SetupStruct p <$> mapM (instantiateSetupValue sc s) vs
    SetupArray () vs         -> SetupArray () <$> mapM (instantiateSetupValue sc s) vs
    SetupElem{}              -> return v
    SetupField{}             -> return v
    SetupCast{}              -> return v
    SetupUnion{}             -> return v
    SetupNull{}              -> return v
    SetupGlobal{}            -> return v
    SetupGlobalInitializer{} -> return v
    SetupMux empty _ _ _     -> absurd empty
    SetupEnum  empty         -> absurd empty
    SetupTuple empty _       -> absurd empty
    SetupSlice empty         -> absurd empty
  where
    doTerm (TypedTerm schema t) = TypedTerm schema <$> scInstantiateExt sc s t

------------------------------------------------------------------------

resolveSetupValueLLVM ::
  (?w4EvalTactic :: W4EvalTactic, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options ->
  LLVMCrucibleContext arch ->
  SharedContext ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  SetupValue (LLVM arch) ->
  OverrideMatcher (LLVM arch) md (Crucible.MemType, LLVMVal)
resolveSetupValueLLVM opts cc sc spec sval =
  do m <- OM (use setupValueSub)
     s <- OM (use termSub)
     mem <- readGlobal (Crucible.llvmMemVar (ccLLVMContext cc))
     let tyenv = MS.csAllocations spec
         nameEnv = MS.csTypeNames spec
     memTy <- exceptToFail $ typeOfSetupValue cc tyenv nameEnv sval
     sval' <- liftIO $ instantiateSetupValue sc s sval
     lval  <- liftIO $ resolveSetupVal cc mem m tyenv nameEnv sval' `X.catch` handleException opts
     return (memTy, lval)

resolveSetupValue ::
  (?w4EvalTactic :: W4EvalTactic, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options ->
  LLVMCrucibleContext arch ->
  SharedContext ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  Crucible.TypeRepr tp ->
  SetupValue (LLVM arch) ->
  OverrideMatcher (LLVM arch) md (Crucible.MemType, Crucible.RegValue Sym tp)
resolveSetupValue opts cc sc spec tp sval =
  do (memTy, lval) <- resolveSetupValueLLVM opts cc sc spec sval
     sym <- Ov.getSymInterface
     val <- liftIO $ Crucible.unpackMemValue sym tp lval
     return (memTy, val)

-- | Like 'resolveSetupValueLLVM', but specifically geared towards the needs
-- of fields within bitfields. See the Haddocks for 'resolveSetupValBitfield'
-- for the salient details.
resolveSetupValueBitfieldLLVM ::
  (?w4EvalTactic :: W4EvalTactic, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options ->
  LLVMCrucibleContext arch ->
  SharedContext ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  SetupValue (LLVM arch) ->
  String ->
  OverrideMatcher (LLVM arch) md (BitfieldIndex, LLVMVal)
resolveSetupValueBitfieldLLVM opts cc sc spec sval fieldName =
  do m <- OM (use setupValueSub)
     s <- OM (use termSub)
     mem <- readGlobal (Crucible.llvmMemVar (ccLLVMContext cc))
     let tyenv = MS.csAllocations spec
         nameEnv = MS.csTypeNames spec
     sval' <- liftIO $ instantiateSetupValue sc s sval
     liftIO $ resolveSetupValBitfield cc mem m tyenv nameEnv sval' fieldName `X.catch` handleException opts

-- | Like 'resolveSetupValue', but specifically geared towards the needs
-- of fields within bitfields. Note that the LHS value must be a pointer, so
-- there is no need to pass a 'Crucible.TypeRepr' here. Moreover, the second
-- return value is always specialized to 'LLVMPtr'. See also the Haddocks for
-- 'resolveSetupValueBitfieldLLVM' for other differences.
resolveSetupValueBitfield ::
  (?w4EvalTactic :: W4EvalTactic, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options ->
  LLVMCrucibleContext arch ->
  SharedContext ->
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  SetupValue (LLVM arch) ->
  String ->
  OverrideMatcher (LLVM arch) md (BitfieldIndex, LLVMPtr (Crucible.ArchWidth arch))
resolveSetupValueBitfield opts cc sc spec sval fieldName =
  do (bfIndex, lval) <- resolveSetupValueBitfieldLLVM opts cc sc spec sval fieldName
     sym <- Ov.getSymInterface
     val <- liftIO $ Crucible.unpackMemValue sym Crucible.PtrRepr lval
     pure (bfIndex, val)

enableSMTArrayMemoryModel :: W4.ConfigOption W4.BaseBoolType
enableSMTArrayMemoryModel = (W4.configOption W4.knownRepr "smt-array-memory-model")
