{- |
Module      : SAWCentral.Bisimulation
Description : Implementations of SAW-Script bisimulation prover
License     : BSD3
Maintainer  : bboston7
Stability   : experimental

This module provides tools to prove bisimilarity of two circuits, or of a
circuit and a specification. At the moment, it does this through the single
'proveBisimulation' function, but we will expand this module with additional
functionality in the future.

At its core, we want to prove that two circuits executing in lockstep satisfy
some relation over the state of each circuit and their outputs. To achieve this,
the 'proveBisimulation' command takes:
* A list of already proved bisimulation theorems
* A state relation @srel : lhsState -> rhsState -> Bit@
* An output relation @orel : (lhsState, output) -> (rhsState, output) -> Bit@
* A term @lhs : (lhsState, input) -> (lhsState, output)@
* A term @rhs : (rhsState, input) -> (rhsState, output)@
and considers @lhs@ and @rhs@ bisimilar when the following two theorems hold:
* OUTPUT RELATION THEOREM:
    forall s1 s2 in.
      srel s1 s2 -> orel (lhs (s1, in)) (rhs (s2, in))
* STATE RELATION THEOREM:
    forall s1 s2 out1 out2.
      orel (s1, out1) (s2, out2) -> srel s1 s2

The OUTPUT RELATION THEOREM ensures that if the state relation holds prior to
executing @lhs@ and @rhs@, then the output relation holds after executing @lhs@
and @rhs@.  That is, the two terms step together.

The STATE RELATION THEOREM ensures that if the output relation holds over some
state and output value, then the state relation also holds over that same state.
This ensures that the output relation captures the state relation.

To enable compositionality, 'proveBisimulation' takes a list of proven
bisimulation theorems as 'BisimTheorem's.  For each 'BisimTheorem', this
implementation searches for invocations of the functions in the 'BisimTheorem'
and replaces them with uninterpreted values that satisfy the 'BisimTheorem''s
output relation.  Put another way, if @g_lhs@ contains some function @f_lhs@ and
@g_rhs@ contains some function @f_rhs@ where @f_lhs@ and @f_rhs@ satisfy some
output relation @f_orel@, then in the proof of some OUTPUT RELATION THEOREM for
@g_lhs@ and @g_rhs@, the prover can replace @f_lhs@ with an uninterpreted value
@v_lhs@ and @f_rhs@ with an uninterpreted value @v_rhs@.  Lastly, the prover
assumes @v_lhs@ and @v_rhs@ satisfy @f_orel@.

In order to make this assumption about @v_lhs@ and @v_rhs@, the state relation
of the outer terms must ensure that the inner terms' state relation holds.  As
such, the prover generates and proves a side condition for each applied
'BisimTheorem'.  Let @g_lhs_s@ and @g_rhs_s@ be the states for @g_lhs@ and
@g_rhs@ respectively.  Additionally, let there be a function
@extract_inner_state x x_s y@ that takes an outer term @x@, an outer state
@x_s@, and an inner term @y@, and returns the inner state of @x_s@ that @x@
passes to @y@.  Lastly, let @g_srel@ be the state relation for the @g@ terms,
and @f_srel@ be the state relation for the @f@ terms.  The prover then checks:
  COMPOSITION SIDE CONDITION:
    forall g_lhs_s g_rhs_s.
      g_srel g_lhs_s g_rhs_s -> f_srel f_lhs_s f_rhs_s
      where
        f_lhs_s = extract_inner_state g_lhs g_lhs_s f_lhs
        f_rhs_s = extract_inner_state g_rhs g_rhs_s f_rhs

The reason for all of this complexity around composition is ultimately to reduce
the burden on the SMT solver by uninterpreting functions so that the SMT solver
may handle more complex proofs.
-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module SAWCentral.Bisimulation
  ( BisimTheorem, proveBisimulation )
  where

import Control.Monad (foldM, forM_, unless)
import Control.Monad.IO.Class (MonadIO(..))
import qualified Control.Monad.State.Strict as State
import Control.Monad.Trans.Class (MonadTrans(..))
import Data.Foldable (foldl')
import qualified Data.IntSet as IntSet
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import qualified Data.Text as Text

import qualified Cryptol.TypeCheck.Type as C
import qualified Cryptol.Utils.PP as C

import SAWCentral.BisimulationTheorem
import SAWCentral.Builtins (unfold_term)
import SAWCentral.Options (Verbosity(..))
import SAWCentral.Panic (panic)
import SAWCentral.Proof
import SAWCentral.Prover.Util (checkBooleanSchema)
import SAWCentral.Value

import qualified CryptolSAWCore.Cryptol as C
import SAWCore.SharedTerm
import SAWCore.Term.Functor
import SAWCore.Term.Pretty (showTerm)
import CryptolSAWCore.TypedTerm
import SAWCore.Recognizer

-- State used to facilitate the replacement of a 'Constant' application in a
-- 'Term' with an 'ExtCns'.  Used in 'replaceConstantTerm' and
-- 'replaceConstantTermF'
data ReplaceState = ReplaceState {
    rsMemo :: Map.Map TermIndex Term
 -- ^ Memoization table to avoid re-visiting the same shared term
  , rsExtCns :: Maybe Term
 -- ^ ExtCns that replaces the 'Constant' application, if the constant could be
 -- located.
  , rsApp :: Maybe (TermF Term)
 -- ^ Application that was replaced, if it could be located.
  }

-- Components needed for a bisimulation proof.
data BisimComponents = BisimComponents {
    bcTheorem :: BisimTheorem
 -- ^ Bisimulation theorem capturing relations and outputs
  , bcInputType :: C.Type
 -- ^ Input type of the bisimilar functions
  }

-- An initial 'ReplaceState'
emptyReplaceState :: ReplaceState
emptyReplaceState = ReplaceState Map.empty Nothing Nothing

-- | Translate a list of 'TypedTerm' representing theorems for input to the
-- given validity-checking script and attempt to prove them.
proveAll :: ProofScript () -> [TypedTerm] -> TopLevel ()
proveAll script ts = do
  sc <- getSharedContext
  pos <- getPosition
  forM_ (zip [0..] ts) $ \(n, t) -> do
    io $ checkBooleanSchema (ttType t)
    prop <- io $ predicateToProp sc Universal (ttTerm t)
    let goal = ProofGoal
              { goalNum  = n
              , goalType = "prove"
              , goalName = "prove_bisim"
              , goalLoc  = show pos
              , goalDesc = ""
              , goalSequent = propToSequent prop
              , goalTags = mempty
              }
    res <- runProofScript script prop goal Nothing "prove_bisim" True False
    case res of
      UnfinishedProof {} -> failProof res
      ValidProof _ thm -> recordProof thm
      InvalidProof {} ->  failProof res
  where
    failProof :: ProofResult -> TopLevel ()
    failProof res = do
      opts <- rwPPOpts <$> getTopLevelRW
      fail $ "prove_bisim failed.\n" ++ showsProofResult opts res ""

-- | Generate 'Term' for application of a relation
scRelation :: TypedTerm -> Term -> Term -> TopLevel Term
scRelation rel relLhs relRhs = do
  sc <- getSharedContext
  io $ scApplyAll sc (ttTerm rel) [relLhs, relRhs]

-- | Build the COMPOSITION SIDE CONDITION for 'bc' and 'bt'.  See the
-- documentation at the top of this file for information on the COMPOSITION SIDE
-- CONDITION.
--
-- This function works by examining the specific calls to @f_lhs@ in @g_lhs@ and
-- @f_rhs@ in @g_rhs@ to deduce how these subfunctions access state in their
-- respective super functions.  It then extracts these accessors and
-- instantiates them with the specific @g_lhs_s@ and @g_rhs_s@ values passed
-- into @g_lhs@ and @g_rhs@ respectively.
buildCompositionSideCondition
  :: BisimComponents
  -- ^ Components of the outer bisimulation under verification
  -> BisimTheorem
  -- ^ Bisimulation theorem concerning inner function
  -> TopLevel TypedTerm
buildCompositionSideCondition bc innerBt = do
  sc <- getSharedContext
  let outerBt = bcTheorem bc

  lhsOuterState <- io $ scLocalVar sc 0        -- g_lhs_s
  rhsOuterState <- io $ scLocalVar sc 1        -- g_rhs_s

  -- NOTE: Although not used in the final formula, we need to capture the input
  -- to the outer functions because the extracted inner function applications
  -- depend on it.  Therefore, it is necessary to match the expected form of the
  -- inner ExtCns that this function instantiates.
  input    <- io $ scLocalVar sc 2        -- in

  -- Locate inner function calls on each side and replace their arguments with
  -- 'ExtCns's
  (lhsInnerEc, lhsInnerApp) <-
    openConstantApp (bisimTheoremLhs innerBt) (bisimTheoremLhs outerBt)
  (rhsInnerEc, rhsInnerApp) <-
    openConstantApp (bisimTheoremRhs innerBt) (bisimTheoremRhs outerBt)

  -- Extract state accessors from each inner function
  lhsInnerState <- stateFromApp lhsInnerApp  -- f_lhs_s
  rhsInnerState <- stateFromApp rhsInnerApp  -- f_rhs_s

  -- Outer state relation
  -- g_srel g_lhs_s g_rhs_s
  outerRel <-
    scRelation (bisimTheoremStateRelation outerBt) lhsOuterState rhsOuterState

  -- Inner state relation
  -- f_srel f_lhs_s f_rhs_s
  innerRel <-
    scRelation (bisimTheoremStateRelation innerBt) lhsInnerState rhsInnerState

  -- Replace extcns in inner relation with outer inputs
  lhsTuple <- io $ scTuple sc [lhsOuterState, input]  -- (f_lhs_s, in)
  rhsTuple <- io $ scTuple sc [rhsOuterState, input]  -- (f_rhs_s, in)
  innerRel' <- io $
    scInstantiateExt sc
                     (Map.fromList [ (ecVarIndex lhsInnerEc, lhsTuple)
                                   , (ecVarIndex rhsInnerEc, rhsTuple)])
                     innerRel

  -- outer state relation implies inner state relation
  -- g_srel g_lhs_s g_rhs_s -> f_srel f_lhs_s f_rhs_s
  implication <- io $ scImplies sc outerRel innerRel'

  -- Theorem to prove. Note that the 'input' is ultimately unused (see NOTE on
  -- 'input' at the top of this function).
  -- forall g_lhs_s g_rhs_s. g_srel g_lhs_s g_rhs_s -> f_srel f_lhs_s f_rhs_s
  args <- io $ mapM
    (\(name, t) -> (name,) <$> C.importType sc C.emptyEnv t)
    [ ("input", bcInputType bc)
    , ("rhsState", bisimTheoremRhsStateType outerBt)
    , ("lhsState", bisimTheoremLhsStateType outerBt) ]
  theorem <- io $ scLambdaList sc args implication
  io $ mkTypedTerm sc theorem

-- | Extract the state from the 'App' within a bisimulation side. Fails if 'app'
-- is not an 'App'.
stateFromApp :: TermF Term -> TopLevel Term
stateFromApp app = do
  sc <- getSharedContext
  case app of
    App _ arg -> io $ scFlatTermF sc $ PairLeft arg
    _ -> do
      term <- io $ scTermF sc app
      fail $ "Error: " ++ showTerm term ++ " is not an App"

-- | Given a term containing the application of a 'Constant', locate this
-- application and replace its argument with an 'ExtCns'.  Returns the inserted
-- 'ExtCns' and the updated 'App'.  Fails if 'constant' is not a 'Constant'.
openConstantApp :: TypedTerm
                -- ^ 'Constant' to search for.
                -> TypedTerm
                -- ^ 'TypeTerm' to locate 'Constant' in.  Must itself be a
                -- 'Constant' (will be unfolded).
                -> TopLevel (ExtCns Term, TermF Term)
openConstantApp constant t = do
  sc <- getSharedContext
  -- Unfold constant
  name <- Text.unpack <$> constantName (unwrapTermF (ttTerm t))
  tUnfolded <- unfold_term [name] t

  -- Break down lambda into its component parts.
  (nm, tp, body) <- lambdaOrFail tUnfolded

  -- Replace outer function's argument with an 'ExtCns'
  -- NOTE: The bisimulation relation type ensures this is a single argument
  -- lambda, so it's OK to apply scOpenTerm once and not recurse
  (ec, tExtconsified) <- io $ scOpenTerm sc nm tp 0 body
  extractedF <- extractApp constant tExtconsified
  pure (ec, extractedF)

  where
    -- Break down lambda into its component parts.  Fails if 'tt' is not a
    -- lambda.
    lambdaOrFail :: TypedTerm -> TopLevel (LocalName, Term, Term)
    lambdaOrFail tt =
      case asLambda (ttTerm tt) of
        Just lambda -> return lambda
        Nothing ->
          fail $ "Error: Expected a lambda term, got " ++ show (ppTypedTerm tt)

-- Traverses 'term' and extracts the application of 'constant' within it.  Fails
-- if 'constant' cannot be found within 'term'.
extractApp :: TypedTerm
           -- ^ 'Constant' to search for.
           -> Term
           -- ^ 'Term' to search in.
           -> TopLevel (TermF Term)
extractApp constant term =
  case snd $ go (IntSet.empty, Nothing) term of
    Just app -> return app
    Nothing -> fail $ unlines [ "Error: Failed to locate constant in term."
                              , "  Constant: " ++ show (ppTypedTerm constant)
                              , "  Term: " ++ showTerm term ]
  where
    go :: (IntSet.IntSet, Maybe (TermF Term))
       -> Term
       -> (IntSet.IntSet, Maybe (TermF Term))
    go (seen, acc) t =
      case acc of
        Just res -> (seen, Just res)
        Nothing ->
          case t of
            Unshared tf -> termf (seen, acc) tf
            STApp{ stAppIndex = i, stAppTermF = tf } ->
              if IntSet.member i seen
              then (seen, acc)
              else termf (IntSet.insert i seen, acc) tf

    termf :: (IntSet.IntSet, Maybe (TermF Term))
          -> TermF Term
          -> (IntSet.IntSet, Maybe (TermF Term))
    termf (seen, acc) tf =
      case tf of
        App fn _ | unwrapTermF fn == unwrapTermF (ttTerm constant) ->
          (seen, Just tf)
        _ -> foldl' go (seen, acc) tf

-- | Apply a prior proof result to simplify a bisimulation 'Term'.  Returns an
-- updated 'Term', and a potential side condition that must be proven (or
-- 'Nothing' if simplification had no effect).
--
-- This function works by searching for the functions from 'bt' in 'term'.  If
-- it finds them, it replaces the calls in 'term' with 'ExtCns's and adds an
-- assumption that the output relation holds over those 'ExtCns's.  This has the
-- effect of saving the SMT solver from having to reason again about
-- subrelations that have already been proven.  More formally, if @g_1@ and
-- @g_2@ contain subfunctions @f_1@ and @f_2@ that satisfy some output relation
-- @orel@, then this function replaces @f_1@ and @f_2@ with the uninterpreted
-- values @v_1@ and @v_2@ respectively and adds the assumption @orel v_1 v_2@.
--
-- When simplification succeeds, this function also returns the side condition
-- that the outer state relation from @g_1@ and @g_2@ implies that the inner
-- state relation on @f_1@ and @f_2@ holds.  See the documentation on
-- 'buildSuperStateRelation' for more information on the side condition.
applyTheorem :: BisimTheorem
             -- ^ Theorem to apply
             -> BisimComponents
             -- ^ Components of bisimulation under verification
             -> Term
             -- ^ Term to simplify
             -> TopLevel (Term, Maybe TypedTerm)
applyTheorem bt bc term0 = do
  sc <- getSharedContext

  -- Attempt to replace calls in 'term0' to the left side of 'bt' with an
  -- 'ExtCns'.  In other words, replace @f_1@ with @v_1@.
  let tpLhs = C.TCon (C.TC (C.TCTuple 2)) [ bisimTheoremLhsStateType bt
                                          , bisimTheoremOutputType bt ]
  (term1, lhsRs) <-
    State.runStateT (replaceConstantTerm (bisimTheoremLhs bt) tpLhs term0)
                    emptyReplaceState

  -- Attempt to replace calls in 'term1' to the right side of 'bt' with an
  -- 'ExtCns'.  In other words, replace @f_2@ with @v_2@.
  let tpRhs = C.TCon (C.TC (C.TCTuple 2)) [ bisimTheoremRhsStateType bt
                                          , bisimTheoremOutputType bt ]
  (term2, rhsRs) <-
    State.runStateT (replaceConstantTerm (bisimTheoremRhs bt) tpRhs term1)
                    emptyReplaceState

  case (rsExtCns lhsRs, rsExtCns rhsRs) of
    (Just lhsEc, Just rhsEc) -> do
      -- Simplification succeeded! Add assumption and generate side condition

      -- Apply inner output relation to 'ExtCns's
      -- orel v_1 v_2
      app <- io $ scApplyAll sc
                              (ttTerm (bisimTheoremOutputRelation bt))
                              [ lhsEc , rhsEc ]

      -- Use implication to assume relation holds in the main condition
      -- orel v_1 v_2 -> term2
      main <- io $ scImplies sc app term2

      -- Build side condition
      side <- buildCompositionSideCondition bc bt

      pure (main, Just side)
    _ ->
      -- Application failed to match on one or both sides.  Return the Term
      -- unchanged.
      pure (term0, Nothing)

-- | Apply multiple proof results to simplify a bisimulation 'Term'.  Returns an
-- updated 'Term' and a list of side conditions that must be proven.  See the
-- documentation for 'applyTheorem' for more info.
applyAllTheorems :: [BisimTheorem]
                 -- ^ Theorems to apply
                 -> BisimComponents
                 -- ^ Components of bisimulation under verification
                 -> Term
                 -- ^ Term to simplify
                 -> TopLevel (Term, [TypedTerm])
applyAllTheorems bthms bc term = foldM go (term, []) bthms
  where
    go :: (Term, [TypedTerm]) -> BisimTheorem -> TopLevel (Term, [TypedTerm])
    go (curTerm, sides) bt = do
      (nextTerm, mSideCondition) <- applyTheorem bt bc curTerm
      case mSideCondition of
        Nothing ->
          -- Application failed
          pure (nextTerm, sides)
        Just sideCondition -> pure (nextTerm, sideCondition : sides)


-- | Build the OUTPUT RELATION THEOREM for 'bc', as well as COMPOSITION SIDE
-- CONDITION terms for any theorems used in the OUTPUT RELATION THEOREM.
-- Returns a list of TypedTerms that must be proved. See the documentation at
-- the top of this file for information on OUTPUT RELATION THEOREM and
-- COMPOSITION SIDE CONDITION.
buildOutputRelationTheorem :: [BisimTheorem]
                           -- ^ Theorems available to use in proof
                           -> BisimComponents
                           -- ^ Components of bisimulation under verification
                           -> TopLevel [TypedTerm]
buildOutputRelationTheorem bthms bc = do
  sc <- getSharedContext
  let outerBt = bcTheorem bc

  -- Outer function inputs. See comments to the right of each line to see how
  -- they line up with the documentation at the top of this file.
  lhsState <- io $ scLocalVar sc 0        -- s1
  rhsState <- io $ scLocalVar sc 1        -- s2
  input <- io $ scLocalVar sc 2           -- in

  -- LHS/RHS constants
  let lhs = ttTerm (bisimTheoremLhs outerBt)
  let rhs = ttTerm (bisimTheoremRhs outerBt)

  -- LHS/RHS inputs
  lhsTuple <- io $ scTuple sc [lhsState, input]  -- (s1, in)
  rhsTuple <- io $ scTuple sc [rhsState, input]  -- (s2, in)

  -- LHS/RHS outputs
  -- lhs (s1, in)
  lhsOutput <- io $ scApply sc lhs lhsTuple
  -- rhs (s2, in)
  rhsOutput <- io $ scApply sc rhs rhsTuple

  -- Initial relation result
  -- srel s1 s2
  initRelation <-
    scRelation (bisimTheoremStateRelation outerBt) lhsState rhsState

  -- Relation over outputs
  -- orel (lhs (s1, in)) (rhs (s2, in))
  relationRes <-
    scRelation (bisimTheoremOutputRelation outerBt) lhsOutput rhsOutput

  -- initRelation implies relationRes
  -- srel s1 s2 -> orel (lhs (s1, in)) (rhs (s2, in))
  implication <- io $ scImplies sc initRelation relationRes

  -- Unfold LHS/RHS constants to reveal opportunities for simplification
  let vs = map ecVarIndex $ mapMaybe asConstant [lhs, rhs]
  implication_unfolded <-
    io $ scUnfoldConstants sc vs implication >>= betaNormalize sc

  -- Simplify Term with any theorems that apply
  (implication', sideConditions) <- applyAllTheorems bthms bc implication_unfolded

  -- Function to prove
  -- forall s1 s2 in out1 out2.
  --   srel s1 s2 -> orel (lhs (s1, in)) (rhs (s2, in))
  args <- io $ mapM
    (\(name, t) -> (name,) <$> C.importType sc C.emptyEnv t)
    [ ("input", bcInputType bc)
    , ("rhsState", bisimTheoremRhsStateType outerBt)
    , ("lhsState", bisimTheoremLhsStateType outerBt) ]
  theorem <- io $ scLambdaList sc args implication'

  tt <- io $ mkTypedTerm sc theorem

  pure $ tt : sideConditions

-- | Build the STATE RELATION THEOREM for 'bc'. See the documentation at the top
-- of this file for information on the STATE RELATION THEOREM.
buildStateRelationTheorem :: BisimComponents -> TopLevel TypedTerm
buildStateRelationTheorem bc = do
  sc <- getSharedContext
  let outerBt = bcTheorem bc

  -- Outer function inputs. See comments to the right of each line to see how
  -- they line up with the documentation at the top of this file.
  lhsState <- io $ scLocalVar sc 0        -- s1
  rhsState <- io $ scLocalVar sc 1        -- s2
  initLhsOutput <- io $ scLocalVar sc 2   -- out1
  initRhsOutput <- io $ scLocalVar sc 3   -- out2

  -- LHS/RHS initial outputs
  lhsTuple <- io $ scTuple sc [lhsState, initLhsOutput]  -- (s1, out1)
  rhsTuple <- io $ scTuple sc [rhsState, initRhsOutput]  -- (s2, out2)

  -- LHS of implication
  -- orel (s1, out1) (s2, out2)
  lhsRelation <-
    scRelation (bisimTheoremOutputRelation outerBt) lhsTuple rhsTuple

  -- RHS of implication
  -- srel s1 s2
  rhsRelation <-
    scRelation (bisimTheoremStateRelation outerBt) lhsState rhsState

  -- lhsRelation implies rhsRelation
  -- orel (s1, out1) (s2, out2) -> srel s1 s2
  implication <- io $ scImplies sc lhsRelation rhsRelation

  -- Function to prove
  -- forall s1 s2 in out1 out2.
  --   orel (s1, out1) (s2, out2) -> srel s1 s2
  args <- io $ mapM
    (\(name, t) -> (name,) <$> C.importType sc C.emptyEnv t)
    [ ("initRhsOutput", bisimTheoremOutputType outerBt)
    , ("initLhsOutput", bisimTheoremOutputType outerBt)
    , ("rhsState", bisimTheoremRhsStateType outerBt)
    , ("lhsState", bisimTheoremLhsStateType outerBt) ]
  theorem <- io $ scLambdaList sc args implication

  io $ mkTypedTerm sc theorem

-- | Use bisimulation to prove that two terms simulate each other.  Proves the
-- OUTPUT RELATION THEOREM and STATE RELATION THEOREM for the bisimilar terms.
-- Additionally enables compositionality through the 'bthms' parameter.  This
-- function also proves the COMPOSITION SIDE CONDITION for every successfully
-- applied theorem in 'bthms'.  See the documentation at the top of this file
-- for the definitions of bisimulation and these theorems.
proveBisimulation ::
  ProofScript () ->
  -- ^ Proof script to use over generated bisimulation term
  [BisimTheorem] ->
  -- ^ Previously proved theorems that may be applied
  TypedTerm ->
  -- ^ Relation over states for terms to prove bisimilar. Must have type
  -- @lhsState -> rhsState -> Bit@  Also called the "state relation".
  TypedTerm ->
  -- ^ Relation over states and outputs for terms to prove bisimilar. Must have
  -- type @(lhsState, output) -> (rhsState, output) -> Bit@.  Also called the
  -- "output relation".
  TypedTerm ->
  -- ^ LHS of bisimulation. Must have type
  -- @(lhsState, input) -> (lhsState, output)@
  TypedTerm ->
  -- ^ RHS of bisimulation. Must have type
  -- @(rhsState, input) -> (rhsState, output)@
  TopLevel BisimTheorem
proveBisimulation script bthms srel orel lhs rhs = do
  -- Typechecking
  (lhsStateType, rhsStateType, outputType) <- typecheckOutputRelation
  typecheckStateRelation lhsStateType rhsStateType
  (lhsName, lhsInputType) <- typecheckSide lhs lhsStateType outputType
  (rhsName, rhsInputType) <- typecheckSide rhs rhsStateType outputType
  unless (lhsInputType == rhsInputType) $
    fail $ unlines [ "Error: Mismatched input types in bisimulation terms."
                   , "  LHS input type: " ++ C.pretty lhsInputType
                   , "  RHS input type: " ++ C.pretty rhsInputType ]

  let bt = BisimTheorem
           { bisimTheoremStateRelation = srel
           , bisimTheoremOutputRelation = orel
           , bisimTheoremLhs = lhs
           , bisimTheoremRhs = rhs
           , bisimTheoremOutputType = outputType
           , bisimTheoremLhsStateType = lhsStateType
           , bisimTheoremRhsStateType = rhsStateType
           }

  let bc = BisimComponents
           { bcTheorem = bt
           , bcInputType = lhsInputType
           }
  outputTheorems <- buildOutputRelationTheorem bthms bc
  stateTheorem <- buildStateRelationTheorem bc
  proveAll script $ stateTheorem : outputTheorems

  -- Proof succeeded!
  printOutLnTop Info $ concat [ "Successfully proved bisimulation between "
                              , Text.unpack lhsName
                              , " and "
                              , Text.unpack rhsName ]

  return $ BisimTheorem srel orel lhs rhs outputType lhsStateType rhsStateType

  where
    -- Typecheck output relation. The expected type is:
    -- @(lhsStateType, outputType) -> (rhsStateType, outputType) -> Bit@
    --
    -- If the relation typechecks, 'typecheckOutputRelation' evaluates to a
    -- tuple of:
    -- @(lhsStateType, rhsStateType, outputType)@
    -- Otherwise, this invokes 'fail' with a description of the specific
    -- typechecking error.
    typecheckOutputRelation :: TopLevel (C.Type, C.Type, C.Type)
    typecheckOutputRelation =
      case ttType orel of
        TypedTermSchema
          (C.Forall
            []
            []
            (C.TCon
              (C.TC C.TCFun)
              [ C.TCon (C.TC (C.TCTuple 2)) [s1, o1]
              , C.TCon
                (C.TC C.TCFun)
                [ C.TCon (C.TC (C.TCTuple 2)) [s2, o2]
                , C.TCon (C.TC C.TCBit) []]])) -> do
          unless (o1 == o2) $ fail $ unlines
            [ "Error: Mismatched output types in relation."
            , "LHS output type: " ++ C.pretty o1
            , "RHS output type: " ++ C.pretty o2 ]

          return (s1, s2, o1)
        _ -> fail $ "Error: Unexpected output relation type: "
                 ++ show (ppTypedTermType (ttType orel))

    -- Check that 'lhsStateType' and 'rhsStateType' match the extracted types
    -- from 'typecheckOutputRelation'.  Invokes 'fail' if the types do not
    -- match.
    typecheckStateRelation :: C.Type -> C.Type -> TopLevel ()
    typecheckStateRelation lhsStateType rhsStateType =
      case ttType srel of
        TypedTermSchema
          (C.Forall
            []
            []
            (C.TCon
              (C.TC C.TCFun)
              [ s1
              , C.TCon
                (C.TC C.TCFun)
                [ s2, C.TCon (C.TC C.TCBit) []]])) -> do
          unless (s1 == lhsStateType) $ fail $ unlines
            [ "Error: LHS of state relation and output relations have incompatible state types:"
            , "  State relation LHS state type: " ++ C.pretty s1
            , "  Output relation LHS state type: " ++ C.pretty lhsStateType ]

          unless (s2 == rhsStateType) $ fail $ unlines
            [ "Error: RHS of state relation and output relations have incompatible state types:"
            , "  State relation RHS state type: " ++ C.pretty s2
            , "  Output relation RHS state type: " ++ C.pretty rhsStateType ]
        _ -> fail $ "Error: Unexpected state relation type: "
                 ++ show (ppTypedTermType (ttType srel))

    -- Typecheck bisimulation term. The expected type for a bisimulation term
    -- is:
    -- @(stateType, inputType) -> (stateType, outputType)@
    --
    -- If the term typechecks, this function returns a pair containing the name
    -- of the 'Constant' and @inputType@.  Otherwise, this function invokes
    -- 'fail' with a description of the specific typechecking error.
    typecheckSide
      :: TypedTerm -> C.Type -> C.Type -> TopLevel (Text.Text, C.Type)
    typecheckSide side stateType outputType = do
      -- Check that 'side' is a 'Constant' (necessary for composition)
      name <- constantName $ unwrapTermF $ ttTerm side

      -- Check function arguments
      case ttType side of
        TypedTermSchema
          (C.Forall
            []
            []
            (C.TCon
              (C.TC C.TCFun)
              [ C.TCon (C.TC (C.TCTuple 2)) [s, i]
              , C.TCon (C.TC (C.TCTuple 2)) [s', o] ])) -> do
          unless (s == stateType) $ fail $ unlines
            [ "Error: State type in bisimulation term input does not match state type in relation."
            , "  Expected: " ++ C.pretty stateType
            , "  Actual: " ++ C.pretty s]

          unless (s' == stateType) $ fail $ unlines
            [ "Error: State type in bisimulation term output does not match state type in relation."
            , "  Expected: " ++ C.pretty stateType
            , "  Actual: " ++ C.pretty s']

          unless (o == outputType) $ fail $ unlines
            [ "Error: Output type in bisimulation term does not match output type in relation."
            ,"  Expected: " ++ C.pretty outputType
            , "  Actual: " ++ C.pretty o ]

          return (name, i)
        _ ->
          let stStr = C.pretty stateType in
          fail $ unlines
          [ "Error: Unexpected bisimulation term type."
          , "  Expected: (" ++ stStr ++ ", inputType) -> (" ++ stStr ++ ", outputType)"
          , "  Actual: " ++ show (ppTypedTermType (ttType side)) ]

-- | Replace the invocation of a specific 'Constant' with an 'ExtCns'.  The
-- function returns the resulting 'Term' and updates a 'ReplaceState' to hold
-- the generated 'ExtCns' and the specific 'App' that was replaced.
replaceConstantTerm :: TypedTerm
                    -- ^ 'Constant' to replace application of
                    -> C.Type
                    -- ^ 'constant's return type
                    -> Term
                    -- ^ 'Term' to perform replacement in
                    -> State.StateT ReplaceState TopLevel Term
replaceConstantTerm constant constantRetType term = do
  sc <- lift getSharedContext
  case term of
    Unshared termF -> do
      termF' <- replaceConstantTermF termF
      liftIO $ scTermF sc termF'
    STApp{ stAppIndex = i, stAppTermF = termF } -> do
      table <- State.gets rsMemo
      case Map.lookup i table of
        Just x -> return x
        Nothing -> do
          termF' <- replaceConstantTermF termF
          term' <- liftIO $ scTermF sc termF'
          let table' = Map.insert i term' table
          State.modify$ \st -> st { rsMemo = table' }
          return term'
  where
    -- | Partner function to 'replaceConstantTerm' that operates over 'TermF's.
    replaceConstantTermF
      :: TermF Term -> State.StateT ReplaceState TopLevel (TermF Term)
    replaceConstantTermF termF = do
      case termF of
        App x _ | unwrapTermF x == unwrapTermF (ttTerm constant) ->
          State.gets rsExtCns >>= \case
            Just v ->
              State.gets rsApp >>= \case
                Just a | a == termF ->
                  -- Encountered another call to the function under replacement
                  -- that matches the replaced function.  This can happen even
                  -- when the underlying Cryptol does not explicitly make
                  -- multiple calls because translation to SAWCore can insert
                  -- additional function calls with the same arguments.  In this
                  -- case, simply return the same 'ExtCns' already generated.
                  return $ unwrapTermF v
                Just _ -> do
                  -- Encountered a call to the function under replacement with
                  -- different arguments.  This isn't yet supported.
                  name <- Text.unpack <$> lift (constantName (unwrapTermF x))
                  fail $ concat ["Error: Encountered multiple calls to "
                                , name
                                , ". Use of composition with multiple "
                                , "subfunction calls is not yet supported."
                                ]
                _ -> panic "replaceConstantTermF"
                           ["rsApp should always exist when rsExtCns exists"]
            Nothing -> do
              sc <- lift getSharedContext

              -- Generate an 'ExtCns' and return it, thereby replacing 'termF'
              -- with it.
              tp <- liftIO $ C.importType sc C.emptyEnv constantRetType
              name <- lift $ constantName $ unwrapTermF x
              v <- liftIO $ scFreshGlobal sc name tp
              State.modify $ \st -> st { rsExtCns = Just v, rsApp = Just termF }
              return $ unwrapTermF v
        _ ->
          -- Recurse
          mapM (replaceConstantTerm constant constantRetType) termF

-- Extract the name from a 'Constant'. Fails if provided another kind of 'TermF'
constantName :: TermF Term -> TopLevel Text.Text
constantName (Constant e) = return $ toShortName $ ecName e
constantName tf = do
  sc <- getSharedContext
  term <- io $ scTermF sc tf
  fail $ "Error: Expected a constant, but got: " ++ showTerm term
