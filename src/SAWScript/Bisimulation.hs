{- |
Module      : SAWScript.Bisimulation
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
* A relation @rel : (lhsState, output) -> (rhsState, output) -> Bit@
* A term @lhs : (lhsState, input) -> (lhsState, output)@
* A term @rhs : (rhsState, input) -> (rhsState, output)@
and considers @lhs@ and @rhs@ bisimilar when:
  forall s1 s2 in out1 out2.
    rel (s1, out1) (s2, out2) -> rel (lhs (s1, in)) (rhs (s2, in))

One natural question is why the relation has the type
@(lhsState, output) -> (rhsState, output) -> Bit@ instead of something simpler
like @lhsState -> rhsState -> Bit@. We require the user to specify when outputs
satisfy the relation because it is not always the case that circuit outputs
agree exactly after each simulation step. Specifically, one circuit may complete
some calculation in @N@ steps and another in @M@ steps where @N != M@. In this
case, the user may not want to check the circuit outputs for equality until the
greater of @N@ and @M@ steps have passed. The simpler relation type would not
enable specification of this property.

The main downside of this approach is that the resulting forall in the formula
sent to the SMT solver quantifies over the initial output of the circuits prior
to simulating a step. This can be confusing when reading the SAW source code,
and could be resolved by requiring the user to provide two different relations
(one over states, and one over states and outputs), but this puts more burden on
the end user who would have to write two relations rather than just one. As
such, we've chosen the approach that's easier on the end user, rather than the
one that's easier on the SAW implementer.
-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module SAWScript.Bisimulation
  ( proveBisimulation )
  where

import Control.Monad (unless)

import qualified Cryptol.TypeCheck.Type as C
import qualified Cryptol.Utils.PP as C

import SAWScript.Builtins (provePrim)
import SAWScript.Crucible.Common.MethodSpec (ppTypedTermType)
import SAWScript.Proof
import SAWScript.Value

import qualified Verifier.SAW.Cryptol as C
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedTerm

-- | Use bisimulation to prove that two terms simulate each other.
--
-- Given the following:
-- * A relation @rel : (lhsState, output) -> (rhsState, output) -> Bit@
-- * A term @lhs : (lhsState, input) -> (lhsState, output)@
-- * A term @rhs : (rhsState, input) -> (rhsState, output)@
-- the prover considers @lhs@ and @rhs@ bisimilar when:
--   forall s1 s2 in out1 out2.
--     rel (s1, out1) (s2, out2) -> rel (lhs (s1, in)) (rhs (s2, in))
proveBisimulation ::
  ProofScript () ->
  -- ^ Proof script to use over generated bisimulation term
  TypedTerm ->
  -- ^ Relation over states and outputs for terms to prove bisimilar. Must have
  -- type @(lhsState, output) -> (rhsState, output) -> Bit@.
  TypedTerm ->
  -- ^ LHS of bisimulation. Must have type
  -- @(lhsState, input) -> (lhsState, output)@
  TypedTerm ->
  -- ^ RHS of bisimulation. Must have type
  -- @(rhsState, input) -> (rhsState, output)@
  TopLevel ProofResult
proveBisimulation script relation lhs rhs = do
  sc <- getSharedContext

  -- Typechecking
  (lhsStateType, rhsStateType, outputType) <- typecheckRelation
  lhsInputType <- typecheckSide lhs lhsStateType outputType
  rhsInputType <- typecheckSide rhs rhsStateType outputType
  unless (lhsInputType == rhsInputType) $
    fail $ unlines [ "Error: Mismatched input types in bisimulation terms."
                   , "  LHS input type: " ++ C.pretty lhsInputType
                   , "  RHS input type: " ++ C.pretty rhsInputType ]

  -- Outer function inputs. See comments to the right of each line to see how
  -- they line up with the @forall@ in the haddocs for this function.
  input <- io $ scLocalVar sc 0           -- in
  lhsState <- io $ scLocalVar sc 1        -- s1
  rhsState <- io $ scLocalVar sc 2        -- s2
  initLhsOutput <- io $ scLocalVar sc 3   -- out1
  initRhsOutput <- io $ scLocalVar sc 4   -- out2

  -- LHS/RHS inputs
  lhsTuple <- io $ scTuple sc [lhsState, input]  -- (s1, in)
  rhsTuple <- io $ scTuple sc [rhsState, input]  -- (s2, in)

  -- LHS/RHS outputs
  lhsOutput <- io $ scApply sc (ttTerm lhs) lhsTuple  -- lhs (s1, in)
  rhsOutput <- io $ scApply sc (ttTerm rhs) rhsTuple  -- rhs (s2, in)

  -- Initial relation inputs
  initRelArg1 <- io $ scTuple sc [lhsState, initLhsOutput]  -- (s1, out1)
  initRelArg2 <- io $ scTuple sc [rhsState, initRhsOutput]  -- (s2, out2)

  -- Initial relation result
  -- rel (s1, out1) (s2, out2)
  initRelation <- scRelation sc initRelArg1 initRelArg2

  -- Relation over outputs
  -- rel (lhs (s1, in)) (rhs (s2, in))
  relationRes <- scRelation sc lhsOutput rhsOutput

  -- initRelation implies relationRes
  -- rel (s1, out1) (s2, out2) -> rel (lhs (s1, in)) (rhs (s2, in))
  implication <- io $ scImplies sc initRelation relationRes

  -- Function to prove
  -- forall s1 s2 in out1 out2.
  --   rel (s1, out1) (s2, out2) -> rel (lhs (s1, in)) (rhs (s2, in))
  args <- io $ mapM
    (\(name, t) -> (name,) <$> C.importType sc C.emptyEnv t)
    [ ("initRhsOutput", outputType)
    , ("initLhsOutput", outputType)
    , ("rhsState", rhsStateType)
    , ("lhsState", lhsStateType)
    , ("input", lhsInputType) ]
  theorem <- io $ scLambdaList sc args implication

  io (mkTypedTerm sc theorem) >>= provePrim script

  where
    -- Typecheck relation. The expected type for a relation is:
    -- @(lhsStateType, outputType) -> (rhsStateType, outputType) -> Bit@
    --
    -- If the relation typechecks, 'typecheckRelation' evaluates to a tuple of:
    -- @(lhsStateType, rhsStateType, outputType)@
    -- Otherwise, this invokes 'fail' with a description of the specific
    -- typechecking error.
    typecheckRelation :: TopLevel (C.Type, C.Type, C.Type)
    typecheckRelation =
      case ttType relation of
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
        _ -> fail $ "Error: Unexpected relation type: "
                 ++ show (ppTypedTermType (ttType relation))

    -- Typecheck bisimulation term. The expected type for a bisimulation term
    -- is:
    -- @(stateType, inputType) -> (stateType, outputType)@
    --
    -- If the term typechecks, this function returns @inputType@.  Otherwise,
    -- this funciton invokes 'fail' with a description of the specific
    -- typechecking error.
    typecheckSide :: TypedTerm -> C.Type -> C.Type -> TopLevel C.Type
    typecheckSide side stateType outputType =
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
            , "  Expected: " ++ C.pretty outputType
            , "  Actual: " ++ C.pretty o ]

          return i
        _ ->
          let stStr = C.pretty stateType in
          fail $ unlines
          [ "Error: Unexpected bisimulation term type."
          , "  Expected: (" ++ stStr ++ ", inputType) -> (" ++ stStr ++ ", outputType)"
          , "  Actual: " ++ show (ppTypedTermType (ttType side)) ]

    -- Generate 'Term' for application of a relation
    scRelation :: SharedContext -> Term -> Term -> TopLevel Term
    scRelation sc relLhs relRhs = io $
      scApplyAll sc (ttTerm relation) [relLhs, relRhs]
