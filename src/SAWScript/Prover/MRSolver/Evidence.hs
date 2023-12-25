{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : SAWScript.Prover.MRSolver.Evidence
Copyright   : Galois, Inc. 2023
License     : BSD3
Maintainer  : westbrook@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

This module defines multiple outward facing components of MRSolver, most
notably the 'MREvidence' type which provides evidence for the truth of a
refinement proposition proved by MRSolver, and used in @Proof.hs@. This module
also defines the 'MREnv' type, the global MRSolver state.

Note: In order to avoid circular dependencies, the 'FunAssump' type and its
dependents in this file ('Refnset' and 'MREvidence') are given a type
parameter @t@ which in practice always be 'TheoremNonce' from @Value.hs@.
The reason we cannot just import @Value.hs@ here directly is because the
'Refnset' type is used in @Value.hs@ - specifically, in the 'VRefnset'
constructor of the 'Value' datatype.
-}

module SAWScript.Prover.MRSolver.Evidence where

import Data.Foldable (foldMap')

import Data.Map (Map)
import qualified Data.Map as Map

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap

import Data.Set (Set)
import qualified Data.Set as Set

import Verifier.SAW.Term.Functor
import Verifier.SAW.Term.Pretty
import Verifier.SAW.Recognizer
import Verifier.SAW.Cryptol.Monadify
import SAWScript.Prover.SolverStats

import SAWScript.Prover.MRSolver.Term


----------------------------------------------------------------------
-- * Function Refinement Assumptions
----------------------------------------------------------------------

-- | A representation of a refinement proof goal, i.e., a term of the form:
-- > (a1:A1) -> ... -> (an:An) -> refinesS ev rtp1 rtp2 t1 t2
data RefinesS = RefinesS {
  -- | The context of the refinement, i.e. @[(a1,A1), ..., (an,An)]@
  -- from the term above
  refnCtx :: [(LocalName, Term)],
  -- | The event type of the refinement, i.e. @ev@ above
  refnEv :: Term,
  -- | The LHS return type of the refinement, i.e. @rtp1@ above
  refnRType1 :: Term,
  -- | The RHS return type of the refinement, i.e. @rtp2@ above
  refnRType2 :: Term,
  -- | The LHS term of the refinement, i.e. @t1@ above
  refnLHS :: Term,
  -- | The RHS term of the refinement, i.e. @t2@ above
  refnRHS :: Term
}

-- | Recognizes a term of the form:
-- @(a1:A1) -> ... -> (an:An) -> refinesS ev1 ev2 stack1 stack2 rtp1 rtp2 t1 t2@
-- and returns:
-- @RefinesS [(a1,A1), ..., (an,An)] ev1 ev2 stack1 stack2 rtp1 rtp2 t1 t2@
asRefinesS :: Recognizer Term RefinesS
asRefinesS (asPiList -> (args, asApplyAll ->
                         (asGlobalDef -> Just "SpecM.refinesS",
                          [ev, rtp1, rtp2,
                           asApplyAll -> (asGlobalDef -> Just "SpecM.eqRR", _),
                           t1, t2]))) =
  Just $ RefinesS args ev rtp1 rtp2 t1 t2
asRefinesS (asPiList -> (_, asApplyAll -> (asGlobalDef -> Just "SpecM.refinesS", _))) =
  error "FIXME: MRSolver does not yet accept refinesS goals with non-trivial return relation"
asRefinesS _ = Nothing

-- | The right-hand-side of a 'FunAssump': either a 'FunName' and arguments, if
-- it is an opaque 'FunAsump', or a 'NormComp', if it is a rewrite 'FunAssump'
data FunAssumpRHS = OpaqueFunAssump FunName [Term]
                  | RewriteFunAssump Term

-- | An assumption that a named function refines some specification. This has
-- the form
--
-- > forall x1, ..., xn. F e1 ... ek |= m
--
-- for some universal context @x1:T1, .., xn:Tn@, some list of argument
-- expressions @ei@ over the universal @xj@ variables, and some right-hand side
-- computation expression @m@.
data FunAssump t = FunAssump {
  -- | The uvars that were in scope when this assumption was created
  fassumpCtx :: MRVarCtx,
  -- | The function on the left-hand-side
  fassumpFun :: FunName,
  -- | The argument expressions @e1, ..., en@ over the 'fassumpCtx' uvars
  fassumpArgs :: [Term],
  -- | The right-hand side upper bound @m@ over the 'fassumpCtx' uvars
  fassumpRHS :: FunAssumpRHS,
  -- | An optional annotation, which in the case of SAWScript, is always a
  -- 'TheoremNonce' indicating from which 'Theorem' this assumption comes
  fassumpAnnotation :: Maybe t
}

-- | Recognizes a term of the form:
-- @(a1:A1) -> ... -> (an:An) -> refinesS ev rtp rtp eqRR (f b1 ... bm) t2@,
-- and returns: @FunAssump f [a1,...,an] [b1,...,bm] rhs ann@,
-- where @ann@ is the given argument and @rhs@ is either
-- @OpaqueFunAssump g [c1,...,cl]@ if @t2@ is @g c1 ... cl@,
-- or @RewriteFunAssump t2@ otherwise
asFunAssump :: Maybe t -> Recognizer Term (FunAssump t)
asFunAssump ann (asRefinesS -> Just (RefinesS args
                                     (asGlobalDef -> Just "SpecM.VoidEv")
                                     _ _ (asApplyAll -> (asGlobalFunName -> Just f1, args1))
                                     t2@(asApplyAll -> (asGlobalFunName -> mb_f2, args2)))) =
  let rhs = maybe (RewriteFunAssump t2) (\f2 -> OpaqueFunAssump f2 args2) mb_f2
   in Just $ FunAssump { fassumpCtx = mrVarCtxFromOuterToInner args,
                         fassumpFun = f1, fassumpArgs = args1,
                         fassumpRHS = rhs,
                         fassumpAnnotation = ann }
asFunAssump _ _ = Nothing


----------------------------------------------------------------------
-- * Refinement Sets
----------------------------------------------------------------------

-- | A set of refinements whose left-hand-sides are function applications,
-- represented as 'FunAssump's. Internally, a map from the 'VarIndex'es of the
-- LHS functions to 'FunAssump's describing the complete refinement.
type Refnset t = HashMap VarIndex (Map [TermProj] (FunAssump t))

-- | The 'Refnset' with no refinements
emptyRefnset :: Refnset t
emptyRefnset = HashMap.empty

-- | Given a 'FunName' and a 'Refnset', return the 'FunAssump' which has
-- the given 'FunName' as its LHS function, if possible
lookupFunAssump :: FunName -> Refnset t -> Maybe (FunAssump t)
lookupFunAssump (GlobalName (GlobalDef _ ix _ _ _) projs) refSet =
    HashMap.lookup ix refSet >>= Map.lookup projs
lookupFunAssump _ _ = Nothing

-- | Add a 'FunAssump' to a 'Refnset'
addFunAssump :: FunAssump t -> Refnset t -> Refnset t
addFunAssump fa@(fassumpFun -> GlobalName (GlobalDef _ ix _ _ _) projs) =
    HashMap.insertWith (\_ -> Map.insert projs fa) ix
                       (Map.singleton projs fa)
addFunAssump _ = error "Cannot insert a non-global name into a Refnset"

-- | Return the list of 'FunAssump's in a given 'Refnset'
listFunAssumps :: Refnset t -> [FunAssump t]
listFunAssumps = concatMap Map.elems . HashMap.elems


----------------------------------------------------------------------
-- * Mr Solver Environments
----------------------------------------------------------------------

-- | A global MR Solver environment
data MREnv = MREnv {
  -- | The debug level, which controls debug printing
  mreDebugLevel :: Int,
  -- | The options for pretty-printing to be used by MRSolver in error messages
  -- and debug printing
  mrePPOpts :: PPOpts
}

-- | The empty 'MREnv'
emptyMREnv :: MREnv
emptyMREnv = MREnv { mreDebugLevel = 0, mrePPOpts = defaultPPOpts }

-- | Set the debug level of a Mr Solver environment
mrEnvSetDebugLevel :: Int -> MREnv -> MREnv
mrEnvSetDebugLevel dlvl env = env { mreDebugLevel = dlvl }


----------------------------------------------------------------------
-- * Mr Solver Evidence
----------------------------------------------------------------------

-- | An entry in 'MREvidence' indicating a usage of an SMT solver or a
-- 'FunAssump'
data MREvidenceEntry t = MREUsedSolver !SolverStats !Term
                       | MREUsedFunAssump !t

-- | Records evidence for the truth of a refinement proposition proved by
-- MRSolver. Currently, this is just a list of 'MREvidenceEntry's indicating
-- each instance where MRSolver needed to use an SMT solver or a 'FunAssump'.
-- FIXME: Have this data type actually provide evidence! i.e. have it keep
-- track of each refinement theorem used by MRSolver along the way.
type MREvidence t = [MREvidenceEntry t]

-- | Verify that the given evidence in fact supports the given refinement
-- proposition. Returns the identifiers of all the theorems depended on while
-- checking evidence.
-- FIXME: Actually take in a refinement to check against!
checkMREvidence :: Ord t => MREvidence t -> IO (Set t, SolverStats)
checkMREvidence = return . foldMap' checkEntry
  where checkEntry (MREUsedSolver stats _) = (mempty, stats)
        checkEntry (MREUsedFunAssump t) = (Set.singleton t, mempty)
