{- |
Module      : SAWScript.Crucible.Common
Description : Crucible-related material that is not specific to a given language
License     : BSD3
Maintainer  : langston
Stability   : provisional
-}

{-# LANGUAGE RankNTypes #-}

module SAWScript.Crucible.Common
  ( ppAbortedResult
  , Sym
  , LabeledPred
  , LabeledPred'
  , labelWithSimError
  ) where

import           Control.Lens
import           Lang.Crucible.Simulator.ExecutionTree (AbortedResult(..), GlobalPair)
import           Lang.Crucible.Simulator.CallFrame (SimFrame)
import qualified Lang.Crucible.Simulator.SimError as Crucible
import           Lang.Crucible.Backend (AbortExecReason(..), ppAbortExecReason)
import           Lang.Crucible.Backend.SAWCore (SAWCoreBackend)
import qualified Data.Parameterized.Nonce as Nonce
import qualified What4.Solver.Yices as Yices
import qualified What4.Expr as W4
import qualified What4.Interface as W4 (Pred)
import qualified What4.ProgramLoc as W4
import qualified What4.LabeledPred as W4

import qualified Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>), (<>))

type LabeledPred sym = W4.LabeledPred (W4.Pred sym) Crucible.SimError
type LabeledPred' sym = W4.LabeledPred (W4.Pred sym) PP.Doc

-- | Convert a predicate with a 'PP.Doc' label to one with a 'Crucible.SimError'
labelWithSimError ::
  W4.ProgramLoc ->
  (PP.Doc -> String) ->
  LabeledPred' Sym ->
  LabeledPred Sym
labelWithSimError loc conv lp =
  lp & W4.labeledPredMsg
     %~ (Crucible.SimError loc . Crucible.AssertFailureSimError . conv)

-- | The symbolic backend we use for SAW verification
type Sym = SAWCoreBackend Nonce.GlobalNonceGenerator (Yices.Connection Nonce.GlobalNonceGenerator) (W4.Flags W4.FloatReal)

ppAbortedResult :: (forall l args. GlobalPair Sym (SimFrame Sym ext l args) -> PP.Doc)
                -> AbortedResult Sym ext
                -> PP.Doc
ppAbortedResult _ (AbortedExec InfeasibleBranch _) =
  PP.text "Infeasible branch"
ppAbortedResult ppGP (AbortedExec abt gp) = do
  ppAbortExecReason abt PP.<$$> ppGP gp
ppAbortedResult ppGP (AbortedBranch loc _predicate trueBranch falseBranch) =
  PP.vcat
    [ PP.text "Both branches aborted after a symbolic branch."
    , PP.text "Location of control-flow branching:"
    , PP.indent 2 (PP.text (show (W4.plSourceLoc loc)))
    , PP.text "Message from the true branch:"
    , PP.indent 2 (ppAbortedResult ppGP trueBranch)
    , PP.text "Message from the false branch:"
    , PP.indent 2 (ppAbortedResult ppGP falseBranch)
    ]
ppAbortedResult _ (AbortedExit ec) =
  PP.text "Branch exited:" PP.<+> PP.text (show ec)
