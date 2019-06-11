{- |
Module      : SAWScript.Crucible.Common
Description : Crucible-related material that is not specific to a given language
License     : BSD3
Maintainer  : langston
Stability   : provisional
-}

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RankNTypes #-}

module SAWScript.Crucible.Common
  ( AllocIndex(..)
  , nextAllocIndex
  , PrePost(..)
  , ppAbortedResult
  , Sym
  ) where

import           Data.Data (Data)
import           GHC.Generics (Generic)

import           Lang.Crucible.Simulator.ExecutionTree (AbortedResult(..), GlobalPair)
import           Lang.Crucible.Simulator.CallFrame (SimFrame)
import           Lang.Crucible.Backend (AbortExecReason(..), ppAbortExecReason)
import           Lang.Crucible.Backend.SAWCore (SAWCoreBackend)
import qualified Data.Parameterized.Nonce as Nonce
import qualified What4.Solver.Yices as Yices
import qualified What4.Expr as W4

import qualified Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>), (<>))

-- | The symbolic backend we use for SAW verification
type Sym = SAWCoreBackend Nonce.GlobalNonceGenerator (Yices.Connection Nonce.GlobalNonceGenerator) (W4.Flags W4.FloatReal)

-- | How many allocations have we made in this method spec?
newtype AllocIndex = AllocIndex Int
  deriving (Data, Eq, Generic, Ord, Show)

nextAllocIndex :: AllocIndex -> AllocIndex
nextAllocIndex (AllocIndex n) = AllocIndex (n + 1)

-- | Are we writing preconditions or postconditions?
data PrePost
  = PreState | PostState
  deriving (Data, Eq, Generic, Ord, Show)

ppAbortedResult :: (forall l args. GlobalPair Sym (SimFrame Sym ext l args) -> PP.Doc)
                -> AbortedResult Sym ext
                -> PP.Doc
ppAbortedResult _ (AbortedExec InfeasibleBranch _) =
  PP.text "Infeasible branch"
ppAbortedResult ppGP (AbortedExec abt gp) = do
  ppAbortExecReason abt PP.<$$> ppGP gp
ppAbortedResult ppGP (AbortedBranch _predicate trueBranch falseBranch) =
  PP.vcat
    [ PP.text "Both branches aborted after a symbolic branch."
    -- TODO: These conditions can be large, symbolic SAWCore predicates, so they
    -- aren't really helpful to show. It would be nice if Crucible tracked the
    -- source location associated with the branch, then we could print that.
    -- See https://github.com/GaloisInc/crucible/issues/260

    -- , text "Branch condition:"
    -- , indent 2 (text (show predicate))
    , PP.text "Message from the true branch:"
    , PP.indent 2 (ppAbortedResult ppGP trueBranch)
    , PP.text "Message from the false branch:"
    , PP.indent 2 (ppAbortedResult ppGP falseBranch)
    ]
ppAbortedResult _ (AbortedExit ec) =
  PP.text "Branch exited:" PP.<+> PP.text (show ec)
