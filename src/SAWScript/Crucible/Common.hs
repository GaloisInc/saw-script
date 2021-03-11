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
  , setupProfiling
  , SAWCruciblePersonality(..)
  , newSAWCoreBackend
  , sawCoreState
  ) where

import           Lang.Crucible.Simulator (GenericExecutionFeature)
import           Lang.Crucible.Simulator.ExecutionTree (AbortedResult(..), GlobalPair)
import           Lang.Crucible.Simulator.CallFrame (SimFrame)
import           Lang.Crucible.Simulator.Profiling
import           Lang.Crucible.Backend (AbortExecReason(..), ppAbortExecReason, IsSymInterface)
import           Lang.Crucible.Backend.Online
import qualified Data.Parameterized.Nonce as Nonce
import qualified What4.Solver.Yices as Yices
import qualified What4.Config as W4
import qualified What4.Expr as W4
import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4
import qualified What4.ProgramLoc as W4 (plSourceLoc)

import System.Directory (createDirectoryIfMissing)
import System.FilePath ((</>))
import qualified Prettyprinter as PP


import Verifier.SAW.SharedTerm as SC
import Verifier.SAW.Simulator.What4.ReturnTrip (SAWCoreState, newSAWCoreState)

-- | The symbolic backend we use for SAW verification
type Sym = OnlineBackendUserSt Nonce.GlobalNonceGenerator Yices.Connection SAWCoreState (W4.Flags W4.FloatReal)

data SAWCruciblePersonality sym = SAWCruciblePersonality


newSAWCoreBackend :: SC.SharedContext -> IO Sym
newSAWCoreBackend sc =
  do st <- newSAWCoreState sc
     sym <- newOnlineBackend W4.FloatRealRepr Nonce.globalNonceGenerator Yices.yicesDefaultFeatures st
     W4.extendConfig Yices.yicesOptions (W4.getConfiguration sym)
     return sym

sawCoreState :: Sym -> IO (SAWCoreState Nonce.GlobalNonceGenerator)
sawCoreState sym = pure (onlineUserState (W4.sbUserState sym))

ppAbortedResult :: (forall l args. GlobalPair Sym (SimFrame Sym ext l args) -> PP.Doc ann)
                -> AbortedResult Sym ext
                -> PP.Doc ann
ppAbortedResult _ (AbortedExec InfeasibleBranch _) =
  PP.pretty "Infeasible branch"
ppAbortedResult ppGP (AbortedExec abt gp) = do
  PP.vcat
    [ ppAbortExecReason abt
    , ppGP gp
    ]
ppAbortedResult ppGP (AbortedBranch loc _predicate trueBranch falseBranch) =
  PP.vcat
    [ PP.pretty "Both branches aborted after a symbolic branch."
    , PP.pretty "Location of control-flow branching:"
    , PP.indent 2 (PP.pretty (W4.plSourceLoc loc))
    , PP.pretty "Message from the true branch:"
    , PP.indent 2 (ppAbortedResult ppGP trueBranch)
    , PP.pretty "Message from the false branch:"
    , PP.indent 2 (ppAbortedResult ppGP falseBranch)
    ]
ppAbortedResult _ (AbortedExit ec) =
  PP.pretty "Branch exited:" PP.<+> PP.viaShow ec

setupProfiling ::
  IsSymInterface sym =>
  sym -> String -> Maybe FilePath ->
  IO (IO (), [GenericExecutionFeature sym])
setupProfiling _ _ Nothing = return (return (), [])
setupProfiling sym profSource (Just dir) =
  do tbl <- newProfilingTable

     createDirectoryIfMissing True dir

     startRecordingSolverEvents sym tbl

     let profOutFile = dir </> "report_data.js"
         saveProf = writeProfileReport profOutFile "Crucible profile" profSource
         profOpts = ProfilingOptions
                      { periodicProfileInterval = 5
                      , periodicProfileAction = saveProf
                      }

     pfs <- profilingFeature tbl profilingEventFilter (Just profOpts)
     return (saveProf tbl, [pfs])
