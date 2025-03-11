{- |
Module      : SAWCentral.Crucible.Common
Description : Crucible-related material that is not specific to a given language
License     : BSD3
Maintainer  : langston
Stability   : provisional
-}

{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}

module SAWCentral.Crucible.Common
  ( ppAbortedResult
  , Sym
  , Backend
  , SomeOnlineBackend(..)
  , SomeBackend(..)
  , IsSymBackend(..)
  , HasSymInterface(..)
  , OnlineSolver(..)
  , PathSatSolver(..)
  , setupProfiling
  , SAWCruciblePersonality(..)
  , newSAWCoreExprBuilder
  , newSAWCoreBackend
  , newSAWCoreBackendWithTimeout
  , defaultSAWCoreBackendTimeout
  , sawCoreState
  ) where

import           Lang.Crucible.Simulator (GenericExecutionFeature)
import           Lang.Crucible.Simulator.ExecutionTree (AbortedResult(..), GlobalPair)
import           Lang.Crucible.Simulator.CallFrame (SimFrame)
import           Lang.Crucible.Simulator.Profiling
import           Lang.Crucible.Backend
                   (AbortExecReason(..), ppAbortExecReason, IsSymInterface, IsSymBackend(..),
                    HasSymInterface(..), SomeBackend(..))
import           Lang.Crucible.Backend.Online (OnlineBackend, newOnlineBackend)
import qualified Data.Parameterized.Nonce as Nonce
import           What4.Protocol.Online (OnlineSolver(..))
import qualified What4.Solver.CVC5 as CVC5
import qualified What4.Solver.Z3 as Z3
import qualified What4.Solver.Yices as Yices
import qualified What4.Protocol.SMTLib2 as SMT2

import qualified What4.Config as W4
import qualified What4.Expr as W4
import qualified What4.Expr.Builder as W4
import qualified What4.Interface as W4
import qualified What4.ProgramLoc as W4 (plSourceLoc)

import Control.Lens ( (^.) )
import System.Directory (createDirectoryIfMissing)
import System.FilePath ((</>))
import qualified Prettyprinter as PP


import Verifier.SAW.SharedTerm as SC
import Verifier.SAW.Simulator.What4.ReturnTrip (SAWCoreState, newSAWCoreState)

data PathSatSolver
  = PathSat_Z3
  | PathSat_Yices
 deriving (Eq, Ord, Show)


-- | The symbolic backend we use for SAW verification
type Sym = W4.ExprBuilder Nonce.GlobalNonceGenerator SAWCoreState (W4.Flags W4.FloatReal)
type Backend solver = OnlineBackend solver Nonce.GlobalNonceGenerator SAWCoreState (W4.Flags W4.FloatReal)

data SomeOnlineBackend =
  forall solver. OnlineSolver solver =>
    SomeOnlineBackend (Backend solver)

data SAWCruciblePersonality sym = SAWCruciblePersonality

sawCoreState :: Sym -> IO (SAWCoreState Nonce.GlobalNonceGenerator)
sawCoreState sym = pure (sym ^. W4.userState)

newSAWCoreExprBuilder :: SC.SharedContext -> Bool -> IO Sym
newSAWCoreExprBuilder sc what4PushMuxOps =
  do st <- newSAWCoreState sc
     sym <- W4.newExprBuilder W4.FloatRealRepr st Nonce.globalNonceGenerator
     pushMuxOpsSetting <- W4.getOptionSetting W4.pushMuxOpsOption $ W4.getConfiguration sym
     _ <- W4.setOpt pushMuxOpsSetting what4PushMuxOps
     pure sym

defaultSAWCoreBackendTimeout :: Integer
defaultSAWCoreBackendTimeout = 10000

newSAWCoreBackend :: PathSatSolver -> Sym -> IO SomeOnlineBackend
newSAWCoreBackend pss sym = newSAWCoreBackendWithTimeout pss sym 0

newSAWCoreBackendWithTimeout :: PathSatSolver -> Sym -> Integer -> IO SomeOnlineBackend
newSAWCoreBackendWithTimeout PathSat_Yices sym timeout =
  do bak <- newOnlineBackend sym Yices.yicesDefaultFeatures
     W4.extendConfig Z3.z3Options (W4.getConfiguration sym)
     W4.extendConfig Yices.yicesOptions (W4.getConfiguration sym)
     W4.extendConfig CVC5.cvc5Options (W4.getConfiguration sym)
     yicesTimeoutSetting <- W4.getOptionSetting Yices.yicesGoalTimeout (W4.getConfiguration sym)
     _ <- W4.setOpt yicesTimeoutSetting timeout
     return (SomeOnlineBackend (bak :: Backend Yices.Connection))

newSAWCoreBackendWithTimeout PathSat_Z3 sym timeout =
  do bak <- newOnlineBackend sym (SMT2.defaultFeatures Z3.Z3)
     W4.extendConfig Z3.z3Options (W4.getConfiguration sym)
     W4.extendConfig Yices.yicesOptions (W4.getConfiguration sym)
     W4.extendConfig CVC5.cvc5Options (W4.getConfiguration sym)
     z3TimeoutSetting <- W4.getOptionSetting Z3.z3Timeout (W4.getConfiguration sym)
     _ <- W4.setOpt z3TimeoutSetting timeout
     return (SomeOnlineBackend (bak :: Backend (SMT2.Writer Z3.Z3)))

ppAbortedResult :: (forall l args. GlobalPair Sym (SimFrame Sym ext l args) -> PP.Doc ann)
                -> AbortedResult Sym ext
                -> PP.Doc ann
ppAbortedResult _ (AbortedExec InfeasibleBranch{} _) =
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
ppAbortedResult _ (AbortedExit ec _gp) =
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
