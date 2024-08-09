{- |
Module      : SAWCentral.Crucible.Common
Description : Crucible-related material that is not specific to a given language
License     : BSD3
Maintainer  : langston
Stability   : provisional
-}

{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
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
  , baseCryptolType
  , getGlobalPair
  , runCFG
  , setupArg
  , setupArgs
  ) where

import qualified Cryptol.TypeCheck.Type as Cryptol
import qualified Lang.Crucible.CFG.Core as Crucible
import qualified Lang.Crucible.CFG.Extension as Crucible (IsSyntaxExtension)
import qualified Lang.Crucible.FunctionHandle as Crucible
import qualified Lang.Crucible.LLVM.MemModel as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import           Lang.Crucible.Simulator (GenericExecutionFeature)
import           Lang.Crucible.Simulator.ExecutionTree (AbortedResult(..), GlobalPair)
import           Lang.Crucible.Simulator.CallFrame (SimFrame)
import           Lang.Crucible.Simulator.Profiling
import           Lang.Crucible.Backend
                   (AbortExecReason(..), ppAbortExecReason, IsSymInterface, IsSymBackend(..),
                    HasSymInterface(..), SomeBackend(..))
import           Lang.Crucible.Backend.Online (OnlineBackend, newOnlineBackend)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr (natValue)
import qualified Data.Parameterized.Nonce as Nonce
import qualified Data.Parameterized.TraversableFC as FC
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
import Data.IORef
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import System.Directory (createDirectoryIfMissing)
import System.FilePath ((</>))
import qualified Prettyprinter as PP


import CryptolSAWCore.TypedTerm
import SAWCore.SharedTerm as SC
import SAWCoreWhat4.ReturnTrip
         (SAWCoreState, baseSCType, bindSAWTerm, newSAWCoreState)

import SAWCentral.Options (Options, Verbosity(..), printOutLn)

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
  "Infeasible branch"
ppAbortedResult ppGP (AbortedExec abt gp) = do
  PP.vcat
    [ ppAbortExecReason abt
    , ppGP gp
    ]
ppAbortedResult ppGP (AbortedBranch loc _predicate trueBranch falseBranch) =
  PP.vcat
    [ "Both branches aborted after a symbolic branch."
    , "Location of control-flow branching:"
    , PP.indent 2 (PP.pretty (W4.plSourceLoc loc))
    , "Message from the true branch:"
    , PP.indent 2 (ppAbortedResult ppGP trueBranch)
    , "Message from the false branch:"
    , PP.indent 2 (ppAbortedResult ppGP falseBranch)
    ]
ppAbortedResult _ (AbortedExit ec _gp) =
  "Branch exited:" PP.<+> PP.viaShow ec

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

baseCryptolType :: Crucible.BaseTypeRepr tp -> Maybe Cryptol.Type
baseCryptolType bt =
  case bt of
    Crucible.BaseBoolRepr -> pure $ Cryptol.tBit
    Crucible.BaseBVRepr w -> pure $ Cryptol.tWord (Cryptol.tNum (natValue w))
    Crucible.BaseIntegerRepr -> pure $ Cryptol.tInteger
    Crucible.BaseArrayRepr {} -> Nothing
    Crucible.BaseFloatRepr _ -> Nothing
    Crucible.BaseStringRepr _ -> Nothing
    Crucible.BaseComplexRepr  -> Nothing
    Crucible.BaseRealRepr     -> Nothing
    Crucible.BaseStructRepr ts ->
      Cryptol.tTuple <$> baseCryptolTypes ts
  where
    baseCryptolTypes :: Ctx.Assignment Crucible.BaseTypeRepr args -> Maybe [Cryptol.Type]
    baseCryptolTypes Ctx.Empty = pure []
    baseCryptolTypes (xs Ctx.:> x) =
      do ts <- baseCryptolTypes xs
         t <- baseCryptolType x
         pure (ts ++ [t])

setupArg ::
  forall tp.
  SharedContext ->
  Sym ->
  IORef (Seq TypedExtCns) ->
  Crucible.TypeRepr tp ->
  IO (Crucible.RegEntry Sym tp)
setupArg sc sym ecRef tp = do
  st <- sawCoreState sym
  case (Crucible.asBaseType tp, tp) of
    (Crucible.AsBaseType btp, _) ->
      do cty <-
           case baseCryptolType btp of
             Just cty -> pure cty
             Nothing ->
               fail $ unwords ["Unsupported type for Crucible extraction:", show btp]
         sc_tp <- baseSCType sym sc btp
         t     <- freshGlobal cty sc_tp
         elt   <- bindSAWTerm sym st btp t
         return (Crucible.RegEntry tp elt)

    (Crucible.NotBaseType, Crucible.LLVMPointerRepr w) ->
      do let cty = Cryptol.tWord (Cryptol.tNum (natValue w))
         sc_tp <- scBitvector sc (natValue w)
         t     <- freshGlobal cty sc_tp
         elt   <- bindSAWTerm sym st (Crucible.BaseBVRepr w) t
         elt'  <- Crucible.llvmPointer_bv sym elt
         return (Crucible.RegEntry tp elt')

    (Crucible.NotBaseType, _) ->
      fail $ unwords ["Crucible extraction currently only supports Crucible base types", show tp]
  where
    freshGlobal cty sc_tp =
      do ecs <- readIORef ecRef
         let len = Seq.length ecs
         ec <- scFreshEC sc ("arg_" <> Text.pack (show len)) sc_tp
         writeIORef ecRef (ecs Seq.|> TypedExtCns cty ec)
         scVariable sc ec

setupArgs ::
  SharedContext ->
  Sym ->
  Crucible.FnHandle init ret ->
  IO (Seq TypedExtCns, Crucible.RegMap Sym init)
setupArgs sc sym fn =
  do ecRef  <- newIORef Seq.empty
     regmap <- Crucible.RegMap <$> FC.traverseFC (setupArg sc sym ecRef) (Crucible.handleArgTypes fn)
     ecs    <- readIORef ecRef
     return (ecs, regmap)

getGlobalPair ::
  Options ->
  Crucible.PartialResult sym ext v ->
  IO (Crucible.GlobalPair sym v)
getGlobalPair opts pr =
  case pr of
    Crucible.TotalRes gp -> return gp
    Crucible.PartialRes _ _ gp _ -> do
      printOutLn opts Info "Symbolic simulation completed with side conditions."
      return gp

runCFG ::
  (Crucible.IsSyntaxExtension ext, IsSymInterface sym) =>
  Crucible.SimContext p sym ext ->
  Crucible.SymGlobalState sym ->
  Crucible.FnHandle args a ->
  Crucible.CFG ext blocks init a ->
  Crucible.RegMap sym init ->
  IO (Crucible.ExecResult p sym ext (Crucible.RegEntry sym a))
runCFG simCtx globals h cfg args =
  do let initExecState =
           Crucible.InitialState simCtx globals Crucible.defaultAbortHandler (Crucible.handleReturnType h) $
           Crucible.runOverrideSim (Crucible.handleReturnType h)
                    (Crucible.regValue <$> (Crucible.callCFG cfg args))
     Crucible.executeCrucible [] initExecState
