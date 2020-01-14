{-# Language FlexibleContexts #-}
{-# Language ScopedTypeVariables #-}
{-# Language LambdaCase #-}
{-# Language ImplicitParams #-}
{-# Language TypeApplications #-}
{-# Language DataKinds #-}

module SAWScript.Crucible.LLVM.X86 where

import System.IO (stdout)

import Control.Exception (catch)
import Control.Lens (view, (^.))
import Control.Monad.ST (stToIO)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State (execStateT)
import Control.Monad.Error (MonadError(..))

import Data.Foldable (forM_)
import qualified Data.Text as Text
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Text.Encoding (decodeUtf8, encodeUtf8)
import qualified Data.Map as Map

import Data.Parameterized.Some
import Data.Parameterized.Context (singleton)
import Data.Parameterized.Nonce (globalNonceGenerator)
import qualified Data.Parameterized.Context as Ctx

import qualified Text.LLVM.AST as LLVM

import qualified SAWScript.Crucible.LLVM.CrucibleLLVM as Crucible

import SAWScript.Proof
import SAWScript.Prover.SBV
import SAWScript.Prover.SolverStats
import SAWScript.Prover.Versions
import SAWScript.TopLevel
import SAWScript.Value
import SAWScript.Options
import SAWScript.X86
  ( RelevantElf(..), X86Error(..)
  , findSymbol, getElf, getGoals, getRelevant, gGoal, posFn
  )
import SAWScript.X86Spec
  ( Sym
  , freshRegister, mkGlobalMap
  )

import qualified SAWScript.Crucible.Common.MethodSpec as MS
import qualified SAWScript.Crucible.Common.Setup.Type as Setup

import SAWScript.Crucible.LLVM.Builtins (setupLLVMCrucibleContext)
import SAWScript.Crucible.LLVM.Override
import SAWScript.Crucible.LLVM.ResolveSetupValue
import SAWScript.Crucible.LLVM.MethodSpecIR

import What4.FunctionName (functionNameFromText)
import What4.ProgramLoc (Position(..), mkProgramLoc)
import What4.Expr (FloatModeRepr(..))
import What4.FunctionName (functionNameFromText)

import Lang.Crucible.Analysis.Postdom (postdomInfo)
import Lang.Crucible.Backend.SAWCore
import Lang.Crucible.CFG.Core
  ( SomeCFG(..), TypeRepr(..)
  , cfgHandle, knownRepr
  )
import Lang.Crucible.FunctionHandle (insertHandleMap, emptyHandleMap)
import Lang.Crucible.Simulator.EvalStmt (executeCrucible)
import Lang.Crucible.Simulator.ExecutionTree
  ( ExecResult(..), ExecState(..), FnState(..), SimContext(..)
  , simHandleAllocator
  )
import Lang.Crucible.Simulator.GlobalState (insertGlobal, emptyGlobals)
import Lang.Crucible.Simulator.Operations (defaultAbortHandler)
import Lang.Crucible.Simulator.OverrideSim (callCFG, readGlobal, runOverrideSim)
import Lang.Crucible.Simulator.RegMap (RegEntry(..), RegMap(..), regValue)
import Lang.Crucible.Simulator.RegValue (RegValue'(..), RegValue)

import Lang.Crucible.LLVM.MemModel (emptyMem, mkMemVar)
import Lang.Crucible.LLVM.DataLayout (EndianForm(..))

import Data.Macaw.Types (BVType)
import Data.Macaw.Discovery
  ( FunctionExploreReason(..)
  , analyzeFunction, emptyDiscoveryState
  )
import Data.Macaw.Memory (MemSegmentOff)
import Data.Macaw.Symbolic
  ( GlobalMap, LookupFunctionHandle(..), MacawExt, MacawSimulatorState(..), MacawCrucibleRegTypes(..)
  , macawExtensions, mkFunCFG
  )
import Data.Macaw.Symbolic.Backend (MacawSymbolicArchFunctions(..), crucArchRegTypes)
import Data.Macaw.X86.Symbolic (newSymFuns, x86_64MacawEvalFn, x86_64MacawSymbolicFns)
import Data.Macaw.X86
import Data.Macaw.X86.X86Reg

type Regs = Ctx.Assignment (RegValue' Sym) (MacawCrucibleRegTypes X86_64)

argRegs :: [X86Reg (BVType 64)]
argRegs = [RDI, RSI, RDX, RCX, R8, R9]

retReg :: X86Reg (BVType 64)
retReg = RAX

llvmTypeToMemType ::
  Crucible.TypeContext ->
  LLVM.Type ->
  Either String Crucible.MemType
llvmTypeToMemType lc t = let ?lc = lc in Crucible.liftMemType t

buildMethodSpec ::
  forall x.
  BuiltinContext ->
  Options ->
  LLVMModule x ->
  String ->
  String ->
  [LLVM.Type] ->
  LLVM.Type ->
  LLVMCrucibleSetupM () ->
  TopLevel (MS.CrucibleMethodSpecIR (Crucible.LLVM x))
buildMethodSpec bic opts lm nm addr args ret setup =
  setupLLVMCrucibleContext bic opts lm $ \cc -> do
    let methodId = LLVMMethodId nm Nothing
    let programLoc = mkProgramLoc (functionNameFromText $ Text.pack nm) . OtherPos $ Text.pack addr
    let LLVMModule _ _ mtrans = lm
    let lc = mtrans ^. Crucible.transContext . Crucible.llvmTypeCtx
    (mtargs, mtret) <- case (,) <$> mapM (llvmTypeToMemType lc) args <*> llvmTypeToMemType lc ret of
      Left err -> fail err
      Right x -> pure x
    let initialMethodSpec = MS.makeCrucibleMethodSpecIR @(Crucible.LLVM x) methodId mtargs (Just mtret) programLoc lm
    view Setup.csMethodSpec <$> execStateT (runLLVMCrucibleSetupM setup) (Setup.makeCrucibleSetupState cc initialMethodSpec)

initialMemory ::
  Sym ->
  MS.CrucibleMethodSpecIR (Crucible.LLVM x) ->
  IO (GlobalMap Sym 64, Crucible.MemImpl Sym, Regs)
initialMemory sym ms = do
  let globs = mkGlobalMap Map.empty
  mem <- emptyMem LittleEndian
  -- TODO: allocations from spec
  regs <- Ctx.traverseWithIndex (freshRegister sym) knownRepr
  pure (globs, mem, regs)

checkPost ::
  MS.CrucibleMethodSpecIR (Crucible.LLVM x) ->
  Crucible.MemImpl Sym ->
  Regs ->
  IO ()
checkPost _ _ _ = pure () -- TODO

-- ^ Verify that an x86_64 function (following the System V AMD64 ABI) conforms
-- to an LLVM specification. This allows for compositional verification of LLVM
-- functions that call x86_64 functions (but not the other way around).
crucible_llvm_verify_x86 ::
  BuiltinContext ->
  Options ->
  Some LLVMModule {- ^ Module to associate with method spec -} ->
  FilePath {- ^ Path to ELF file -} ->
  String {- ^ Function's symbol in ELF file -} ->
  [LLVM.Type] {- ^ Types of function arguments -}->
  LLVM.Type {- ^ Function return type -}->
  LLVMCrucibleSetupM () ->
  TopLevel (SomeLLVM MS.CrucibleMethodSpecIR)
crucible_llvm_verify_x86 bic opts (Some (llvmModule :: LLVMModule x)) path nm args ret setup = do
    let sc = biSharedContext bic
    sym <- liftIO $ newSAWCoreBackend FloatRealRepr sc globalNonceGenerator
    halloc <- getHandleAlloc
    mvar <- liftIO $ mkMemVar halloc
    sfs <- liftIO $ newSymFuns sym

    elf <- liftIO $ getElf path >>= getRelevant
    (addr :: MemSegmentOff 64) <- liftIO . findSymbol (symMap elf) . encodeUtf8 $ Text.pack nm
    (_, Some finfo) <- liftIO . stToIO . analyzeFunction nolog addr UserRequest
      $ emptyDiscoveryState (memory elf) (funSymMap elf) x86_64_linux_info
    SomeCFG cfg <- liftIO $ mkFunCFG x86_64MacawSymbolicFns halloc fname posFn finfo

    methodSpec <- buildMethodSpec bic opts llvmModule nm (show addr) args ret setup

    (globs :: GlobalMap Sym 64, mem, regs) <- liftIO $ initialMemory sym methodSpec

    let
      ctx :: SimContext (MacawSimulatorState Sym) Sym (MacawExt X86_64)
      ctx = SimContext
            { _ctxSymInterface = sym
            , ctxSolverProof = id
            , ctxIntrinsicTypes = Crucible.llvmIntrinsicTypes
            , simHandleAllocator = halloc
            , printHandle = stdout
            , extensionImpl =
              macawExtensions (x86_64MacawEvalFn sfs) mvar globs $ LookupFunctionHandle $ \_ _ _ ->
                fail "Attempted to call a function during x86 verification"
            , _functionBindings =
              insertHandleMap (cfgHandle cfg) (UseCFG cfg $ postdomInfo cfg) emptyHandleMap
            , _cruciblePersonality = MacawSimulatorState
            , _profilingMetrics = Map.empty
            }
      globals = insertGlobal mvar mem emptyGlobals
      initial = InitialState ctx globals defaultAbortHandler macawStructRepr
                $ runOverrideSim macawStructRepr
                $ crucGenArchConstraints x86_64MacawSymbolicFns
                $ do r <- callCFG cfg $ RegMap $ singleton $ RegEntry macawStructRepr regs
                     mem' <- readGlobal mvar
                     liftIO $ checkPost methodSpec mem' $ regValue r
                     pure $ regValue r
    liftIO $ executeCrucible [] initial >>= \case
      FinishedResult{} -> pure ()
      AbortedResult{} -> printOutLn opts Warn "Function never returns"
      TimeoutResult{} -> fail "Execution timed out"

    gs <- liftIO $ getGoals sym
    liftIO . forM_ gs $ \g ->
      do term <- gGoal sc g
         (mb, stats) <- proveUnintSBV z3 [] Nothing sc term
         putStrLn $ ppStats stats
         case mb of
           Nothing -> putStrLn "Success"
           Just ex -> fail $ "Failure, counterexample: " <> show ex
      `catch` \(X86Error e) -> fail $ "Failure, error: " <> e

    pure $ SomeLLVM methodSpec
  where
    nolog _ = pure ()
    fname = functionNameFromText $ Text.pack nm
    macawStructRepr = StructRepr $ crucArchRegTypes x86_64MacawSymbolicFns
