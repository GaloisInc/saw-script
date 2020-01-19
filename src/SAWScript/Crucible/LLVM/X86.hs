{-# Language OverloadedStrings #-}
{-# Language FlexibleContexts #-}
{-# Language ScopedTypeVariables #-}
{-# Language PatternSynonyms #-}
{-# Language LambdaCase #-}
{-# Language TupleSections #-}
{-# Language ImplicitParams #-}
{-# Language TypeApplications #-}
{-# Language GADTs #-}
{-# Language DataKinds #-}

module SAWScript.Crucible.LLVM.X86 where

import System.IO (stdout)

import Control.Exception (catch)
import Control.Lens (view, (^.))
import Control.Monad.ST (stToIO)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State (execStateT)

import Data.Type.Equality ((:~:)(..), testEquality)
import Data.Foldable (foldlM, forM_)
import qualified Data.Text as Text
import Data.Text.Encoding (encodeUtf8)
import qualified Data.Map as Map
import Data.Map (Map)

import qualified Text.LLVM.AST as LLVM

import Data.Parameterized.Some (Some(..))
import Data.Parameterized.NatRepr (knownNat)
import Data.Parameterized.Context (singleton)
import Data.Parameterized.Nonce (globalNonceGenerator)
import qualified Data.Parameterized.Context as Ctx

-- saw-script
import SAWScript.Prover.SBV
import SAWScript.Prover.SolverStats
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
import SAWScript.Crucible.LLVM.MethodSpecIR
import SAWScript.Crucible.LLVM.ResolveSetupValue
  ( resolveSetupVal, typeOfSetupValue
  )

-- what4
import What4.Expr (FloatModeRepr(..))
import What4.FunctionName (functionNameFromText)
import What4.Interface (BaseTypeRepr(..), bvLit, natLit, freshConstant, userSymbol)
import What4.ProgramLoc (Position(..), mkProgramLoc, plSourceLoc)

-- crucible
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

-- crucible-llvm
import Lang.Crucible.LLVM.Bytes (Bytes, bytesToInteger)
import Lang.Crucible.LLVM.DataLayout (EndianForm(..), defaultDataLayout, noAlignment)
import Lang.Crucible.LLVM.Extension (LLVM, X86, ArchRepr(..))
import Lang.Crucible.LLVM.Intrinsics (llvmArch, llvmIntrinsicTypes, llvmTypeCtx)
import Lang.Crucible.LLVM.MemModel
  ( AllocType(..), LLVMPointerType, LLVMPtr, MemImpl, Mutability(..)
  , pattern LLVMPointer, pattern LLVMPointerRepr
  , doMalloc, doPtrAddOffset, doStore
  , loadRaw, storeConstRaw
  , bitvectorType, toStorableType
  , emptyMem, mkMemVar
  , assertSafe, unpackMemValue
  , ppMem, ppPtr
  )
import Lang.Crucible.LLVM.MemType (Ident, MemType, memTypeSize)
import Lang.Crucible.LLVM.Translation (transContext)
import Lang.Crucible.LLVM.TypeContext (TypeContext, liftMemType)

-- macaw
import Data.Macaw.Types (BVType)
import Data.Macaw.Discovery
  ( FunctionExploreReason(..)
  , analyzeFunction, emptyDiscoveryState
  )
import Data.Macaw.Memory (MemSegment(..), MemSegmentOff(..), segmentSize)
import Data.Macaw.Symbolic
  ( GlobalMap, LookupFunctionHandle(..), MacawExt, MacawSimulatorState(..), MacawCrucibleRegTypes
  , macawExtensions, mkFunCFG
  )
import Data.Macaw.Symbolic.Backend (MacawSymbolicArchFunctions(..), crucArchRegTypes)
import Data.Macaw.X86.Symbolic
  ( newSymFuns, x86_64MacawEvalFn, x86_64MacawSymbolicFns
  , lookupX86Reg, updateX86Reg
  )
import Data.Macaw.X86
import Data.Macaw.X86.X86Reg

type Regs = Ctx.Assignment (RegValue' Sym) (MacawCrucibleRegTypes X86_64)

llvmTypeToMemType ::
  TypeContext ->
  LLVM.Type ->
  Either String MemType
llvmTypeToMemType lc t = let ?lc = lc in liftMemType t

buildMethodSpec ::
  BuiltinContext ->
  Options ->
  LLVMModule (X86 64) ->
  String ->
  String ->
  [LLVM.Type] ->
  Maybe LLVM.Type ->
  LLVMCrucibleSetupM () ->
  TopLevel (MS.CrucibleMethodSpecIR (LLVM (X86 64)))
buildMethodSpec bic opts lm nm addr args ret setup =
  setupLLVMCrucibleContext bic opts lm $ \cc -> do
    let methodId = LLVMMethodId nm Nothing
    let programLoc = mkProgramLoc (functionNameFromText $ Text.pack nm) . OtherPos $ Text.pack addr
    let LLVMModule _ _ mtrans = lm
    let lc = mtrans ^. transContext . llvmTypeCtx
    (mtargs, mtret) <- case (,) <$> mapM (llvmTypeToMemType lc) args <*> mapM (llvmTypeToMemType lc) ret of
      Left err -> fail err
      Right x -> pure x
    let initialMethodSpec = MS.makeCrucibleMethodSpecIR @(LLVM (X86 64)) methodId mtargs mtret programLoc lm
    view Setup.csMethodSpec <$> execStateT (runLLVMCrucibleSetupM setup) (Setup.makeCrucibleSetupState cc initialMethodSpec)

setReg ::
  X86Reg (BVType 64) ->
  RegValue Sym (LLVMPointerType 64) ->
  Regs ->
  IO Regs
setReg reg val regs = case updateX86Reg reg (RV . const val) regs of
  Just regs' -> pure regs'
  Nothing -> fail $ mconcat ["Invalid register: ", show reg]

setRegSetupValue ::
  Sym ->
  LLVMCrucibleContext (X86 64) ->
  Map MS.AllocIndex (LLVMPtr Sym 64) ->
  Map MS.AllocIndex LLVMAllocSpec ->
  Map MS.AllocIndex Ident ->
  MemImpl Sym ->
  Regs ->
  (X86Reg (BVType 64), MS.SetupValue (LLVM (X86 64))) ->
  IO Regs
setRegSetupValue sym cc env tyenv nameEnv mem regs (reg, sval) = do
  let ?ptrWidth = knownNat @64
  val <- unpackMemValue sym (LLVMPointerRepr $ knownNat @64)
    =<< resolveSetupVal cc mem env tyenv nameEnv sval
  setReg reg val regs

getReg ::
  X86Reg (BVType 64) ->
  Regs ->
  IO (RegValue Sym (LLVMPointerType 64))
getReg reg regs = case lookupX86Reg reg regs of
  Just (RV val) -> pure val
  Nothing -> fail $ mconcat ["Invalid register: ", show reg]

allocate ::
  Sym ->
  MemImpl Sym ->
  String ->
  MemType ->
  Mutability ->
  IO (LLVMPtr Sym 64, MemImpl Sym)
allocate sym mem nm mt mut = do
  let ?ptrWidth = knownNat @64
  sz <- bvLit sym knownNat . bytesToInteger $ memTypeSize defaultDataLayout mt
  doMalloc sym HeapAlloc mut nm mem sz noAlignment

allocateStack ::
  Sym ->
  MemImpl Sym ->
  Bytes ->
  IO (LLVMPtr Sym 64, MemImpl Sym)
allocateStack sym mem bytes = do
  let ?ptrWidth = knownNat @64
  let szInt = bytesToInteger bytes
  sz <- bvLit sym knownNat $ szInt + 8
  (base, mem') <- doMalloc sym HeapAlloc Mutable "stack_alloc" mem sz noAlignment
  sn <- case userSymbol "stack" of
    Left err -> fail $ "Invalid symbol for stack: " <> show err
    Right sn -> pure sn
  fresh <- LLVMPointer <$> natLit sym 0 <*> freshConstant sym sn (BaseBVRepr $ knownNat @64)
  ptr <- doPtrAddOffset sym mem' base =<< bvLit sym knownNat szInt
  (ptr,) <$> doStore sym mem' ptr (LLVMPointerRepr $ knownNat @64) (bitvectorType 8) noAlignment fresh

executeAllocation ::
  Sym ->
  (Map MS.AllocIndex (LLVMPtr Sym 64), MemImpl Sym) ->
  (MS.AllocIndex, LLVMAllocSpec) ->
  IO (Map MS.AllocIndex (LLVMPtr Sym 64), MemImpl Sym)
executeAllocation sym (env, mem) (i, LLVMAllocSpec mut _memTy sz loc) = do
  let ?ptrWidth = knownNat @64
  sz' <- liftIO $ bvLit sym knownNat $ bytesToInteger sz
  (ptr, mem') <- doMalloc sym HeapAlloc mut (show $ plSourceLoc loc) mem sz' noAlignment
  pure (Map.insert i ptr env, mem')

executePointsTo ::
  Sym ->
  LLVMCrucibleContext (X86 64) ->
  Map MS.AllocIndex (LLVMPtr Sym 64) ->
  Map MS.AllocIndex LLVMAllocSpec ->
  Map MS.AllocIndex Ident ->
  MemImpl Sym ->
  LLVMPointsTo (X86 64) ->
  IO (MemImpl Sym)
executePointsTo sym cc env tyenv nameEnv mem (LLVMPointsTo _ tptr tval) = do
  let ?ptrWidth = knownNat @64
  ptr <- unpackMemValue sym (LLVMPointerRepr $ knownNat @64)
    =<< resolveSetupVal cc mem env tyenv Map.empty tptr
  val <- resolveSetupVal cc mem env tyenv Map.empty tval
  storTy <- toStorableType =<< typeOfSetupValue cc tyenv nameEnv tval
  storeConstRaw sym mem ptr storTy noAlignment val

argRegs :: [X86Reg (BVType 64)]
argRegs = [RDI, RSI, RDX, RCX, R8, R9]

retReg :: X86Reg (BVType 64)
retReg = RAX

setArgsRet ::
  Sym ->
  LLVMCrucibleContext (X86 64) ->
  Map MS.AllocIndex (LLVMPtr Sym 64) ->
  Map MS.AllocIndex LLVMAllocSpec ->
  Map MS.AllocIndex Ident ->
  MemImpl Sym ->
  Regs ->
  Maybe (MS.SetupValue (LLVM (X86 64))) ->
  [MS.SetupValue (LLVM (X86 64))] ->
  IO Regs
setArgsRet sym cc env tyenv nameEnv mem regs mret args
  | length args > length argRegs = fail "More arguments than would fit into registers"
  | otherwise =
      let pairs = (case mret of Nothing -> []; Just ret -> [(retReg, ret)]) <> zip argRegs args
      in foldlM (setRegSetupValue sym cc env tyenv nameEnv mem) regs pairs

-- ^ Given the spec, build the initial memory, register map, and global map.
initialMemory ::
  Sym ->
  LLVMCrucibleContext (X86 64) ->
  Integer ->
  MS.CrucibleMethodSpecIR (LLVM (X86 64)) ->
  IO (GlobalMap Sym 64, MemImpl Sym, Regs, Map MS.AllocIndex (LLVMPtr Sym 64))
initialMemory sym cc globalSize ms = do
  let ?ptrWidth = knownNat @64
  mem <- emptyMem LittleEndian
  regs <- Ctx.traverseWithIndex (freshRegister sym) knownRepr

  sz <- bvLit sym knownNat globalSize
  (ptr, mem') <- doMalloc sym GlobalAlloc Immutable "globals" mem sz noAlignment
  let globs = mkGlobalMap $ Map.singleton 0 ptr

  -- Allocate a reasonable amount of stack (4 KiB + 1 qword for IP)
  (rsp, mem'') <- allocateStack sym mem' 4096
  regs' <- setReg RSP rsp regs

  let tyenv = ms ^. MS.csPreState . MS.csAllocs
      nameEnv = MS.csTypeNames ms

  (env, mem''') <- foldlM (executeAllocation sym) (Map.empty, mem'') . Map.assocs
    $ tyenv

  mem'''' <- foldlM (executePointsTo sym cc env tyenv nameEnv) mem'''
    $ ms ^. MS.csPreState . MS.csPointsTos

  regs'' <- setArgsRet sym cc env tyenv nameEnv mem'''' regs' (ms ^. MS.csRetValue) . fmap snd . Map.elems
    $ ms ^. MS.csArgBindings

  pure (globs, mem'''', regs'', env)

checkPointsTo ::
  Sym ->
  LLVMCrucibleContext (X86 64) ->
  Map MS.AllocIndex (LLVMPtr Sym 64) ->
  Map MS.AllocIndex LLVMAllocSpec ->
  Map MS.AllocIndex Ident ->
  MemImpl Sym ->
  LLVMPointsTo (X86 64) ->
  IO ()
checkPointsTo sym cc env tyenv nameEnv mem (LLVMPointsTo _ tptr texpected) = do
  let ?ptrWidth = knownNat @64
  ptr <- unpackMemValue sym (LLVMPointerRepr $ knownNat @64)
    =<< resolveSetupVal cc mem env tyenv Map.empty tptr
  storTy <- toStorableType =<< typeOfSetupValue cc tyenv nameEnv texpected
  actual <- assertSafe sym =<< loadRaw sym mem ptr storTy noAlignment
  -- TODO
  pure ()

-- ^ Assert the postcondition for the spec, given the final memory and register map.
checkPost ::
  Sym ->
  LLVMCrucibleContext (X86 64) ->
  Map MS.AllocIndex (LLVMPtr Sym 64) ->
  MS.CrucibleMethodSpecIR (LLVM (X86 64)) ->
  MemImpl Sym ->
  Regs ->
  IO ()
checkPost sym cc env ms mem regs = do
  let tyenv = ms ^. MS.csPreState . MS.csAllocs
      nameEnv = MS.csTypeNames ms
  forM_ (ms ^. MS.csPostState . MS.csPointsTos)
    $ checkPointsTo sym cc env tyenv nameEnv mem

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
  Maybe LLVM.Type {- ^ Function return type -}->
  LLVMCrucibleSetupM () ->
  TopLevel (SomeLLVM MS.CrucibleMethodSpecIR)
crucible_llvm_verify_x86 bic opts (Some (llvmModule :: LLVMModule x)) path nm args ret setup
  | Just Refl <- testEquality (X86Repr $ knownNat @64) . llvmArch
                 $ llvmModule ^. modTrans . transContext = do
      let sc = biSharedContext bic
      sym <- liftIO $ newSAWCoreBackend FloatRealRepr sc globalNonceGenerator
      halloc <- getHandleAlloc
      mvar <- liftIO $ mkMemVar halloc
      sfs <- liftIO $ newSymFuns sym

      liftIO . printOutLn opts Info $ mconcat ["Finding symbol for \"", nm, "\""]
      elf <- liftIO $ getElf path >>= getRelevant
      (addr :: MemSegmentOff 64) <- liftIO . findSymbol (symMap elf) . encodeUtf8 $ Text.pack nm
      addrInt <- if segmentBase (segoffSegment addr) == 0
        then pure . toInteger $ segmentOffset (segoffSegment addr) + segoffOffset addr
        else fail $ mconcat ["Address of \"", nm, "\" is not an absolute address"]
      let maxAddr = addrInt + toInteger (segmentSize $ segoffSegment addr)

      liftIO . printOutLn opts Info $ mconcat ["Found symbol at address ", show addr, ", building CFG"]
      (_, Some finfo) <- liftIO . stToIO . analyzeFunction (const $ pure ()) addr UserRequest
        $ emptyDiscoveryState (memory elf) (funSymMap elf) x86_64_linux_info
      SomeCFG cfg <- liftIO $ mkFunCFG x86_64MacawSymbolicFns halloc (functionNameFromText $ Text.pack nm) posFn finfo

      let
        -- It's unpleasant that we need to do this to use resolveSetupVal.
        cc :: LLVMCrucibleContext x
        cc = LLVMCrucibleContext
             { _ccLLVMModule = llvmModule
             , _ccBackend = sym
             , _ccLLVMSimContext = error "Attempted to access ccLLVMSimContext"
             , _ccLLVMGlobals = error "Attempted to access ccLLVMGlobals"
             , _ccBasicSS = biBasicSS bic
             }

      liftIO $ printOutLn opts Info "Examining specification to determine preconditions"
      methodSpec <- buildMethodSpec bic opts llvmModule nm (show addr) args ret setup
      (globs :: GlobalMap Sym 64, mem, regs, env) <- liftIO $ initialMemory sym cc maxAddr methodSpec

      let
        ctx :: SimContext (MacawSimulatorState Sym) Sym (MacawExt X86_64)
        ctx = SimContext
              { _ctxSymInterface = sym
              , ctxSolverProof = id
              , ctxIntrinsicTypes = llvmIntrinsicTypes
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
        macawStructRepr = StructRepr $ crucArchRegTypes x86_64MacawSymbolicFns
        initial = InitialState ctx globals defaultAbortHandler macawStructRepr
                  $ runOverrideSim macawStructRepr
                  $ crucGenArchConstraints x86_64MacawSymbolicFns
                  $ do r <- callCFG cfg $ RegMap $ singleton $ RegEntry macawStructRepr regs
                       mem' <- readGlobal mvar
                       liftIO $ printOutLn opts Info
                         "Examining specification to determine postconditions"
                       liftIO $ checkPost sym cc env methodSpec mem' $ regValue r
                       pure $ regValue r

      liftIO $ printOutLn opts Info "Simulating function"
      liftIO $ executeCrucible [] initial >>= \case
        FinishedResult{} -> pure ()
        AbortedResult{} -> printOutLn opts Warn "Warning: function never returns"
        TimeoutResult{} -> fail "Execution timed out"

      liftIO $ printOutLn opts Info "Simulation finished, running solver on goals"
      gs <- liftIO $ getGoals sym
      liftIO $ print gs
      liftIO . forM_ gs $ \g ->
        do term <- gGoal sc g
           (mb, stats) <- proveUnintSBV z3 [] Nothing sc term
           putStrLn $ ppStats stats
           case mb of
             Nothing -> printOutLn opts Info "Goal succeeded"
             Just ex -> fail $ "Failure, counterexample: " <> show ex
        `catch` \(X86Error e) -> fail $ "Failure, error: " <> e

      liftIO $ printOutLn opts Info "All goals succeeded"
      pure $ SomeLLVM methodSpec
  | otherwise = fail "LLVM module must be 64-bit"
