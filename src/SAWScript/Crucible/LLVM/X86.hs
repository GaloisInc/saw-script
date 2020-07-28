{- |
Module      : SAWScript.Crucible.LLVM.X86
Description : Implements a SAWScript primitive for verifying x86_64 functions
              against LLVM specifications.
Maintainer  : sbreese
Stability   : provisional
-}

{-# Language OverloadedStrings #-}
{-# Language FlexibleContexts #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeOperators #-}
{-# Language PatternSynonyms #-}
{-# Language LambdaCase #-}
{-# Language MultiWayIf #-}
{-# Language TupleSections #-}
{-# Language ImplicitParams #-}
{-# Language TypeApplications #-}
{-# Language GADTs #-}
{-# Language DataKinds #-}
{-# Language ConstraintKinds #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language TemplateHaskell #-}

module SAWScript.Crucible.LLVM.X86
  ( crucible_llvm_verify_x86
  ) where

import Control.Lens.TH (makeLenses)

import System.IO (stdout)
import Control.Exception (throw)
import Control.Lens (view, use, (&), (^.), (.~), (.=))
import Control.Monad.ST (stToIO)
import Control.Monad.State
import Control.Monad.Catch (MonadThrow)

import qualified Data.BitVector.Sized as BV
import Data.Foldable (foldlM)
import Data.IORef
import qualified Data.List.NonEmpty as NE
import qualified Data.Vector as Vector
import qualified Data.Text as Text
import Data.Text.Encoding (encodeUtf8)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe

import qualified Text.LLVM.AST as LLVM

import Data.Parameterized.Some
import Data.Parameterized.NatRepr
import Data.Parameterized.Context hiding (view)
import Data.Parameterized.Nonce

import Verifier.SAW.FiniteValue
import Verifier.SAW.Recognizer
import Verifier.SAW.Term.Functor
import Verifier.SAW.TypedTerm

import SAWScript.Proof
import SAWScript.Prover.SolverStats
import SAWScript.TopLevel
import SAWScript.Value
import SAWScript.Options
import SAWScript.X86 hiding (Options)
import SAWScript.X86Spec

import qualified SAWScript.Crucible.Common.MethodSpec as MS
import qualified SAWScript.Crucible.Common.Override as O
import qualified SAWScript.Crucible.Common.Setup.Type as Setup

import SAWScript.Crucible.LLVM.Builtins
import SAWScript.Crucible.LLVM.MethodSpecIR
import SAWScript.Crucible.LLVM.ResolveSetupValue
import qualified SAWScript.Crucible.LLVM.Override as LO

import qualified What4.Expr as W4
import qualified What4.FunctionName as W4
import qualified What4.Interface as W4
import qualified What4.LabeledPred as W4
import qualified What4.ProgramLoc as W4

import qualified Lang.Crucible.Analysis.Postdom as C
import qualified Lang.Crucible.Backend as C
import qualified Lang.Crucible.Backend.SAWCore as C
import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.FunctionHandle as C
import qualified Lang.Crucible.Simulator.EvalStmt as C
import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.GlobalState as C
import qualified Lang.Crucible.Simulator.Operations as C
import qualified Lang.Crucible.Simulator.OverrideSim as C
import qualified Lang.Crucible.Simulator.RegMap as C
import qualified Lang.Crucible.Simulator.SimError as C

import qualified Lang.Crucible.LLVM.DataLayout as C.LLVM
import qualified Lang.Crucible.LLVM.Extension as C.LLVM
import qualified Lang.Crucible.LLVM.Intrinsics as C.LLVM
import qualified Lang.Crucible.LLVM.MemModel as C.LLVM
import qualified Lang.Crucible.LLVM.MemType as C.LLVM
import qualified Lang.Crucible.LLVM.Translation as C.LLVM
import qualified Lang.Crucible.LLVM.TypeContext as C.LLVM

import qualified Data.Macaw.Types as Macaw
import qualified Data.Macaw.Discovery as Macaw
import qualified Data.Macaw.Memory as Macaw
import qualified Data.Macaw.Symbolic as Macaw
import qualified Data.Macaw.Symbolic.Backend as Macaw
import qualified Data.Macaw.X86.Symbolic as Macaw
import qualified Data.Macaw.X86 as Macaw
import qualified Data.Macaw.X86.X86Reg as Macaw

import qualified Data.ElfEdit as Elf

-------------------------------------------------------------------------------
-- ** Utility type synonyms and functions

type LLVMArch = C.LLVM.X86 64
type LLVM = C.LLVM.LLVM LLVMArch
type LLVMOverrideMatcher = O.OverrideMatcher LLVM
type Regs = Assignment (C.RegValue' Sym) (Macaw.MacawCrucibleRegTypes Macaw.X86_64)
type Register = Macaw.X86Reg (Macaw.BVType 64)
type Mem = C.LLVM.MemImpl Sym
type Ptr = C.LLVM.LLVMPtr Sym 64
type X86Constraints =
  ( C.LLVM.HasPtrWidth (C.LLVM.ArchWidth LLVMArch)
  , C.LLVM.HasLLVMAnn Sym
  , ?lc :: C.LLVM.TypeContext
  )

newtype X86Sim a = X86Sim { unX86Sim :: StateT X86State IO a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadState X86State, MonadThrow)

data X86State = X86State
  { _x86Sym :: Sym
  , _x86Options :: Options
  , _x86SharedContext :: SharedContext
  , _x86CrucibleContext :: LLVMCrucibleContext LLVMArch
  , _x86Elf :: Elf.Elf 64
  , _x86RelevantElf :: RelevantElf
  , _x86MethodSpec :: MS.CrucibleMethodSpecIR LLVM
  , _x86Mem :: Mem
  , _x86Regs :: Regs
  , _x86GlobalBase :: Ptr
  }
makeLenses ''X86State

runX86Sim :: X86State -> X86Sim a -> IO (a, X86State)
runX86Sim st m = runStateT (unX86Sim m) st

throwX86 :: MonadThrow m => String -> m a
throwX86 = throw . X86Error

setReg ::
  (MonadIO m, MonadThrow m) =>
  Register ->
  C.RegValue Sym (C.LLVM.LLVMPointerType 64) ->
  Regs ->
  m Regs
setReg reg val regs
  | Just regs' <- Macaw.updateX86Reg reg (C.RV . const val) regs = pure regs'
  | otherwise = throwX86 $ mconcat ["Invalid register: ", show reg]

getReg ::
  (MonadIO m, MonadThrow m) =>
  Register ->
  Regs ->
  m (C.RegValue Sym (C.LLVM.LLVMPointerType 64))
getReg reg regs = case Macaw.lookupX86Reg reg regs of
  Just (C.RV val) -> pure val
  Nothing -> throwX86 $ mconcat ["Invalid register: ", show reg]

-------------------------------------------------------------------------------
-- ** Entrypoint

-- | Verify that an x86_64 function (following the System V AMD64 ABI) conforms
-- to an LLVM specification. This allows for compositional verification of LLVM
-- functions that call x86_64 functions (but not the other way around).
crucible_llvm_verify_x86 ::
  BuiltinContext ->
  Options ->
  Some LLVMModule {- ^ Module to associate with method spec -} ->
  FilePath {- ^ Path to ELF file -} ->
  String {- ^ Function's symbol in ELF file -} ->
  [(String, Integer)] {- ^ Global variable symbol names and sizes (in bytes) -} ->
  Bool {-^ Whether to enable path satisfiability checking (currently ignored) -} ->
  LLVMCrucibleSetupM () {- ^ Specification to verify against -} ->
  ProofScript SatResult {- ^ Tactic used to use when discharging goals -} ->
  TopLevel (SomeLLVM MS.CrucibleMethodSpecIR)
crucible_llvm_verify_x86 bic opts (Some (llvmModule :: LLVMModule x)) path nm globsyms _checkSat setup tactic
  | Just Refl <- testEquality (C.LLVM.X86Repr $ knownNat @64) . C.LLVM.llvmArch
                 $ modTrans llvmModule ^. C.LLVM.transContext = do
      let ?ptrWidth = knownNat @64
      let sc = biSharedContext bic
      bbMapRef <- liftIO $ newIORef mempty
      let ?badBehaviorMap = bbMapRef
      sym <- liftIO $ C.newSAWCoreBackend W4.FloatRealRepr sc globalNonceGenerator
      halloc <- getHandleAlloc
      let mvar = C.LLVM.llvmMemVar . view C.LLVM.transContext $ modTrans llvmModule
      sfs <- liftIO $ Macaw.newSymFuns sym

      (C.SomeCFG cfg, elf, relf, addr) <- liftIO $ buildCFG opts halloc path nm
      addrInt <- if Macaw.segmentBase (Macaw.segoffSegment addr) == 0
        then pure . toInteger $ Macaw.segmentOffset (Macaw.segoffSegment addr) + Macaw.segoffOffset addr
        else fail $ mconcat ["Address of \"", nm, "\" is not an absolute address"]
      let maxAddr = addrInt + toInteger (Macaw.segmentSize $ Macaw.segoffSegment addr)

      let
        cc :: LLVMCrucibleContext x
        cc = LLVMCrucibleContext
          { _ccLLVMModule = llvmModule
          , _ccBackend = sym
          , _ccBasicSS = biBasicSS bic

          -- It's unpleasant that we need to do this to use resolveSetupVal.
          , _ccLLVMSimContext = error "Attempted to access ccLLVMSimContext"
          , _ccLLVMGlobals = error "Attempted to access ccLLVMGlobals"
          }

      liftIO . printOutLn opts Info $ mconcat
        [ "Simulating function \""
        , nm
        , "\" (at address "
        , show addr
        , ")"
        ]

      liftIO $ printOutLn opts Info "Examining specification to determine preconditions"
      methodSpec <- buildMethodSpec bic opts llvmModule nm (show addr) setup

      let ?lc = modTrans llvmModule ^. C.LLVM.transContext . C.LLVM.llvmTypeCtx

      emptyState <- liftIO $ initialState sym opts sc cc elf relf methodSpec globsyms maxAddr
      (env, preState) <- liftIO . runX86Sim emptyState $ setupMemory globsyms

      let
        funcLookup = Macaw.LookupFunctionHandle $ \_ _ _ ->
          fail "Attempted to call a function during x86 verification"
        noExtraValidityPred _ _ _ _ = return Nothing
        ctx :: C.SimContext (Macaw.MacawSimulatorState Sym) Sym (Macaw.MacawExt Macaw.X86_64)
        ctx = C.SimContext
              { C._ctxSymInterface = sym
              , C.ctxSolverProof = id
              , C.ctxIntrinsicTypes = C.LLVM.llvmIntrinsicTypes
              , C.simHandleAllocator = halloc
              , C.printHandle = stdout
              , C.extensionImpl =
                Macaw.macawExtensions (Macaw.x86_64MacawEvalFn sfs) mvar
                (mkGlobalMap . Map.singleton 0 $ preState ^. x86GlobalBase)
                funcLookup noExtraValidityPred
              , C._functionBindings = C.insertHandleMap (C.cfgHandle cfg) (C.UseCFG cfg $ C.postdomInfo cfg) C.emptyHandleMap
              , C._cruciblePersonality = Macaw.MacawSimulatorState
              , C._profilingMetrics = Map.empty
              }
        globals = C.insertGlobal mvar (preState ^. x86Mem) C.emptyGlobals
        macawStructRepr = C.StructRepr $ Macaw.crucArchRegTypes Macaw.x86_64MacawSymbolicFns
        initial = C.InitialState ctx globals C.defaultAbortHandler macawStructRepr
                  $ C.runOverrideSim macawStructRepr
                  $ Macaw.crucGenArchConstraints Macaw.x86_64MacawSymbolicFns
                  $ do
          r <- C.callCFG cfg . C.RegMap . singleton . C.RegEntry macawStructRepr $ preState ^. x86Regs
          globals' <- C.readGlobals
          mem' <- C.readGlobal mvar
          let finalState = preState
                { _x86Mem = mem'
                , _x86Regs = C.regValue r
                , _x86CrucibleContext = cc & ccLLVMGlobals .~ globals'
                }
          liftIO $ printOutLn opts Info
            "Examining specification to determine postconditions"
          liftIO . void . runX86Sim finalState $ assertPost globals' env (preState ^. x86Mem) (preState ^. x86Regs)
          pure $ C.regValue r

      liftIO $ printOutLn opts Info "Simulating function"
      liftIO $ C.executeCrucible [] initial >>= \case
        C.FinishedResult{} -> pure ()
        C.AbortedResult{} -> printOutLn opts Warn "Warning: function never returns"
        C.TimeoutResult{} -> fail "Execution timed out"

      checkGoals sym opts sc tactic
 
      pure $ SomeLLVM methodSpec
  | otherwise = fail "LLVM module must be 64-bit"

--------------------------------------------------------------------------------
-- ** Computing the CFG

-- | Load the given ELF file and use Macaw to construct a Crucible CFG.
buildCFG ::
  Options ->
  C.HandleAllocator ->
  String {- ^ Path to ELF file -} ->
  String {- ^ Function's symbol in ELF file -} ->
  IO ( C.SomeCFG
       (Macaw.MacawExt Macaw.X86_64)
       (EmptyCtx ::> Macaw.ArchRegStruct Macaw.X86_64)
       (Macaw.ArchRegStruct Macaw.X86_64)
     , Elf.Elf 64
     , RelevantElf
     , Macaw.MemSegmentOff 64
     )
buildCFG opts halloc path nm = do
  printOutLn opts Info $ mconcat ["Finding symbol for \"", nm, "\""]
  elf <- getElf path
  relf <- getRelevant elf
  (addr :: Macaw.MemSegmentOff 64) <-
    case findSymbols (symMap relf) . encodeUtf8 $ Text.pack nm of
      (addr:_) -> pure addr
      _ -> fail $ mconcat ["Could not find symbol \"", nm, "\""]
  printOutLn opts Info $ mconcat ["Found symbol at address ", show addr, ", building CFG"]
  let
    initialDiscoveryState =
      Macaw.emptyDiscoveryState (memory relf) (funSymMap relf) Macaw.x86_64_linux_info
      & Macaw.trustedFunctionEntryPoints .~ Set.empty
  (_fstate, Some finfo) <-
    stToIO $ Macaw.analyzeFunction (const $ pure ()) addr Macaw.UserRequest initialDiscoveryState
  scfg <- Macaw.mkFunCFG Macaw.x86_64MacawSymbolicFns halloc
    (W4.functionNameFromText $ Text.pack nm) posFn finfo
  pure (scfg, elf, relf, addr)

--------------------------------------------------------------------------------
-- ** Computing the specification

-- | Construct the method spec like we normally would in crucible_llvm_verify.
-- Unlike in crucible_llvm_verify, we can't reuse the simulator state (due to the
-- different memory layout / RegMap).
buildMethodSpec ::
  BuiltinContext ->
  Options ->
  LLVMModule LLVMArch ->
  String {- ^ Name of method -} ->
  String {- ^ Source location for method spec (here, we use the address) -} ->
  LLVMCrucibleSetupM () ->
  TopLevel (MS.CrucibleMethodSpecIR LLVM)
buildMethodSpec bic opts lm nm loc setup =
  setupLLVMCrucibleContext bic opts lm $ \cc -> do
    let methodId = LLVMMethodId nm Nothing
    let programLoc =
          W4.mkProgramLoc (W4.functionNameFromText $ Text.pack nm)
          . W4.OtherPos $ Text.pack loc
    let lc = modTrans lm ^. C.LLVM.transContext . C.LLVM.llvmTypeCtx
    (args, ret) <- case llvmSignature opts lm nm of
      Left err -> fail $ mconcat ["Could not find declaration for \"", nm, "\": ", err]
      Right x -> pure x
    (mtargs, mtret) <- case (,) <$> mapM (llvmTypeToMemType lc) args <*> mapM (llvmTypeToMemType lc) ret of
      Left err -> fail err
      Right x -> pure x
    let initialMethodSpec = MS.makeCrucibleMethodSpecIR @(C.LLVM.LLVM (C.LLVM.X86 64))
          methodId mtargs mtret programLoc lm
    view Setup.csMethodSpec <$> execStateT (runLLVMCrucibleSetupM setup)
      (Setup.makeCrucibleSetupState cc initialMethodSpec)

llvmTypeToMemType ::
  C.LLVM.TypeContext ->
  LLVM.Type ->
  Either String C.LLVM.MemType
llvmTypeToMemType lc t = let ?lc = lc in C.LLVM.liftMemType t

-- | Find a function declaration in the LLVM AST and return its signature.
llvmSignature ::
  Options ->
  LLVMModule LLVMArch ->
  String ->
  Either String ([LLVM.Type], Maybe LLVM.Type)
llvmSignature opts llvmModule nm =
  case findDecl (modAST llvmModule) nm of
    Left err -> case findDefMaybeStatic (modAST llvmModule) nm of
      Left _ -> Left $ displayVerifExceptionOpts opts err
      Right defs -> pure
        ( LLVM.typedType <$> LLVM.defArgs (NE.head defs)
        , case LLVM.defRetType $ NE.head defs of
            LLVM.PrimType LLVM.Void -> Nothing
            x -> Just x
        )
    Right decl -> pure
      ( LLVM.decArgs decl
      , case LLVM.decRetType decl of
          LLVM.PrimType LLVM.Void -> Nothing
          x -> Just x
      )

--------------------------------------------------------------------------------
-- ** Building the initial state

initialState ::
  X86Constraints =>
  Sym ->
  Options ->
  SharedContext ->
  LLVMCrucibleContext LLVMArch ->
  Elf.Elf 64 ->
  RelevantElf ->
  MS.CrucibleMethodSpecIR LLVM ->
  [(String, Integer)] {- ^ Global variable symbol names and sizes (in bytes) -} ->
  Integer {- ^ Minimum size of the global allocation (here, the end of the .text segment -} ->
  IO X86State
initialState sym opts sc cc elf relf ms globs maxAddr = do
  emptyMem <- C.LLVM.emptyMem C.LLVM.LittleEndian
  emptyRegs <- traverseWithIndex (freshRegister sym) C.knownRepr
  let
    align = C.LLVM.exponentToAlignment 4
    allocGlobalEnd :: MS.AllocGlobal LLVM -> Integer
    allocGlobalEnd (LLVMAllocGlobal _ (LLVM.Symbol nm)) = globalEnd nm
    globalEnd :: String -> Integer
    globalEnd nm = maybe 0 (\entry -> fromIntegral $ Elf.steValue entry + Elf.steSize entry) $
      (Vector.!? 0)
      . Vector.filter (\e -> Elf.steName e == encodeUtf8 (Text.pack nm))
      . mconcat
      . fmap Elf.elfSymbolTableEntries
      $ Elf.elfSymtab elf
  sz <- W4.bvLit sym knownNat . BV.mkBV knownNat . maximum $ mconcat
    [ [maxAddr, globalEnd "_end"]
    , globalEnd . fst <$> globs
    , allocGlobalEnd <$> ms ^. MS.csGlobalAllocs
    ]
  (base, mem) <- C.LLVM.doMalloc sym C.LLVM.GlobalAlloc C.LLVM.Immutable
    "globals" emptyMem sz align
  pure $ X86State
    { _x86Sym = sym
    , _x86Options = opts
    , _x86SharedContext = sc
    , _x86CrucibleContext = cc
    , _x86Elf = elf
    , _x86RelevantElf = relf
    , _x86MethodSpec = ms
    , _x86Mem = mem
    , _x86Regs = emptyRegs
    , _x86GlobalBase = base
    }

--------------------------------------------------------------------------------
-- ** Precondition

-- | Given the method spec, build the initial memory, register map, and global map.
setupMemory ::
  X86Constraints =>
  [(String, Integer)] {- ^ Global variable symbol names and sizes (in bytes) -} ->
  X86Sim (Map MS.AllocIndex Ptr)
setupMemory globsyms = do
  setupGlobals globsyms

  -- Allocate a reasonable amount of stack (4 KiB + 1 qword for IP)
  allocateStack 4096

  ms <- use x86MethodSpec

  let
    tyenv = ms ^. MS.csPreState . MS.csAllocs
    nameEnv = MS.csTypeNames ms

  env <- foldlM assumeAllocation Map.empty . Map.assocs $ tyenv

  mapM_ (assumePointsTo env tyenv nameEnv) $ ms ^. MS.csPreState . MS.csPointsTos

  setArgs env tyenv nameEnv . fmap snd . Map.elems $ ms ^. MS.csArgBindings

  pure env

-- | Given an alist of symbol names and sizes (in bytes), allocate space and copy
-- the corresponding globals from the Macaw memory to the Crucible LLVM memory model.
setupGlobals ::
  X86Constraints =>
  [(String, Integer)] {- ^ Global variable symbol names and sizes (in bytes) -} ->
  X86Sim ()
setupGlobals globsyms = do
  sym <- use x86Sym
  mem <- use x86Mem
  relf <- use x86RelevantElf
  base <- use x86GlobalBase
  let
    readInitialGlobal :: (String, Integer) -> IO [(String, Integer, [Integer])]
    readInitialGlobal (nm, sz) = do
      res <- loadGlobal relf (encodeUtf8 $ Text.pack nm, sz, Bytes)
      pure $ (\(name, addr, _unit, bytes) -> (name, addr, bytes)) <$> res
    convertByte :: Integer -> IO (C.LLVM.LLVMVal Sym)
    convertByte byte =
      C.LLVM.LLVMValInt <$> W4.natLit sym 0 <*> W4.bvLit sym (knownNat @8) (BV.mkBV knownNat byte)
    writeGlobal :: Mem -> (String, Integer, [Integer]) -> IO Mem
    writeGlobal m (_nm, addr, bytes) = do
      ptr <- C.LLVM.doPtrAddOffset sym m base =<< W4.bvLit sym knownNat (BV.mkBV knownNat addr)
      v <- Vector.fromList <$> mapM convertByte bytes
      let st = C.LLVM.arrayType (fromIntegral $ length bytes) $ C.LLVM.bitvectorType 1
      C.LLVM.storeConstRaw sym m ptr st C.LLVM.noAlignment
        $ C.LLVM.LLVMValArray (C.LLVM.bitvectorType 1) v
  globs <- liftIO $ mconcat <$> mapM readInitialGlobal globsyms
  mem' <- liftIO $ foldlM writeGlobal mem globs
  x86Mem .= mem'

-- | Allocate memory for the stack, and pushes a fresh pointer as the return
-- address.
allocateStack ::
  X86Constraints =>
  Integer {- ^ Stack size in bytes -} ->
  X86Sim ()
allocateStack szInt = do
  sym <- use x86Sym
  mem <- use x86Mem
  regs <- use x86Regs
  let align = C.LLVM.exponentToAlignment 4
  sz <- liftIO $ W4.bvLit sym knownNat $ BV.mkBV knownNat $ szInt + 8
  (base, mem') <- liftIO $ C.LLVM.doMalloc sym C.LLVM.HeapAlloc C.LLVM.Mutable
    "stack_alloc" mem sz align
  sn <- case W4.userSymbol "stack" of
    Left err -> throwX86 $ "Invalid symbol for stack: " <> show err
    Right sn -> pure sn
  fresh <- liftIO $ C.LLVM.LLVMPointer
    <$> W4.natLit sym 0
    <*> W4.freshConstant sym sn (W4.BaseBVRepr $ knownNat @64)
  ptr <- liftIO $ C.LLVM.doPtrAddOffset sym mem' base =<< W4.bvLit sym knownNat (BV.mkBV knownNat szInt)
  finalMem <- liftIO $ C.LLVM.doStore sym mem' ptr
    (C.LLVM.LLVMPointerRepr $ knownNat @64)
    (C.LLVM.bitvectorType 8) align fresh
  x86Mem .= finalMem
  finalRegs <- setReg Macaw.RSP ptr regs
  x86Regs .= finalRegs

-- | Process a crucible_alloc statement, allocating the requested memory and
-- associating a pointer to that memory with the appropriate index.
assumeAllocation ::
  X86Constraints =>
  Map MS.AllocIndex Ptr ->
  (MS.AllocIndex, LLVMAllocSpec) {- ^ crucible_alloc statement -} ->
  X86Sim (Map MS.AllocIndex Ptr)
assumeAllocation env (i, LLVMAllocSpec mut _memTy align sz loc) = do
  cc <- use x86CrucibleContext
  sym <- use x86Sym
  mem <- use x86Mem
  sz' <- liftIO $ resolveSAWSymBV cc knownNat sz
  (ptr, mem') <- liftIO $ C.LLVM.doMalloc sym C.LLVM.HeapAlloc mut
    (show $ W4.plSourceLoc loc) mem sz' align
  x86Mem .= mem'
  pure $ Map.insert i ptr env

-- | Process a crucible_points_to statement, writing some SetupValue to a pointer.
assumePointsTo ::
  X86Constraints =>
  Map MS.AllocIndex Ptr {- ^ Associates each AllocIndex with the corresponding allocation -} ->
  Map MS.AllocIndex LLVMAllocSpec {- ^ Associates each AllocIndex with its specification -} ->
  Map MS.AllocIndex C.LLVM.Ident {- ^ Associates each AllocIndex with its name -} ->
  LLVMPointsTo LLVMArch {- ^ crucible_points_to statement from the precondition -} ->
  X86Sim ()
assumePointsTo env tyenv nameEnv (LLVMPointsTo _ cond tptr tptval) = do
  when (isJust cond) $ throwX86 "unsupported x86_64 command: crucible_conditional_points_to"
  tval <- checkConcreteSizePointsToValue tptval
  sym <- use x86Sym
  cc <- use x86CrucibleContext
  mem <- use x86Mem
  ptr <- resolvePtrSetupValue env tyenv tptr
  val <- liftIO $ resolveSetupVal cc mem env tyenv Map.empty tval
  storTy <- liftIO $ C.LLVM.toStorableType =<< typeOfSetupValue cc tyenv nameEnv tval
  mem' <- liftIO $ C.LLVM.storeConstRaw sym mem ptr storTy C.LLVM.noAlignment val
  x86Mem .= mem'

resolvePtrSetupValue ::
  X86Constraints =>
  Map MS.AllocIndex Ptr ->
  Map MS.AllocIndex LLVMAllocSpec ->
  MS.SetupValue LLVM ->
  X86Sim Ptr
resolvePtrSetupValue env tyenv tptr = do
  sym <- use x86Sym
  cc <- use x86CrucibleContext
  mem <- use x86Mem
  elf <- use x86Elf
  base <- use x86GlobalBase
  case tptr of
    MS.SetupGlobal () nm -> case
      (Vector.!? 0)
      . Vector.filter (\e -> Elf.steName e == encodeUtf8 (Text.pack nm))
      . mconcat
      . fmap Elf.elfSymbolTableEntries
      $ Elf.elfSymtab elf of
      Nothing -> throwX86 $ mconcat ["Global symbol \"", nm, "\" not found"]
      Just entry -> do
        let addr = fromIntegral $ Elf.steValue entry
        liftIO $ C.LLVM.doPtrAddOffset sym mem base =<< W4.bvLit sym knownNat (BV.mkBV knownNat addr)
    _ -> liftIO $ C.LLVM.unpackMemValue sym (C.LLVM.LLVMPointerRepr $ knownNat @64)
         =<< resolveSetupVal cc mem env tyenv Map.empty tptr

checkConcreteSizePointsToValue :: LLVMPointsToValue LLVMArch -> X86Sim (MS.SetupValue LLVM)
checkConcreteSizePointsToValue = \case
  ConcreteSizeValue val -> return val
  SymbolicSizeValue{} -> throwX86 "unsupported x86_64 command: crucible_points_to_array_prefix"

-- | Write each SetupValue passed to crucible_execute_func to the appropriate
-- x86_64 register from the calling convention.
setArgs ::
  X86Constraints =>
  Map MS.AllocIndex Ptr {- ^ Associates each AllocIndex with the corresponding allocation -} ->
  Map MS.AllocIndex LLVMAllocSpec {- ^ Associates each AllocIndex with its specification -} ->
  Map MS.AllocIndex C.LLVM.Ident {- ^ Associates each AllocIndex with its name -} ->
  [MS.SetupValue LLVM] {- ^ Arguments passed to crucible_execute_func -} ->
  X86Sim ()
setArgs env tyenv nameEnv args
  | length args > length argRegs = throwX86 "More arguments than would fit into general-purpose registers"
  | otherwise = do
      sym <- use x86Sym
      cc <- use x86CrucibleContext
      mem <- use x86Mem
      let
        setRegSetupValue rs (reg, sval) = typeOfSetupValue cc tyenv nameEnv sval >>= \ty ->
          case ty of
            C.LLVM.PtrType _ -> do
              val <- C.LLVM.unpackMemValue sym (C.LLVM.LLVMPointerRepr $ knownNat @64)
                =<< resolveSetupVal cc mem env tyenv nameEnv sval
              setReg reg val rs
            C.LLVM.IntType 64 -> do
              val <- C.LLVM.unpackMemValue sym (C.LLVM.LLVMPointerRepr $ knownNat @64)
                =<< resolveSetupVal cc mem env tyenv nameEnv sval
              setReg reg val rs
            C.LLVM.IntType _ -> do
              C.LLVM.LLVMValInt base off <- resolveSetupVal cc mem env tyenv nameEnv sval
              case testLeq (incNat $ W4.bvWidth off) (knownNat @64) of
                Nothing -> fail "Argument bitvector does not fit in a single general-purpose register"
                Just LeqProof -> do
                  off' <- W4.bvZext sym (knownNat @64) off
                  val <- C.LLVM.unpackMemValue sym (C.LLVM.LLVMPointerRepr $ knownNat @64)
                    $ C.LLVM.LLVMValInt base off'
                  setReg reg val rs
            _ -> fail "Argument does not fit into a single general-purpose register"
      regs <- use x86Regs
      newRegs <- liftIO . foldlM setRegSetupValue regs $ zip argRegs args
      x86Regs .= newRegs
  where argRegs = [Macaw.RDI, Macaw.RSI, Macaw.RDX, Macaw.RCX, Macaw.R8, Macaw.R9]

--------------------------------------------------------------------------------
-- ** Postcondition

-- | Assert the postcondition for the spec, given the final memory and register map.
assertPost ::
  X86Constraints =>
  C.SymGlobalState Sym ->
  Map MS.AllocIndex Ptr ->
  Mem {- ^ The state of memory before simulation -} ->
  Regs {- ^ The state of the registers before simulation -} ->
  X86Sim ()
assertPost globals env premem preregs = do
  sym <- use x86Sym
  opts <- use x86Options
  sc <- use x86SharedContext
  cc <- use x86CrucibleContext
  ms <- use x86MethodSpec
  postregs <- use x86Regs
  let
    tyenv = ms ^. MS.csPreState . MS.csAllocs
    nameEnv = MS.csTypeNames ms

  prersp <- getReg Macaw.RSP preregs
  expectedIP <- liftIO $ C.LLVM.doLoad sym premem prersp (C.LLVM.bitvectorType 8)
    (C.LLVM.LLVMPointerRepr $ knownNat @64) C.LLVM.noAlignment
  actualIP <- getReg Macaw.X86_IP postregs
  correctRetAddr <- liftIO $ C.LLVM.ptrEq sym C.LLVM.PtrWidth actualIP expectedIP
  liftIO . C.addAssertion sym . C.LabeledPred correctRetAddr . C.SimError W4.initializationLoc
    $ C.AssertFailureSimError "Instruction pointer not set to return address" ""

  stack <- liftIO $ C.LLVM.doPtrAddOffset sym premem prersp =<< W4.bvLit sym knownNat (BV.mkBV knownNat 8)
  postrsp <- getReg Macaw.RSP postregs
  correctStack <- liftIO $ C.LLVM.ptrEq sym C.LLVM.PtrWidth stack postrsp
  liftIO $ C.addAssertion sym . C.LabeledPred correctStack . C.SimError W4.initializationLoc
    $ C.AssertFailureSimError "Stack not preserved" ""

  returnMatches <- case (ms ^. MS.csRetValue, ms ^. MS.csRet) of
    (Just expectedRet, Just retTy) -> do
      postRAX <- C.LLVM.ptrToPtrVal <$> getReg Macaw.RAX postregs
      pure [LO.matchArg opts sc cc ms MS.PostState postRAX retTy expectedRet]
    _ -> pure []

  pointsToMatches <- forM (ms ^. MS.csPostState . MS.csPointsTos)
    $ assertPointsTo env tyenv nameEnv

  let setupConditionMatches = fmap
        (LO.learnSetupCondition opts sc cc ms MS.PostState)
        $ ms ^. MS.csPostState . MS.csConditions

  let
    initialTerms = Map.fromList
      [ (ecVarIndex ec, ttTerm tt)
      | tt <- ms ^. MS.csPreState . MS.csFreshVars
      , let Just ec = asExtCns (ttTerm tt)
      ]
    initialFree = Set.fromList . fmap (LO.termId . ttTerm) $ ms ^. MS.csPostState . MS.csFreshVars

  result <- liftIO
    . O.runOverrideMatcher sym globals env initialTerms initialFree (ms ^. MS.csLoc)
    . sequence_ $ mconcat
    [ returnMatches
    , pointsToMatches
    , setupConditionMatches
    ]
  st <- case result of
    Left err -> throwX86 $ show err
    Right (_, st) -> pure st
  liftIO . forM_ (view LO.osAsserts st) $ \(W4.LabeledPred p r) ->
    C.addAssertion sym $ C.LabeledPred p r

-- | Assert that a points-to postcondition holds.
assertPointsTo ::
  X86Constraints =>
  Map MS.AllocIndex Ptr {- ^ Associates each AllocIndex with the corresponding allocation -} ->
  Map MS.AllocIndex LLVMAllocSpec {- ^ Associates each AllocIndex with its specification -} ->
  Map MS.AllocIndex C.LLVM.Ident {- ^ Associates each AllocIndex with its name -} ->
  LLVMPointsTo LLVMArch {- ^ crucible_points_to statement from the precondition -} ->
  X86Sim (LLVMOverrideMatcher md ())
assertPointsTo env tyenv nameEnv (LLVMPointsTo _ cond tptr tptexpected) = do
  when (isJust cond) $ throwX86 "unsupported x86_64 command: crucible_conditional_points_to"
  texpected <- checkConcreteSizePointsToValue tptexpected
  sym <- use x86Sym
  opts <- use x86Options
  sc <- use x86SharedContext
  cc <- use x86CrucibleContext
  ms <- use x86MethodSpec
  mem <- use x86Mem
  ptr <- resolvePtrSetupValue env tyenv tptr
  memTy <- liftIO $ typeOfSetupValue cc tyenv nameEnv texpected
  storTy <- liftIO $ C.LLVM.toStorableType memTy
  actual <- liftIO $ C.LLVM.assertSafe sym =<< C.LLVM.loadRaw sym mem ptr storTy C.LLVM.noAlignment
  pure $ LO.matchArg opts sc cc ms MS.PostState actual memTy texpected

-- | Gather and run the solver on goals from the simulator.
checkGoals ::
  Sym ->
  Options ->
  SharedContext ->
  ProofScript SatResult ->
  TopLevel ()
checkGoals sym opts sc tactic = do
  gs <- liftIO $ getGoals sym
  liftIO . printOutLn opts Info $ mconcat
    [ "Simulation finished, running solver on "
    , show $ length gs
    , " goals"
    ]
  forM_ (zip [0..] gs) $ \(n, g) -> do
    term <- liftIO $ gGoal sc g
    let proofgoal = ProofGoal n "vc" (show $ gMessage g) term
    r <- evalStateT tactic $ startProof proofgoal
    case r of
      Unsat stats -> do
        liftIO . printOutLn opts Info $ ppStats stats
      SatMulti stats vals -> do
        printOutLnTop Info $ unwords ["Subgoal failed:", show $ gMessage g]
        printOutLnTop Info (show stats)
        printOutLnTop OnlyCounterExamples "----------Counterexample----------"
        ppOpts <- sawPPOpts . rwPPOpts <$> getTopLevelRW
        case vals of
          [] -> printOutLnTop OnlyCounterExamples "<<All settings of the symbolic variables constitute a counterexample>>"
          _ -> let showAssignment (name, val) =
                     mconcat [ " ", name, ": ", show $ ppFirstOrderValue ppOpts val ]
               in mapM_ (printOutLnTop OnlyCounterExamples . showAssignment) vals
        printOutLnTop OnlyCounterExamples "----------------------------------"
        throwTopLevel "Proof failed."
  liftIO $ printOutLn opts Info "All goals succeeded"
