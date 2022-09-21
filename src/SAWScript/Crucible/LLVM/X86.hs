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
{-# Language RankNTypes #-}
{-# Language ConstraintKinds #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language TemplateHaskell #-}
{-# Language ViewPatterns #-}

module SAWScript.Crucible.LLVM.X86
  ( llvm_verify_x86
  , llvm_verify_fixpoint_x86
  , llvm_verify_x86_with_invariant
  , defaultStackBaseAlign
  ) where

import Control.Lens.TH (makeLenses)

import System.IO (stdout)
import Control.Exception (throw)
import Control.Lens (Getter, to, view, use, (&), (^.), (.~), (%~), (.=))
import Control.Monad.State
import Control.Monad.Reader (runReaderT)
import Control.Monad.Catch (MonadThrow)

import qualified Data.BitVector.Sized as BV
import Data.Foldable (foldlM)
import           Data.IORef
import qualified Data.List.NonEmpty as NE
import qualified Data.Vector as Vector
import qualified Data.Text as Text
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import Data.Text.Encoding (decodeUtf8, encodeUtf8)
import Data.Time.Clock (getCurrentTime, diffUTCTime)
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe

import qualified Text.LLVM.AST as LLVM

import Data.Parameterized.Some
import qualified Data.Parameterized.Map as MapF
import Data.Parameterized.NatRepr
import Data.Parameterized.Nonce (GlobalNonceGenerator)
import Data.Parameterized.Context hiding (view, zipWithM)

import Verifier.SAW.CryptolEnv
import Verifier.SAW.FiniteValue
import Verifier.SAW.Name (toShortName)
import Verifier.SAW.Prelude
import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedTerm
import Verifier.SAW.SCTypeCheck (scTypeCheck)

import Verifier.SAW.Simulator.What4.ReturnTrip

import SAWScript.Proof
import SAWScript.Prover.SolverStats
import SAWScript.TopLevel
import SAWScript.Value
import SAWScript.Options
import SAWScript.X86 hiding (Options)
import SAWScript.X86Spec
import SAWScript.Crucible.Common
import SAWScript.Crucible.Common.Override (MetadataMap)

import qualified SAWScript.Crucible.Common as Common
import qualified SAWScript.Crucible.Common.MethodSpec as MS
import qualified SAWScript.Crucible.Common.Override as O
import qualified SAWScript.Crucible.Common.Setup.Type as Setup
import SAWScript.Crucible.LLVM.Builtins
import SAWScript.Crucible.LLVM.MethodSpecIR hiding (LLVM)
import SAWScript.Crucible.LLVM.ResolveSetupValue
import qualified SAWScript.Crucible.LLVM.Override as LO
import qualified SAWScript.Crucible.LLVM.MethodSpecIR as LMS (LLVM)

import qualified What4.Concrete as W4
import qualified What4.Config as W4
import qualified What4.Expr as W4
import qualified What4.FunctionName as W4
import qualified What4.Interface as W4
import qualified What4.LabeledPred as W4
import qualified What4.ProgramLoc as W4
import qualified What4.Expr.Builder as W4.B

import qualified Lang.Crucible.Analysis.Postdom as C
import qualified Lang.Crucible.Backend as C
import qualified Lang.Crucible.Backend.Online as C
import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.CFG.Extension as C
import qualified Lang.Crucible.FunctionHandle as C
import qualified Lang.Crucible.Simulator.EvalStmt as C
import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.GlobalState as C
import qualified Lang.Crucible.Simulator.Operations as C
import qualified Lang.Crucible.Simulator.OverrideSim as C
import qualified Lang.Crucible.Simulator.RegMap as C
import qualified Lang.Crucible.Simulator.SimError as C
import qualified Lang.Crucible.Simulator.PathSatisfiability as C

import qualified Lang.Crucible.LLVM.Bytes as C.LLVM
import qualified Lang.Crucible.LLVM.DataLayout as C.LLVM
import qualified Lang.Crucible.LLVM.Extension as C.LLVM
import qualified Lang.Crucible.LLVM.Intrinsics as C.LLVM
import qualified Lang.Crucible.LLVM.MemModel as C.LLVM
import qualified Lang.Crucible.LLVM.MemType as C.LLVM
import qualified Lang.Crucible.LLVM.SimpleLoopFixpoint as Crucible.LLVM.Fixpoint
import qualified Lang.Crucible.LLVM.SimpleLoopInvariant as SimpleInvariant
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
type LLVM = LMS.LLVM LLVMArch
type LLVMOverrideMatcher rorw a = O.OverrideMatcher LLVM rorw a
type Regs = Assignment (C.RegValue' Sym) (Macaw.MacawCrucibleRegTypes Macaw.X86_64)
type Register = Macaw.X86Reg (Macaw.BVType 64)
type Mem = C.LLVM.MemImpl Sym
type Ptr = C.LLVM.LLVMPtr Sym 64
type X86Constraints =
  ( C.LLVM.HasPtrWidth (C.LLVM.ArchWidth LLVMArch)
  , C.LLVM.HasLLVMAnn Sym
  , ?memOpts :: C.LLVM.MemOptions
  , ?lc :: C.LLVM.TypeContext
  , ?w4EvalTactic :: W4EvalTactic
  )

newtype X86Sim a = X86Sim { unX86Sim :: StateT X86State IO a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadState X86State, MonadThrow)

data X86State = X86State
  { _x86Backend :: SomeOnlineBackend
  , _x86Options :: Options
  , _x86SharedContext :: SharedContext
  , _x86CrucibleContext :: LLVMCrucibleContext LLVMArch
  , _x86ElfSymtab :: Elf.Symtab 64
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

x86Sym :: Getter X86State Sym
x86Sym = to (\st -> case _x86Backend st of SomeOnlineBackend bak -> backendGetSym bak)

defaultStackBaseAlign :: Integer
defaultStackBaseAlign = 16

integerToAlignment ::
  (MonadIO m, MonadThrow m) =>
  Integer ->
  m C.LLVM.Alignment
integerToAlignment i
  | Just ba <- C.LLVM.toAlignment (C.LLVM.toBytes i) = pure ba
  | otherwise = throwX86 $ mconcat ["Invalid alignment specified: ", show i]

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

-- TODO: extend to more than general purpose registers
stringToReg :: Text -> Maybe (Some Macaw.X86Reg)
stringToReg s = case s of
  "rax" -> Just $ Some Macaw.RAX
  "rbx" -> Just $ Some Macaw.RBX
  "rcx" -> Just $ Some Macaw.RCX
  "rdx" -> Just $ Some Macaw.RDX
  "rsp" -> Just $ Some Macaw.RSP
  "rbp" -> Just $ Some Macaw.RBP
  "rsi" -> Just $ Some Macaw.RSI
  "rdi" -> Just $ Some Macaw.RDI
  "r8" -> Just $ Some Macaw.R8
  "r9" -> Just $ Some Macaw.R9
  "r10" -> Just $ Some Macaw.R10
  "r11" -> Just $ Some Macaw.R11
  "r12" -> Just $ Some Macaw.R12
  "r13" -> Just $ Some Macaw.R13
  "r14" -> Just $ Some Macaw.R14
  "r15" -> Just $ Some Macaw.R15
  _ -> Nothing

cryptolUninterpreted ::
  (MonadIO m, MonadThrow m) =>
  CryptolEnv ->
  String ->
  SharedContext ->
  [Term] ->
  m Term
cryptolUninterpreted env nm sc xs =
  case lookupIn nm $ eTermEnv env of
    Left _err -> throwX86 $ mconcat
      [ "Failed to lookup Cryptol name \"", nm
      , "\" in Cryptol environment"
      ]
    Right t -> liftIO $ scApplyAll sc t xs

llvmPointerBlock :: C.LLVM.LLVMPtr sym w -> W4.SymNat sym
llvmPointerBlock = fst . C.LLVM.llvmPointerView
llvmPointerOffset :: C.LLVM.LLVMPtr sym w -> W4.SymBV sym w
llvmPointerOffset = snd . C.LLVM.llvmPointerView

-- | Compare pointers that are not valid LLVM pointers. Comparing the offsets
-- as unsigned bitvectors is not sound, because of overflow (e.g. `base - 1` is
-- less than `base`, but -1 is not less than 0 when compared as unsigned). It
-- is safe to allow a small negative offset, because each pointer base is
-- mapped to an address that is not in the first page (4K), which is never
-- mapped on X86_64 Linux. Specifically, assume pointer1 = (base1, offset1) and
-- pointer2 = (base2, offset2), and size1 is the size of the allocation of
-- base1 and size2 is the size of the allocation of base2. If offset1 is in the
-- interval [-4096, size1], and offset2 is in the interval [-4096, size2], then
-- the unsigned comparison between pointer1 and pointer2 is equivalent with the
-- unsigned comparison between offset1 + 4096 and offset2 + 4096.
doPtrCmp ::
  (sym -> W4.SymBV sym w -> W4.SymBV sym w -> IO (W4.Pred sym)) ->
  Macaw.PtrOp sym w (C.RegValue sym C.BoolType)
doPtrCmp f = Macaw.ptrOp $ \bak mem w xPtr xBits yPtr yBits x y -> do
  let sym = backendGetSym bak
  let ptr_as_bv_for_cmp ptr = do
        page_size <- W4.bvLit sym (W4.bvWidth $ llvmPointerOffset ptr) $
          BV.mkBV (W4.bvWidth $ llvmPointerOffset ptr) 4096
        ptr_as_bv <- W4.bvAdd sym (llvmPointerOffset ptr) page_size
        is_valid <- Macaw.isValidPtr sym mem w ptr
        is_negative_offset <- W4.bvIsNeg sym (llvmPointerOffset ptr)
        is_not_overflow <- W4.notPred sym =<< W4.bvIsNeg sym ptr_as_bv
        ok <- W4.orPred sym is_valid
          =<< W4.andPred sym is_negative_offset is_not_overflow
        return (ptr_as_bv, ok)
  both_bits <- W4.andPred sym xBits yBits
  both_ptrs <- W4.andPred sym xPtr yPtr
  same_region <- W4.natEq sym (llvmPointerBlock x) (llvmPointerBlock y)
  (x_ptr_as_bv, ok_x) <- ptr_as_bv_for_cmp x
  (y_ptr_as_bv, ok_y) <- ptr_as_bv_for_cmp y
  ok_both_ptrs <- W4.andPred sym both_ptrs
    =<< W4.andPred sym same_region
    =<< W4.andPred sym ok_x ok_y
  res_both_bits <- f sym (llvmPointerOffset x) (llvmPointerOffset y)
  res_both_ptrs <- f sym x_ptr_as_bv y_ptr_as_bv
  undef <- Macaw.mkUndefinedBool sym "ptr_cmp"
  W4.itePred sym both_bits res_both_bits
    =<< W4.itePred sym ok_both_ptrs res_both_ptrs undef

-------------------------------------------------------------------------------
-- ** Entrypoint

-- | Verify that an x86_64 function (following the System V AMD64 ABI) conforms
-- to an LLVM specification. This allows for compositional verification of LLVM
-- functions that call x86_64 functions (but not the other way around).
llvm_verify_x86 ::
  Some LLVMModule {- ^ Module to associate with method spec -} ->
  FilePath {- ^ Path to ELF file -} ->
  String {- ^ Function's symbol in ELF file -} ->
  [(String, Integer)] {- ^ Global variable symbol names and sizes (in bytes) -} ->
  Bool {- ^ Whether to enable path satisfiability checking -} ->
  LLVMCrucibleSetupM () {- ^ Specification to verify against -} ->
  ProofScript () {- ^ Tactic used to use when discharging goals -} ->
  TopLevel (SomeLLVM MS.ProvedSpec)
llvm_verify_x86 llvmModule path nm globsyms checkSat =
  llvm_verify_x86_common llvmModule path nm globsyms checkSat NoFixpoint

-- | Verify that an x86_64 function (following the System V AMD64 ABI) conforms
-- to an LLVM specification. This allows for compositional verification of LLVM
-- functions that call x86_64 functions (but not the other way around).
llvm_verify_fixpoint_x86 ::
  Some LLVMModule {- ^ Module to associate with method spec -} ->
  FilePath {- ^ Path to ELF file -} ->
  String {- ^ Function's symbol in ELF file -} ->
  [(String, Integer)] {- ^ Global variable symbol names and sizes (in bytes) -} ->
  Bool {- ^ Whether to enable path satisfiability checking -} ->
  TypedTerm {- ^ Function specifying the loop -} ->
  LLVMCrucibleSetupM () {- ^ Specification to verify against -} ->
  ProofScript () {- ^ Tactic used to use when discharging goals -} ->
  TopLevel (SomeLLVM MS.ProvedSpec)
llvm_verify_fixpoint_x86 llvmModule path nm globsyms checkSat f =
  llvm_verify_x86_common llvmModule path nm globsyms checkSat (SimpleFixpoint f)

-- | Verify that an x86_64 function (following the System V AMD64 ABI) conforms
-- to an LLVM specification. This allows for compositional verification of LLVM
-- functions that call x86_64 functions (but not the other way around).
llvm_verify_x86_with_invariant ::
  Some LLVMModule {- ^ Module to associate with method spec -} ->
  FilePath {- ^ Path to ELF file -} ->
  String {- ^ Function's symbol in ELF file -} ->
  [(String, Integer)] {- ^ Global variable symbol names and sizes (in bytes) -} ->
  Bool {- ^ Whether to enable path satisfiability checking -} ->
  (String, Integer, TypedTerm) {- ^ Name of the looping symbol, and function specifying the loop -} ->
  LLVMCrucibleSetupM () {- ^ Specification to verify against -} ->
  ProofScript () {- ^ Tactic used to use when discharging goals -} ->
  TopLevel (SomeLLVM MS.ProvedSpec)
llvm_verify_x86_with_invariant llvmModule path nm globsyms checkSat (loopName,loopNum,f) =
  llvm_verify_x86_common llvmModule path nm globsyms checkSat
    (SimpleInvariant loopName loopNum f)

data FixpointSelect
 = NoFixpoint
 | SimpleFixpoint TypedTerm
 | SimpleInvariant String Integer TypedTerm

llvm_verify_x86_common ::
  Some LLVMModule {- ^ Module to associate with method spec -} ->
  FilePath {- ^ Path to ELF file -} ->
  String {- ^ Function's symbol in ELF file -} ->
  [(String, Integer)] {- ^ Global variable symbol names and sizes (in bytes) -} ->
  Bool {- ^ Whether to enable path satisfiability checking -} ->
  FixpointSelect ->
  LLVMCrucibleSetupM () {- ^ Specification to verify against -} ->
  ProofScript () {- ^ Tactic used to use when discharging goals -} ->
  TopLevel (SomeLLVM MS.ProvedSpec)
llvm_verify_x86_common (Some (llvmModule :: LLVMModule x)) path nm globsyms checkSat fixpointSelect setup tactic
  | Just Refl <- testEquality (C.LLVM.X86Repr $ knownNat @64) . C.LLVM.llvmArch
                 $ modTrans llvmModule ^. C.LLVM.transContext = do
      start <- io getCurrentTime
      laxLoadsAndStores <- gets rwLaxLoadsAndStores
      pathSatSolver <- gets rwPathSatSolver
      let ?ptrWidth = knownNat @64
      let ?memOpts = C.LLVM.defaultMemOptions
                       { C.LLVM.laxLoadsAndStores = laxLoadsAndStores
                       }
      let ?recordLLVMAnnotation = \_ _ _ -> return ()
      sc <- getSharedContext
      opts <- getOptions
      basic_ss <- getBasicSS
      rw <- getTopLevelRW
      sym <- liftIO $ newSAWCoreExprBuilder sc
      mdMap <- liftIO $ newIORef mempty
      SomeOnlineBackend bak <- liftIO $
        newSAWCoreBackendWithTimeout pathSatSolver sym $ rwCrucibleTimeout rw
      cacheTermsSetting <- liftIO $ W4.getOptionSetting W4.B.cacheTerms $ W4.getConfiguration sym
      _ <- liftIO $ W4.setOpt cacheTermsSetting $ rwWhat4HashConsingX86 rw
      liftIO $ W4.extendConfig
        [ W4.opt
            LO.enableSMTArrayMemoryModel
            (W4.ConcreteBool $ rwSMTArrayMemoryModel rw)
            ("Enable SMT array memory model" :: Text)
        ]
        (W4.getConfiguration sym)
      let ?w4EvalTactic = W4EvalTactic { doW4Eval = rwWhat4Eval rw }
      sawst <- liftIO $ sawCoreState sym
      halloc <- getHandleAlloc
      let mvar = C.LLVM.llvmMemVar . view C.LLVM.transContext $ modTrans llvmModule
      sfs <- liftIO $ Macaw.newSymFuns sym
      let cenv = rwCryptol rw
      liftIO $ sawRegisterSymFunInterp sawst (Macaw.fnAesEnc sfs) $ cryptolUninterpreted cenv "aesenc"
      liftIO $ sawRegisterSymFunInterp sawst (Macaw.fnAesEncLast sfs) $ cryptolUninterpreted cenv "aesenclast"
      liftIO $ sawRegisterSymFunInterp sawst (Macaw.fnAesDec sfs) $ cryptolUninterpreted cenv "aesdec"
      liftIO $ sawRegisterSymFunInterp sawst (Macaw.fnAesDecLast sfs) $ cryptolUninterpreted cenv "aesdeclast"
      liftIO $ sawRegisterSymFunInterp sawst (Macaw.fnAesKeyGenAssist sfs) $ cryptolUninterpreted cenv "aeskeygenassist"
      liftIO $ sawRegisterSymFunInterp sawst (Macaw.fnAesIMC sfs) $ cryptolUninterpreted cenv "aesimc"
      liftIO $ sawRegisterSymFunInterp sawst (Macaw.fnClMul sfs) $ cryptolUninterpreted cenv "clmul"
      liftIO $ sawRegisterSymFunInterp sawst (Macaw.fnShasigma0 sfs) $ cryptolUninterpreted cenv "sigma_0"
      liftIO $ sawRegisterSymFunInterp sawst (Macaw.fnShasigma1 sfs) $ cryptolUninterpreted cenv "sigma_1"
      liftIO $ sawRegisterSymFunInterp sawst (Macaw.fnShaSigma0 sfs) $ cryptolUninterpreted cenv "SIGMA_0"
      liftIO $ sawRegisterSymFunInterp sawst (Macaw.fnShaSigma1 sfs) $ cryptolUninterpreted cenv "SIGMA_1"
      liftIO $ sawRegisterSymFunInterp sawst (Macaw.fnShaCh sfs) $ cryptolUninterpreted cenv "Ch"
      liftIO $ sawRegisterSymFunInterp sawst (Macaw.fnShaMaj sfs) $ cryptolUninterpreted cenv "Maj"

      let preserved = Set.fromList . catMaybes $ stringToReg . Text.toLower . Text.pack <$> rwPreservedRegs rw
      (C.SomeCFG cfg, elf, relf, addr, cfgs) <- io $ buildCFG opts halloc preserved path nm
      addrInt <- if Macaw.segmentBase (Macaw.segoffSegment addr) == 0
        then pure . toInteger $ Macaw.segmentOffset (Macaw.segoffSegment addr) + Macaw.segoffOffset addr
        else fail $ mconcat ["Address of \"", nm, "\" is not an absolute address"]
      let maxAddr = addrInt + toInteger (Macaw.segmentSize $ Macaw.segoffSegment addr)

      let
        cc :: LLVMCrucibleContext x
        cc = LLVMCrucibleContext
          { _ccLLVMModule = llvmModule
          , _ccBackend = SomeOnlineBackend bak
          , _ccBasicSS = basic_ss

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
      methodSpec <- buildMethodSpec llvmModule nm (show addr) checkSat setup

      let ?lc = modTrans llvmModule ^. C.LLVM.transContext . C.LLVM.llvmTypeCtx

      emptyState <- io $ initialState bak opts sc cc elf relf methodSpec globsyms maxAddr
      balign <- integerToAlignment $ rwStackBaseAlign rw
      (env, preState) <- io . runX86Sim emptyState $ setupMemory globsyms balign

      let
        funcLookup = Macaw.LookupFunctionHandle $ \st _mem regs -> do
          C.LLVM.LLVMPointer _base off <- getReg Macaw.X86_IP regs
          case BV.asUnsigned <$> W4.asBV off of
            Nothing -> fail $ mconcat
              [ "Attempted to call a function with non-concrete address "
              , show $ W4.ppExpr off
              ]
            Just funcAddr -> do
              case Macaw.resolveRegionOff (memory relf) 0 $ fromIntegral funcAddr of
                Nothing -> fail $ mconcat
                  [ "Failed to resolve function address "
                  , show $ W4.ppExpr off
                  ]
                Just funcAddrOff -> do
                  case Map.lookup funcAddrOff cfgs of
                    Just (C.SomeCFG funcCFG) ->
                      pure
                        ( C.cfgHandle funcCFG
                        , st & C.stateContext . C.functionBindings
                          %~ C.FnBindings . C.insertHandleMap (C.cfgHandle funcCFG) (C.UseCFG funcCFG $ C.postdomInfo funcCFG) . C.fnBindings
                        )
                    Nothing -> fail $ mconcat
                      [ "Unable to find CFG for function at address "
                      , show $ W4.ppExpr off
                      ]
        archEvalFns = Macaw.x86_64MacawEvalFn sfs Macaw.defaultMacawArchStmtExtensionOverride
        lookupSyscall = Macaw.unsupportedSyscalls "saw-script"
        noExtraValidityPred _ _ _ _ = return Nothing
        defaultMacawExtensions_x86_64 =
          Macaw.macawExtensions
          archEvalFns mvar
          (mkGlobalMap . Map.singleton 0 $ preState ^. x86GlobalBase)
          funcLookup
          lookupSyscall
          noExtraValidityPred
        sawMacawExtensions = defaultMacawExtensions_x86_64
          { C.extensionExec = \s0 st -> case s0 of
              Macaw.PtrLt w x y -> doPtrCmp W4.bvUlt st mvar w x y
              Macaw.PtrLeq w x y -> doPtrCmp W4.bvUle st mvar w x y
              _ -> (C.extensionExec defaultMacawExtensions_x86_64) s0 st
          }
        ctx :: C.SimContext (Macaw.MacawSimulatorState Sym) Sym (Macaw.MacawExt Macaw.X86_64)
        ctx = C.SimContext
              { C._ctxBackend = SomeBackend bak
              , C.ctxSolverProof = \x -> x
              , C.ctxIntrinsicTypes = C.LLVM.llvmIntrinsicTypes
              , C.simHandleAllocator = halloc
              , C.printHandle = stdout
              , C.extensionImpl = sawMacawExtensions
              , C._functionBindings = C.FnBindings $ C.insertHandleMap (C.cfgHandle cfg) (C.UseCFG cfg $ C.postdomInfo cfg) C.emptyHandleMap
              , C._cruciblePersonality = Macaw.MacawSimulatorState
              , C._profilingMetrics = Map.empty
              }

      (globals, assumes) <-
          do let globals0 = C.insertGlobal mvar (preState ^. x86Mem) C.emptyGlobals
             liftIO $ setupPrestateConditions methodSpec cc (preState ^. x86Mem) env globals0
                       (methodSpec ^. MS.csPreState . MS.csConditions)

      let
        macawStructRepr = C.StructRepr $ Macaw.crucArchRegTypes Macaw.x86_64MacawSymbolicFns
        initial = C.InitialState ctx globals C.defaultAbortHandler macawStructRepr
                  $ C.runOverrideSim macawStructRepr
                  $ Macaw.crucGenArchConstraints Macaw.x86_64MacawSymbolicFns
                  $ do
          liftIO $
            forM_ assumes $ \(C.LabeledPred p (md, reason)) ->
              do expr <- resolveSAWPred cc p
                 let loc = MS.conditionLoc md
                 C.addAssumption bak
                   (C.GenericAssumption loc reason expr)
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
          liftIO . void . runX86Sim finalState $
            assertPost globals' env (preState ^. x86Mem) (preState ^. x86Regs) mdMap
          pure $ C.regValue r

      liftIO $ printOutLn opts Info "Simulating function"

      psatf <-
         if checkSat then
           do f <- liftIO (C.pathSatisfiabilityFeature sym (C.considerSatisfiability bak))
              pure [C.genericToExecutionFeature f]
         else
           pure []

      simpleLoopFixpointFeature <-
        case fixpointSelect of
          NoFixpoint -> return []
          SimpleFixpoint func ->
            do f <- liftIO (setupSimpleLoopFixpointFeature sym sc sawst cfg mvar func)
               return [f]
          SimpleInvariant loopFixpointSymbol loopNum func ->
            do (loopaddr :: Macaw.MemSegmentOff 64) <-
                 case findSymbols (symMap relf) . encodeUtf8 $ Text.pack loopFixpointSymbol of
                   (loopaddr:_) -> pure loopaddr
                   _ -> fail $ mconcat ["Could not find symbol \"", nm, "\""]
               case Map.lookup loopaddr cfgs of
                 Nothing -> throwX86 $ "Unable to discover looping CFG from address " <> show loopaddr
                 Just (C.SomeCFG loopcfg) ->
                   do let printFn = printOutLn opts Info
                      f <- liftIO (setupSimpleLoopInvariantFeature sym printFn loopNum
                                                                   sc sawst mdMap loopcfg mvar func)
                      return [f]

      let execFeatures = simpleLoopFixpointFeature ++ psatf

      liftIO $ C.executeCrucible execFeatures initial >>= \case
        C.FinishedResult{} -> pure ()
        C.AbortedResult _ ar -> do
          printOutLn opts Warn "Warning: function never returns"
          print $ Common.ppAbortedResult
            ( \gp ->
                case C.lookupGlobal mvar $ gp ^. C.gpGlobals of
                  Nothing -> "LLVM memory global variable not initialized"
                  Just mem -> C.LLVM.ppMem $ C.LLVM.memImplHeap mem
            )
            ar
        C.TimeoutResult{} -> fail "Execution timed out"

      (stats,vcstats) <- checkGoals bak opts nm sc tactic mdMap

      end <- io getCurrentTime
      let diff = diffUTCTime end start
      ps <- io (MS.mkProvedSpec MS.SpecProved methodSpec stats vcstats mempty diff)
      returnProof $ SomeLLVM ps

  | otherwise = fail "LLVM module must be 64-bit"



setupSimpleLoopFixpointFeature ::
  ( sym ~ W4.B.ExprBuilder n st fs
  , C.IsSymInterface sym
  , ?memOpts::C.LLVM.MemOptions
  , C.LLVM.HasLLVMAnn sym
  , C.IsSyntaxExtension ext
  ) =>
  sym ->
  SharedContext ->
  SAWCoreState n ->
  C.CFG ext blocks init ret ->
  C.GlobalVar C.LLVM.Mem ->
  TypedTerm ->
  IO (C.ExecutionFeature p sym ext rtp)

setupSimpleLoopFixpointFeature sym sc sawst cfg mvar func =
  Crucible.LLVM.Fixpoint.simpleLoopFixpoint sym cfg mvar fixpoint_func

 where
  fixpoint_func fixpoint_substitution condition =
    do let fixpoint_substitution_as_list = reverse $ MapF.toList fixpoint_substitution
       let body_exprs = map (mapSome $ Crucible.LLVM.Fixpoint.bodyValue) (MapF.elems fixpoint_substitution)
       let uninterpreted_constants = foldMap
             (viewSome $ Set.map (mapSome $ W4.varExpr sym) . W4.exprUninterpConstants sym)
             (Some condition : body_exprs)
       let filtered_uninterpreted_constants = Set.toList $ Set.filter
             (\(Some variable) ->
               not (List.isPrefixOf "creg_join_var" $ show $ W4.printSymExpr variable)
               && not (List.isPrefixOf "cmem_join_var" $ show $ W4.printSymExpr variable)
               && not (List.isPrefixOf "cundefined" $ show $ W4.printSymExpr variable)
               && not (List.isPrefixOf "calign_amount" $ show $ W4.printSymExpr variable))
             uninterpreted_constants
       body_tms <- mapM (viewSome $ toSC sym sawst) filtered_uninterpreted_constants
       implicit_parameters <- mapM (scExtCns sc) $ Set.toList $ foldMap getAllExtSet body_tms

       arguments <- forM fixpoint_substitution_as_list $ \(MapF.Pair _ fixpoint_entry) ->
         toSC sym sawst $ Crucible.LLVM.Fixpoint.headerValue fixpoint_entry
       applied_func <- scApplyAll sc (ttTerm func) $ implicit_parameters ++ arguments
       applied_func_selectors <- forM [1 .. (length fixpoint_substitution_as_list)] $ \i ->
         scTupleSelector sc applied_func i (length fixpoint_substitution_as_list)
       result_substitution <- MapF.fromList <$> zipWithM
         (\(MapF.Pair variable _) applied_func_selector ->
           MapF.Pair variable <$> bindSAWTerm sym sawst (W4.exprType variable) applied_func_selector)
         fixpoint_substitution_as_list
         applied_func_selectors

       explicit_parameters <- forM fixpoint_substitution_as_list $ \(MapF.Pair variable _) ->
         toSC sym sawst variable
       inner_func <- case asConstant (ttTerm func) of
         Just (_, Just (asApplyAll -> (isGlobalDef "Prelude.fix" -> Just (), [_, inner_func]))) ->
           return inner_func
         _ -> fail $ "not Prelude.fix: " ++ showTerm (ttTerm func)
       func_body <- betaNormalize sc
         =<< scApplyAll sc inner_func ((ttTerm func) : (implicit_parameters ++ explicit_parameters))

       step_arguments <- forM fixpoint_substitution_as_list $ \(MapF.Pair _ fixpoint_entry) ->
         toSC sym sawst $ Crucible.LLVM.Fixpoint.bodyValue fixpoint_entry
       tail_applied_func <- scApplyAll sc (ttTerm func) $ implicit_parameters ++ step_arguments
       explicit_parameters_tuple <- scTuple sc explicit_parameters
       let lhs = Prelude.last step_arguments
       w <- scNat sc 64
       rhs <- scBvMul sc w (head implicit_parameters) =<< scBvNat sc w =<< scNat sc 128
       loop_condition <- scBvULt sc w lhs rhs
       output_tuple_type <- scTupleType sc =<< mapM (scTypeOf sc) explicit_parameters
       loop_body <- scIte sc output_tuple_type loop_condition tail_applied_func explicit_parameters_tuple

       induction_step_condition <- scEq sc loop_body func_body
       result_condition <- bindSAWTerm sym sawst W4.BaseBoolRepr induction_step_condition

       return (result_substitution, result_condition)


-- | This procedure sets up the simple loop fixpoint feature.
--   Its main task is to massage the user-provided invariant
--   term into the form expected by the Crucible exeuction
--   feature.
setupSimpleLoopInvariantFeature ::
  ( sym ~ W4.B.ExprBuilder n st fs
  , C.IsSymInterface sym
  , n ~ GlobalNonceGenerator
  , ?memOpts::C.LLVM.MemOptions
  , C.LLVM.HasLLVMAnn sym
  , C.IsSyntaxExtension ext
  ) =>
  sym ->
  (String -> IO ()) {- ^ logging function -} ->
  Integer {- ^ Which loop are we targeting? -} ->
  SharedContext ->
  SAWCoreState n ->
  IORef MetadataMap ->
  C.CFG ext blocks init ret ->
  C.GlobalVar C.LLVM.Mem ->
  TypedTerm {- ^ user-provided invariant term -} ->
  IO (C.ExecutionFeature p sym ext rtp)

setupSimpleLoopInvariantFeature sym printFn loopNum sc sawst mdMap cfg mvar func =
  SimpleInvariant.simpleLoopInvariant sym loopNum cfg mvar invariant_func

 where
  invariant_func phase implicit_params invariant_substitution =
    do let subst_pairs = reverse (MapF.toList invariant_substitution)
       let filtered_implicit_params = filter
             (\ (Some variable) ->
               -- We filter variables with the following special names from appearing as
               -- implicit arguments to the loop invariant.  These are basically all various
               -- kinds of underspecification appearing from various underlying components
               -- and don't make sense as arguments to the loop invariant.
               not (List.isPrefixOf "creg_join_var" $ show $ W4.printSymExpr variable)
               && not (List.isPrefixOf "cmem_join_var" $ show $ W4.printSymExpr variable)
               && not (List.isPrefixOf "cundefined" $ show $ W4.printSymExpr variable)
               && not (List.isPrefixOf "calign_amount" $ show $ W4.printSymExpr variable)
               && not (List.isPrefixOf "cnoSatisfyingWrite" $ show $ W4.printSymExpr variable)
             )
             implicit_params
       body_tms <- mapM (viewSome $ toSC sym sawst) filtered_implicit_params
       implicit_params' <- mapM (scExtCns sc) $ Set.toList $ foldMap getAllExtSet body_tms
       initial_exprs <-
         forM subst_pairs $
           \ (MapF.Pair _var (SimpleInvariant.InvariantEntry initVal _current)) ->
               toSC sym sawst initVal
       current_exprs <-
         forM subst_pairs $
           \ (MapF.Pair _var (SimpleInvariant.InvariantEntry _init current)) ->
               toSC sym sawst current

       initial_tuple <- scTuple sc initial_exprs
       current_tuple <- scTuple sc current_exprs

       -- use the provided logging function to print the discovered
       -- implicit parameters
       when (phase == SimpleInvariant.InitialInvariant) $
         do printFn "Loop invariant implicit parameters!"
            forM_ implicit_params' $ \x ->
                do printFn (show (ppTerm Verifier.SAW.SharedTerm.defaultPPOpts x))
                   tp <- scTypeOf sc x
                   printFn (show (ppTerm Verifier.SAW.SharedTerm.defaultPPOpts tp))

       -- actually apply the arguments to the given term
       inv <- scApplyAll sc (ttTerm func) (implicit_params' ++ [initial_tuple, current_tuple])

       -- check that the produced term is type-correct
       res <- scTypeCheck sc Nothing inv
       case res of
         Left _tcErr ->
           do tpType <- scTypeOf sc initial_tuple
              fail $ unlines [ "Loop invariant has incorrect type! State tuple has type:"
                             , show (ppTerm Verifier.SAW.SharedTerm.defaultPPOpts tpType)
                             ]
         Right tp ->
           do ok <- scConvertible sc True tp =<< scBoolType sc
              unless ok $
                fail $ unlines [ "Loop invariant must return a boolean value, but got:"
                               , show (ppTerm Verifier.SAW.SharedTerm.defaultPPOpts tp)
                                  -- TODO, get ppOpts from the right place
                               ]
       b <- bindSAWTerm sym sawst W4.BaseBoolRepr inv

       -- Add goal metadata for the initial and inductive invariants
       case phase of
         SimpleInvariant.HypotheticalInvariant -> return b
         SimpleInvariant.InitialInvariant ->
           do (ann,b') <- W4.annotateTerm sym b
              loc <- W4.getCurrentProgramLoc sym
              let md = MS.ConditionMetadata
                       { MS.conditionLoc = loc
                       , MS.conditionTags = Set.singleton "initial loop invariant"
                       , MS.conditionType = "initial loop invariant"
                       , MS.conditionContext = ""
                       }
              modifyIORef mdMap (Map.insert ann md)
              return b'
         SimpleInvariant.InductiveInvariant ->
           do (ann,b') <- W4.annotateTerm sym b
              loc <- W4.getCurrentProgramLoc sym
              let md = MS.ConditionMetadata
                       { MS.conditionLoc = loc
                       , MS.conditionTags = Set.singleton "inductive loop invariant"
                       , MS.conditionType = "inductive loop invariant"
                       , MS.conditionContext = ""
                       }
              modifyIORef mdMap (Map.insert ann md)
              return b'

--------------------------------------------------------------------------------
-- ** Computing the CFG

-- | Load the given ELF file and use Macaw to construct a Crucible CFG.
buildCFG ::
  Options ->
  C.HandleAllocator ->
  Set (Some Macaw.X86Reg) {- ^ Registers to treat as callee-saved -} ->
  String {- ^ Path to ELF file -} ->
  String {- ^ Function's symbol in ELF file -} ->
  IO ( C.SomeCFG
       (Macaw.MacawExt Macaw.X86_64)
       (EmptyCtx ::> Macaw.ArchRegStruct Macaw.X86_64)
       (Macaw.ArchRegStruct Macaw.X86_64)
     , Elf.ElfHeaderInfo 64
     , RelevantElf
     , Macaw.MemSegmentOff 64
     , Map
       (Macaw.MemSegmentOff 64)
       (C.SomeCFG
         (Macaw.MacawExt Macaw.X86_64)
         (EmptyCtx ::> Macaw.ArchRegStruct Macaw.X86_64)
         (Macaw.ArchRegStruct Macaw.X86_64))
     )
buildCFG opts halloc preserved path nm = do
  printOutLn opts Info $ mconcat ["Finding symbol for \"", nm, "\""]
  elf <- getElf path
  relf <- getRelevant elf
  (addr :: Macaw.MemSegmentOff 64) <-
    case findSymbols (symMap relf) . encodeUtf8 $ Text.pack nm of
      (addr:_) -> pure addr
      _ -> fail $ mconcat ["Could not find symbol \"", nm, "\""]
  printOutLn opts Info $ mconcat ["Found symbol at address ", show addr, ", building CFG"]
  let
    preservedRegs = Set.union preserved Macaw.x86CalleeSavedRegs
    preserveFn :: forall t. Macaw.X86Reg t -> Bool
    preserveFn r = Set.member (Some r) preservedRegs
    macawCallParams = Macaw.x86_64CallParams { Macaw.preserveReg = preserveFn }
    macawArchInfo = (Macaw.x86_64_info preserveFn)
      { Macaw.archCallParams = macawCallParams
      }
    initialDiscoveryState =
      Macaw.emptyDiscoveryState (memory relf) (funSymMap relf) macawArchInfo
      -- "inline" any function addresses that we happen to jump to
      & Macaw.trustedFunctionEntryPoints .~ Map.empty
    finalState = Macaw.cfgFromAddrsAndState initialDiscoveryState [addr] []
    finfos = finalState ^. Macaw.funInfo
  cfgs <- forM finfos $ \(Some finfo) ->
    Macaw.mkFunCFG Macaw.x86_64MacawSymbolicFns halloc
    (W4.functionNameFromText . decodeUtf8 $ Macaw.discoveredFunName finfo)
    posFn finfo

  case Map.lookup addr cfgs of
    Nothing -> throwX86 $ "Unable to discover CFG from address " <> show addr
    Just scfg -> pure (scfg, elf, relf, addr, cfgs)

--------------------------------------------------------------------------------
-- ** Computing the specification

-- | Construct the method spec like we normally would in llvm_verify.
-- Unlike in llvm_verify, we can't reuse the simulator state (due to the
-- different memory layout / RegMap).
buildMethodSpec ::
  LLVMModule LLVMArch ->
  String {- ^ Name of method -} ->
  String {- ^ Source location for method spec (here, we use the address) -} ->
  Bool {- ^ check sat -} ->
  LLVMCrucibleSetupM () ->
  TopLevel (MS.CrucibleMethodSpecIR LLVM)
buildMethodSpec lm nm loc checkSat setup =
  setupLLVMCrucibleContext checkSat lm $ \cc -> do
    let methodId = LLVMMethodId nm Nothing
    let programLoc =
          W4.mkProgramLoc (W4.functionNameFromText $ Text.pack nm)
          . W4.OtherPos $ Text.pack loc
    let lc = modTrans lm ^. C.LLVM.transContext . C.LLVM.llvmTypeCtx
    opts <- getOptions
    (args, ret) <- case llvmSignature opts lm nm of
      Left err -> fail $ mconcat ["Could not find declaration for \"", nm, "\": ", err]
      Right x -> pure x
    (mtargs, mtret) <- case (,) <$> mapM (llvmTypeToMemType lc) args <*> mapM (llvmTypeToMemType lc) ret of
      Left err -> fail err
      Right x -> pure x
    let initialMethodSpec = MS.makeCrucibleMethodSpecIR @LLVM
          methodId mtargs mtret programLoc lm
    view Setup.csMethodSpec <$>
      execStateT
        (runReaderT (runLLVMCrucibleSetupM setup) Setup.makeCrucibleSetupRO)
        (Setup.makeCrucibleSetupState emptyResolvedState cc initialMethodSpec)

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
  (X86Constraints, OnlineSolver solver) =>
  Backend solver ->
  Options ->
  SharedContext ->
  LLVMCrucibleContext LLVMArch ->
  Elf.ElfHeaderInfo 64 ->
  RelevantElf ->
  MS.CrucibleMethodSpecIR LLVM ->
  [(String, Integer)] {- ^ Global variable symbol names and sizes (in bytes) -} ->
  Integer {- ^ Minimum size of the global allocation (here, the end of the .text segment -} ->
  IO X86State
initialState bak opts sc cc elf relf ms globs maxAddr = do
  let sym = backendGetSym bak
  emptyMem <- C.LLVM.emptyMem C.LLVM.LittleEndian
  emptyRegs <- traverseWithIndex (freshRegister sym) C.knownRepr
  symTab <- case Elf.decodeHeaderSymtab elf of
    Nothing -> throwX86 "Elf file has no symbol table"
    Just (Left _err) -> throwX86 "Failed to decode symbol table"
    Just (Right st) -> pure st
  let
    align = C.LLVM.exponentToAlignment 4
    allocGlobalEnd :: MS.AllocGlobal LLVM -> Integer
    allocGlobalEnd (LLVMAllocGlobal _ (LLVM.Symbol nm)) = globalEnd nm
    globalEnd :: String -> Integer
    globalEnd nm = maybe 0 (\entry -> fromIntegral $ Elf.steValue entry + Elf.steSize entry) $
      (Vector.!? 0)
      . Vector.filter (\e -> Elf.steName e == encodeUtf8 (Text.pack nm))
      $ Elf.symtabEntries symTab
  sz <- W4.bvLit sym knownNat . BV.mkBV knownNat . maximum $ mconcat
    [ [maxAddr, globalEnd "_end"]
    , globalEnd . fst <$> globs
    , allocGlobalEnd <$> ms ^. MS.csGlobalAllocs
    ]
  (base, mem) <- C.LLVM.doMalloc bak C.LLVM.GlobalAlloc C.LLVM.Immutable
    "globals" emptyMem sz align
  pure $ X86State
    { _x86Backend = SomeOnlineBackend bak
    , _x86Options = opts
    , _x86SharedContext = sc
    , _x86CrucibleContext = cc
    , _x86ElfSymtab = symTab
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
  C.LLVM.Alignment {- ^ Stack base alignment -} ->
  X86Sim (Map MS.AllocIndex Ptr)
setupMemory globsyms balign = do
  setupGlobals globsyms

  -- Allocate a reasonable amount of stack (4 KiB + 0b10000 for least valid alignment + 1 qword for IP)
  allocateStack (4096 + 16) balign

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
  SomeOnlineBackend bak <- use x86Backend
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
      ptr <- C.LLVM.doPtrAddOffset bak m base =<< W4.bvLit sym knownNat (BV.mkBV knownNat addr)
      v <- Vector.fromList <$> mapM convertByte bytes
      let st = C.LLVM.arrayType (fromIntegral $ length bytes) $ C.LLVM.bitvectorType 1
      C.LLVM.storeConstRaw bak m ptr st C.LLVM.noAlignment
        $ C.LLVM.LLVMValArray (C.LLVM.bitvectorType 1) v
  globs <- liftIO $ mconcat <$> mapM readInitialGlobal globsyms
  mem' <- liftIO $ foldlM writeGlobal mem globs
  x86Mem .= mem'

-- | Allocate memory for the stack, and pushes a fresh pointer as the return
-- address.
allocateStack ::
  X86Constraints =>
  Integer {- ^ Stack size in bytes -} ->
  C.LLVM.Alignment {- ^ Stack base alignment -} ->
  X86Sim ()
allocateStack szInt balign = do
  SomeOnlineBackend bak <- use x86Backend
  sym <- use x86Sym
  mem <- use x86Mem
  regs <- use x86Regs
  sz <- liftIO $ W4.bvLit sym knownNat $ BV.mkBV knownNat $ szInt + 8
  (base, mem') <- liftIO $ C.LLVM.doMalloc bak C.LLVM.HeapAlloc C.LLVM.Mutable "stack_alloc" mem sz balign
  sn <- case W4.userSymbol "stack" of
    Left err -> throwX86 $ "Invalid symbol for stack: " <> show err
    Right sn -> pure sn
  fresh <- liftIO $ C.LLVM.LLVMPointer
    <$> W4.natLit sym 0
    <*> W4.freshConstant sym sn (W4.BaseBVRepr $ knownNat @64)
  ptr <- liftIO $ C.LLVM.doPtrAddOffset bak mem' base =<< W4.bvLit sym knownNat (BV.mkBV knownNat szInt)
  writeAlign <- integerToAlignment defaultStackBaseAlign
  finalMem <- liftIO $ C.LLVM.doStore bak mem' ptr
    (C.LLVM.LLVMPointerRepr $ knownNat @64)
    (C.LLVM.bitvectorType 8) writeAlign fresh
  x86Mem .= finalMem
  finalRegs <- setReg Macaw.RSP ptr regs
  x86Regs .= finalRegs

-- | Process an llvm_alloc statement, allocating the requested memory and
-- associating a pointer to that memory with the appropriate index.
assumeAllocation ::
  X86Constraints =>
  Map MS.AllocIndex Ptr ->
  (MS.AllocIndex, LLVMAllocSpec) {- ^ llvm_alloc statement -} ->
  X86Sim (Map MS.AllocIndex Ptr)
assumeAllocation env (i, LLVMAllocSpec mut _memTy align sz md False initialization) = do
  SomeOnlineBackend bak <- use x86Backend
  cc <- use x86CrucibleContext
  mem <- use x86Mem
  sz' <- liftIO $ resolveSAWSymBV cc knownNat sz
  let loc = MS.conditionLoc md
  (ptr, mem') <- liftIO $ LO.doAllocSymInit bak mem mut align sz' (show $ W4.plSourceLoc loc) initialization
  x86Mem .= mem'
  pure $ Map.insert i ptr env
assumeAllocation env _ = pure env
  -- no allocation is done for llvm_fresh_pointer
  -- TODO: support llvm_fresh_pointer in x86 verification

-- | Process an llvm_points_to statement, writing some SetupValue to a pointer.
assumePointsTo ::
  X86Constraints =>
  Map MS.AllocIndex Ptr {- ^ Associates each AllocIndex with the corresponding allocation -} ->
  Map MS.AllocIndex LLVMAllocSpec {- ^ Associates each AllocIndex with its specification -} ->
  Map MS.AllocIndex C.LLVM.Ident {- ^ Associates each AllocIndex with its name -} ->
  LLVMPointsTo LLVMArch {- ^ llvm_points_to statement from the precondition -} ->
  X86Sim ()
assumePointsTo env tyenv nameEnv (LLVMPointsTo _ cond tptr tptval) = do
  opts <- use x86Options
  cc <- use x86CrucibleContext
  mem <- use x86Mem
  ptr <- resolvePtrSetupValue env tyenv nameEnv tptr
  cond' <- liftIO $ mapM (resolveSAWPred cc . ttTerm) cond
  mem' <- liftIO $ LO.storePointsToValue opts cc env tyenv nameEnv mem cond' ptr tptval Nothing
  x86Mem .= mem'
assumePointsTo env tyenv nameEnv (LLVMPointsToBitfield _ tptr fieldName tptval) = do
  opts <- use x86Options
  cc <- use x86CrucibleContext
  mem <- use x86Mem
  (bfIndex, ptr) <- resolvePtrSetupValueBitfield env tyenv nameEnv tptr fieldName
  mem' <- liftIO $ LO.storePointsToBitfieldValue opts cc env tyenv nameEnv mem ptr bfIndex tptval
  x86Mem .= mem'

resolvePtrSetupValue ::
  X86Constraints =>
  Map MS.AllocIndex Ptr ->
  Map MS.AllocIndex LLVMAllocSpec ->
  Map MS.AllocIndex C.LLVM.Ident {- ^ Associates each AllocIndex with its name -} ->
  MS.SetupValue LLVM ->
  X86Sim Ptr
resolvePtrSetupValue env tyenv nameEnv tptr = do
  SomeOnlineBackend bak <- use x86Backend
  sym <- use x86Sym
  cc <- use x86CrucibleContext
  mem <- use x86Mem
  symTab <- use x86ElfSymtab
  base <- use x86GlobalBase
  case tptr of
    MS.SetupGlobal () nm -> case
      (Vector.!? 0)
      . Vector.filter (\e -> Elf.steName e == encodeUtf8 (Text.pack nm))
      $ Elf.symtabEntries symTab of
      Nothing -> throwX86 $ mconcat ["Global symbol \"", nm, "\" not found"]
      Just entry -> do
        let addr = fromIntegral $ Elf.steValue entry
        liftIO $ C.LLVM.doPtrAddOffset bak mem base =<< W4.bvLit sym knownNat (BV.mkBV knownNat addr)
    _ -> liftIO $ C.LLVM.unpackMemValue sym (C.LLVM.LLVMPointerRepr $ knownNat @64)
         =<< resolveSetupVal cc mem env tyenv nameEnv tptr

-- | Like 'resolvePtrSetupValue', but specifically geared towards the needs of
-- fields within bitfields. In addition to returning the resolved 'Ptr', this
-- also returns the 'BitfieldIndex' for the field within the bitfield. This
-- ends up being useful for call sites to this function so that they do not
-- have to recompute it.
resolvePtrSetupValueBitfield ::
  X86Constraints =>
  Map MS.AllocIndex Ptr ->
  Map MS.AllocIndex LLVMAllocSpec ->
  Map MS.AllocIndex C.LLVM.Ident {- ^ Associates each AllocIndex with its name -} ->
  MS.SetupValue LLVM ->
  String ->
  X86Sim (BitfieldIndex, Ptr)
resolvePtrSetupValueBitfield env tyenv nameEnv tptr fieldName = do
  sym <- use x86Sym
  cc <- use x86CrucibleContext
  mem <- use x86Mem
  -- symTab <- use x86ElfSymtab
  -- base <- use x86GlobalBase
  case tptr of
    -- TODO RGS: What should we do about the SetupGlobal case?
    {-
    MS.SetupGlobal () nm -> case
      (Vector.!? 0)
      . Vector.filter (\e -> Elf.steName e == encodeUtf8 (Text.pack nm))
      $ Elf.symtabEntries symTab of
      Nothing -> throwX86 $ mconcat ["Global symbol \"", nm, "\" not found"]
      Just entry -> do
        let addr = fromIntegral $ Elf.steValue entry
        liftIO $ C.LLVM.doPtrAddOffset sym mem base =<< W4.bvLit sym knownNat (BV.mkBV knownNat addr)
    -}
    _ -> do
      (bfIndex, lval) <- liftIO $ resolveSetupValBitfield cc mem env tyenv nameEnv tptr fieldName
      val <- liftIO $ C.LLVM.unpackMemValue sym (C.LLVM.LLVMPointerRepr $ knownNat @64) lval
      pure (bfIndex, val)

-- | Write each SetupValue passed to llvm_execute_func to the appropriate
-- x86_64 register from the calling convention.
setArgs ::
  X86Constraints =>
  Map MS.AllocIndex Ptr {- ^ Associates each AllocIndex with the corresponding allocation -} ->
  Map MS.AllocIndex LLVMAllocSpec {- ^ Associates each AllocIndex with its specification -} ->
  Map MS.AllocIndex C.LLVM.Ident {- ^ Associates each AllocIndex with its name -} ->
  [MS.SetupValue LLVM] {- ^ Arguments passed to llvm_execute_func -} ->
  X86Sim ()
setArgs env tyenv nameEnv args
  | length args > length argRegs = throwX86 "More arguments than would fit into general-purpose registers"
  | otherwise = do
      sym <- use x86Sym
      cc <- use x86CrucibleContext
      mem <- use x86Mem
      let
        setRegSetupValue rs (reg, sval) =
          exceptToFail (typeOfSetupValue cc tyenv nameEnv sval) >>= \case
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
  IORef MetadataMap {- ^ metadata map -} ->
  X86Sim ()
assertPost globals env premem preregs mdMap = do
  SomeOnlineBackend bak <- use x86Backend
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
  expectedIP <- liftIO $ C.LLVM.doLoad bak premem prersp (C.LLVM.bitvectorType 8)
    (C.LLVM.LLVMPointerRepr $ knownNat @64) C.LLVM.noAlignment
  actualIP <- getReg Macaw.X86_IP postregs
  correctRetAddr <- liftIO $ C.LLVM.ptrEq sym C.LLVM.PtrWidth actualIP expectedIP
  liftIO . C.addAssertion bak . C.LabeledPred correctRetAddr . C.SimError W4.initializationLoc
    $ C.AssertFailureSimError "Instruction pointer not set to return address" ""

  stack <- liftIO $ C.LLVM.doPtrAddOffset bak premem prersp =<< W4.bvLit sym knownNat (BV.mkBV knownNat 8)
  postrsp <- getReg Macaw.RSP postregs
  correctStack <- liftIO $ C.LLVM.ptrEq sym C.LLVM.PtrWidth stack postrsp
  liftIO $ C.addAssertion bak . C.LabeledPred correctStack . C.SimError W4.initializationLoc
    $ C.AssertFailureSimError "Stack not preserved" ""

  returnMatches <- case (ms ^. MS.csRetValue, ms ^. MS.csRet) of
    (Just expectedRet, Just retTy) -> do
      postRAX <- C.LLVM.ptrToPtrVal <$> getReg Macaw.RAX postregs
      case (postRAX, C.LLVM.memTypeBitwidth retTy) of
        (C.LLVM.LLVMValInt base off, Just retTyBits) -> do
          let
            truncateRAX :: forall r. NatRepr r -> X86Sim (C.LLVM.LLVMVal Sym)
            truncateRAX rsz =
              case (testLeq (knownNat @1) rsz, testLeq rsz (W4.bvWidth off)) of
                (Just LeqProof, Just LeqProof) ->
                  case testStrictLeq rsz (W4.bvWidth off) of
                    Left LeqProof -> do
                      offTrunc <- liftIO $ W4.bvTrunc sym rsz off
                      pure $ C.LLVM.LLVMValInt base offTrunc
                    _ -> pure $ C.LLVM.LLVMValInt base off
                _ -> throwX86 "Width of return type is zero bits"
          postRAXTrunc <- viewSome truncateRAX (mkNatRepr retTyBits)
          let md = MS.ConditionMetadata
                   { MS.conditionLoc = ms ^. MS.csLoc
                   , MS.conditionTags = mempty
                   , MS.conditionType = "return value matching"
                   , MS.conditionContext = ""
                   }
          pure [LO.matchArg opts sc cc ms MS.PostState md postRAXTrunc retTy expectedRet]
        _ -> throwX86 $ "Invalid return type: " <> show (C.LLVM.ppMemType retTy)
    _ -> pure []


  pointsToMatches <- forM (ms ^. MS.csPostState . MS.csPointsTos)
    $ assertPointsTo env tyenv nameEnv

  let setupConditionMatchesPost = fmap -- assert postconditions
        (LO.learnSetupCondition opts sc cc ms MS.PostState)
        $ ms ^. MS.csPostState . MS.csConditions

  let
    initialECs = Map.fromList
      [ (ecVarIndex ec, ec)
      | tt <- ms ^. MS.csPreState . MS.csFreshVars
      , let ec = tecExt tt
      ]
    initialFree = Set.fromList . fmap (ecVarIndex . tecExt) $ ms ^. MS.csPostState . MS.csFreshVars

  initialTerms <- liftIO $ traverse (scExtCns sc) initialECs

  result <- liftIO
    . O.runOverrideMatcher sym globals env initialTerms initialFree (ms ^. MS.csLoc)
    . sequence_ $ mconcat
    [ returnMatches
    , pointsToMatches
    , setupConditionMatchesPost
    , [LO.assertTermEqualities sc cc]
    ]
  st <- case result of
    Left err -> throwX86 $ show err
    Right (_, st) -> pure st
  liftIO . forM_ (view LO.osAsserts st) $ \(md, W4.LabeledPred p r) ->
       do (ann,p') <- W4.annotateTerm sym p
          modifyIORef mdMap (Map.insert ann md)
          C.addAssertion bak (W4.LabeledPred p' r)

-- | Assert that a points-to postcondition holds.
assertPointsTo ::
  X86Constraints =>
  Map MS.AllocIndex Ptr {- ^ Associates each AllocIndex with the corresponding allocation -} ->
  Map MS.AllocIndex LLVMAllocSpec {- ^ Associates each AllocIndex with its specification -} ->
  Map MS.AllocIndex C.LLVM.Ident {- ^ Associates each AllocIndex with its name -} ->
  LLVMPointsTo LLVMArch {- ^ llvm_points_to statement from the precondition -} ->
  X86Sim (LLVMOverrideMatcher md ())
assertPointsTo env tyenv nameEnv pointsTo@(LLVMPointsTo md cond tptr tptval) = do
  opts <- use x86Options
  sc <- use x86SharedContext
  cc <- use x86CrucibleContext
  ms <- use x86MethodSpec
  let loc = MS.conditionLoc md

  ptr <- resolvePtrSetupValue env tyenv nameEnv tptr
  pure $ do
    err <- LO.matchPointsToValue opts sc cc ms MS.PostState md cond ptr tptval
    case err of
      Just msg -> do
        doc <- LO.ppPointsToAsLLVMVal opts cc sc ms pointsTo
        O.failure loc (O.BadPointerLoad (Right doc) msg)
      Nothing -> pure ()
assertPointsTo env tyenv nameEnv pointsTo@(LLVMPointsToBitfield md tptr fieldName tptval) = do
  opts <- use x86Options
  sc <- use x86SharedContext
  cc <- use x86CrucibleContext
  ms <- use x86MethodSpec
  let loc = MS.conditionLoc md

  (bfIndex, ptr) <- resolvePtrSetupValueBitfield env tyenv nameEnv tptr fieldName
  pure $ do
    err <- LO.matchPointsToBitfieldValue opts sc cc ms MS.PostState md ptr bfIndex tptval
    case err of
      Just msg -> do
        doc <- LO.ppPointsToAsLLVMVal opts cc sc ms pointsTo
        O.failure loc (O.BadPointerLoad (Right doc) msg)
      Nothing -> pure ()

-- | Gather and run the solver on goals from the simulator.
checkGoals ::
  IsSymBackend Sym bak =>
  bak ->
  Options ->
  String ->
  SharedContext ->
  ProofScript () ->
  IORef MetadataMap {- ^ metadata map -} ->
  TopLevel (SolverStats, [MS.VCStats])
checkGoals bak opts nm sc tactic mdMap = do
  gs <- liftIO $ getGoals (SomeBackend bak) mdMap
  liftIO . printOutLn opts Info $ mconcat
    [ "Simulation finished, running solver on "
    , show $ length gs
    , " goals"
    ]
  outs <- forM (zip [0..] gs) $ \(n, g) -> do
    term <- liftIO $ gGoal sc g
    let md = gMd g
    let ploc = MS.conditionLoc md
    let gloc = (unwords [show (W4.plSourceLoc ploc)
                       ,"in"
                       , show (W4.plFunction ploc)]) ++
               (if Prelude.null (MS.conditionContext md) then [] else
                  "\n" ++ MS.conditionContext md)
    let proofgoal = ProofGoal
                    { goalNum  = n
                    , goalType = MS.conditionType md
                    , goalName = nm
                    , goalLoc  = gloc
                    , goalDesc = show $ gMessage g
                    , goalSequent = propToSequent term
                    , goalTags = MS.conditionTags md
                    }
    res <- runProofScript tactic term proofgoal (Just (gLoc g))
             (Text.unwords
              ["X86 verification condition", Text.pack (show n), Text.pack (show (gMessage g))])
             False -- do not record this theorem in the database
             False -- TODO! useSequentGoals
    case res of
      ValidProof stats thm ->
        return (stats, MS.VCStats md stats (thmSummary thm) (thmNonce thm) (thmDepends thm) (thmElapsedTime thm))
      UnfinishedProof pst -> do
        printOutLnTop Info $ unwords ["Subgoal failed:", show $ gMessage g]
        printOutLnTop Info (show (psStats pst))
        throwTopLevel $ "Proof failed: " ++ show (length (psGoals pst)) ++ " goals remaining."
      InvalidProof stats vals _pst -> do
        printOutLnTop Info $ unwords ["Subgoal failed:", show $ gMessage g]
        printOutLnTop Info (show stats)
        printOutLnTop OnlyCounterExamples "----------Counterexample----------"
        ppOpts <- sawPPOpts . rwPPOpts <$> getTopLevelRW
        case vals of
          [] -> printOutLnTop OnlyCounterExamples "<<All settings of the symbolic variables constitute a counterexample>>"
          _ -> let showEC ec = Text.unpack (toShortName (ecName ec)) in
               let showAssignment (ec, val) =
                     mconcat [ " ", showEC ec, ": ", show $ ppFirstOrderValue ppOpts val ]
               in mapM_ (printOutLnTop OnlyCounterExamples . showAssignment) vals
        printOutLnTop OnlyCounterExamples "----------------------------------"
        throwTopLevel "Proof failed."
  liftIO $ printOutLn opts Info "All goals succeeded"

  let stats = mconcat (map fst outs)
  let vcstats = map snd outs
  return (stats, vcstats)
