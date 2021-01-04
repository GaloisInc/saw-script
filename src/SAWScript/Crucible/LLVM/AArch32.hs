{- |
Module      : SAWScript.Crucible.LLVM.AArch32
Description : Implements a SAWScript primitive for verifying aarch32 functions
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
{-# Language RankNTypes #-}
{-# Language DataKinds #-}
{-# Language ConstraintKinds #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language TemplateHaskell #-}

module SAWScript.Crucible.LLVM.AArch32
  ( llvm_verify_aarch32
  ) where

import Control.Lens.TH (makeLenses)

import GHC.Natural (Natural)

import System.IO (stdout)
import Control.Exception (Exception(..), throw)
import Control.Lens (view, use, toListOf, folded, (&), (^.), (.~), (%~), (.=))
import Control.Applicative ((<|>))
import Control.Monad.State
import Control.Monad.Catch (MonadThrow)

import qualified Data.BitVector.Sized as BV
import Data.Foldable (foldlM)
import qualified Data.List.NonEmpty as NE
import qualified Data.Vector as Vector
import qualified Data.Text as Text
import Data.Text.Encoding (decodeUtf8, encodeUtf8)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
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
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedTerm
import Verifier.SAW.Recognizer (asBool)

import SAWScript.Proof
import SAWScript.Prover.SolverStats
import SAWScript.TopLevel
import SAWScript.Value
import SAWScript.Options

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
import qualified What4.Solver.Yices as Yices

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
import qualified Lang.Crucible.Simulator.PathSatisfiability as C

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
import qualified Data.Macaw.Memory.LoadCommon as Macaw
import qualified Data.Macaw.Memory.ElfLoader as Macaw
import qualified Data.Macaw.CFG as Macaw
import qualified Data.Macaw.Symbolic as Macaw
import qualified Data.Macaw.Symbolic.Backend as Macaw
import qualified Data.Macaw.AArch32.Symbolic as Macaw
import qualified Data.Macaw.AArch32.Symbolic as Macaw.AArch32
import qualified Data.Macaw.ARM as Macaw
import qualified Data.Macaw.ARM.ARMReg as Macaw

import qualified Data.ElfEdit as Elf

import qualified Language.ASL.Globals as ASL

-------------------------------------------------------------------------------
-- ** Utility type synonyms and functions

type Sym = C.SAWCoreBackend GlobalNonceGenerator Yices.Connection (W4.Flags W4.FloatReal)
type LLVMArch = C.LLVM.X86 32
type LLVM = C.LLVM.LLVM LLVMArch
type LLVMOverrideMatcher = O.OverrideMatcher LLVM
type Regs = Assignment (C.RegValue' Sym) (Macaw.MacawCrucibleRegTypes Macaw.ARM)
type Register = Macaw.ARMReg (Macaw.BVType 32)
type Mem = C.LLVM.MemImpl Sym
type Ptr = C.LLVM.LLVMPtr Sym 32
type AArch32Constraints =
  ( C.LLVM.HasPtrWidth (C.LLVM.ArchWidth LLVMArch)
  , C.LLVM.HasLLVMAnn Sym
  , ?lc :: C.LLVM.TypeContext
  )

newtype AArch32Error = AArch32Error String deriving Show
instance Exception AArch32Error

throwAArch32 :: MonadThrow m => String -> m a
throwAArch32 = throw . AArch32Error

data RelevantElf = RelevantElf
  { memory :: Macaw.Memory 32
  , funSymMap :: Macaw.AddrSymMap 32
  , symMap :: Macaw.AddrSymMap 32
  }

data Unit = Bytes | Words | DWords | QWords | V128s | V256s deriving Show

unitByteSize :: Unit -> (forall w. (1 <= w) => NatRepr w -> a) -> a
unitByteSize u k =
  case u of
    Bytes  -> k (knownNat @1)
    Words  -> k (knownNat @2)
    DWords -> k (knownNat @4)
    QWords -> k (knownNat @8)
    V128s  -> k (knownNat @16)
    V256s  -> k (knownNat @32)

getElf :: FilePath -> IO (Elf.ElfHeaderInfo 32)
getElf path =
  do bs <- BS.readFile path
     case Elf.decodeElfHeaderInfo bs of
       Right (Elf.SomeElf hdr)
         | Elf.ELFCLASS32 <- Elf.headerClass (Elf.header hdr) -> pure hdr
         | otherwise -> throwAArch32 "64-bit ELF format"
       Left _ -> throwAArch32 "Invalid ELF header"


getRelevant :: Elf.ElfHeaderInfo 32 -> IO RelevantElf
getRelevant elf =
  case (Macaw.memoryForElf opts elf, Macaw.memoryForElfAllSymbols opts elf) of
    (Left err, _) -> throwAArch32 err
    (_, Left err) -> throwAArch32 err
    (Right (mem, faddrs, _warnings, _errs), Right (_, addrs, _, _)) ->
      do let toEntry msym = (Macaw.memSymbolStart msym, Macaw.memSymbolName msym)
         return RelevantElf { memory = mem
                            , funSymMap = Map.fromList (map toEntry faddrs)
                            , symMap = Map.fromList (map toEntry addrs)
                            }

  where
    opts = Macaw.LoadOptions
      { Macaw.loadOffset = Just 0
      }

posFn :: Macaw.MemSegmentOff 32 -> W4.Position
posFn = W4.OtherPos . Text.pack . show

findSymbols :: Macaw.AddrSymMap 32 -> ByteString -> [Macaw.MemSegmentOff 32]
findSymbols addrs nm = Map.findWithDefault [] nm invertedMap
  where
  invertedMap = Map.fromListWith (++) [ (y,[x]) | (x,y) <- Map.toList addrs ]

loadGlobal ::
  RelevantElf ->
  (ByteString, Integer, Unit) ->
  IO [(String, Integer, Unit, [Integer])]
loadGlobal elf (nm,n,u) =
  case findSymbols (symMap elf) nm of
    [] -> do print $ symMap elf
             err "Global not found"
    _  -> mapM loadLoc (findSymbols (symMap elf) nm)
  where
  mem   = memory elf
  sname = BSC.unpack nm

  readOne a = case u of
                Bytes  -> check (Macaw.readWord8    mem a)
                Words  -> check (Macaw.readWord16le mem a)
                DWords -> check (Macaw.readWord32le mem a)
                QWords -> check (Macaw.readWord64le mem a)
                _      -> err ("unsuported global size: " ++ show u)

  nextAddr = Macaw.incAddr $ fromIntegral (unitByteSize u natValue :: Natural)

  addrsFor o = Prelude.take (fromIntegral n) (iterate nextAddr o)

  check :: (Show b, Integral a) => Either b a -> IO Integer
  check res = case res of
                Left e  -> err (show e)
                Right a -> return (fromIntegral a)


  loadLoc off = do let start = Macaw.segoffAddr off
                       a  = Macaw.memWordToUnsigned (Macaw.addrOffset start)
                   is <- mapM readOne (addrsFor start)
                   return (sname, a, u, is)

  err :: [Char] -> IO a
  err xs = fail $ unlines
                    [ "Failed to load global."
                    , "*** Global: " ++ show nm
                    , "*** Error: " ++ xs
                    ]

freshVal ::
  Sym -> C.TypeRepr t -> Bool {- ptrOK ?-}-> String -> IO (C.RegValue Sym t)
freshVal sym t ptrOk nm =
  case t of
    C.BoolRepr -> do
      sn <- symName nm
      W4.freshConstant sym sn C.BaseBoolRepr
    C.StructRepr tps ->
      traverseWithIndex (\idx repr -> C.RV <$> freshVal sym repr True (nm ++ "_field_" ++ show idx)) tps
    C.LLVM.LLVMPointerRepr w
      | ptrOk, Just Refl <- testEquality w (knownNat @64) -> do
          sn_base <- symName (nm ++ "_base")
          sn_off <- symName (nm ++ "_off")
          base <- W4.freshConstant sym sn_base C.BaseNatRepr
          off <- W4.freshConstant sym sn_off (C.BaseBVRepr w)
          return (C.LLVM.LLVMPointer base off)
      | otherwise -> do
          sn <- symName nm
          base <- W4.natLit sym 0
          off <- W4.freshConstant sym sn (C.BaseBVRepr w)
          return (C.LLVM.LLVMPointer base off)
    it -> fail ("[freshVal] Unexpected type repr: " ++ show it)

  where
  symName s =
    case W4.userSymbol ("macaw_" ++ s) of
      Left err -> error ("Invalid symbol name " ++ show s ++ ": " ++ show err)
      Right a -> return a

freshRegister :: Sym -> Index ctx tp -> C.TypeRepr tp -> IO (C.RegValue' Sym tp)
freshRegister sym idx repr = C.RV <$> freshVal sym repr True ("reg" ++ show idx)

mkGlobalMap ::
  C.LLVM.HasLLVMAnn Sym =>
  Map.Map Macaw.RegionIndex Ptr ->
  Macaw.GlobalMap Sym C.LLVM.Mem 32
mkGlobalMap rmap sym mem region off =
  mapConcreteRegion <|> passThroughConcreteRegion <|> mapSymbolicRegion
  where
    mapConcreteRegion = maybe mzero id (addOffset <$> thisRegion)
    thisRegion = join (findRegion <$> W4.asNat region)
    findRegion r = Map.lookup (fromIntegral r) rmap
    addOffset p = C.LLVM.doPtrAddOffset sym mem p off
      where ?ptrWidth = knownNat
    passThroughConcreteRegion =
      case W4.asNat region of
        Nothing -> mzero
        Just _ -> return (C.LLVM.LLVMPointer region off)
    -- If the symbolic nat is (symbolically) equal to any of the entries in the
    -- rmap, we need to do the translation; otherwise, we pass it through
    mapSymbolicRegion = foldlM muxSymbolicRegion (C.LLVM.LLVMPointer region off) (Map.toList rmap)
    muxSymbolicRegion others (regionNum, basePtr) = do
      thisRegionNat <- W4.natLit sym (fromIntegral regionNum)
      isEqRegion <- W4.natEq sym thisRegionNat region
      adjustedPtr <- addOffset basePtr
      C.LLVM.muxLLVMPtr sym isEqRegion adjustedPtr others

data Goal = Goal
  { gAssumes :: [Term]
  , gShows :: Term
  , gLoc :: W4.ProgramLoc
  , gMessage :: C.SimErrorReason
  }

gGoal :: SharedContext -> Goal -> IO Prop
gGoal sc g0 = predicateToProp sc Universal [] =<< go (gAssumes g)
  where
  g = g0 { gAssumes = mapMaybe skip (gAssumes g0) }

  _shG = do putStrLn "Assuming:"
            mapM_ _shT (gAssumes g)
            putStrLn "Shows:"
            _shT (gShows g)


  _shT t = putStrLn ("  " ++ showTerm t)

  skip a = case asBool a of
             Just True -> Nothing
             _         -> Just a

  go xs = case xs of
            []     -> return (gShows g)
            a : as -> scImplies sc a =<< go as

getGoals :: Sym -> IO [Goal]
getGoals sym =
  do obls <- C.proofGoalsToList <$> C.getProofObligations sym
     mapM toGoal obls
  where
  toGoal (C.ProofGoal asmps g) =
    do as <- mapM (C.toSC sym) (toListOf (folded . C.labeledPred) asmps)
       p  <- C.toSC sym (g ^. C.labeledPred)
       let C.SimError loc msg = g^.C.labeledPredMsg
       return Goal { gAssumes = as
                   , gShows   = p
                   , gLoc     = loc
                   , gMessage = msg
                   }

newtype AArch32Sim a = AArch32Sim { unAArch32Sim :: StateT AArch32State IO a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadState AArch32State, MonadThrow)

data AArch32State = AArch32State
  { _aarch32Sym :: Sym
  , _aarch32Options :: Options
  , _aarch32SharedContext :: SharedContext
  , _aarch32CrucibleContext :: LLVMCrucibleContext LLVMArch
  , _aarch32ElfSymtab :: Elf.Symtab 32
  , _aarch32RelevantElf :: RelevantElf
  , _aarch32MethodSpec :: MS.CrucibleMethodSpecIR LLVM
  , _aarch32Mem :: Mem
  , _aarch32Regs :: Regs
  , _aarch32GlobalBase :: Ptr
  }
makeLenses ''AArch32State

runAArch32Sim :: AArch32State -> AArch32Sim a -> IO (a, AArch32State)
runAArch32Sim st m = runStateT (unAArch32Sim m) st

setReg ::
  (MonadIO m, MonadThrow m) =>
  Register ->
  C.RegValue Sym (C.LLVM.LLVMPointerType 32) ->
  Regs ->
  m Regs
setReg reg val regs = pure $ Macaw.AArch32.updateReg reg (C.RV . const val) regs

getReg ::
  (MonadIO m, MonadThrow m) =>
  Register ->
  Regs ->
  m (C.RegValue Sym (C.LLVM.LLVMPointerType 32))
getReg reg regs = case Macaw.AArch32.lookupReg reg regs of C.RV val -> pure val

-------------------------------------------------------------------------------
-- ** Entrypoint

llvm_verify_aarch32 ::
  Some LLVMModule {- ^ Module to associate with method spec -} ->
  FilePath {- ^ Path to ELF file -} ->
  String {- ^ Function's symbol in ELF file -} ->
  [(String, Integer)] {- ^ Global variable symbol names and sizes (in bytes) -} ->
  Bool {- ^ Whether to enable path satisfiability checking -} ->
  LLVMCrucibleSetupM () {- ^ Specification to verify against -} ->
  ProofScript SatResult {- ^ Tactic used to use when discharging goals -} ->
  TopLevel (SomeLLVM MS.CrucibleMethodSpecIR)
llvm_verify_aarch32 (Some (llvmModule :: LLVMModule x)) path nm globsyms checkSat setup tactic
  | Just Refl <- testEquality (C.LLVM.X86Repr $ knownNat @32) . C.LLVM.llvmArch $ modTrans llvmModule ^. C.LLVM.transContext = do
      let ?ptrWidth = knownNat @32
      let ?recordLLVMAnnotation = \_ _ -> return ()
      sc <- getSharedContext
      opts <- getOptions
      basic_ss <- getBasicSS
      sym <- liftIO $ C.newSAWCoreBackend W4.FloatRealRepr sc globalNonceGenerator
      halloc <- getHandleAlloc
      let mvar = C.LLVM.llvmMemVar . view C.LLVM.transContext $ modTrans llvmModule
      sfs <- liftIO $ Macaw.newSymFuns sym

      (C.SomeCFG cfg, elf, relf, addr, cfgs) <- liftIO $ buildCFG opts halloc path nm
      liftIO . print $ cfg
      addrInt <- if Macaw.segmentBase (Macaw.segoffSegment addr) == 0
        then pure . toInteger $ Macaw.segmentOffset (Macaw.segoffSegment addr) + Macaw.segoffOffset addr
        else fail $ mconcat ["Address of \"", nm, "\" is not an absolute address"]
      let maxAddr = addrInt + toInteger (Macaw.segmentSize $ Macaw.segoffSegment addr)

      let
        cc :: LLVMCrucibleContext x
        cc = LLVMCrucibleContext
          { _ccLLVMModule = llvmModule
          , _ccBackend = sym
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

      liftIO $ printOutLn opts Info "foo"

      emptyState <- liftIO $ initialState sym opts sc cc elf relf methodSpec globsyms maxAddr
      liftIO $ printOutLn opts Info "bar"
      (env, preState) <- liftIO . runAArch32Sim emptyState $ setupMemory globsyms
      liftIO $ printOutLn opts Info "baz"

      let
        funcLookup = Macaw.LookupFunctionHandle $ \st _mem regs -> do
          C.LLVM.LLVMPointer _base off <- getReg Macaw.ip_reg regs
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
                          %~ C.insertHandleMap (C.cfgHandle funcCFG) (C.UseCFG funcCFG $ C.postdomInfo funcCFG)
                        )
                    Nothing -> fail $ mconcat
                      [ "Unable to find CFG for function at address "
                      , show $ W4.ppExpr off
                      ]
        noExtraValidityPred _ _ _ _ = return Nothing
        ctx :: C.SimContext (Macaw.MacawSimulatorState Sym) Sym (Macaw.MacawExt Macaw.ARM)
        ctx = C.SimContext
              { C._ctxSymInterface = sym
              , C.ctxSolverProof = id
              , C.ctxIntrinsicTypes = C.LLVM.llvmIntrinsicTypes
              , C.simHandleAllocator = halloc
              , C.printHandle = stdout
              , C.extensionImpl =
                Macaw.macawExtensions (Macaw.aarch32MacawEvalFn sfs) mvar
                (mkGlobalMap . Map.singleton 0 $ preState ^. aarch32GlobalBase)
                funcLookup noExtraValidityPred
              , C._functionBindings = C.insertHandleMap (C.cfgHandle cfg) (C.UseCFG cfg $ C.postdomInfo cfg) C.emptyHandleMap
              , C._cruciblePersonality = Macaw.MacawSimulatorState
              , C._profilingMetrics = Map.empty
              }
        globals = C.insertGlobal mvar (preState ^. aarch32Mem) C.emptyGlobals
        macawStructRepr = C.StructRepr $ Macaw.crucArchRegTypes Macaw.aarch32MacawSymbolicFns
        initial = C.InitialState ctx globals C.defaultAbortHandler macawStructRepr
                  $ C.runOverrideSim macawStructRepr
                  $ Macaw.crucGenArchConstraints Macaw.aarch32MacawSymbolicFns
                  $ do
          r <- C.callCFG cfg . C.RegMap . singleton . C.RegEntry macawStructRepr $ preState ^. aarch32Regs
          globals' <- C.readGlobals
          mem' <- C.readGlobal mvar
          let finalState = preState
                { _aarch32Mem = mem'
                , _aarch32Regs = C.regValue r
                , _aarch32CrucibleContext = cc & ccLLVMGlobals .~ globals'
                }
          liftIO $ printOutLn opts Info
            "Examining specification to determine postconditions"
          liftIO . void . runAArch32Sim finalState $ assertPost globals' env (preState ^. aarch32Mem) (preState ^. aarch32Regs)
          pure $ C.regValue r

      liftIO $ printOutLn opts Info "Simulating function"

      psatf <-
         if checkSat then
           do f <- liftIO (C.pathSatisfiabilityFeature sym (C.considerSatisfiability sym))
              pure [C.genericToExecutionFeature f]
         else
           pure []

      let execFeatures = psatf

      liftIO $ C.executeCrucible execFeatures initial >>= \case
        C.FinishedResult{} -> pure ()
        C.AbortedResult{} -> printOutLn opts Warn "Warning: function never returns"
        C.TimeoutResult{} -> fail "Execution timed out"

      stats <- checkGoals sym opts sc tactic

      returnProof $ SomeLLVM (methodSpec & MS.csSolverStats .~ stats)
  | otherwise = fail "LLVM module must be AArch32"

--------------------------------------------------------------------------------
-- ** Computing the CFG

-- | Load the given ELF file and use Macaw to construct a Crucible CFG.
buildCFG ::
  Options ->
  C.HandleAllocator ->
  String {- ^ Path to ELF file -} ->
  String {- ^ Function's symbol in ELF file -} ->
  IO ( C.SomeCFG
       (Macaw.MacawExt Macaw.ARM)
       (EmptyCtx ::> Macaw.ArchRegStruct Macaw.ARM)
       (Macaw.ArchRegStruct Macaw.ARM)
     , Elf.ElfHeaderInfo 32
     , RelevantElf
     , Macaw.MemSegmentOff 32
     , Map
       (Macaw.MemSegmentOff 32)
       (C.SomeCFG
         (Macaw.MacawExt Macaw.ARM)
         (EmptyCtx ::> Macaw.ArchRegStruct Macaw.ARM)
         (Macaw.ArchRegStruct Macaw.ARM))
     )
buildCFG opts halloc path nm = do
  printOutLn opts Info $ mconcat ["Finding symbol for \"", nm, "\""]
  elf <- getElf path
  relf <- getRelevant elf
  (addr :: Macaw.MemSegmentOff 32) <-
    case findSymbols (symMap relf) . encodeUtf8 $ Text.pack nm of
      (addr:_) -> pure addr
      _ -> fail $ mconcat ["Could not find symbol \"", nm, "\""]
  printOutLn opts Info $ mconcat ["Found symbol at address ", show addr, ", building CFG"]
  let
    initialDiscoveryState =
      Macaw.emptyDiscoveryState (memory relf) (funSymMap relf) Macaw.arm_linux_info
      -- "inline" any function addresses that we happen to jump to
      & Macaw.trustedFunctionEntryPoints .~ Map.empty
    finalState = Macaw.cfgFromAddrsAndState initialDiscoveryState [addr] []
    finfos = finalState ^. Macaw.funInfo
  cfgs <- forM finfos $ \(Some finfo) ->
    Macaw.mkFunCFG Macaw.aarch32MacawSymbolicFns halloc
    (W4.functionNameFromText . decodeUtf8 $ Macaw.discoveredFunName finfo)
    posFn finfo

  case Map.lookup addr cfgs of
    Nothing -> throwAArch32 $ "Unable to discover CFG from address " <> show addr
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
  AArch32Constraints =>
  Sym ->
  Options ->
  SharedContext ->
  LLVMCrucibleContext LLVMArch ->
  Elf.ElfHeaderInfo 32 ->
  RelevantElf ->
  MS.CrucibleMethodSpecIR LLVM ->
  [(String, Integer)] {- ^ Global variable symbol names and sizes (in bytes) -} ->
  Integer {- ^ Minimum size of the global allocation (here, the end of the .text segment -} ->
  IO AArch32State
initialState sym opts sc cc elf relf ms globs maxAddr = do
  emptyMem <- C.LLVM.emptyMem C.LLVM.LittleEndian
  emptyRegs <- traverseWithIndex (freshRegister sym) C.knownRepr
  symTab <- case Elf.decodeHeaderSymtab elf of
    Nothing -> throwAArch32 "Elf file has no symbol table"
    Just (Left _err) -> throwAArch32 "Failed to decode symbol table"
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
  (base, mem) <- C.LLVM.doMalloc sym C.LLVM.GlobalAlloc C.LLVM.Immutable
    "globals" emptyMem sz align
  pure $ AArch32State
    { _aarch32Sym = sym
    , _aarch32Options = opts
    , _aarch32SharedContext = sc
    , _aarch32CrucibleContext = cc
    , _aarch32ElfSymtab = symTab
    , _aarch32RelevantElf = relf
    , _aarch32MethodSpec = ms
    , _aarch32Mem = mem
    , _aarch32Regs = emptyRegs
    , _aarch32GlobalBase = base
    }

--------------------------------------------------------------------------------
-- ** Precondition

-- | Given the method spec, build the initial memory, register map, and global map.
setupMemory ::
  AArch32Constraints =>
  [(String, Integer)] {- ^ Global variable symbol names and sizes (in bytes) -} ->
  AArch32Sim (Map MS.AllocIndex Ptr)
setupMemory globsyms = do
  setupGlobals globsyms

  liftIO $ putStrLn "1"

  -- Allocate a reasonable amount of stack (4 KiB + 1 qword for IP)
  allocateStack 4096

  liftIO $ putStrLn "2"

  ms <- use aarch32MethodSpec

  let
    tyenv = ms ^. MS.csPreState . MS.csAllocs
    nameEnv = MS.csTypeNames ms

  env <- foldlM assumeAllocation Map.empty . Map.assocs $ tyenv

  liftIO $ putStrLn "3"

  mapM_ (assumePointsTo env tyenv nameEnv) $ ms ^. MS.csPreState . MS.csPointsTos

  liftIO $ putStrLn "4"

  setArgs env tyenv nameEnv . fmap snd . Map.elems $ ms ^. MS.csArgBindings

  liftIO $ putStrLn "5"

  pure env

-- | Given an alist of symbol names and sizes (in bytes), allocate space and copy
-- the corresponding globals from the Macaw memory to the Crucible LLVM memory model.
setupGlobals ::
  AArch32Constraints =>
  [(String, Integer)] {- ^ Global variable symbol names and sizes (in bytes) -} ->
  AArch32Sim ()
setupGlobals globsyms = do
  sym <- use aarch32Sym
  mem <- use aarch32Mem
  relf <- use aarch32RelevantElf
  base <- use aarch32GlobalBase
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
  aarch32Mem .= mem'

-- | Allocate memory for the stack, and pushes a fresh pointer as the return
-- address.
allocateStack ::
  AArch32Constraints =>
  Integer {- ^ Stack size in bytes -} ->
  AArch32Sim ()
allocateStack szInt = do
  sym <- use aarch32Sym
  mem <- use aarch32Mem
  regs <- use aarch32Regs
  let align = C.LLVM.exponentToAlignment 4
  sz <- liftIO $ W4.bvLit sym knownNat $ BV.mkBV knownNat $ szInt + 8
  (base, mem') <- liftIO $ C.LLVM.doMalloc sym C.LLVM.HeapAlloc C.LLVM.Mutable
    "stack_alloc" mem sz align
  sn <- case W4.userSymbol "stack" of
    Left err -> throwAArch32 $ "Invalid symbol for stack: " <> show err
    Right sn -> pure sn
  aarch32Mem .= mem'
  finalRegs <- setReg (Macaw.ARMGlobalBV (ASL.knownGlobalRef @"_R13")) base regs
  aarch32Regs .= finalRegs

-- | Process an llvm_alloc statement, allocating the requested memory and
-- associating a pointer to that memory with the appropriate index.
assumeAllocation ::
  AArch32Constraints =>
  Map MS.AllocIndex Ptr ->
  (MS.AllocIndex, LLVMAllocSpec) {- ^ llvm_alloc statement -} ->
  AArch32Sim (Map MS.AllocIndex Ptr)
assumeAllocation env (i, LLVMAllocSpec mut _memTy align sz loc False) = do
  cc <- use aarch32CrucibleContext
  sym <- use aarch32Sym
  mem <- use aarch32Mem
  sz' <- liftIO $ resolveSAWSymBV cc knownNat sz
  (ptr, mem') <- liftIO $ C.LLVM.doMalloc sym C.LLVM.HeapAlloc mut
    (show $ W4.plSourceLoc loc) mem sz' align
  aarch32Mem .= mem'
  pure $ Map.insert i ptr env
assumeAllocation env _ = pure env
  -- no allocation is done for llvm_fresh_pointer
  -- TODO: support llvm_fresh_pointer in x86 verification

-- | Process an llvm_points_to statement, writing some SetupValue to a pointer.
assumePointsTo ::
  AArch32Constraints =>
  Map MS.AllocIndex Ptr {- ^ Associates each AllocIndex with the corresponding allocation -} ->
  Map MS.AllocIndex LLVMAllocSpec {- ^ Associates each AllocIndex with its specification -} ->
  Map MS.AllocIndex C.LLVM.Ident {- ^ Associates each AllocIndex with its name -} ->
  LLVMPointsTo LLVMArch {- ^ llvm_points_to statement from the precondition -} ->
  AArch32Sim ()
assumePointsTo env tyenv nameEnv (LLVMPointsTo _ cond tptr tptval) = do
  when (isJust cond) $ throwAArch32 "unsupported x86_64 command: llvm_conditional_points_to"
  tval <- checkConcreteSizePointsToValue tptval
  sym <- use aarch32Sym
  cc <- use aarch32CrucibleContext
  mem <- use aarch32Mem
  ptr <- resolvePtrSetupValue env tyenv tptr
  val <- liftIO $ resolveSetupVal cc mem env tyenv Map.empty tval
  storTy <- liftIO $ C.LLVM.toStorableType =<< typeOfSetupValue cc tyenv nameEnv tval
  mem' <- liftIO $ C.LLVM.storeConstRaw sym mem ptr storTy C.LLVM.noAlignment val
  aarch32Mem .= mem'

resolvePtrSetupValue ::
  AArch32Constraints =>
  Map MS.AllocIndex Ptr ->
  Map MS.AllocIndex LLVMAllocSpec ->
  MS.SetupValue LLVM ->
  AArch32Sim Ptr
resolvePtrSetupValue env tyenv tptr = do
  sym <- use aarch32Sym
  cc <- use aarch32CrucibleContext
  mem <- use aarch32Mem
  symTab <- use aarch32ElfSymtab
  base <- use aarch32GlobalBase
  case tptr of
    MS.SetupGlobal () nm -> case
      (Vector.!? 0)
      . Vector.filter (\e -> Elf.steName e == encodeUtf8 (Text.pack nm))
      $ Elf.symtabEntries symTab of
      Nothing -> throwAArch32 $ mconcat ["Global symbol \"", nm, "\" not found"]
      Just entry -> do
        let addr = fromIntegral $ Elf.steValue entry
        liftIO $ C.LLVM.doPtrAddOffset sym mem base =<< W4.bvLit sym knownNat (BV.mkBV knownNat addr)
    _ -> liftIO $ C.LLVM.unpackMemValue sym (C.LLVM.LLVMPointerRepr $ knownNat @32)
         =<< resolveSetupVal cc mem env tyenv Map.empty tptr

checkConcreteSizePointsToValue :: LLVMPointsToValue LLVMArch -> AArch32Sim (MS.SetupValue LLVM)
checkConcreteSizePointsToValue = \case
  ConcreteSizeValue val -> return val
  SymbolicSizeValue{} -> throwAArch32 "unsupported x86_64 command: llvm_points_to_array_prefix"

-- | Write each SetupValue passed to llvm_execute_func to the appropriate
-- x86_64 register from the calling convention.
setArgs ::
  AArch32Constraints =>
  Map MS.AllocIndex Ptr {- ^ Associates each AllocIndex with the corresponding allocation -} ->
  Map MS.AllocIndex LLVMAllocSpec {- ^ Associates each AllocIndex with its specification -} ->
  Map MS.AllocIndex C.LLVM.Ident {- ^ Associates each AllocIndex with its name -} ->
  [MS.SetupValue LLVM] {- ^ Arguments passed to llvm_execute_func -} ->
  AArch32Sim ()
setArgs env tyenv nameEnv args
  | length args > length argRegs = throwAArch32 "More arguments than would fit into general-purpose registers"
  | otherwise = do
      sym <- use aarch32Sym
      cc <- use aarch32CrucibleContext
      mem <- use aarch32Mem
      let
        setRegSetupValue rs (reg, sval) = typeOfSetupValue cc tyenv nameEnv sval >>= \ty ->
          case ty of
            C.LLVM.PtrType _ -> do
              val <- C.LLVM.unpackMemValue sym (C.LLVM.LLVMPointerRepr $ knownNat @32)
                =<< resolveSetupVal cc mem env tyenv nameEnv sval
              setReg reg val rs
            C.LLVM.IntType 32 -> do
              val <- C.LLVM.unpackMemValue sym (C.LLVM.LLVMPointerRepr $ knownNat @32)
                =<< resolveSetupVal cc mem env tyenv nameEnv sval
              setReg reg val rs
            C.LLVM.IntType _ -> do
              C.LLVM.LLVMValInt base off <- resolveSetupVal cc mem env tyenv nameEnv sval
              case testLeq (incNat $ W4.bvWidth off) (knownNat @32) of
                Nothing -> fail "Argument bitvector does not fit in a single general-purpose register"
                Just LeqProof -> do
                  off' <- W4.bvZext sym (knownNat @32) off
                  val <- C.LLVM.unpackMemValue sym (C.LLVM.LLVMPointerRepr $ knownNat @32)
                    $ C.LLVM.LLVMValInt base off'
                  setReg reg val rs
            _ -> fail "Argument does not fit into a single general-purpose register"
      regs <- use aarch32Regs
      newRegs <- liftIO . foldlM setRegSetupValue regs $ zip argRegs args
      aarch32Regs .= newRegs
  where
    argRegs =
      [ Macaw.ARMGlobalBV (ASL.knownGlobalRef @"_R0")
      , Macaw.ARMGlobalBV (ASL.knownGlobalRef @"_R1")
      , Macaw.ARMGlobalBV (ASL.knownGlobalRef @"_R2")
      , Macaw.ARMGlobalBV (ASL.knownGlobalRef @"_R3")
      ]

--------------------------------------------------------------------------------
-- ** Postcondition

-- | Assert the postcondition for the spec, given the final memory and register map.
assertPost ::
  AArch32Constraints =>
  C.SymGlobalState Sym ->
  Map MS.AllocIndex Ptr ->
  Mem {- ^ The state of memory before simulation -} ->
  Regs {- ^ The state of the registers before simulation -} ->
  AArch32Sim ()
assertPost globals env premem preregs = do
  sym <- use aarch32Sym
  opts <- use aarch32Options
  sc <- use aarch32SharedContext
  cc <- use aarch32CrucibleContext
  ms <- use aarch32MethodSpec
  postregs <- use aarch32Regs
  let
    tyenv = ms ^. MS.csPreState . MS.csAllocs
    nameEnv = MS.csTypeNames ms

  expectedIP <- getReg (Macaw.ARMGlobalBV (ASL.knownGlobalRef @"_R14")) preregs
  actualIP <- getReg Macaw.ip_reg postregs
  correctRetAddr <- liftIO $ C.LLVM.ptrEq sym C.LLVM.PtrWidth actualIP expectedIP
  liftIO . C.addAssertion sym . C.LabeledPred correctRetAddr . C.SimError W4.initializationLoc
    $ C.AssertFailureSimError "Instruction pointer not set to return address" ""

  prersp <- getReg (Macaw.ARMGlobalBV (ASL.knownGlobalRef @"_R13")) preregs
  postrsp <- getReg (Macaw.ARMGlobalBV (ASL.knownGlobalRef @"_R13")) postregs
  correctStack <- liftIO $ C.LLVM.ptrEq sym C.LLVM.PtrWidth prersp postrsp
  liftIO $ C.addAssertion sym . C.LabeledPred correctStack . C.SimError W4.initializationLoc
    $ C.AssertFailureSimError "Stack not preserved" ""

  returnMatches <- case (ms ^. MS.csRetValue, ms ^. MS.csRet) of
    (Just expectedRet, Just retTy) -> do
      postRAX <- C.LLVM.ptrToPtrVal <$> getReg (Macaw.ARMGlobalBV (ASL.knownGlobalRef @"_R0")) postregs
      case (postRAX, C.LLVM.memTypeBitwidth retTy) of
        (C.LLVM.LLVMValInt base off, Just retTyBits) -> do
          let
            truncateRAX :: forall r. NatRepr r -> AArch32Sim (C.LLVM.LLVMVal Sym)
            truncateRAX rsz =
              case (testLeq (knownNat @1) rsz, testLeq rsz (W4.bvWidth off)) of
                (Just LeqProof, Just LeqProof) ->
                  case testStrictLeq rsz (W4.bvWidth off) of
                    Left LeqProof -> do
                      offTrunc <- liftIO $ W4.bvTrunc sym rsz off
                      pure $ C.LLVM.LLVMValInt base offTrunc
                    _ -> pure $ C.LLVM.LLVMValInt base off
                _ -> throwAArch32 "Width of return type is zero bits"
          postRAXTrunc <- viewSome truncateRAX (mkNatRepr retTyBits)
          pure [LO.matchArg opts sc cc ms MS.PostState postRAXTrunc retTy expectedRet]
        _ -> throwAArch32 $ "Invalid return type: " <> show (C.LLVM.ppMemType retTy)
    _ -> pure []

  pointsToMatches <- forM (ms ^. MS.csPostState . MS.csPointsTos)
    $ assertPointsTo env tyenv nameEnv

  let setupConditionMatches = fmap
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
    , setupConditionMatches
    ]
  st <- case result of
    Left err -> throwAArch32 $ show err
    Right (_, st) -> pure st
  liftIO . forM_ (view LO.osAsserts st) $ \(W4.LabeledPred p r) ->
    C.addAssertion sym $ C.LabeledPred p r

-- | Assert that a points-to postcondition holds.
assertPointsTo ::
  AArch32Constraints =>
  Map MS.AllocIndex Ptr {- ^ Associates each AllocIndex with the corresponding allocation -} ->
  Map MS.AllocIndex LLVMAllocSpec {- ^ Associates each AllocIndex with its specification -} ->
  Map MS.AllocIndex C.LLVM.Ident {- ^ Associates each AllocIndex with its name -} ->
  LLVMPointsTo LLVMArch {- ^ llvm_points_to statement from the precondition -} ->
  AArch32Sim (LLVMOverrideMatcher md ())
assertPointsTo env tyenv nameEnv (LLVMPointsTo _ cond tptr tptexpected) = do
  when (isJust cond) $ throwAArch32 "unsupported x86_64 command: llvm_conditional_points_to"
  texpected <- checkConcreteSizePointsToValue tptexpected
  sym <- use aarch32Sym
  opts <- use aarch32Options
  sc <- use aarch32SharedContext
  cc <- use aarch32CrucibleContext
  ms <- use aarch32MethodSpec
  mem <- use aarch32Mem
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
  TopLevel SolverStats
checkGoals sym opts sc tactic = do
  gs <- liftIO $ getGoals sym
  liftIO . printOutLn opts Info $ mconcat
    [ "Simulation finished, running solver on "
    , show $ length gs
    , " goals"
    ]
  stats <- forM (zip [0..] gs) $ \(n, g) -> do
    term <- liftIO $ gGoal sc g
    let proofgoal = ProofGoal n "vc" (show $ gMessage g) term
    r <- evalStateT tactic $ startProof proofgoal
    case r of
      Unsat stats -> return stats
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
  return (mconcat stats)
