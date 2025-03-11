{-# Language DataKinds, OverloadedStrings #-}
{-# Language RankNTypes, TypeOperators #-}
{-# Language PatternSynonyms #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE GADTs #-}
module SAWScript.X86
  ( Options(..)
  , proof
  , proofWithOptions
  , linuxInfo
  , bsdInfo
  , Fun(..)
  , Goal(..)
  , gGoal
  , gLoc
  , getGoals
  , X86Error(..)
  , X86Unsupported(..)
  , SharedContext
  , CallHandler
  , Sym
  , RelevantElf(..)
  , getElf
  , getRelevant
  , findSymbols
  , posFn
  , loadGlobal
  ) where


import Control.Lens ((^.))
import Control.Exception(Exception(..),throwIO)
import Control.Monad.IO.Class(liftIO)

import qualified Data.BitVector.Sized as BV
import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import           Data.IORef
import qualified Data.Map as Map
import qualified Data.Text as Text
import           Data.Text.Encoding(decodeUtf8)
import           System.IO(hFlush,stdout)
import           Data.Maybe(mapMaybe, fromMaybe)

-- import Text.PrettyPrint.ANSI.Leijen(pretty)

import qualified Data.ElfEdit as Elf

import Data.Parameterized.Some(Some(..))
import Data.Parameterized.Context(EmptyCtx,(::>),singleton)

-- What4
import What4.Interface(asNat,asBV)
import qualified What4.Interface as W4
import qualified What4.Config as W4
import What4.FunctionName(functionNameFromText)
import What4.ProgramLoc(ProgramLoc,Position(OtherPos))

-- Crucible
import Lang.Crucible.Analysis.Postdom (postdomInfo)
import Lang.Crucible.CFG.Core(SomeCFG(..), TypeRepr(..), cfgHandle)
import Lang.Crucible.CFG.Common(GlobalVar)
import Lang.Crucible.Simulator.RegMap(regValue, RegMap(..), RegEntry(..))
import Lang.Crucible.Simulator.RegValue(RegValue'(..))
import Lang.Crucible.Simulator.GlobalState(insertGlobal,emptyGlobals)
import Lang.Crucible.Simulator.Operations(defaultAbortHandler)
import Lang.Crucible.Simulator.OverrideSim(runOverrideSim, callCFG, readGlobal)
import Lang.Crucible.Simulator.EvalStmt(executeCrucible)
import Lang.Crucible.Simulator.ExecutionTree
          (ExecResult(..), SimContext(..), FnState(..)
          , ExecState(InitialState)
          , FunctionBindings(..)
          )
import Lang.Crucible.Simulator.SimError(SimError(..), SimErrorReason)
import Lang.Crucible.Backend
          (getProofObligations,ProofGoal(..),labeledPredMsg,labeledPred,goalsToList
          ,assumptionsPred,IsSymBackend(..),SomeBackend(..),HasSymInterface(..))
import Lang.Crucible.FunctionHandle(HandleAllocator,newHandleAllocator,insertHandleMap,emptyHandleMap)


-- Crucible LLVM
import SAWCentral.Crucible.LLVM.CrucibleLLVM
  (Mem, ppPtr, pattern LLVMPointer, bytesToInteger)
import Lang.Crucible.LLVM.Intrinsics(llvmIntrinsicTypes)
import Lang.Crucible.LLVM.MemModel (mkMemVar)
import qualified Lang.Crucible.LLVM.MemModel as Crucible

-- Macaw
import Data.Macaw.Architecture.Info(ArchitectureInfo)
import Data.Macaw.Discovery(analyzeFunction)
import Data.Macaw.Discovery.State(FunctionExploreReason(UserRequest)
                                 , emptyDiscoveryState, AddrSymMap)
import Data.Macaw.Memory( Memory, MemSegment(..), MemSegmentOff(..)
                        , segmentBase, segmentOffset
                        , addrOffset, memWordToUnsigned
                        , segoffAddr, incAddr
                        , readWord8, readWord16le, readWord32le, readWord64le)
import Data.Macaw.Memory.ElfLoader( LoadOptions(..)
                                  , memoryForElfAllSymbols
                                  , memoryForElf
                                  , MemSymbol(..)
                                  )
import Data.Macaw.Symbolic( ArchRegStruct
                          , mkFunCFG
                          , GlobalMap
                          , MacawSimulatorState(..)
                          , macawExtensions
                          , MemModelConfig(..)
                          , unsupportedSyscalls
                          , defaultMacawArchStmtExtensionOverride
                          )
import qualified Data.Macaw.Symbolic as Macaw ( LookupFunctionHandle(..) )
import Data.Macaw.Symbolic( MacawExt
                                  , MacawFunctionArgs
                                  )
import Data.Macaw.Symbolic.Backend(MacawSymbolicArchFunctions(..), crucArchRegTypes)
import Data.Macaw.X86(X86Reg(..), x86_64_linux_info,x86_64_freeBSD_info)
import Data.Macaw.X86.ArchTypes(X86_64)
import Data.Macaw.X86.Symbolic
  ( x86_64MacawSymbolicFns, x86_64MacawEvalFn, newSymFuns
  , lookupX86Reg
  )
import Data.Macaw.X86.Crucible(SymFuns(..))


-- Saw Core
import Verifier.SAW.SharedTerm(Term, mkSharedContext, SharedContext, scImplies)
import Verifier.SAW.Term.Pretty(showTerm)
import Verifier.SAW.Recognizer(asBool)

import Verifier.SAW.Simulator.What4.ReturnTrip (sawRegisterSymFunInterp, toSC, saw_ctx)

-- Cryptol Verifier
import Verifier.SAW.CryptolEnv(CryptolEnv,initCryptolEnv,loadCryptolModule,defaultPrimitiveOptions)
import Verifier.SAW.Cryptol.Prelude(scLoadPreludeModule,scLoadCryptolModule)

-- SAWScript
import SAWScript.X86Spec hiding (Prop)
import SAWScript.Proof(boolToProp, Prop)
import SAWCentral.Crucible.Common.MethodSpec (ConditionMetadata(..))
import SAWCentral.Crucible.Common.Override (MetadataMap)
import SAWCentral.Crucible.Common
  ( newSAWCoreBackend, newSAWCoreExprBuilder
  , sawCoreState, SomeOnlineBackend(..)
  , PathSatSolver
  )


--------------------------------------------------------------------------------
-- Input Options

-- | What we'd like done, plus additional information from the "outside world".
data Options = Options
  { fileName  :: FilePath
    -- ^ Name of the elf file to process.

  , function :: Fun
    -- ^ Function that we'd like to extract.

  , archInfo :: ArchitectureInfo X86_64
    -- ^ Architectural flavor.  See "linuxInfo" and "bsdInfo".

  , backend :: SomeBackend Sym
    -- ^ The Crucible backend to use.

  , allocator :: HandleAllocator
    -- ^ The handle allocator used to allocate @memvar@

  , memvar :: GlobalVar Mem
    -- ^ The global variable storing the heap

  , cryEnv :: CryptolEnv

  , extraGlobals :: [(ByteString,Integer,Unit)]
    -- ^ Additional globals to auto-load from the ELF file
  }

linuxInfo :: ArchitectureInfo X86_64
linuxInfo = x86_64_linux_info

bsdInfo :: ArchitectureInfo X86_64
bsdInfo = x86_64_freeBSD_info


--------------------------------------------------------------------------------
-- Spec

data Fun = Fun { funName :: ByteString, funSpec :: FunSpec }


--------------------------------------------------------------------------------

type CallHandler = Sym -> Macaw.LookupFunctionHandle (MacawSimulatorState Sym) Sym X86_64

-- | Run a top-level proof.
-- Should be used when making a standalone proof script.
proof ::
  (FilePath -> IO ByteString) ->
  PathSatSolver ->
  ArchitectureInfo X86_64 ->
  FilePath {- ^ ELF binary -} ->
  Maybe FilePath {- ^ Cryptol spec, if any -} ->
  [(ByteString,Integer,Unit)] ->
  Fun ->
  IO (SharedContext,Integer,[Goal])
proof fileReader pss archi file mbCry globs fun =
  do sc  <- mkSharedContext
     halloc  <- newHandleAllocator
     scLoadPreludeModule sc
     scLoadCryptolModule sc
     sym <- newSAWCoreExprBuilder sc False
     SomeOnlineBackend bak <- newSAWCoreBackend pss sym
     let ?fileReader = fileReader
     cenv <- loadCry sym mbCry
     mvar <- mkMemVar "saw_x86:llvm_memory" halloc
     proofWithOptions Options
       { fileName = file
       , function = fun
       , archInfo = archi
       , backend = SomeBackend bak
       , allocator = halloc
       , memvar = mvar
       , cryEnv = cenv
       , extraGlobals = globs
       }

-- | Run a proof using the given backend.
-- Useful for integrating with other tool.
proofWithOptions :: Options -> IO (SharedContext,Integer,[Goal])
proofWithOptions opts =
  do let path = fileName opts
     elf <- getRelevant path =<< getElf path
     translate opts elf (function opts)

-- | Add interpretations for the symbolic functions, by looking
-- them up in the Cryptol environment.  There should be definitions
-- for "aesenc", "aesenclast", and "clmul".
registerSymFuns :: Opts -> IO (SymFuns Sym)
registerSymFuns opts =
  do let sym = optsSym opts
     st  <- sawCoreState sym
     sfs <- newSymFuns sym

     sawRegisterSymFunInterp st (fnAesEnc     sfs) (mk2 "aesenc")
     sawRegisterSymFunInterp st (fnAesEncLast sfs) (mk2 "aesenclast")
     sawRegisterSymFunInterp st (fnClMul      sfs) (mk2 "clmul")

     return sfs

  where
  err nm xs =
    unlines [ "Type error in call to " ++ show (nm::String) ++ ":"
            , "*** Expected: 2 arguments"
            , "*** Given:    " ++ show (length xs) ++ " arguments"
            ]

  mk2 nm _sc xs = case xs of
                    [_,_] -> cryTerm opts nm xs
                    _     -> fail (err nm xs)

--------------------------------------------------------------------------------
-- ELF

-- | These are the parts of the ELF file that we care about.
data RelevantElf = RelevantElf
  { memory    :: Memory 64
  , funSymMap :: AddrSymMap 64
  , symMap    :: AddrSymMap 64
  }

-- | Parse an elf file.
getElf :: FilePath -> IO (Elf.ElfHeaderInfo 64)
getElf path =
  do bs <- BS.readFile path
     case Elf.decodeElfHeaderInfo bs of
       Left (off, msg) ->
           malformed path $ "Invalid ELF header at offset " ++ show off ++
                            ": " ++ msg
       Right (Elf.SomeElf hdr) ->
           let elfmachine = Elf.headerMachine (Elf.header hdr)
               elfclass = Elf.headerClass (Elf.header hdr)
           in case (elfmachine, elfclass) of
               (Elf.EM_X86_64, Elf.ELFCLASS64) ->
                   pure hdr
               (Elf.EM_X86_64, _) ->
                   -- Note that 32-bit x86 is a different machine; if
                   -- we do see a 32-bit x86_64 bin though it might be
                   -- one of the several 32-on-64 ABIs (akin to mips
                   -- N32) that haven't caught on, so call it
                   -- unsupported rather than malformed.
                   unsupported path $ "Unexpected ELF class " ++ show elfclass
               (_, _) ->
                   unsupported path $ "Unexpected ELF machine " ++ show elfmachine


-- | Extract a Macaw "memory" from an ELF file and resolve symbols.
getRelevant :: FilePath -> Elf.ElfHeaderInfo 64 -> IO RelevantElf
getRelevant path elf =
  case (memoryForElf opts elf, memoryForElfAllSymbols opts elf) of
    (Left err, _) -> malformed path err
    (_, Left err) -> malformed path err
    (Right (mem, faddrs, _warnings, _errs), Right (_, addrs, _, _)) ->
      do let toEntry msym = (memSymbolStart msym, memSymbolName msym)
         return RelevantElf { memory = mem
                            , funSymMap = Map.fromList (map toEntry faddrs)
                            , symMap = Map.fromList (map toEntry addrs)
                            }

  where
  -- XXX: What options do we want?
  opts = LoadOptions { loadOffset = Just 0
                     }




-- | Find the address(es) of a symbol by name.
findSymbols :: AddrSymMap 64 -> ByteString -> [ MemSegmentOff 64 ]
findSymbols addrs nm = Map.findWithDefault [] nm invertedMap
  where
  invertedMap = Map.fromListWith (++) [ (y,[x]) | (x,y) <- Map.toList addrs ]

-- | Find the single address of a symbol, or fail.
findSymbol :: FilePath -> AddrSymMap 64 -> ByteString -> IO (MemSegmentOff 64)
findSymbol path addrs nm =
  case findSymbols addrs nm of
    [addr] -> return $! addr
    []     -> malformed path ("Could not find function " ++ show nm)
    _      -> malformed path ("Multiple definitions for " ++ show nm)


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
                Bytes  -> check (readWord8    mem a)
                Words  -> check (readWord16le mem a)
                DWords -> check (readWord32le mem a)
                QWords -> check (readWord64le mem a)
                _      -> err ("unsuported global size: " ++ show u)

  nextAddr = incAddr (bytesToInteger (1 *. u))

  addrsFor o = take (fromIntegral n) (iterate nextAddr o)

  check :: (Show b, Integral a) => Either b a -> IO Integer
  check res = case res of
                Left e  -> err (show e)
                Right a -> return (fromIntegral a)


  loadLoc off = do let start = segoffAddr off
                       a  = memWordToUnsigned (addrOffset start)
                   is <- mapM readOne (addrsFor start)
                   return (sname, a, u, is)

  err :: [Char] -> IO a
  err xs = fail $ unlines
                    [ "Failed to load global."
                    , "*** Global: " ++ show nm
                    , "*** Error: " ++ xs
                    ]


-- | The position associated with a specific location.
posFn :: MemSegmentOff 64 -> Position
posFn = OtherPos . Text.pack . show


-- | Load a file with Cryptol decls.
loadCry ::
  (?fileReader :: FilePath -> IO ByteString) =>
  Sym -> Maybe FilePath ->
  IO CryptolEnv
loadCry sym mb =
  do sc <- saw_ctx <$> sawCoreState sym
     env <- initCryptolEnv sc
     case mb of
       Nothing   -> return env
       Just file -> snd <$> loadCryptolModule sc defaultPrimitiveOptions env file


--------------------------------------------------------------------------------
-- Translation

callHandler :: Overrides -> CallHandler
callHandler callMap sym = Macaw.LookupFunctionHandle $ \st mem regs -> do
  case lookupX86Reg X86_IP regs of
    Just (RV ptr) | LLVMPointer base off <- ptr ->
      case (asNat base, BV.asUnsigned <$> asBV off) of
        (Just b, Just o) ->
           case Map.lookup (b,o) callMap of
             Just h  -> case h sym of
                          Macaw.LookupFunctionHandle f -> f st mem regs
             Nothing ->
               fail ("No over-ride for function: " ++ show (ppPtr ptr))

        _ -> fail ("Non-static call: " ++ show (ppPtr ptr))

    _ -> fail "[Bug?] Failed to obtain the value of the IP register."


-- | Verify the given function.  The function matches it sepcification,
-- as long as the returned goals can be discharged.
-- Returns the shared context and the goals (from the Sym)
-- and the integer is the (aboslute) address of the function.
translate ::
  Options -> RelevantElf -> Fun -> IO (SharedContext, Integer, [Goal])
translate opts elf fun =
  do let name = funName fun
     sayLn ("Translating function: " ++ BSC.unpack name)

     -- TODO? do we need to pass in the mdMap into more places in this mode?
     mdMap <- newIORef mempty

     let ?memOpts = Crucible.defaultMemOptions
     let ?recordLLVMAnnotation = \_ _ _ -> return ()

     let bak   = backend opts
         sym   = case bak of SomeBackend b -> backendGetSym b
         sopts = Opts { optsBackend = bak, optsCry = cryEnv opts, optsMvar = memvar opts }

     sfs <- registerSymFuns sopts

     (globs,st,checkPost) <-
        case funSpec fun of
          NewStyle mkSpec debug ->
            do gss <- mapM (loadGlobal elf) (extraGlobals opts)
               spec0 <- mkSpec (cryEnv opts)
               let spec = spec0 {specGlobsRO = concat (specGlobsRO spec0:gss)}
               (gs,st,po) <- verifyMode spec sopts
               debug st
               return (gs,st,\st1 -> debug st1 >> po st1)

     addr <- doSim opts elf sfs name globs st checkPost

     gs <- getGoals bak mdMap
     sc <- saw_ctx <$> sawCoreState sym
     return (sc, addr, gs)


setSimulatorVerbosity :: (W4.IsSymExprBuilder sym) => Int -> sym -> IO ()
setSimulatorVerbosity verbosity sym = do
  verbSetting <- W4.getOptionSetting W4.verbosity (W4.getConfiguration sym)
  _ <- W4.setOpt verbSetting (toInteger verbosity)
  return ()



doSim ::
  (?memOpts::Crucible.MemOptions, Crucible.HasLLVMAnn Sym) =>
  Options ->
  RelevantElf ->
  SymFuns Sym ->
  ByteString ->
  (GlobalMap Sym Crucible.Mem 64, Overrides) ->
  State ->
  (State -> IO ()) ->
  IO Integer
doSim opts elf sfs name (globs,overs) st checkPost =
  do say "  Looking for address... "
     let path = fileName opts
     addr <- findSymbol path (symMap elf) name
     -- addr :: MemSegmentOff 64
     let addrInt =
           let seg :: MemSegment 64
               seg = segoffSegment addr
           in if segmentBase seg == 0
                 then toInteger (segmentOffset seg + segoffOffset addr)
                 else error "  Not an absolute address"

     sayLn (show addr)

     SomeCFG cfg <- statusBlock "  Constructing CFG... "
                    $ makeCFG opts elf name addr

     -- writeFile "XXX.hs" (show cfg)

     let sym  = case backend opts of SomeBackend bak -> backendGetSym bak
         mvar = memvar opts

     setSimulatorVerbosity 0 sym

     execResult <- statusBlock "  Simulating... " $ do
       let crucRegTypes = crucArchRegTypes x86
       let macawStructRepr = StructRepr crucRegTypes
       -- The global pointer validity predicate is required if your memory
       -- representation has gaps that are not supposed to be mapped and you
       -- want to verify that no memory accesses touch unmapped regions.
       --
       -- The memory setup for this verifier does not have that problem, and
       -- thus does not need any additional validity predicates.
       let noExtraValidityPred _ _ _ _ = return Nothing
       let archEvalFns = x86_64MacawEvalFn sfs defaultMacawArchStmtExtensionOverride
       let lookupSyscall = unsupportedSyscalls "saw-script"
       let mmConf = MemModelConfig
                      { globalMemMap = globs
                      , lookupFunctionHandle = callHandler overs sym
                      , lookupSyscallHandle = lookupSyscall
                      , mkGlobalPointerValidityAssertion = noExtraValidityPred
                      , resolvePointer = pure
                      , concreteImmutableGlobalRead = \_ _ -> pure Nothing
                      , lazilyPopulateGlobalMem = \_ _ -> pure
                      }
       let ctx :: SimContext (MacawSimulatorState Sym) Sym (MacawExt X86_64)
           ctx = SimContext { _ctxBackend = backend opts
                              , ctxSolverProof = \a -> a
                              , ctxIntrinsicTypes = llvmIntrinsicTypes
                              , simHandleAllocator = allocator opts
                              , printHandle = stdout
                              , extensionImpl = macawExtensions archEvalFns mvar mmConf
                              , _functionBindings = FnBindings $
                                insertHandleMap (cfgHandle cfg) (UseCFG cfg (postdomInfo cfg)) emptyHandleMap
                              , _cruciblePersonality = MacawSimulatorState
                              , _profilingMetrics = Map.empty
                              }
       let initGlobals = insertGlobal mvar (stateMem st) emptyGlobals

       executeCrucible []
         $ InitialState ctx initGlobals defaultAbortHandler macawStructRepr
         $ runOverrideSim macawStructRepr
         $ do let args :: RegMap Sym (MacawFunctionArgs X86_64)
                  args = RegMap (singleton (RegEntry macawStructRepr
                                                      (stateRegs st)))
              crucGenArchConstraints x86 $
                  do r <- callCFG cfg args
                     mem <- readGlobal mvar
                     let regs = regValue r
                     let sta = State { stateMem = mem, stateRegs = regs }
                     liftIO (checkPost sta)
                     pure regs

     case execResult of
       FinishedResult {} -> pure ()
       AbortedResult {}  -> sayLn "[Warning] Function never returns"
       TimeoutResult {}  -> timeout path

     return addrInt


type TheCFG = SomeCFG (MacawExt X86_64)
                      (EmptyCtx ::> ArchRegStruct X86_64)
                      (ArchRegStruct X86_64)


-- | Generate a CFG for the function at the given address.
makeCFG ::
  Options ->
  RelevantElf ->
  ByteString ->
  MemSegmentOff 64 ->
  IO TheCFG
makeCFG opts elf name addr =
  do (_,Some funInfo) <- return $ analyzeFunction addr UserRequest empty
     -- writeFile "MACAW.cfg" (show (pretty funInfo))
     mkFunCFG x86 (allocator opts) cruxName posFn funInfo
  where
  txtName   = decodeUtf8 name
  cruxName  = functionNameFromText txtName
  empty = emptyDiscoveryState (memory elf) (funSymMap elf) (archInfo opts)



--------------------------------------------------------------------------------
-- Goals

data Goal = Goal
  { gAssumes :: [ Term ]              -- ^ Assuming these
  , gShows   :: Term                  -- ^ We need to show this
  , gMd      :: ConditionMetadata     -- ^ Metadata about the goal
  , gMessage :: SimErrorReason        -- ^ We should say this if the proof fails
  }

gLoc :: Goal -> ProgramLoc
gLoc = conditionLoc . gMd

-- | The proposition that needs proving (i.e., assumptions imply conclusion)
gGoal :: SharedContext -> Goal -> IO Prop
gGoal sc g0 = boolToProp sc [] =<< go (gAssumes g)
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

getGoals :: SomeBackend Sym -> IORef MetadataMap -> IO [Goal]
getGoals (SomeBackend bak) mdMap =
  do finalMdMap <- readIORef mdMap
     obls <- maybe [] goalsToList <$> getProofObligations bak
     st <- sawCoreState sym
     mapM (toGoal st finalMdMap) obls
  where
  sym = backendGetSym bak

  toGoal st finalMdMap (ProofGoal asmps g) =
    do a1 <- toSC sym st =<< assumptionsPred sym asmps
       p  <- toSC sym st (g ^. labeledPred)
       let SimError loc msg = g^.labeledPredMsg
       let defaultMd = ConditionMetadata
                       { conditionLoc = loc
                       , conditionTags = mempty
                       , conditionType = "safety assertion"
                       , conditionContext = ""
                       }
       let md = fromMaybe defaultMd $
                  do ann <- W4.getAnnotation sym (g^.labeledPred)
                     Map.lookup ann finalMdMap
       return Goal { gAssumes = [a1]
                   , gShows   = p
                   , gMd      = md
                   , gMessage = msg
                   }

instance Show Goal where
  showsPrec _ g = showString "Goal { gAssumes = "
                . showList (map (show . showTerm) (gAssumes g))
                . showString ", gShows = " . shows (showTerm (gShows g))
                . showString ", gLoc = " . shows (gLoc g)
                . showString ", gMessage = " . shows (show (gMessage g))
                . showString " }"


--------------------------------------------------------------------------------
-- Specialize the generic functions to the X86.

-- | All functions related to X86.
x86 :: MacawSymbolicArchFunctions X86_64
x86 = x86_64MacawSymbolicFns



--------------------------------------------------------------------------------
-- Calling Convention
-- see: http://refspecs.linuxfoundation.org/elf/x86_64-abi-0.99.pdf
-- Need to preserve: %rbp, %rbx, %r12--%r15
-- Preserve control bits in MXCSR
-- Preserve x87 control word.
-- On entry:
--   CPU is in x87 mode
--   DF in $rFLAGS is clear one entry and return.
-- "Red zone" 128 bytes past the end of the stack %rsp.
--    * not modified by interrupts


--------------------------------------------------------------------------------
-- Errors

-- | Exception for hitting an unsupported object or feature. The arguments
--   are the filename we were looking at, and a message.
data X86Unsupported = X86Unsupported FilePath String deriving Show

-- | Exception for miscellaneous errors during verification. The arguments
--   are the filename we were looking at, also optionally a function/symbol
--   name, and a message.
data X86Error       = X86Error FilePath (Maybe String) String deriving Show

instance Exception X86Unsupported
instance Exception X86Error

unsupported :: FilePath -> String -> IO a
unsupported path x = throwIO (X86Unsupported path x)

malformed :: FilePath -> String -> IO a
malformed path x = throwIO (X86Error path Nothing x)

timeout :: FilePath -> IO a
timeout path = throwIO (X86Error path Nothing "Execution timed out")


--------------------------------------------------------------------------------
-- Status output


say :: String -> IO ()
say x = putStr x >> hFlush stdout

sayLn :: String -> IO ()
sayLn = putStrLn

sayOK :: IO ()
sayOK = sayLn "[OK]"

statusBlock :: String -> IO a -> IO a
statusBlock msg m =
  do say msg
     a <- m
     sayOK
     return a
