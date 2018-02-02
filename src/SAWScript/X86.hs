{-# Language DataKinds, OverloadedStrings, GADTs, TypeApplications #-}
module SAWScript.X86
  ( Options(..)
  , main
  , linuxInfo
  , bsdInfo
  ) where


import Control.Exception(Exception(..),throwIO)
import Control.Monad(unless)
import Control.Monad.ST(stToIO)
import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import           Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.Text as Text
import           Data.Text.Encoding(decodeUtf8)
import           Control.Lens((^.))

import Data.ElfEdit (Elf, parseElf, ElfGetResult(..))

import Data.Parameterized.Some(Some(..))
import Data.Parameterized.Classes(knownRepr)
import Data.Parameterized.Context(field)

-- Crucible
import Lang.Crucible.CFG.Core(SomeCFG(..))
import Lang.Crucible.CFG.Common(freshGlobalVar)
import Lang.Crucible.BaseTypes(BaseTypeRepr(..))
import Lang.Crucible.Solver.Interface(freshConstant)
import Lang.Crucible.Solver.SAWCoreBackend(toSC)
import Lang.Crucible.Simulator.RegMap(regValue)
import Lang.Crucible.Simulator.RegValue(RegValue'(RV,unRV))
import Lang.Crucible.Simulator.ExecutionTree
          (gpValue,ExecResult(..),PartialResult(..))
import Lang.Crucible.ProgramLoc(Position(OtherPos))
import Lang.Crucible.FunctionHandle(newHandleAllocator)
import Lang.Crucible.FunctionName(functionNameFromText)

-- Macaw
import Data.Macaw.Architecture.Info(ArchitectureInfo)
import Data.Macaw.Discovery(analyzeFunction)
import Data.Macaw.Discovery.State(CodeAddrReason(UserRequest)
                                 , emptyDiscoveryState)
import Data.Macaw.Types(TypeRepr(..), typeRepr)
import Data.Macaw.Memory(Memory, MemSymbol(..), MemSegmentOff
                        , AddrSymMap )
import Data.Macaw.Memory.ElfLoader( LoadOptions(..)
                                  , LoadStyle(..)
                                  , memoryForElf
                                  , resolveElfFuncSymbols )
import Data.Macaw.Symbolic(mkFunCFG, runCodeBlock)
import Data.Macaw.Symbolic.CrucGen(MacawSymbolicArchFunctions(..))
import Data.Macaw.Symbolic.PersistentState(ToCrucibleType,macawAssignToCrucM)
import Data.Macaw.X86(X86Reg(..), x86_64_linux_info,x86_64_freeBSD_info)
import Data.Macaw.X86.ArchTypes(X86_64)
import Data.Macaw.X86.Symbolic(x86_64MacawSymbolicFns, x86_64MacawEvalFn)
import Data.Macaw.X86.Crucible(SymFuns)


-- Saw Core
import Verifier.SAW.SharedTerm(Term)

-- Saw Script
import SAWScript.CrucibleMethodSpecIR(Sym)



--------------------------------------------------------------------------------
-- Input Options

-- | What we'd like done, plus additional information from the "outside world".
data Options = Options
  { fileName  :: FilePath
    -- ^ Name of the elf file to process.

  , functions :: [ByteString]
    -- ^ Functions that we'd like ot extract.

  , symFuns   :: SymFuns Sym
    -- ^ Symbolic function names for complex instructinos.
    -- Should be created once during initialization.

  , archInfo :: ArchitectureInfo X86_64
    -- ^ Architectural flavor.  See "linuxInfo" and "bsdInfo".

  , backend :: Sym
    -- ^ The Crucible backend to use.
  }

linuxInfo :: ArchitectureInfo X86_64
linuxInfo = x86_64_linux_info

bsdInfo :: ArchitectureInfo X86_64
bsdInfo = x86_64_freeBSD_info



-- | The main entry point.
-- Extracts SAW core terms for the functions specified in the "Options".
main :: Options -> IO (Map ByteString Term)
main opts =
  do elf <- getRelevant =<< getElf (fileName opts)
     ts <- mapM (translate opts elf) (functions opts)
     return $ Map.fromList $ zip (functions opts) ts


--------------------------------------------------------------------------------
-- ELF

-- | These are the parts of the ELF file that we care about.
data RelevnatElf = RelevnatElf
  { memory  :: Memory 64
  , symMap  :: AddrSymMap 64
  }

-- | Parse an elf file.
getElf :: FilePath -> IO (Elf 64)
getElf path =
  do bytes <- BS.readFile path
     case parseElf bytes of
       Elf64Res [] e     -> return e
       Elf64Res _ _      -> malformed "64-bit ELF input"
       Elf32Res _ _      -> unsupported "32-bit ELF format"
       ElfHeaderError {} -> malformed "Invalid ELF header"



-- | Extract a Macaw "memory" from an ELF file and resolve symbols.
getRelevant :: Elf 64 -> IO RelevnatElf
getRelevant elf =
  case memoryForElf opts elf of
    Left err -> malformed err
    Right (ixMap,mem) ->
      do let (errs,addrs) = resolveElfFuncSymbols mem ixMap elf
         unless (null errs) (malformed "Failed to resolve ELF symbols.")
         let toEntry msym = (memSymbolStart msym, memSymbolName msym)
         return RelevnatElf { memory = mem
                            , symMap = Map.fromList (map toEntry addrs)
                            }

  where
  -- XXX: What options do we want?
  opts = LoadOptions { loadRegionIndex    = Just 1
                     , loadStyleOverride  = Just LoadBySection
                     , includeBSS         = False
                     }




-- | Find the address of a symbol by name.
findSymbol :: AddrSymMap 64 -> ByteString -> IO (MemSegmentOff 64)
findSymbol addrs nm =
  case Map.findWithDefault [] nm invertedMap of
    [addr] -> return $! addr
    []     -> malformed ("Could not find function " ++ show nm)
    _      -> malformed ("Multiple definitions for " ++ show nm)
  where
  invertedMap = Map.fromListWith (++) [ (y,[x]) | (x,y) <- Map.toList addrs ]


-- | The possition associated with a specific location.
posFn :: MemSegmentOff 64 -> Position
posFn = OtherPos . Text.pack . show

--------------------------------------------------------------------------------
-- Translation

-- | Translate the function with the given name to SAW core.
translate :: Options -> RelevnatElf -> ByteString -> IO Term
translate opts elf name =
  do addr <- findSymbol (symMap elf) name
     (_,Some funInfo) <- stToIO $ analyzeFunction quiet addr UserRequest empty
     halloc  <- stToIO $ newHandleAllocator
     baseVar <- stToIO $ freshGlobalVar halloc baseName knownRepr
     let memBaseVarMap = Map.singleton 1 baseVar
     SomeCFG g <- stToIO $ mkFunCFG x86_64MacawSymbolicFns
                                    halloc
                                    memBaseVarMap
                                    cruxName
                                    posFn
                                    funInfo

     let sym = backend opts
     regs <- macawAssignToCrucM (mkReg sym)
                                (crucGenRegAssignment x86_64MacawSymbolicFns)

     execResult <- runCodeBlock sym x86_64MacawSymbolicFns
                          (x86_64MacawEvalFn (symFuns opts)) halloc g regs

     case execResult of
       FinishedExecution _ (TotalRes p) ->
        -- XXX: Temporary, just to make sure the types work out,
        -- this translates the first register (whatever that is)
        toSC (backend opts)
          (unRV ((regValue (p^.gpValue)) ^. (field @0)))
       _ -> malformed "Bad simulation result"



  where
  empty = emptyDiscoveryState (memory elf) (symMap elf) (archInfo opts)

  txtName   = decodeUtf8 name
  baseName  = Text.append "mem_base_" txtName
  cruxName  = functionNameFromText txtName




mkReg :: Sym -> X86Reg tp -> IO (RegValue' Sym (ToCrucibleType tp))
mkReg sym r =
  case typeRepr r of
    BoolTypeRepr -> RV <$> freshConstant sym nm BaseBoolRepr
    BVTypeRepr w -> RV <$> freshConstant sym nm (BaseBVRepr w)
    TupleTypeRepr{} ->
      unsupported "macaw-symbolic does not support tuple types."
  where
  nm = crucGenArchRegName x86_64MacawSymbolicFns r


--------------------------------------------------------------------------------
-- Logging
quiet :: Applicative m => a -> m ()
quiet _ = pure ()



--------------------------------------------------------------------------------
-- Errors

data X86Unsupported = X86Unsupported String deriving Show
data X86Error       = X86Error String deriving Show

instance Exception X86Unsupported
instance Exception X86Error

unsupported :: String -> IO a
unsupported x = throwIO (X86Unsupported x)

malformed :: String -> IO a
malformed x = throwIO (X86Error x)


{-

main :: IO ()
main = do
  putStrLn "Start test case"
  Some gen <- newIONonceGenerator
  halloc <- C.newHandleAllocator
  sym <- C.newSimpleBackend gen
  let x86ArchFns :: MS.MacawSymbolicArchFunctions MX.X86_64
      x86ArchFns = MX.x86_64MacawSymbolicFns

  let posFn :: M.MemSegmentOff 64 -> C.Position
      posFn = C.OtherPos . Text.pack . show

  let loadOpt :: Elf.LoadOptions
      loadOpt = Elf.LoadOptions { Elf.loadRegionIndex = Just 1
                                , Elf.loadStyleOverride = Just Elf.LoadBySection
                                , Elf.includeBSS = False
                                }

  memBaseVar <- stToIO $ C.freshGlobalVar halloc "add_mem_base" C.knownRepr

  let memBaseVarMap :: MS.MemSegmentMap 64
      memBaseVarMap = Map.singleton 1 memBaseVar

  let addrSymMap :: M.AddrSymMap 64
      addrSymMap = Map.fromList [ (M.memSymbolStart msym, M.memSymbolName msym)
                                | msym <- nameAddrList ]
  let archInfo :: M.ArchitectureInfo MX.X86_64
      archInfo =  MX.x86_64_linux_info

  let ds0 :: M.DiscoveryState MX.X86_64
      ds0 = M.emptyDiscoveryState mem addrSymMap archInfo

  putStrLn "Analyze a function"
  let logFn addr = ioToST $ do
        putStrLn $ "Analyzing " ++ show addr

  (_, Some funInfo) <- stToIO $ M.analyzeFunction logFn addAddr M.UserRequest ds0
  putStrLn "Make CFG"
  C.SomeCFG g <- stToIO $ MS.mkFunCFG x86ArchFns halloc memBaseVarMap "add" posFn funInfo

  regs <- MS.macawAssignToCrucM (mkReg x86ArchFns sym) (MS.crucGenRegAssignment x86ArchFns)

  symFuns <- MX.newSymFuns sym

  putStrLn "Run code block"
  execResult <- MS.runCodeBlock sym x86ArchFns (MX.x86_64MacawEvalFn symFuns) halloc g regs
  case execResult of
    C.FinishedExecution _ (C.TotalRes _pair) -> do
      putStrLn "Done"
    _ -> do
      fail "Partial execution returned."

  -- Steps:
  -- Load up Elf file.
  -- Call symbolic simulator
  -- Check Result

-}
