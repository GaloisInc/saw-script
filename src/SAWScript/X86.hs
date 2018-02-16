{-# Language DataKinds, OverloadedStrings, GADTs, TypeApplications #-}
{-# Language RankNTypes, TypeOperators #-}
{-# Language RecordWildCards #-}
{-# Language AllowAmbiguousTypes, ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}
{-# Language PatternSynonyms #-}
{-# Language ImplicitParams #-}
{-# OPTIONS_GHC -w #-}

module SAWScript.X86
  ( Options(..)
  , main
  , linuxInfo
  , bsdInfo

    -- * Specifications
  , FunSpec(..)
  , Spec

  ) where


import Control.Exception(Exception(..),throwIO)
import Control.Monad(unless)
import Control.Monad.ST(ST,stToIO)
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
import Data.Parameterized.Context(Assignment,EmptyCtx,(::>),field,Idx)

-- Crucible
import Lang.Crucible.Vector(Vector)
import qualified Lang.Crucible.Vector as Vector
import Lang.Crucible.CFG.Core(SomeCFG(..))
import Lang.Crucible.CFG.Common(freshGlobalVar,GlobalVar)
import Lang.Crucible.Types
import Lang.Crucible.Solver.Interface (Pred)
import Lang.Crucible.Simulator.RegMap(regValue)
import Lang.Crucible.Simulator.RegValue(RegValue,RegValue'(unRV))
import Lang.Crucible.Simulator.GlobalState(lookupGlobal)
import Lang.Crucible.Simulator.ExecutionTree
          (GlobalPair,gpValue,ExecResult(..),PartialResult(..)
          , gpGlobals)
import Lang.Crucible.ProgramLoc(Position(OtherPos))
import Lang.Crucible.FunctionHandle(HandleAllocator,newHandleAllocator)
import Lang.Crucible.FunctionName(functionNameFromText)

-- Crucible LLVM
import Lang.Crucible.LLVM.MemModel (LLVMPointerType,Mem,mkMemVar,emptyMem)
import Lang.Crucible.LLVM.DataLayout(EndianForm(LittleEndian))


-- Macaw
import Data.Macaw.Architecture.Info(ArchitectureInfo)
import Data.Macaw.Discovery(analyzeFunction)
import Data.Macaw.Discovery.State(CodeAddrReason(UserRequest)
                                 , emptyDiscoveryState)
import Data.Macaw.Memory(Memory, MemSymbol(..), MemSegmentOff
                        , AddrSymMap )
import Data.Macaw.Memory.ElfLoader( LoadOptions(..)
                                  , LoadStyle(..)
                                  , memoryForElf
                                  , resolveElfFuncSymbols )
import Data.Macaw.Symbolic( ArchRegStruct
                          , MacawArchEvalFn,ArchRegContext,mkFunCFG,
                                                        runCodeBlock)
import Data.Macaw.Symbolic.CrucGen(MacawSymbolicArchFunctions(..),MacawExt,
                                   MacawCrucibleRegTypes)
import Data.Macaw.Symbolic.PersistentState(ToCrucibleType,macawAssignToCrucM)
import Data.Macaw.X86(X86Reg(..), x86_64_linux_info,x86_64_freeBSD_info)
import Data.Macaw.X86.ArchTypes(X86_64)
import Data.Macaw.X86.Symbolic ( x86_64MacawSymbolicFns, x86_64MacawEvalFn)
import Data.Macaw.X86.Crucible(SymFuns)


-- Saw Core
import Verifier.SAW.SharedTerm(Term)

-- SAWScript
import SAWScript.X86Spec
  (Sym,Spec,Pre,Post,runPreSpec,runPostSpec,RegAssign,macawLookup)



--------------------------------------------------------------------------------
-- Input Options


-- | What we'd like done, plus additional information from the "outside world".
data Options = Options
  { fileName  :: FilePath
    -- ^ Name of the elf file to process.

  , functions :: [FunSpec]
    -- ^ Functions that we'd like to extract.

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


--------------------------------------------------------------------------------
-- Spec

data FunSpec = FunSpec
  { funName   :: ByteString
  , funSetup  :: Spec Pre RegAssign
    -- ^ Setup initial memory and registers.

  , funPost   :: RegAssign -> Spec Post Term
    -- ^ Compute post condition, using the initial values of the registers.
  }





--------------------------------------------------------------------------------

-- | The main entry point.
-- Extracts SAW core terms for the functions specified in the "Options".
main :: Options -> IO (Map ByteString Term)
main opts =
  do elf <- getRelevant =<< getElf (fileName opts)
     ts <- mapM (translate opts elf) (functions opts)
     return $ Map.fromList $ zip (map funName (functions opts)) ts


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

-- | Translate an assertion about the function with the given name to
-- a SAW core term.
translate :: Options -> RelevnatElf -> FunSpec -> IO Term
translate opts elf fspec =
  do let name = funName fspec
     addr <- findSymbol (symMap elf) name
     (halloc, SomeCFG cfg) <- stToIO (makeCFG opts elf name addr)

     mvar <- stToIO (mkMemVar halloc)
     m0   <- emptyMem LittleEndian
     let sym    = backend opts
     (initRegs, m1) <- runPreSpec sym m0 (funSetup fspec)
     regs <- macawAssignToCrucM (return . macawLookup initRegs) genRegAssign
     execResult <-
        runCodeBlock sym x86 (x86_eval opts) halloc (mvar,m1) cfg regs


     let postSpec = funPost fspec initRegs

     case execResult of
       FinishedExecution _ctx res ->
          case res of
            TotalRes gp ->
              do mem <- getMem gp mvar
                 runPostSpec sym (regValue (gp ^. gpValue)) mem postSpec
            PartialRes pre gp _ ->
              do mem <- getMem gp mvar
                 -- XXX: we also need to do something about this pre
                 runPostSpec sym (regValue (gp ^. gpValue)) mem postSpec


       _ -> malformed "Bad simulation result"

-- | Get the current model of the memory.
getMem :: GlobalPair sym a ->
          GlobalVar Mem ->
          IO (RegValue sym Mem)
getMem st mvar =
  case lookupGlobal mvar (st ^. gpGlobals) of
    Just mem -> return mem
    Nothing  -> fail ("Global heap value not initialized: " ++ show mvar)


relate :: Options -> Regs -> Maybe (Pred Sym) -> Regs -> IO Term
relate = undefined

data Regs = XXX

getRegs :: Sym -> a -> IO Regs
getRegs = undefined


-- | Generate a CFG for the function at the given address.
makeCFG ::
  Options ->
  RelevnatElf ->
  ByteString ->
  MemSegmentOff 64 ->
  ST s ( HandleAllocator s
       , SomeCFG (MacawExt X86_64)
                 (EmptyCtx ::> ArchRegStruct X86_64)
                 (ArchRegStruct X86_64)
       )
makeCFG opts elf name addr =
  do (_,Some funInfo) <- analyzeFunction quiet addr UserRequest empty
     halloc  <- newHandleAllocator
     baseVar <- freshGlobalVar halloc baseName knownRepr
     let memBaseVarMap = Map.singleton 1 baseVar
     g <- mkFunCFG x86 halloc memBaseVarMap cruxName posFn funInfo
     return (halloc, g)
  where
  txtName   = decodeUtf8 name
  cruxName  = functionNameFromText txtName
  baseName  = Text.append "mem_base_" txtName

  empty = emptyDiscoveryState (memory elf) (symMap elf) (archInfo opts)






--------------------------------------------------------------------------------
-- Specialize 

-- | All functions related to X86.
x86 :: MacawSymbolicArchFunctions X86_64
x86 = x86_64MacawSymbolicFns

genRegAssign :: Assignment X86Reg (ArchRegContext X86_64)
genRegAssign = crucGenRegAssignment x86

-- | Evaluate a specific instruction.
x86_eval :: Options -> MacawArchEvalFn Sym X86_64
x86_eval opts = x86_64MacawEvalFn (symFuns opts)




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

