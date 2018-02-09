{-# Language DataKinds, OverloadedStrings, GADTs, TypeApplications #-}
{-# Language RankNTypes, TypeOperators #-}
{-# Language RecordWildCards #-}
{-# Language AllowAmbiguousTypes, ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}
module SAWScript.X86
  ( Options(..)
  , main
  , linuxInfo
  , bsdInfo
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
import Lang.Crucible.CFG.Common(freshGlobalVar)
import Lang.Crucible.Types(BVType,BoolType)
import Lang.Crucible.BaseTypes(BaseTypeRepr(..))
import Lang.Crucible.Solver.Interface(freshConstant)
import Lang.Crucible.Solver.SAWCoreBackend(toSC)
import Lang.Crucible.Simulator.RegMap(regValue)
import Lang.Crucible.Simulator.RegValue(RegValue'(RV,unRV))
import Lang.Crucible.Simulator.ExecutionTree
          (gpValue,ExecResult(..),PartialResult(..))
import Lang.Crucible.ProgramLoc(Position(OtherPos))
import Lang.Crucible.FunctionHandle(HandleAllocator,newHandleAllocator)
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
import Data.Macaw.Symbolic( ArchRegStruct
                          , MacawArchEvalFn,ArchRegContext,mkFunCFG,
                                                        runCodeBlock)
import Data.Macaw.Symbolic.CrucGen(MacawSymbolicArchFunctions(..),MacawExt,
                                   MacawCrucibleRegTypes)
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

-- | Translate an assertion about the function with the given name to
-- a SAW core term.
translate :: Options -> RelevnatElf -> ByteString -> IO Term
translate opts elf name =
  do addr <- findSymbol (symMap elf) name
     (halloc, SomeCFG cfg) <- stToIO (makeCFG opts elf name addr)

     let sym = backend opts
     regs <- macawAssignToCrucM (mkReg sym) genRegAssign


     execResult <- runCodeBlock sym x86 (x86_eval opts) halloc cfg regs


     case execResult of
       FinishedExecution _ (TotalRes p) ->
          do startRegs <- getRegs sym regs
             endRegs   <- getRegs sym (regValue (p^.gpValue))
             relate opts startRegs endRegs

       _ -> malformed "Bad simulation result"

relate :: Options -> Regs -> Regs -> IO Term
relate = undefined




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
     return (halloc,g)
  where
  txtName   = decodeUtf8 name
  cruxName  = functionNameFromText txtName
  baseName  = Text.append "mem_base_" txtName

  empty = emptyDiscoveryState (memory elf) (symMap elf) (archInfo opts)


-- | Make up a fresh variable for a specific register.
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
-- Registers 

data Regs = Regs
  { rIP    :: Term             -- ^ 0 (64)
  , rGP    :: Vector 16 Term   -- ^ 1--16 (64)
  , rFlag  :: Vector 9  Term   -- ^ 17--25 (Bool)
  , rFP    :: FPRegs
  , rVec   :: Vector 16 Term   -- ^ 59--74 (256)

  }

data FPRegs = FPRegs
  { fpStatus :: Vector 16 Term  -- ^26--41 (bool)
  , fpTop    :: Term            -- ^42 (3)
  , fpTags   :: Vector 8 Term   -- ^ 43--50 (2)
  , fpRegs   :: Vector 8 Term   -- ^ 51-58 (80)
  }


getReg :: forall w n ctx.
  ( Idx n ctx (BVType w)
  , ctx ~ MacawCrucibleRegTypes X86_64
  ) =>
  Sym -> Assignment (RegValue' Sym) ctx ->
  IO Term
getReg sym a = toSC sym (unRV (a ^. (field @n)))

getFlag :: forall n ctx.
  ( Idx n ctx BoolType
  , ctx ~ MacawCrucibleRegTypes X86_64
  ) =>
  Sym -> Assignment (RegValue' Sym) ctx ->
  IO Term
getFlag sym a = toSC sym (unRV (a ^. (field @n)))

getRegs ::
  Sym ->
  Assignment (RegValue' Sym) (MacawCrucibleRegTypes X86_64) ->
  IO Regs
getRegs sym a =
  do rIP  <- getReg @64 @0 sym a

     Just rGP <- Vector.fromList knownRepr <$> sequence
       [ getReg @64 @1 sym a
       , getReg @64 @2 sym a
       , getReg @64 @3 sym a
       , getReg @64 @4 sym a
       , getReg @64 @5 sym a
       , getReg @64 @6 sym a
       , getReg @64 @7 sym a
       , getReg @64 @8 sym a

       , getReg @64 @9 sym a
       , getReg @64 @10 sym a
       , getReg @64 @11 sym a
       , getReg @64 @12 sym a
       , getReg @64 @13 sym a
       , getReg @64 @14 sym a
       , getReg @64 @15 sym a
       , getReg @64 @16 sym a
       ]

     Just rFlag <- Vector.fromList knownRepr <$> sequence
        [ getFlag @17 sym a
        , getFlag @18 sym a
        , getFlag @19 sym a
        , getFlag @20 sym a
        , getFlag @21 sym a
        , getFlag @22 sym a
        , getFlag @23 sym a
        , getFlag @24 sym a
        , getFlag @25 sym a
        ]

     rFP <-
       do -- X87 status registers
          Just fpStatus <- Vector.fromList knownRepr <$> sequence
            [ getFlag @26 sym a
            , getFlag @27 sym a
            , getFlag @28 sym a
            , getFlag @29 sym a
            , getFlag @30 sym a
            , getFlag @31 sym a
            , getFlag @32 sym a
            , getFlag @33 sym a
            , getFlag @34 sym a
            , getFlag @36 sym a
            , getFlag @36 sym a
            , getFlag @37 sym a
            , getFlag @38 sym a
            , getFlag @39 sym a
            , getFlag @40 sym a
            , getFlag @41 sym a
            ]

          fpTop <- getReg @3 @42 sym a

          -- Tags
          Just fpTags <- Vector.fromList knownRepr <$> sequence
            [ getReg @2 @43 sym a
            , getReg @2 @44 sym a
            , getReg @2 @45 sym a
            , getReg @2 @46 sym a
            , getReg @2 @47 sym a
            , getReg @2 @48 sym a
            , getReg @2 @49 sym a
            , getReg @2 @50 sym a
            ]

          -- Floating point register
          Just fpRegs <- Vector.fromList knownRepr <$> sequence
            [ getReg @80 @51 sym a
            , getReg @80 @52 sym a
            , getReg @80 @53 sym a
            , getReg @80 @54 sym a
            , getReg @80 @55 sym a
            , getReg @80 @56 sym a
            , getReg @80 @57 sym a
            , getReg @80 @58 sym a
            ]

          return FPRegs { .. }

     -- Vector registers
     Just rVec <- Vector.fromList knownRepr <$> sequence
       [ getReg @256 @59 sym a
       , getReg @256 @60 sym a
       , getReg @256 @61 sym a
       , getReg @256 @62 sym a
       , getReg @256 @63 sym a
       , getReg @256 @64 sym a
       , getReg @256 @65 sym a
       , getReg @256 @66 sym a
       , getReg @256 @67 sym a
       , getReg @256 @68 sym a
       , getReg @256 @69 sym a
       , getReg @256 @70 sym a
       , getReg @256 @71 sym a
       , getReg @256 @72 sym a
       , getReg @256 @73 sym a
       , getReg @256 @74 sym a
       ]

     return Regs { .. }




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

