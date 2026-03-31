{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module SAWCentral.Crucible.LLVM.X86Support
  ( X86Error(..)
  , X86Unsupported(..)
  , RelevantElf(..)
  , getElf
  , getRelevant
  , findSymbols
  , posFn
  , loadGlobal
  , Unit(..)
  , freshRegister
  , mkGlobalMap
  ) where

import GHC.Natural(Natural)

import Control.Applicative ( (<|>) )
import Control.Exception(Exception(..), throwIO)
import Control.Monad (MonadPlus(..), join)

import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Foldable (foldlM)

import Data.Parameterized.NatRepr
import qualified Data.Parameterized.Context as Ctx

import qualified Data.ElfEdit as Elf

-- What4
import What4.ProgramLoc(Position(OtherPos))
import What4.Interface
          (natEq, freshNat, natLit, asNat, userSymbol, freshConstant)

-- Crucible
import Lang.Crucible.Backend (HasSymInterface(backendGetSym))
import Lang.Crucible.Simulator.RegMap
import Lang.Crucible.Types (TypeRepr(..),BaseTypeRepr(..))
import qualified Lang.Crucible.LLVM.MemModel as Crucible

-- Macaw
import Data.Macaw.Discovery.State (AddrSymMap)
import Data.Macaw.Memory(
    Memory, MemSegmentOff(..),
    RegionIndex,
    addrOffset, memWordToUnsigned,
    segoffAddr, incAddr,
    readWord8, readWord16le, readWord32le, readWord64le
 )
import Data.Macaw.Memory.ElfLoader(
    LoadOptions(..),
    memoryForElfAllSymbols,
    memoryForElf,
    MemSymbol(..)
 )
import Data.Macaw.Symbolic (GlobalMap(..))

-- SAW Crucible
import SAWCentral.Crucible.Common (Sym)
import SAWCentral.Crucible.LLVM.CrucibleLLVM
  ( doPtrAddOffset
  , pattern LLVMPointerRepr
  , LLVMPtr
  , muxLLVMPtr
  , Bytes, toBytes
  , bytesToInteger
  , pattern LLVMPointer
  )


------------------------------------------------------------

data Unit = Bytes | Words | DWords | QWords | V128s | V256s deriving Show


(*.) :: Integer -> Unit -> Bytes
n *. u = toBytes (fromInteger n * bs)
  where bs = unitByteSize u natValue :: Natural

unitByteSize :: Unit -> (forall w. (1 <= w) => NatRepr w -> a) -> a
unitByteSize u k =
  case u of
    Bytes  -> k (knownNat @1)
    Words  -> k (knownNat @2)
    DWords -> k (knownNat @4)
    QWords -> k (knownNat @8)
    V128s  -> k (knownNat @16)
    V256s  -> k (knownNat @32)


--------------------------------------------------------------------------------

freshRegister :: Sym -> Ctx.Index ctx tp -> TypeRepr tp -> IO (RegValue' Sym tp)
freshRegister sym idx repr = RV <$> freshVal sym repr True ("reg" ++ show idx)

freshVal ::
  Sym -> TypeRepr t -> Bool {- ptrOK ?-}-> String -> IO (RegValue Sym t)
freshVal sym t ptrOk nm =
  case t of
    BoolRepr -> do
      sn <- symName nm
      freshConstant sym sn BaseBoolRepr
    LLVMPointerRepr w
      | ptrOk, Just Refl <- testEquality w (knownNat @64) -> do
          sn_base <- symName (nm ++ "_base")
          sn_off <- symName (nm ++ "_off")
          base <- freshNat sym sn_base
          off <- freshConstant sym sn_off (BaseBVRepr w)
          return (LLVMPointer base off)
      | otherwise -> do
          sn <- symName nm
          base <- natLit sym 0
          off <- freshConstant sym sn (BaseBVRepr w)
          return (LLVMPointer base off)
    it -> fail ("[freshVal] Unexpected type repr: " ++ show it)

  where
  symName s =
    case userSymbol ("macaw_" ++ s) of
      Left err -> error ("Invalid symbol name " ++ show s ++ ": " ++ show err)
      Right a -> return a


--------------------------------------------------------------------------------

-- | Implements a layer to map 'LLVMPtr's to their underlying allocations, as
-- tracked by the 'RegionIndex' map
--
-- NOTE: If the initial obvious mapping (where the concrete nat is in the map)
-- fails, there are two possibilities:
--
-- 1. The region ID is concrete but not in the map.  We should just pass it
--    through without modifying it, since it is a valid LLVM pointer
-- 2. The region ID is symbolic.  In this case, we need to generate a mux that
--    dispatches to the entries in the map when they match, or otherwise passes
--    the pointer through untouched.
--
-- If the region ID is concretely zero, it should be the case that the
-- 'RegionIndex' map would translate it into a real 'LLVMPtr' since the only map
-- entry (established in 'setupGlobals') is for 0.
mkGlobalMap ::
  (?memOpts::Crucible.MemOptions, Crucible.HasLLVMAnn Sym) =>
  Map RegionIndex (LLVMPtr Sym 64) ->
  GlobalMap Sym Crucible.Mem 64
mkGlobalMap rmap = GlobalMap $ \bak mem region off ->
  let
    sym = backendGetSym bak

    mapConcreteRegion = maybe mzero id (addOffset <$> thisRegion)
    thisRegion = join (findRegion <$> asNat region)
    findRegion r = Map.lookup (fromIntegral r) rmap
    addOffset p = doPtrAddOffset bak mem p off
      where ?ptrWidth = knownNat
    passThroughConcreteRegion =
      case asNat region of
        Nothing -> mzero
        Just _ -> return (LLVMPointer region off)
    -- If the symbolic nat is (symbolically) equal to any of the entries in the
    -- rmap, we need to do the translation; otherwise, we pass it through
    mapSymbolicRegion = foldlM muxSymbolicRegion (LLVMPointer region off) (Map.toList rmap)
    muxSymbolicRegion others (regionNum, basePtr) = do
      thisRegionNat <- natLit sym (fromIntegral regionNum)
      isEqRegion <- natEq sym thisRegionNat region
      adjustedPtr <- addOffset basePtr
      muxLLVMPtr sym isEqRegion adjustedPtr others

  in mapConcreteRegion <|> passThroughConcreteRegion <|> mapSymbolicRegion


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
           malformed path $ "Invalid ELF header at offset " <> Text.pack (show off) <>
                            ": " <> Text.pack msg
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
    (Left err, _) -> malformed path $ Text.pack err
    (_, Left err) -> malformed path $ Text.pack err
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
                _      -> err ("unsupported global size: " ++ show u)

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
data X86Error       = X86Error FilePath (Maybe Text) Text deriving Show

instance Exception X86Unsupported
instance Exception X86Error

unsupported :: FilePath -> String -> IO a
unsupported path x = throwIO (X86Unsupported path x)

malformed :: FilePath -> Text -> IO a
malformed path x = throwIO (X86Error path Nothing x)
