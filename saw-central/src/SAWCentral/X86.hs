{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
module SAWCentral.X86
  ( X86Error(..)
  , X86Unsupported(..)
  , RelevantElf(..)
  , getElf
  , getRelevant
  , findSymbols
  , posFn
  , loadGlobal
  ) where


import Control.Exception(Exception(..), throwIO)

import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Map as Map
import           Data.Text (Text)
import qualified Data.Text as Text

import qualified Data.ElfEdit as Elf

import What4.ProgramLoc(Position(OtherPos))

-- Crucible LLVM
import SAWCentral.Crucible.LLVM.CrucibleLLVM (bytesToInteger)

-- Macaw
import Data.Macaw.Discovery.State (AddrSymMap)
import Data.Macaw.Memory( Memory, MemSegmentOff(..)
                        , addrOffset, memWordToUnsigned
                        , segoffAddr, incAddr
                        , readWord8, readWord16le, readWord32le, readWord64le)
import Data.Macaw.Memory.ElfLoader( LoadOptions(..)
                                  , memoryForElfAllSymbols
                                  , memoryForElf
                                  , MemSymbol(..)
                                  )

-- SAWCentral
import SAWCentral.X86Spec hiding (Prop)


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
