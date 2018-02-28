{-# Language ImplicitParams #-}
{-# Language DataKinds #-}
{-# Language TypeFamilies #-}
{-# Language TypeSynonymInstances #-}
module SAWScript.X86Spec.Memory
  ( MemType(..)
  , SizeOf(..)
  , WriteMem(..)
  , allocBytes
  , allocArray
  , readMem
  , readArray
  , PtrAdd(..)
  , Bytes
  , toBytes
  , bytesToInteger
  , Mutability(..)
  , (.*)
  ) where

import GHC.TypeLits(Nat)

import Data.Parameterized.NatRepr(NatRepr,knownNat,natValue)

import qualified Lang.Crucible.LLVM.MemModel.Type as LLVM
import Lang.Crucible.LLVM.MemModel.Generic(AllocType(HeapAlloc), Mutability(..))
import Lang.Crucible.LLVM.MemModel
  ( doStore, doLoad, doMalloc, doPtrAddOffset, coerceAny)
import Lang.Crucible.LLVM.Bytes(Bytes,toBytes,bytesToInteger)
import Lang.Crucible.LLVM.MemModel.Pointer (projectLLVM_bv)
import Lang.Crucible.LLVM.MemModel.Type(bitvectorType)

import SAWScript.X86Spec.Types
import SAWScript.X86Spec.Monad
import SAWScript.X86Spec.Literal

-- | Types that can be stored in memory.
class MemType (t :: X86Type) where
  -- | Size of the type, in bytes.
  type ByteSize t :: Nat
  byteSizeNat :: X86 t -> NatRepr (ByteSize t)

instance MemType AByte where
  type ByteSize AByte = 1
  byteSizeNat _ = knownNat

instance MemType AWord where
  type ByteSize AWord = 2
  byteSizeNat _ = knownNat

instance MemType ADWord where
  type ByteSize ADWord = 4
  byteSizeNat _ = knownNat

instance MemType AQWord where
  type ByteSize AQWord = 8
  byteSizeNat _ = knownNat

instance MemType AVec where
  type ByteSize AVec = 32
  byteSizeNat _ = knownNat

instance MemType APtr where
  type ByteSize APtr = 8
  byteSizeNat _ = knownNat


class SizeOf t where
  sizeOf :: t -> Bytes

instance MemType t => SizeOf (X86 t) where
  sizeOf = toBytes . natValue . byteSizeNat

instance (MemType t, Infer t) => SizeOf (Value t) where
  sizeOf = sizeOf . typeOf

-- | Multiply a size by a constant.
-- Useful for working with arrays (sizes, advnacing, etc.)
(.*) :: SizeOf t => Integer -> t -> Bytes
n .* t = toBytes (n * bytesToInteger (sizeOf t))

-- | The LLVM type used when manipulating values of the given type in memory.
llvmType :: SizeOf t => t -> LLVM.Type
llvmType x = bitvectorType (sizeOf x)


class WriteMem t where
  writeMem :: Value APtr -> t -> Spec Pre ()

instance (MemType t, Infer t) => WriteMem (Value t) where
  writeMem (Value p) v@(Value x) =
    updMem_ $ \sym mem ->
      do let w = typeOf v
         let ?ptrWidth = knownNat
         doStore sym mem p (crucRepr w) (llvmType w) x

instance (SizeOf t, WriteMem t) => WriteMem [t] where
  writeMem p xs =
    case xs of
      []     -> return ()
      v : vs -> do writeMem p v
                   p1 <- ptrAdd p (sizeOf v)
                   writeMem p1 vs



-- | Read a value from memory.
-- Currently this is an unaligned read (i.e., any alignment will do).
-- We probably want to have an aligned read also.
readMem :: MemType t => X86 t -> Value APtr -> Spec Post (Value t)
readMem w (Value p) =
  withMem $ \sym mem ->
    do let ?ptrWidth = knownNat
       anyV <- doLoad sym mem p (llvmType w) 0
       Value <$> coerceAny sym (crucRepr w) anyV



-- | Allocate a pointer that points to the given number of bytes (on the heap).
-- The allocated memory is not initialized, so it should not be read until
-- it has been initialized.
class AllocBytes t where
  allocBytes :: String -> Mutability -> t -> Spec Pre (Value APtr)

instance (t ~ AQWord) => AllocBytes (Value t) where
  allocBytes str mut (Value n) =
    let ?ptrWidth = knownNat in
    updMem $ \sym m ->
      do (v,mem1) <- doMalloc sym HeapAlloc mut str m =<< projectLLVM_bv sym n
         return (Value v, mem1)

instance AllocBytes Bytes where
  allocBytes str mut b = allocBytes str mut =<< literal (bytesToInteger b)


class PtrAdd t where
  ptrAdd :: Value APtr -> t -> Spec p (Value APtr)

instance (t ~ AQWord) => PtrAdd (Value t) where
  ptrAdd (Value p) (Value o) = withMem $ \sym mem ->
    let ?ptrWidth = knownNat
    in Value <$> (doPtrAddOffset sym mem p =<< projectLLVM_bv sym o)

instance PtrAdd Bytes where
  ptrAdd p x = ptrAdd p =<< literal (bytesToInteger x)




-- | Allocate an array, an initialize it with the given values.
allocArray ::
  (Infer t, MemType t) =>
  String ->
  Mutability ->
  [ Value t ] ->
  Spec Pre (Value APtr)
allocArray str mut xs =
  do let n  = fromIntegral (length xs)
         bs = bytesToInteger (sizeOf (typeOf (head xs)))
     sz    <- literal (n * bs)
     ptr   <- allocBytes str mut sz
     writeMem ptr xs
     return ptr



-- | Read out an array of values of the given type.
readArray ::
  MemType t =>
  X86 t ->
  Value APtr ->
  Int ->
  Spec Post [ Value t ]
readArray ty p n
  | n > 0 = do v  <- readMem ty p
               p1 <- ptrAdd p (sizeOf ty)
               vs <- readArray ty p1 (n-1)
               return (v : vs)
  | otherwise = return []


