{-# Language ImplicitParams #-}
{-# Language DataKinds #-}
{-# Language TypeFamilies #-}
{-# Language TypeSynonymInstances #-}
{-# Language FlexibleInstances #-}
module SAWScript.X86Spec.Memory
  ( MemType(..)
  , SizeOf(..)
  , WriteMem(..)
  , AllocBytes(..)
  , allocArray
  , allocArrayOf
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
  ( storeConstRaw, doLoad, doMalloc, doPtrAddOffset, coerceAny, packMemValue )
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

instance MemType (Bits 8) where
  type ByteSize (Bits 8) = 1
  byteSizeNat _ = knownNat

instance MemType (Bits 16) where
  type ByteSize (Bits 16) = 2
  byteSizeNat _ = knownNat

instance MemType (Bits 32) where
  type ByteSize (Bits 32) = 4
  byteSizeNat _ = knownNat

instance MemType (Bits 64) where
  type ByteSize (Bits 64) = 8
  byteSizeNat _ = knownNat

instance MemType (Bits 128) where
  type ByteSize (Bits 128) = 16
  byteSizeNat _ = knownNat

instance MemType (Bits 256) where
  type ByteSize (Bits 256) = 32
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

instance (MemType t, a ~ X86 t) => WriteMem (a, Value t) where
  writeMem (Value p) (w,Value x) =
    updMem_ $ \sym mem ->
      do let ?ptrWidth = knownNat
         let ty = llvmType w
         val <- packMemValue sym ty (crucRepr w) x
         -- Here we use the write that ignore mutability.
         -- This is because we are writinging initialization code.
         storeConstRaw sym mem p ty val

instance (MemType t, Infer t) => WriteMem (Value t) where
  writeMem p x = writeMem p (infer, x)

instance (MemType t, a ~ X86 t) => WriteMem (a, [Value t]) where
  writeMem p (t,xs) =
    case xs of
      []     -> return ()
      v : vs -> do writeMem p (t,v)
                   p1 <- ptrAdd p (sizeOf t)
                   writeMem p1 (t,vs)



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

instance (t ~ Bits 64) => AllocBytes (Value t) where
  allocBytes str mut (Value n) =
    let ?ptrWidth = knownNat in
    updMem $ \sym m ->
      do (v,mem1) <- doMalloc sym HeapAlloc mut str m =<< projectLLVM_bv sym n
         return (Value v, mem1)

instance AllocBytes Bytes where
  allocBytes str mut b = allocBytes str mut =<< literal (bytesToInteger b)


class PtrAdd t where
  ptrAdd :: Value APtr -> t -> Spec p (Value APtr)

instance (t ~ Bits 64) => PtrAdd (Value t) where
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
allocArray = allocArrayOf infer

-- | Allocate an array with elements of the given type.
-- Initialize it with the given values.
allocArrayOf ::
  MemType t =>
  X86 t -> String -> Mutability -> [Value t] -> Spec Pre (Value APtr)
allocArrayOf ty str mut xs =
  do let n  = fromIntegral (length xs)
         bs = bytesToInteger (sizeOf ty)
     sz    <- literal (n * bs)
     ptr   <- allocBytes str mut sz
     writeMem ptr (ty,xs)
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


