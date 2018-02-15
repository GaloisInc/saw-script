{-# Language DataKinds, TypeFamilies, TypeOperators, GADTs #-}
{-# Language MultiParamTypeClasses #-}
{-# Language FlexibleContexts #-}
{-# Language ImplicitParams #-}
{-# Language TypeApplications #-}
{-# Language PatternSynonyms #-}
{-# Language UndecidableInstances #-}
{-# Language TypeSynonymInstances #-}
module SAWScript.X86Spec
  ( Spec

    -- * Types
  , X86Type
  , AByte, AWord, ADWord, AQWord, AVec, APtr, ABool
  , X86(..)

    -- * Defining Values
  , Value
  , fresh
  , SAW(..)
  , Literal(..)

    -- * Memory
  , MemType
  , allocBytes
  , Mutability(..)
  , allocArray
  , readMem
  , writeMem
  , readArray

    -- * Connection with other tools
  , Sym
  , runSpec
  , Rep
  , fromValue
  ) where

import Data.Kind(Type)
import GHC.TypeLits(Nat)
import Control.Monad(liftM,ap)

import Data.Parameterized.Nonce(GlobalNonceGenerator)
import Data.Parameterized.Classes(KnownRepr(knownRepr))
import Data.Parameterized.NatRepr

import Lang.Crucible.Types(CrucibleType,TypeRepr,BoolType)
import Lang.Crucible.BaseTypes
        (BaseTypeRepr(BaseBVRepr,BaseNatRepr,BaseBoolRepr))
import Lang.Crucible.Simulator.RegValue(RegValue)
import Lang.Crucible.Simulator.SimError(SimErrorReason(..))
import Lang.Crucible.Solver.Symbol(SolverSymbol,userSymbol)
import Lang.Crucible.Solver.SAWCoreBackend(SAWCoreBackend, bindSAWTerm)
import Lang.Crucible.Solver.Interface
          (freshConstant,natLit,notPred,addAssertion,natEq,bvLit
          , truePred, falsePred)
import Lang.Crucible.LLVM.MemModel
  (Mem, LLVMPointerType, doStore, doLoad, doMalloc, doPtrAddOffset, coerceAny)
import Lang.Crucible.LLVM.MemModel.Pointer
  (llvmPointer_bv, projectLLVM_bv, pattern LLVMPointer, ptrAdd)
import Lang.Crucible.LLVM.MemModel.Type(bitvectorType)
import Lang.Crucible.LLVM.MemModel.Generic(AllocType(HeapAlloc), Mutability(..))
import qualified Lang.Crucible.LLVM.MemModel.Type as LLVM
import Lang.Crucible.LLVM.Bytes(Bytes,toBytes)

import Verifier.SAW.SharedTerm(Term)


-- | The kind of X86 types.
data {- kind -} X86Type =
    AByte | AWord | ADWord | AQWord | AVec | APtr
  | ABool

type AByte    = 'AByte
type AWord    = 'AWord
type ADWord   = 'ADWord
type AQWord   = 'AQWord
type AVec     = 'AVec
type APtr     = 'APtr
type ABool    = 'ABool


data X86 :: X86Type -> Type where
  Byte    :: X86 AByte
  Word    :: X86 AWord
  DWord   :: X86 ADWord
  QWord   :: X86 AQWord
  Vec     :: X86 AVec
  Ptr     :: X86 APtr
  Bool    :: X86 ABool

type family Rep (x :: X86Type) :: CrucibleType where
  Rep AByte       = LLVMPointerType 8
  Rep AWord       = LLVMPointerType 16
  Rep ADWord      = LLVMPointerType 32
  Rep AQWord      = LLVMPointerType 64
  Rep AVec        = LLVMPointerType 256
  Rep APtr        = LLVMPointerType 64
  Rep ABool       = BoolType

crucRepr :: X86 t -> TypeRepr (Rep t)
crucRepr x =
  case x of
    Byte   -> knownRepr
    Word   -> knownRepr
    DWord  -> knownRepr
    QWord  -> knownRepr
    Vec    -> knownRepr
    Ptr    -> knownRepr
    Bool   -> knownRepr

class MemType (t :: X86Type) where
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

type BitSize x = ByteSize x * 8

bitSizeNat :: MemType t => X86 t -> NatRepr (BitSize t)
bitSizeNat x = natMultiply (byteSizeNat x) (knownNat @8)

byteSize :: MemType t => X86 t -> Bytes
byteSize = toBytes . natValue . byteSizeNat

llvmType :: MemType t => X86 t -> LLVM.Type
llvmType x = bitvectorType (byteSize x)


-- | A value in a X86 specification.
newtype Value t = Value (RegValue Sym (Rep t))

fromValue :: Value t -> RegValue Sym (Rep t)
fromValue (Value t) = t

value :: proxy t -> RegValue Sym (Rep t) -> Value t
value _ x = Value x

symName :: String -> IO SolverSymbol
symName s = case userSymbol s of
              Left err -> fail (show err)
              Right a  -> return a



--------------------------------------------------------------------------------
-- Spec monad

type Sym = SAWCoreBackend GlobalNonceGenerator

newtype Spec a = Spec (Sym -> RegValue Sym Mem -> IO (a, RegValue Sym Mem))

runSpec :: Sym -> RegValue Sym Mem -> Spec a -> IO (a, RegValue Sym Mem)
runSpec sym mem (Spec f) = f sym mem

instance Functor Spec where fmap = liftM

instance Applicative Spec where
  pure a = Spec (\_ m -> return (a,m))
  (<*>) = ap

instance Monad Spec where
  Spec m >>= k = Spec (\r s -> do (a, s1) <- m r s
                                  let Spec m1 = k a
                                  m1 r s1)

io :: IO a -> Spec a
io m = Spec (\_ s -> do a <- m
                        return (a,s))

getSym :: Spec Sym
getSym = Spec (\r s -> return (r,s))

updMem :: (Sym -> RegValue Sym Mem -> IO (a, RegValue Sym Mem)) -> Spec a
updMem f = Spec f

withMem :: (Sym -> RegValue Sym Mem -> IO a) -> Spec a
withMem f = Spec (\r s -> f r s >>= \a -> return (a,s))

updMem_ :: (Sym -> RegValue Sym Mem -> IO (RegValue Sym Mem)) -> Spec ()
updMem_ f = updMem (\sym mem -> do mem1 <- f sym mem
                                   return ((),mem1))

--------------------------------------------------------------------------------

-- | Generate an unknonw value of the given type.
fresh :: X86 t -> String -> Spec (Value t)
fresh x str =
  case x of
    Byte  -> freshBits str x
    Word  -> freshBits str x
    DWord -> freshBits str x
    QWord -> freshBits str x
    Vec   -> freshBits str x
    Ptr   -> freshPtr  str
    Bool  -> freshBool str

-- | An uninitialized boolean value.
freshBool :: String -> Spec (Value ABool)
freshBool str =
  do sym <- getSym
     io $ do nm <- symName str
             Value <$> freshConstant sym nm BaseBoolRepr



-- | Generate a fresh bit-vector thing.
freshBits ::
  (Rep t ~ LLVMPointerType (BitSize t), 1 <= BitSize t, MemType t) =>
  String ->
  X86 t ->
  Spec (Value t)
freshBits str x =
  do sym <- getSym
     io $ do nm <- symName str
             bv <- freshConstant sym nm (BaseBVRepr (bitSizeNat x))
             value x <$> llvmPointer_bv sym bv



-- | An uninitialized pointer value.
freshPtr :: String -> Spec (Value APtr)
freshPtr str =
  getSym >>= \sym -> io (
  do base_nm <- symName (str ++ "_base")
     off_nm  <- symName (str ++ "_offset")
     base    <- freshConstant sym base_nm BaseNatRepr
     offs    <- freshConstant sym off_nm (BaseBVRepr knownNat)
     ok <- notPred sym =<< natEq sym base =<< natLit sym 0
     addAssertion sym ok
        (AssertFailureSimError "[somePtr] pointer used as a bit-vector")
     return (Value (LLVMPointer base offs))
  )


class SAW (t :: X86Type) where
  saw :: X86 t -> Term -> Spec (Value t)

instance SAW ABool where
  saw _ val =
    do sym <- getSym
       Value <$> io (bindSAWTerm sym BaseBoolRepr val)

instance SAW AByte  where saw = sawBits
instance SAW AWord  where saw = sawBits
instance SAW ADWord where saw = sawBits
instance SAW AQWord where saw = sawBits
instance SAW AVec   where saw = sawBits

sawBits ::
  (Rep t ~ LLVMPointerType (BitSize t), 1 <= BitSize t, MemType t) =>
  X86 t -> Term -> Spec (Value t)
sawBits w val =
  do sym <- getSym
     io $ do bv <- bindSAWTerm sym (BaseBVRepr (bitSizeNat w)) val
             value w <$> llvmPointer_bv sym bv

-- | Types that support literals.
class Literal (t :: X86Type) where
  type Lit t
  literal :: X86 t -> Lit t -> Spec (Value t)

instance Literal ABool where
  type Lit ABool = Bool
  literal _ b =
    do sym <- getSym
       return (Value (if b then truePred sym else falsePred sym))

instance Literal AByte where
  type Lit AByte = Integer
  literal = literalBits

instance Literal AWord where
  type Lit AWord = Integer
  literal = literalBits

instance Literal ADWord where
  type Lit ADWord = Integer
  literal = literalBits

instance Literal AQWord where
  type Lit AQWord = Integer
  literal = literalBits

instance Literal AVec where
  type Lit AVec = Integer
  literal = literalBits

-- | A concrete bit-vector.
literalBits ::
  (Rep t ~ LLVMPointerType (BitSize t), 1 <= BitSize t, MemType t) =>
  X86 t -> Integer -> Spec (Value t)
literalBits w val =
  do sym      <- getSym
     value w <$> io (llvmPointer_bv sym =<< bvLit sym (bitSizeNat w) val)



--------------------------------------------------------------------------------

-- | Write a value to memory.
writeMem :: MemType t => X86 t -> Value APtr -> Value t -> Spec ()
writeMem w (Value p) (Value x) =
  updMem_ $ \sym mem ->
    let ?ptrWidth = knownNat
    in doStore sym mem p (crucRepr w) (llvmType w) x

-- | Read a value from memory.
readMem :: MemType t => X86 t -> Value APtr -> Spec (Value t)
readMem w (Value p) =
  withMem $ \sym mem ->
    do let ?ptrWidth = knownNat
       anyV <- doLoad sym mem p (llvmType w) 0
       Value <$> coerceAny sym (crucRepr w) anyV




-- | Allocate a pointer that points to the given number of bytes (on the heap).
-- The allocated memory is not initialized, so it should not be read until
-- it has been initialized.
allocBytes :: String -> Mutability -> Value AQWord -> Spec (Value APtr)
allocBytes str mut (Value n) =
  let ?ptrWidth = knownNat in
  updMem $ \sym m ->
    do (v,mem1) <- doMalloc sym HeapAlloc mut str m =<< projectLLVM_bv sym n
       return (Value v, mem1)



-- | Allocate an array, an initialize it with the given bit-vector values.
allocArray ::
  MemType t =>
  X86 t ->
  String ->
  Mutability ->
  [ Value t ] ->
  Spec (Value APtr)
allocArray ty str mut xs =
  do sym <- getSym
     let n  = fromIntegral (length xs)
         bs = natValue (byteSizeNat ty)
     sz    <- literal QWord (n * bs)
     ptr   <- allocBytes str mut sz
     bytes <- io (bvLit sym knownNat bs)
     doInit bytes ptr xs
     return ptr
  where
  doInit bytes ptr@(Value p) ys =
    case ys of
      [] -> return ()
      y : more ->
        do writeMem ty ptr y
           sym     <- getSym
           nextPtr <- io (Value <$> ptrAdd sym knownNat p bytes)
           doInit bytes nextPtr more



-- | Read out an array of values of the given type.
readArray ::
  MemType t =>
  X86 t ->
  Value APtr ->
  Int ->
  Spec [ Value t ]
readArray ty p0 n0 =
  do sym <- getSym
     amt <- io (bvLit sym knownNat (natValue (byteSizeNat ty)))
     go amt p0 n0
  where
  go amt p@(Value ptr) n
    | n > 0 = do v  <- readMem ty p
                 p1 <- withMem (\sym mem ->
                        let ?ptrWidth = knownNat
                        in Value <$> doPtrAddOffset sym mem ptr amt)
                 vs <- go amt p1 (n-1)
                 return (v : vs)
    | otherwise = return []





