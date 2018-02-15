{-# Language DataKinds, TypeFamilies, TypeOperators, GADTs #-}
{-# Language MultiParamTypeClasses #-}
{-# Language FlexibleContexts #-}
{-# Language ImplicitParams #-}
{-# Language TypeApplications #-}
{-# Language PatternSynonyms #-}
{-# Language UndecidableInstances #-}
{-# Language TypeSynonymInstances #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleInstances #-}
module SAWScript.X86Spec
  ( Spec
  , Pre, Post

    -- * Types
  , X86Type
  , AByte, AWord, ADWord, AQWord, AVec, APtr, ABool
  , ABits2, ABits3, ABigFloat
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

    -- * Registers
  , GetReg(..)
  , IP(..)
  , GPReg(..), GPRegUse(..)
  , VecReg(..)
  , FPReg(..)

  , Flag(..)
  , X87Status(..)
  , X87Top(..)
  , X87Tag(..)

    -- * Connection with other tools
  , Sym
  , runPreSpec
  , runPostSpec
  , Rep
  , fromValue

  ) where

import Data.Kind(Type)
import GHC.TypeLits
import Control.Monad(liftM,ap)
import Control.Lens((^.))

import Data.Parameterized.Nonce(GlobalNonceGenerator)
import Data.Parameterized.Classes(KnownRepr(knownRepr))
import Data.Parameterized.NatRepr
import Data.Parameterized.Context(Assignment,field,Idx)

import Lang.Crucible.Types(CrucibleType,TypeRepr,BoolType)
import Lang.Crucible.BaseTypes
        (BaseTypeRepr(BaseBVRepr,BaseNatRepr,BaseBoolRepr))
import Lang.Crucible.Simulator.RegValue(RegValue,RegValue'(unRV))
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


import Data.Macaw.Symbolic.CrucGen(MacawCrucibleRegTypes)
import Data.Macaw.X86.ArchTypes(X86_64)
import qualified Data.Macaw.X86.Symbolic as M
        (IP,GP,Flag,X87Status,X87Top,X87Tag,FPReg,YMM)
import Data.Macaw.Symbolic.PersistentState()

import Verifier.SAW.SharedTerm(Term)


-- | The kind of X86 types.
data {- kind -} X86Type =
    AByte | AWord | ADWord | AQWord | AVec | APtr
  | ABool
  | ABits3
  | ABits2
  | ABigFloat

type AByte      = 'AByte
type AWord      = 'AWord
type ADWord     = 'ADWord
type AQWord     = 'AQWord
type AVec       = 'AVec
type APtr       = 'APtr
type ABool      = 'ABool
type ABits2     = 'ABits2
type ABits3     = 'ABits3
type ABigFloat  = 'ABigFloat


data X86 :: X86Type -> Type where
  Byte      :: X86 AByte
  Word      :: X86 AWord
  DWord     :: X86 ADWord
  QWord     :: X86 AQWord
  Vec       :: X86 AVec
  Ptr       :: X86 APtr
  Bool      :: X86 ABool
  Bits2     :: X86 ABits2
  Bits3     :: X86 ABits3
  BigFloat  :: X86 ABigFloat

type family Rep (x :: X86Type) :: CrucibleType where
  Rep AByte       = LLVMPointerType 8
  Rep AWord       = LLVMPointerType 16
  Rep ADWord      = LLVMPointerType 32
  Rep AQWord      = LLVMPointerType 64
  Rep AVec        = LLVMPointerType 256
  Rep APtr        = LLVMPointerType 64
  Rep ABool       = BoolType
  Rep ABits2      = LLVMPointerType 2
  Rep ABits3      = LLVMPointerType 3
  Rep ABigFloat   = LLVMPointerType 80  -- or something eles?

crucRepr :: X86 t -> TypeRepr (Rep t)
crucRepr x =
  case x of
    Byte     -> knownRepr
    Word     -> knownRepr
    DWord    -> knownRepr
    QWord    -> knownRepr
    Vec      -> knownRepr
    Ptr      -> knownRepr
    Bool     -> knownRepr
    Bits2    -> knownRepr
    Bits3    -> knownRepr
    BigFloat -> knownRepr

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

type family BitSize (x :: X86Type) :: Nat where
  BitSize AByte     = 8
  BitSize AWord     = 16
  BitSize ADWord    = 32
  BitSize AQWord    = 64
  BitSize AVec      = 256
  BitSize APtr      = 64
  BitSize ABool     = 1   -- XXX: Type error?
  BitSize ABits2    = 2
  BitSize ABits3    = 3
  BitSize ABigFloat = 80

bitSizeNat :: forall t. X86 t -> NatRepr (BitSize t)
bitSizeNat x =
  case x of
    Byte     -> knownNat @(BitSize t)
    Word     -> knownNat @(BitSize t)
    DWord    -> knownNat @(BitSize t)
    QWord    -> knownNat @(BitSize t)
    Vec      -> knownNat @(BitSize t)
    Ptr      -> knownNat @(BitSize t)
    Bool     -> knownNat @(BitSize t)
    Bits2    -> knownNat @(BitSize t)
    Bits3    -> knownNat @(BitSize t)
    BigFloat -> knownNat @(BitSize t)

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

-- | Is this a pre- or post-condition specificiation.
data {- kind -} SpecType = Pre | Post

type Pre  = 'Pre
type Post = 'Post

newtype Spec (p :: SpecType) a =
  Spec (Sym -> RR p -> RegValue Sym Mem -> IO (a, RegValue Sym Mem))

runPreSpec :: Sym -> RegValue Sym Mem -> Spec Pre a -> IO (a, RegValue Sym Mem)
runPreSpec sym mem (Spec f) = f sym () mem

runPostSpec ::
  Sym ->
  Assignment (RegValue' Sym) (MacawCrucibleRegTypes X86_64) ->
  RegValue Sym Mem ->
  Spec Post a ->
  IO a
runPostSpec sym rs mem (Spec f) = fst <$> f sym rs  mem

type family RR (x :: SpecType) where
  RR Pre = ()
  RR Post = Assignment (RegValue' Sym) (MacawCrucibleRegTypes X86_64)

instance Functor (Spec p) where fmap = liftM

instance Applicative (Spec p) where
  pure a = Spec (\_ _ m -> return (a,m))
  (<*>) = ap

instance Monad (Spec p) where
  Spec m >>= k = Spec (\r x s -> do (a, s1) <- m r x s
                                    let Spec m1 = k a
                                    m1 r x s1)

io :: IO a -> Spec p a
io m = Spec (\_ _ s -> do a <- m
                          return (a,s))

getSym :: Spec p Sym
getSym = Spec (\r _ s -> return (r,s))

updMem :: (Sym -> RegValue Sym Mem -> IO (a, RegValue Sym Mem)) -> Spec Pre a
updMem f = Spec (\r _ s -> f r s)

updMem_ :: (Sym -> RegValue Sym Mem -> IO (RegValue Sym Mem)) -> Spec Pre ()
updMem_ f = updMem (\sym mem -> do mem1 <- f sym mem
                                   return ((),mem1))

withMem :: (Sym -> RegValue Sym Mem -> IO a) -> Spec p a
withMem f = Spec (\r _ s -> f r s >>= \a -> return (a,s))

getRegs :: Spec Post (Assignment (RegValue' Sym) (MacawCrucibleRegTypes X86_64))
getRegs = Spec (\_ r s -> return (r,s))


--------------------------------------------------------------------------------
-- Fresh values

-- | Generate an unknonw value of the given type.
fresh :: X86 t -> String -> Spec Pre (Value t)
fresh x str =
  case x of
    Byte      -> freshBits str x
    Word      -> freshBits str x
    DWord     -> freshBits str x
    QWord     -> freshBits str x
    Vec       -> freshBits str x
    Ptr       -> freshPtr  str
    Bool      -> freshBool str
    Bits2     -> freshBits str x
    Bits3     -> freshBits str x
    BigFloat  -> freshBits str x

-- | An uninitialized boolean value.
freshBool :: String -> Spec Pre (Value ABool)
freshBool str =
  do sym <- getSym
     io $ do nm <- symName str
             Value <$> freshConstant sym nm BaseBoolRepr



-- | Generate a fresh bit-vector thing.
freshBits ::
  (Rep t ~ LLVMPointerType (BitSize t), 1 <= BitSize t) =>
  String ->
  X86 t ->
  Spec Pre (Value t)
freshBits str x =
  do sym <- getSym
     io $ do nm <- symName str
             bv <- freshConstant sym nm (BaseBVRepr (bitSizeNat x))
             value x <$> llvmPointer_bv sym bv



-- | An uninitialized pointer value.
freshPtr :: String -> Spec Pre (Value APtr)
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

--------------------------------------------------------------------------------
-- SAW terms

class SAW (t :: X86Type) where
  saw :: X86 t -> Term -> Spec p (Value t)

instance SAW ABool where
  saw _ val =
    do sym <- getSym
       Value <$> io (bindSAWTerm sym BaseBoolRepr val)

instance SAW AByte  where saw = sawBits
instance SAW AWord  where saw = sawBits
instance SAW ADWord where saw = sawBits
instance SAW AQWord where saw = sawBits
instance SAW AVec   where saw = sawBits
instance SAW ABits2 where saw = sawBits
instance SAW ABits3 where saw = sawBits

sawBits ::
  (Rep t ~ LLVMPointerType (BitSize t), 1 <= BitSize t) =>
  X86 t -> Term -> Spec p (Value t)
sawBits w val =
  do sym <- getSym
     io $ do bv <- bindSAWTerm sym (BaseBVRepr (bitSizeNat w)) val
             value w <$> llvmPointer_bv sym bv


--------------------------------------------------------------------------------
-- Literals

-- | Types that support literals.
class Literal (t :: X86Type) where
  type Lit t
  literal :: X86 t -> Lit t -> Spec p (Value t)

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

instance Literal ABits2 where
  type Lit ABits2 = Integer
  literal = literalBits

instance Literal ABits3 where
  type Lit ABits3 = Integer
  literal = literalBits

-- XXX: Big float?

-- | A concrete bit-vector.
literalBits ::
  (Rep t ~ LLVMPointerType (BitSize t), 1 <= BitSize t) =>
  X86 t -> Integer -> Spec p (Value t)
literalBits w val =
  do sym      <- getSym
     value w <$> io (llvmPointer_bv sym =<< bvLit sym (bitSizeNat w) val)



--------------------------------------------------------------------------------
-- Memory

-- | Write a value to memory.
writeMem :: MemType t => X86 t -> Value APtr -> Value t -> Spec Pre ()
writeMem w (Value p) (Value x) =
  updMem_ $ \sym mem ->
    let ?ptrWidth = knownNat
    in doStore sym mem p (crucRepr w) (llvmType w) x

-- | Read a value from memory.
readMem :: MemType t => X86 t -> Value APtr -> Spec Post (Value t)
readMem w (Value p) =
  withMem $ \sym mem ->
    do let ?ptrWidth = knownNat
       anyV <- doLoad sym mem p (llvmType w) 0
       Value <$> coerceAny sym (crucRepr w) anyV


-- | Allocate a pointer that points to the given number of bytes (on the heap).
-- The allocated memory is not initialized, so it should not be read until
-- it has been initialized.
allocBytes :: String -> Mutability -> Value AQWord -> Spec Pre (Value APtr)
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
  Spec Pre (Value APtr)
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
  Spec Post [ Value t ]
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


--------------------------------------------------------------------------------
-- Registers

-- | Get the value of a register.
class GetReg a where
  type RegType a :: X86Type
  getReg :: a -> Spec Post (Value (RegType a))

regValue ::
  forall n t. (Idx n (MacawCrucibleRegTypes X86_64) (Rep t)) =>
  Spec Post (Value t)
regValue =
  do regs <- getRegs
     return (Value (unRV (regs ^. (field @n))))

regValueGP ::
  forall n t. (Idx n (MacawCrucibleRegTypes X86_64) (LLVMPointerType 64)) =>
  GPRegUse t -> Spec Post (Value t)
regValueGP how = case how of
                   AsBits -> regValue @n @AQWord
                   AsPtr  -> regValue @n @APtr

-- | Instruciotn pointer.
data IP = IP

instance GetReg IP where
  type RegType IP = AQWord
  getReg _ = regValue @M.IP

-- | General purpose register.
data GPReg = RAX | RBX | RCX | RDX | RSI | RDI | RSP | RBP
           | R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15

-- | General purpose reigsters may contain either a bit-value or a pointer.
-- This type specifies which form we want to access.
data GPRegUse :: X86Type -> Type where
  AsBits :: GPRegUse AQWord
  AsPtr  :: GPRegUse APtr


instance GetReg (GPReg,GPRegUse t) where
  type RegType (GPReg,GPRegUse t) = t
  getReg (x,use) =
    case x of
      RAX -> regValueGP @(M.GP  0) use
      RBX -> regValueGP @(M.GP  1) use
      RCX -> regValueGP @(M.GP  2) use
      RDX -> regValueGP @(M.GP  3) use
      RSI -> regValueGP @(M.GP  4) use
      RDI -> regValueGP @(M.GP  5) use
      RSP -> regValueGP @(M.GP  6) use
      RBP -> regValueGP @(M.GP  7) use
      R8  -> regValueGP @(M.GP  8) use
      R9  -> regValueGP @(M.GP  9) use
      R10 -> regValueGP @(M.GP 10) use
      R11 -> regValueGP @(M.GP 11) use
      R12 -> regValueGP @(M.GP 12) use
      R13 -> regValueGP @(M.GP 13) use
      R14 -> regValueGP @(M.GP 14) use
      R15 -> regValueGP @(M.GP 15) use

-- | CPU flags
data Flag = CF | PF | AF | ZF | SF | TF | IF | DF | OF

instance GetReg Flag where
  type RegType Flag = ABool
  getReg f =
    case f of
      CF -> regValue @(M.Flag 0)
      PF -> regValue @(M.Flag 1)
      AF -> regValue @(M.Flag 2)
      ZF -> regValue @(M.Flag 3)
      SF -> regValue @(M.Flag 4)
      TF -> regValue @(M.Flag 5)
      IF -> regValue @(M.Flag 6)
      DF -> regValue @(M.Flag 7)
      OF -> regValue @(M.Flag 8)

-- | Vector registers.
data VecReg =
    YMM0  | YMM1  | YMM2  | YMM3  | YMM4  | YMM5  | YMM6  | YMM7
  | YMM8  | YMM9  | YMM10 | YMM11 | YMM12 | YMM13 | YMM14 | YMM15

instance GetReg VecReg where
  type RegType VecReg = AVec
  getReg f =
    case f of
      YMM0  -> regValue @(M.YMM 0)
      YMM1  -> regValue @(M.YMM 1)
      YMM2  -> regValue @(M.YMM 2)
      YMM3  -> regValue @(M.YMM 3)
      YMM4  -> regValue @(M.YMM 4)
      YMM5  -> regValue @(M.YMM 5)
      YMM6  -> regValue @(M.YMM 6)
      YMM7  -> regValue @(M.YMM 7)
      YMM8  -> regValue @(M.YMM 8)
      YMM9  -> regValue @(M.YMM 9)
      YMM10 -> regValue @(M.YMM 10)
      YMM11 -> regValue @(M.YMM 11)
      YMM12 -> regValue @(M.YMM 12)
      YMM13 -> regValue @(M.YMM 13)
      YMM14 -> regValue @(M.YMM 14)
      YMM15 -> regValue @(M.YMM 15)

-- | X87 status registers.
data X87Status = X87_IE | X87_DE | X87_ZE | X87_OE
               | X87_UE | X87_PE | X87_EF | X87_ES
               | X87_C0 | X87_C1 | X87_C2 | X87_C3

instance GetReg X87Status where
  type RegType X87Status = ABool
  getReg f =
    case f of
      X87_IE -> regValue @(M.X87Status 0)
      X87_DE -> regValue @(M.X87Status 1)
      X87_ZE -> regValue @(M.X87Status 2)
      X87_OE -> regValue @(M.X87Status 3)
      X87_UE -> regValue @(M.X87Status 4)
      X87_PE -> regValue @(M.X87Status 5)
      X87_EF -> regValue @(M.X87Status 6)
      X87_ES -> regValue @(M.X87Status 7)
      X87_C0 -> regValue @(M.X87Status 8)
      X87_C1 -> regValue @(M.X87Status 9)
      X87_C2 -> regValue @(M.X87Status 10)
      X87_C3 -> regValue @(M.X87Status 11)
      -- Note: C3 is bit 14 in the x87 FPU status word.
      -- However, our register representation has a separate variable for
      -- each status flag.  So the 11 here refers to the number of the
      -- variable, not the index into the status word.

-- | Top of X87 register stack.
data X87Top = X87Top

instance GetReg X87Top where
  type RegType X87Top = ABits3
  getReg _ = regValue @M.X87Top


-- | X87 tags.
data X87Tag = Tag0 | Tag1 | Tag2 | Tag3
            | Tag4 | Tag5 | Tag6 | Tag7

instance GetReg X87Tag where
  type RegType X87Tag = ABits2
  getReg t =
    case t of
      Tag0 -> regValue @(M.X87Tag 0)
      Tag1 -> regValue @(M.X87Tag 1)
      Tag2 -> regValue @(M.X87Tag 2)
      Tag3 -> regValue @(M.X87Tag 3)
      Tag4 -> regValue @(M.X87Tag 4)
      Tag5 -> regValue @(M.X87Tag 5)
      Tag6 -> regValue @(M.X87Tag 6)
      Tag7 -> regValue @(M.X87Tag 7)

-- | 80-bit floating point registers.
data FPReg = FPReg0 | FPReg1 | FPReg2 | FPReg3
           | FPReg4 | FPReg5 | FPReg6 | FPReg7


instance GetReg FPReg where
  type RegType FPReg = ABigFloat
  getReg t =
    case t of
      FPReg0 -> regValue @(M.FPReg 0)
      FPReg1 -> regValue @(M.FPReg 1)
      FPReg2 -> regValue @(M.FPReg 2)
      FPReg3 -> regValue @(M.FPReg 3)
      FPReg4 -> regValue @(M.FPReg 4)
      FPReg5 -> regValue @(M.FPReg 5)
      FPReg6 -> regValue @(M.FPReg 6)
      FPReg7 -> regValue @(M.FPReg 7)


