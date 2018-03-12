{-# Language DataKinds #-}
{-# Language GADTs #-}
{-# Language KindSignatures #-}
{-# Language TypeApplications #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeFamilies #-}
{-# Language TypeSynonymInstances #-}
module SAWScript.X86Spec.Types
  ( X86Type
  , AByte, AWord, ADWord, AQWord, AVec, APtr, ABool, ABits2, ABits3, ABigFloat
  , X86(..)
  , Infer(..)
  , typeOf
  , BitSize, bitSize

  -- * Mapping to Crucible
  , Sym, Rep, crucRepr

  -- * Values
  , Value(..), value
  ) where

import Data.Kind(Type)
import GHC.TypeLits(Nat)

import Data.Parameterized.NatRepr(NatRepr,knownNat)
import Data.Parameterized.Classes(knownRepr)
import Data.Parameterized.Nonce(GlobalNonceGenerator)

import Lang.Crucible.Types(CrucibleType,TypeRepr,BoolType)
import Lang.Crucible.Simulator.RegValue(RegValue)
import Lang.Crucible.Solver.SAWCoreBackend(SAWCoreBackend)
import Lang.Crucible.LLVM.MemModel(LLVMPointerType)


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


-- | This type is used to specify types explicitly.
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

-- | This type may be used to specify types implicitly
-- (i.e., in contexts where the type can be inferred automatically).
class Infer t where
  infer :: X86 t

instance Infer AByte     where infer = Byte
instance Infer AWord     where infer = Word
instance Infer ADWord    where infer = DWord
instance Infer AQWord    where infer = QWord
instance Infer AVec      where infer = Vec
instance Infer APtr      where infer = Ptr
instance Infer ABool     where infer = Bool
instance Infer ABits2    where infer = Bits2
instance Infer ABits3    where infer = Bits3
instance Infer ABigFloat where infer = BigFloat

-- | Get the type of something with at ype.
typeOf :: Infer t => p t -> X86 t
typeOf _ = infer


-- | Mapping from X86 types to the Crucible types used to implement them.
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

-- | Specify a crucible type expclitily.
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

-- | Size of types in bits.
type family BitSize (x :: X86Type) :: Nat where
  BitSize AByte     = 8
  BitSize AWord     = 16
  BitSize ADWord    = 32
  BitSize AQWord    = 64
  BitSize AVec      = 256
  BitSize APtr      = 64
  BitSize ABool     = 1
  BitSize ABits2    = 2
  BitSize ABits3    = 3
  BitSize ABigFloat = 80

-- | A value level nubmer for the size of the type.
bitSize :: forall t. X86 t -> NatRepr (BitSize t)
bitSize x =
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



-- | The Crucible backend used for speicifcations.
type Sym = SAWCoreBackend GlobalNonceGenerator

-- | A value in a X86 specification.
newtype Value t = Value (RegValue Sym (Rep t))

-- | A helper for constructing values of a specific type.
value :: proxy t -> RegValue Sym (Rep t) -> Value t
value _ x = Value x


