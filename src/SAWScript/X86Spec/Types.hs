{-# Language DataKinds #-}
{-# Language GADTs #-}
{-# Language KindSignatures #-}
{-# Language TypeApplications #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeFamilies #-}
{-# Language TypeSynonymInstances #-}
{-# Language PatternSynonyms #-}
{-# Language ViewPatterns #-}
{-# Language TypeOperators #-}

module SAWScript.X86Spec.Types
  ( X86Type
  , Bits, APtr, ABool, ABigFloat
  , X86(..)
  , Infer(..)
  , typeOf
  , BitSize, bitSize

  , pattern Byte
  , pattern Word
  , pattern DWord
  , pattern QWord
  , pattern V128
  , pattern V256

  -- * Mapping to Crucible
  , Sym, Rep, crucRepr

  -- * Values
  , Value(..), value
  ) where

import Data.Kind(Type)
import GHC.TypeLits(Nat,KnownNat)

import Data.Parameterized.NatRepr
import Data.Parameterized.Classes(knownRepr)
import Data.Parameterized.Nonce(GlobalNonceGenerator)

import Lang.Crucible.Types(CrucibleType,TypeRepr,BoolType)
import Lang.Crucible.Simulator.RegValue(RegValue)
import Lang.Crucible.Solver.SAWCoreBackend(SAWCoreBackend)
import Lang.Crucible.LLVM.MemModel(LLVMPointerType,pattern LLVMPointerRepr)


-- | The kind of X86 types.
data {- kind -} X86Type = APtr | ABits Nat | ABool | ABigFloat

type Bits       = 'ABits
type APtr       = 'APtr
type ABool      = 'ABool
type ABigFloat  = 'ABigFloat

pattern Byte :: () => (t ~ Bits 8) => X86 t
pattern Byte <- Bits (testEquality n8 -> Just Refl)
  where Byte = Bits n8

pattern Word :: () => (t ~ Bits 16) => X86 t
pattern Word <- Bits (testEquality n16 -> Just Refl)
  where Word = Bits n16

pattern DWord :: () => (t ~ Bits 32) => X86 t
pattern DWord <- Bits (testEquality n32 -> Just Refl)
  where DWord = Bits n32

pattern QWord :: () => (t ~ Bits 64) => X86 t
pattern QWord <- Bits (testEquality n64 -> Just Refl)
  where QWord = Bits n64

pattern V128 :: () => (t ~ Bits 128) => X86 t
pattern V128 <- Bits (testEquality n128 -> Just Refl)
  where V128 = Bits n128

pattern V256 :: () => (t ~ Bits 256) => X86 t
pattern V256 <- Bits (testEquality n256 -> Just Refl)
  where V256 = Bits n256


n8 :: NatRepr 8
n8 = knownNat

n16 :: NatRepr 16
n16 = knownNat

n32 :: NatRepr 32
n32  = knownNat

n64 :: NatRepr 64
n64 = knownNat

n128 :: NatRepr 128
n128 = knownNat

n256 :: NatRepr 256
n256 = knownNat


-- | This type is used to specify types explicitly.
data X86 :: X86Type -> Type where
  Bits      :: (1 <= n) => NatRepr n -> X86 (Bits n)
  Ptr       :: X86 APtr
  Bool      :: X86 ABool
  BigFloat  :: X86 ABigFloat

-- | This type may be used to specify types implicitly
-- (i.e., in contexts where the type can be inferred automatically).
class Infer t where
  infer :: X86 t

instance (1 <= n, KnownNat n) =>
         Infer (Bits n)  where infer = Bits knownNat
instance Infer APtr      where infer = Ptr
instance Infer ABool     where infer = Bool
instance Infer ABigFloat where infer = BigFloat

-- | Get the type of something with at ype.
typeOf :: Infer t => p t -> X86 t
typeOf _ = infer


-- | Mapping from X86 types to the Crucible types used to implement them.
type family Rep (x :: X86Type) :: CrucibleType where
  Rep (Bits n)    = LLVMPointerType n   -- or just BVType?
  Rep APtr        = LLVMPointerType 64
  Rep ABool       = BoolType
  Rep ABigFloat   = LLVMPointerType 80  -- or something eles?

-- | Specify a crucible type expclitily.
crucRepr :: X86 t -> TypeRepr (Rep t)
crucRepr x =
  case x of
    Bits n   -> LLVMPointerRepr n
    Ptr      -> knownRepr
    Bool     -> knownRepr
    BigFloat -> knownRepr

-- | Size of types in bits.
type family BitSize (x :: X86Type) :: Nat where
  BitSize (Bits n) = n
  BitSize APtr      = 64
  BitSize ABool     = 1
  BitSize ABigFloat = 80

-- | A value level nubmer for the size of the type.
bitSize :: forall t. X86 t -> NatRepr (BitSize t)
bitSize x =
  case x of
    Bits n   -> n
    Ptr      -> knownNat @(BitSize t)
    Bool     -> knownNat @(BitSize t)
    BigFloat -> knownNat @(BitSize t)



-- | The Crucible backend used for speicifcations.
type Sym = SAWCoreBackend GlobalNonceGenerator

-- | A value in a X86 specification.
newtype Value t = Value (RegValue Sym (Rep t))

-- | A helper for constructing values of a specific type.
value :: proxy t -> RegValue Sym (Rep t) -> Value t
value _ x = Value x


