{-# Language DataKinds #-}
{-# Language TypeOperators #-}
{-# Language TypeFamilies #-}
{-# Language TypeSynonymInstances #-}
module SAWScript.X86Spec.Literal (literal, Literal(..)) where

import GHC.TypeLits (type (<=))

import Lang.Crucible.Solver.Interface(bvLit, truePred, falsePred)
import Lang.Crucible.LLVM.MemModel ( LLVMPointerType )
import Lang.Crucible.LLVM.MemModel.Pointer (llvmPointer_bv)

import SAWScript.X86Spec.Types
import SAWScript.X86Spec.Monad

-- | Types that support literals.
class Literal t where
  type Lit t
  literalAt :: X86 t -> Lit t -> Spec p (Value t)

literal :: (Literal t, Infer t) => Lit t -> Spec p (Value t)
literal = literalAt infer

instance Literal ABool where
  type Lit ABool = Bool
  literalAt _ b =
    do sym <- getSym
       return (Value (if b then truePred sym else falsePred sym))

instance Literal AByte where
  type Lit AByte = Integer
  literalAt = literalBits

instance Literal AWord where
  type Lit AWord = Integer
  literalAt = literalBits

instance Literal ADWord where
  type Lit ADWord = Integer
  literalAt = literalBits

instance Literal AQWord where
  type Lit AQWord = Integer
  literalAt = literalBits

instance Literal AVec where
  type Lit AVec = Integer
  literalAt = literalBits

instance Literal ABits2 where
  type Lit ABits2 = Integer
  literalAt = literalBits

instance Literal ABits3 where
  type Lit ABits3 = Integer
  literalAt = literalBits

-- XXX: Big float?

-- | A concrete bit-vector.
literalBits ::
  (Rep t ~ LLVMPointerType (BitSize t), 1 <= BitSize t) =>
  X86 t -> Integer -> Spec p (Value t)
literalBits w val =
  withSym $ \sym ->
    value w <$> (llvmPointer_bv sym =<< bvLit sym (bitSize w) val)


