{-# Language DataKinds #-}
{-# Language TypeOperators #-}
{-# Language TypeFamilies #-}
{-# Language TypeSynonymInstances #-}
module SAWScript.X86Spec.Literal (literal, Literal(..)) where

import GHC.TypeLits (type (<=))

import Lang.Crucible.Solver.Interface(bvLit, truePred, falsePred)
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

instance (1 <= n) => Literal (Bits n) where
  type Lit (Bits n) = Integer
  literalAt (Bits w) val =
    withSym $ \sym ->
      value (Bits w) <$> (llvmPointer_bv sym =<< bvLit sym w val)

-- XXX: Big float?



