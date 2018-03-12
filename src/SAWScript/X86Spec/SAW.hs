{-# Language DataKinds #-}
{-# Language TypeOperators #-}
{-# Language TypeSynonymInstances #-}
{-# Language TypeFamilies #-}
module SAWScript.X86Spec.SAW (SAW(..)) where

import GHC.TypeLits (type (<=))

import Lang.Crucible.BaseTypes (BaseTypeRepr(BaseBVRepr,BaseBoolRepr))
import Lang.Crucible.LLVM.MemModel ( LLVMPointerType )
import Lang.Crucible.LLVM.MemModel.Pointer (llvmPointer_bv, projectLLVM_bv)
import Lang.Crucible.Solver.SAWCoreBackend(bindSAWTerm, toSC)

import Verifier.SAW.SharedTerm(Term)

import SAWScript.X86Spec.Types
import SAWScript.X86Spec.Monad

-- | Convert between values and SAW Core terms.
class SAW t where
  saw   :: X86 t -> Term -> Spec p (Value t)
  toSAW :: Value t -> Spec p Term

instance SAW ABool where
  saw _ val = withSym $ \sym -> Value <$> bindSAWTerm sym BaseBoolRepr val
  toSAW (Value v) = withSym $ \sym -> toSC sym v

instance SAW AByte  where saw = sawBits; toSAW = toSawBits
instance SAW AWord  where saw = sawBits; toSAW = toSawBits
instance SAW ADWord where saw = sawBits; toSAW = toSawBits
instance SAW AQWord where saw = sawBits; toSAW = toSawBits
instance SAW AVec   where saw = sawBits; toSAW = toSawBits
instance SAW ABits2 where saw = sawBits; toSAW = toSawBits
instance SAW ABits3 where saw = sawBits; toSAW = toSawBits

sawBits ::
  (Rep t ~ LLVMPointerType (BitSize t), 1 <= BitSize t) =>
  X86 t -> Term -> Spec p (Value t)
sawBits w val =
  withSym $ \sym -> do bv <- bindSAWTerm sym (BaseBVRepr (bitSize w)) val
                       value w <$> llvmPointer_bv sym bv

toSawBits ::
  (Rep t ~ LLVMPointerType (BitSize t), 1 <= BitSize t) =>
  Value t -> Spec p Term
toSawBits (Value v) = withSym $ \sym -> toSC sym =<< projectLLVM_bv sym v


