{-# Language DataKinds #-}
{-# Language TypeOperators #-}
{-# Language TypeSynonymInstances #-}
{-# Language TypeFamilies #-}
module SAWScript.X86Spec.SAW (SAW(..)) where

import Lang.Crucible.BaseTypes (BaseTypeRepr(BaseBVRepr,BaseBoolRepr))
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

instance SAW (Bits n) where
  saw (Bits w) val =
    withSym $ \sym -> do bv <- bindSAWTerm sym (BaseBVRepr w) val
                         value (Bits w) <$> llvmPointer_bv sym bv
  toSAW (Value v) = withSym $ \sym -> toSC sym =<< projectLLVM_bv sym v

