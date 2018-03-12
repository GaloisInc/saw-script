{-# Language DataKinds #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}
{-# Language PatternSynonyms #-}
module SAWScript.X86Spec.Fresh (fresh, freshGP, freshRegs, elemList) where

import GHC.TypeLits (type (<=))
import qualified Data.Vector as Vector

import Data.Parameterized.NatRepr(knownNat)

import Lang.Crucible.BaseTypes (BaseTypeRepr(BaseBVRepr,BaseNatRepr,BaseBoolRepr))
import Lang.Crucible.Solver.Symbol(SolverSymbol,userSymbol)
import Lang.Crucible.Solver.Interface(freshConstant)
import Lang.Crucible.LLVM.MemModel ( LLVMPointerType )
import Lang.Crucible.LLVM.MemModel.Pointer( pattern LLVMPointer, llvmPointer_bv )

import SAWScript.X86Spec.Types
import SAWScript.X86Spec.Monad
import SAWScript.X86Spec.Registers


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
  withSym $ \sym ->
    do nm <- symName str
       Value <$> freshConstant sym nm BaseBoolRepr



-- | Generate a fresh bit-vector thing.
freshBits ::
  (Rep t ~ LLVMPointerType (BitSize t), 1 <= BitSize t) =>
  String ->
  X86 t ->
  Spec Pre (Value t)
freshBits str x =
  withSym $ \sym ->
     do nm <- symName str
        bv <- freshConstant sym nm (BaseBVRepr (bitSize x))
        value x <$> llvmPointer_bv sym bv



-- | An uninitialized pointer value.
freshPtr :: String -> Spec Pre (Value APtr)
freshPtr str =
  do ptr <- withSym $ \sym ->
            do base_nm <- symName (str ++ "_base")
               off_nm  <- symName (str ++ "_offset")
               base    <- freshConstant sym base_nm BaseNatRepr
               offs    <- freshConstant sym off_nm (BaseBVRepr knownNat)
               return (Value (LLVMPointer base offs))
     isPtr ptr True
     return ptr

-- | Generate a fresh value for a general purpose register.
freshGP :: GPReg -> GPRegUse t -> Spec Pre (Value t)
freshGP x u =
  case u of
    AsBits -> fresh QWord (show x)
    AsPtr  -> fresh Ptr   (show x)


-- | Generate fresh values for a class of registers.
freshRegs ::
  forall a.
  (Show a, Enum a, Bounded a, Infer (RegType a)) =>
  Spec Pre (a -> Value (RegType a))
freshRegs =
  do vs <- Vector.fromList <$>
              mapM (\a -> fresh infer (show (a :: a))) elemList
     return (\x -> vs Vector.! fromEnum x)

symName :: String -> IO SolverSymbol
symName s = case userSymbol s of
              Left err -> fail (show err)
              Right a  -> return a


elemList :: (Enum a, Bounded a) => [a]
elemList = [ minBound .. maxBound ]
