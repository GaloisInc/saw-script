{-# Language RecordWildCards #-}
{-# Language TypeSynonymInstances #-}
{-# Language GADTs #-}
{-# Language TypeFamilies #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeApplications #-}
{-# Language DataKinds #-}
{-# Language FlexibleInstances #-}
{-# Language FlexibleContexts #-}
{-# Language AllowAmbiguousTypes #-}
module SAWScript.X86Spec.Registers
  ( -- * Register names
    IP(..)
  , GPReg(..)
  , Flag(..)
  , VecReg(..)
  , X87Status(..)
  , X87Top(..)
  , X87Tag(..)
  , FPReg(..)

    -- * Accessing Register
  , RegType
  , GetReg(..)

   -- * Register assignment
  , RegAssign(..)
  , GPRegVal(..), GPValue(..), GPRegUse(..)
  , macawLookup
  ) where

import Control.Lens((^.))

import qualified Flexdis86 as F

import Data.Parameterized.Context(field,Idx)

import Lang.Crucible.Simulator.RegValue(RegValue'(RV,unRV))
import Lang.Crucible.LLVM.MemModel(LLVMPointerType)

import Data.Macaw.Symbolic.PersistentState(ToCrucibleType)
import qualified Data.Macaw.X86.X86Reg as R
import qualified Data.Macaw.X86.Symbolic as M
        (IP,GP,Flag,X87Status,X87Top,X87Tag,FPReg,YMM)
import Data.Macaw.Symbolic.CrucGen(MacawCrucibleRegTypes)
import Data.Macaw.X86.ArchTypes(X86_64)

import SAWScript.X86Spec.Types
import SAWScript.X86Spec.Monad


-- | Instruciotn pointer.
data IP = IP
  deriving (Show,Eq,Ord,Enum,Bounded)

-- | General purpose register.
data GPReg = RAX | RBX | RCX | RDX | RSI | RDI | RSP | RBP
           | R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15
  deriving (Show,Eq,Ord,Enum,Bounded)

-- | General purpose reigsters may contain either a bit-value or a pointer.
-- This type specifies which form we want to access.
data GPRegUse t where
  AsBits :: GPRegUse AQWord
  AsPtr  :: GPRegUse APtr

-- | The value of a general purpose register.
data GPRegVal = GPBits (Value AQWord) | GPPtr (Value APtr)

-- | A convenient way to construct general purpose values, based on their type.
class GPValue t where
  gpValue :: Value t -> GPRegVal

instance GPValue AQWord where gpValue = GPBits
instance GPValue APtr   where gpValue = GPPtr


-- | CPU flags
data Flag = CF | PF | AF | ZF | SF | TF | IF | DF | OF
  deriving (Show,Eq,Ord,Enum,Bounded)


-- | Vector registers.
data VecReg =
    YMM0  | YMM1  | YMM2  | YMM3  | YMM4  | YMM5  | YMM6  | YMM7
  | YMM8  | YMM9  | YMM10 | YMM11 | YMM12 | YMM13 | YMM14 | YMM15
  deriving (Show,Eq,Ord,Enum,Bounded)


-- | X87 status registers.
data X87Status = X87_IE | X87_DE | X87_ZE | X87_OE
               | X87_UE | X87_PE | X87_EF | X87_ES
               | X87_C0 | X87_C1 | X87_C2 | X87_C3
              deriving (Show,Eq,Ord,Enum,Bounded)


-- | Top of X87 register stack.
data X87Top = X87Top
              deriving (Show,Eq,Ord,Enum,Bounded)

-- | X87 tags.
data X87Tag = Tag0 | Tag1 | Tag2 | Tag3
            | Tag4 | Tag5 | Tag6 | Tag7
              deriving (Show,Eq,Ord,Enum,Bounded)

-- | 80-bit floating point registers.
data FPReg = FP0 | FP1 | FP2 | FP3 | FP4 | FP5 | FP6 | FP7
              deriving (Show,Eq,Ord,Enum,Bounded)


-- | A register assignment.
data RegAssign = RegAssign
  { valIP         ::               Value AQWord
  , valGPReg      :: GPReg      -> GPRegVal
  , valVecReg     :: VecReg     -> Value AVec
  , valFPReg      :: FPReg      -> Value ABigFloat
  , valFlag       :: Flag       -> Value ABool
  , valX87Status  :: X87Status  -> Value ABool
  , valX87Top     ::               Value ABits3
  , valX87Tag     :: X87Tag     -> Value ABits2
  }


-- | Convert a register assignment to a form suitable for Macaw CFG generation.
macawLookup :: RegAssign -> R.X86Reg t -> RegValue' Sym (ToCrucibleType t)
macawLookup RegAssign { .. } reg =
  case reg of
    R.X86_IP -> toRV valIP

    R.RAX -> gp RAX
    R.RBX -> gp RBX
    R.RCX -> gp RCX
    R.RDX -> gp RDX
    R.RSI -> gp RSI
    R.RDI -> gp RDI
    R.RSP -> gp RSP
    R.RBP -> gp RBP
    R.R8  -> gp R8
    R.R9  -> gp R9
    R.R10 -> gp R10
    R.R11 -> gp R11
    R.R12 -> gp R12
    R.R13 -> gp R13
    R.R14 -> gp R14
    R.R15 -> gp R15
    R.X86_GP _ -> error "[bug] Unexpecet general purpose register."

    R.YMM (F.YMMR 0)  -> vec YMM0
    R.YMM (F.YMMR 1)  -> vec YMM1
    R.YMM (F.YMMR 2)  -> vec YMM2
    R.YMM (F.YMMR 3)  -> vec YMM3
    R.YMM (F.YMMR 4)  -> vec YMM4
    R.YMM (F.YMMR 5)  -> vec YMM5
    R.YMM (F.YMMR 6)  -> vec YMM6
    R.YMM (F.YMMR 7)  -> vec YMM7
    R.YMM (F.YMMR 8)  -> vec YMM8
    R.YMM (F.YMMR 9)  -> vec YMM9
    R.YMM (F.YMMR 10) -> vec YMM10
    R.YMM (F.YMMR 11) -> vec YMM11
    R.YMM (F.YMMR 12) -> vec YMM12
    R.YMM (F.YMMR 13) -> vec YMM13
    R.YMM (F.YMMR 14) -> vec YMM14
    R.YMM (F.YMMR 15) -> vec YMM15
    R.X86_YMMReg _ -> error "[bug] Unexpected YMM register."

    R.X87_FPUReg (F.MMXR 0)  -> fp FP0
    R.X87_FPUReg (F.MMXR 1)  -> fp FP1
    R.X87_FPUReg (F.MMXR 2)  -> fp FP2
    R.X87_FPUReg (F.MMXR 3)  -> fp FP3
    R.X87_FPUReg (F.MMXR 4)  -> fp FP4
    R.X87_FPUReg (F.MMXR 5)  -> fp FP5
    R.X87_FPUReg (F.MMXR 6)  -> fp FP6
    R.X87_FPUReg (F.MMXR 7)  -> fp FP7
    R.X87_FPUReg _ -> error "[bug] Unexpected FPUReg register."

    R.CF -> flag CF
    R.PF -> flag PF
    R.AF -> flag AF
    R.ZF -> flag ZF
    R.SF -> flag SF
    R.TF -> flag TF
    R.IF -> flag IF
    R.DF -> flag DF
    R.OF -> flag OF
    R.X86_FlagReg _ -> error "[bug] Unexpected flag register."

    R.X87_IE -> x87_status X87_IE
    R.X87_DE -> x87_status X87_DE
    R.X87_ZE -> x87_status X87_ZE
    R.X87_OE -> x87_status X87_OE
    R.X87_UE -> x87_status X87_UE
    R.X87_PE -> x87_status X87_PE
    R.X87_EF -> x87_status X87_EF
    R.X87_ES -> x87_status X87_ES
    R.X87_C0 -> x87_status X87_C0
    R.X87_C1 -> x87_status X87_C1
    R.X87_C2 -> x87_status X87_C2
    R.X87_StatusReg 11 -> x87_status X87_C3

    -- R.X87_C3 -> x87_status X87_C3
    -- This doesn't work because C3 is 14 in flexdis, but Macaw
    -- expects it to be 11.


    R.X87_StatusReg n ->
      error ("[bug] Unexpected X87 status register: " ++ show n)

    R.X87_TopReg -> toRV valX87Top

    R.X87_TagReg 0 -> tag Tag0
    R.X87_TagReg 1 -> tag Tag1
    R.X87_TagReg 2 -> tag Tag2
    R.X87_TagReg 3 -> tag Tag3
    R.X87_TagReg 4 -> tag Tag4
    R.X87_TagReg 5 -> tag Tag5
    R.X87_TagReg 6 -> tag Tag6
    R.X87_TagReg 7 -> tag Tag7
    R.X87_TagReg _ -> error "[bug] Unexpecte X87 tag"


  where
  gp r          = case valGPReg r of
                    GPBits x -> toRV x
                    GPPtr x -> toRV x
  vec r         = toRV (valVecReg r)
  fp r          = toRV (valFPReg r)
  flag r        = toRV (valFlag r)
  x87_status r  = toRV (valX87Status r)
  tag r         = toRV (valX87Tag r)



toRV :: Value t -> RegValue' Sym (Rep t)
toRV (Value x) = RV x



-- | The type of value stored in a register.  Used for reading registers.
type family RegType a where
  RegType IP                  = AQWord
  RegType (GPReg,GPRegUse t)  = t
  RegType Flag                = ABool
  RegType VecReg              = AVec
  RegType X87Status           = ABool
  RegType X87Top              = ABits3
  RegType X87Tag              = ABits2
  RegType FPReg               = ABigFloat





-- | Get the value of a register.
class GetReg a where
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
regValueGP how =
  case how of
    AsBits -> do r <- regValue @n @AQWord
                 isPtr r False
                 return r
    AsPtr  -> do r <- regValue @n @APtr
                 isPtr r True
                 return r



instance GetReg IP where
  getReg _ = regValue @M.IP












instance GetReg (GPReg,GPRegUse t) where
  getReg (x,use) =
    case x of
      -- Flexdi86.Register for the mapping between registers.
      RAX -> regValueGP @(M.GP  0) use
      RBX -> regValueGP @(M.GP  3) use
      RCX -> regValueGP @(M.GP  1) use
      RDX -> regValueGP @(M.GP  2) use
      RSI -> regValueGP @(M.GP  6) use
      RDI -> regValueGP @(M.GP  7) use
      RSP -> regValueGP @(M.GP  4) use
      RBP -> regValueGP @(M.GP  5) use
      R8  -> regValueGP @(M.GP  8) use
      R9  -> regValueGP @(M.GP  9) use
      R10 -> regValueGP @(M.GP 10) use
      R11 -> regValueGP @(M.GP 11) use
      R12 -> regValueGP @(M.GP 12) use
      R13 -> regValueGP @(M.GP 13) use
      R14 -> regValueGP @(M.GP 14) use
      R15 -> regValueGP @(M.GP 15) use


instance GetReg Flag where
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


instance GetReg VecReg where
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


instance GetReg X87Status where
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


instance GetReg X87Top where
  getReg _ = regValue @M.X87Top


instance GetReg X87Tag where
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



instance GetReg FPReg where
  getReg t =
    case t of
      FP0 -> regValue @(M.FPReg 0)
      FP1 -> regValue @(M.FPReg 1)
      FP2 -> regValue @(M.FPReg 2)
      FP3 -> regValue @(M.FPReg 3)
      FP4 -> regValue @(M.FPReg 4)
      FP5 -> regValue @(M.FPReg 5)
      FP6 -> regValue @(M.FPReg 6)
      FP7 -> regValue @(M.FPReg 7)


