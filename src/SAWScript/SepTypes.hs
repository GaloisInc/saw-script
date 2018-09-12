{- |
Module      : SAWScript.SepTypes
Description : Extraction of SAW terms from Crucible using Separable Types
License     : BSD3
Maintainer  : westbrook
Stability   : provisional
-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module SAWScript.SepTypes
       (crucible_llvm_septypes_extract
       ) where

import Data.Text (Text)

import Verifier.SAW.SharedTerm
import Verifier.SAW.OpenTerm
import Verifier.SAW.TypedTerm

import Lang.Crucible.CFG.Core
import Lang.Crucible.Types
import Lang.Crucible.LLVM.Extension

import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Ctx

import SAWScript.CrucibleLLVM
import SAWScript.CrucibleBuiltins
import SAWScript.TopLevel
import SAWScript.Value
import SAWScript.Options

-- | A "proof" that the given 'CrucibleType' is "functional", meaning that it
-- contains no references or function types, and so can be directly represented
-- in SAW
data FunCrucibleType (tp :: CrucibleType) where
  FunCType_Base :: BaseTypeRepr b -> FunCrucibleType (BaseToType b)
  FunCType_Unit :: FunCrucibleType UnitType
  FunCType_Float :: FloatInfoRepr flt -> FunCrucibleType (FloatType flt)
  FunCType_Char :: FunCrucibleType CharType
  FunCType_Maybe :: FunCrucibleType tp -> FunCrucibleType (MaybeType tp)
  FunCType_Struct :: FunCrucibleCtx ctx -> FunCrucibleType (StructType ctx)
  FunCType_Variant :: FunCrucibleCtx ctx -> FunCrucibleType (VariantType ctx)

-- FIXME: for recursive types, require the unrolling to be functional...

type FunCrucibleCtx = Ctx.Assignment FunCrucibleType

-- | Convert a functional Crucible type to a SAW type
funTypeToSAW :: FunCrucibleType tp -> OpenTermM OpenTerm
funTypeToSAW _ = error "funTypeToSAW unimplemented!"

-- | A statically-known Crucible expression. We only track a few expression
-- forms here, namely, constants, variables, and a few arithmetic operations,
-- because some of the memory operations need to know this information; e.g.,
-- @malloc@ must know the size of the memory being allocated.
data StaticExpr tp where
  -- | A Crucible variable for an LLVM value that we know is related to the
  -- given SAW variable
  StaticLLVMVar :: HasPtrWidth w => OpenTerm -> StaticExpr (LLVMPointerType w)

  -- | A bitvector literal
  StaticBVLit :: (1 <= w) => NatRepr w -> Integer -> StaticExpr (BVType w)
  -- | A bitvector addition
  StaticBVAdd :: (1 <= w) => NatRepr w -> StaticExpr (BVType w) ->
                 StaticExpr (BVType w) -> StaticExpr (BVType w)
  -- | A bitvector multiplication
  StaticBVMul :: (1 <= w) => NatRepr w -> StaticExpr (BVType w) ->
                 StaticExpr (BVType w) -> StaticExpr (BVType w)

  -- | The natural number 0
  StaticNatZero :: StaticExpr NatType
  -- | An arbitrary non-zero natural number
  StaticNatNonZero :: StaticExpr NatType

  -- | A statically-known Boolean value
  StaticBool :: Bool -> StaticExpr BoolType

  -- | A statically-known String
  StaticString :: Text -> StaticExpr StringType

  -- | A static struct
  StaticStruct :: Ctx.Assignment StaticExpr ctx -> StaticExpr (StructType ctx)

  -- | A statically-rolled LLVM_pointer recursive value
  StaticRollLLVM :: HasPtrWidth w =>
                    StaticExpr (StructType (EmptyCtx ::> NatType ::> BVType w)) ->
                    StaticExpr (LLVMPointerType w)


-- | A value permission is a relation between a Crucible value and a SAW value,
-- along with a specification of what updates are allowed to the Crucible state
-- via the value
data ValuePerm (tp :: CrucibleType) where
  -- | Represents a functional (i.e., with no references or functions) Crucible
  -- value directly in SAW as itself, with an optional static expression that
  -- gives the SAW value if it is known
  FunValuePerm :: FunCrucibleType tp -> Maybe (StaticExpr tp) -> ValuePerm tp

  -- | Represents LLVM values of a fixed, known value as the unit object
  LLVMFixedWordPerm :: (1 <= w) => NatRepr w -> Integer ->
                       ValuePerm (LLVMPointerType w)

  -- | Represents an LLVM value that points into the heap
  LLVMPtrPerm :: (1 <= w) => NatRepr w -> Maybe String -> [LLVMFieldPerm w] ->
                 ValuePerm (LLVMPointerType w)

  -- | Represents an LLVM value as either one or the other representations
  LLVMSumPerm :: ValuePerm (LLVMPointerType w) ->
                 ValuePerm (LLVMPointerType w) ->
                 ValuePerm (LLVMPointerType w)


-- FIXME HERE: lifetime modality for perms


data LLVMFieldPerm w =
  LLVMFieldPerm
  { fieldPermPerm :: Either (ValuePerm (LLVMPointerType w)) String,
    -- ^ Either a value permission or a recursive permission that refers to an
    -- enclosing 'LLVMPtrPerm' by name
    fieldPermLevel :: LLVMFieldPermLevel,
    -- ^ Whether we currently hold write, read, or no perms to this field
    fieldPermBorrow :: Maybe BorrowDest
    -- ^ Whether this field perm is currently being borrowed
  }

data LLVMFieldPermLevel = FieldLvlW | FieldLvlR | FieldLvlNone

 -- FIXME HERE: how to refer to local Crucible variables in the following? Do we
 -- need all our perms to be indexed by a Crucible ctx?
data BorrowDest
data BorrowSrc

-- FIXME HERE: need to refer to local Crucible variables here too...
data Perm

-- FIXME HERE: GlobalSymbol is not exported from crucible-llvm, so this is just
-- a dummy placeholder until that is fixed...
data GlobalSymbol

-- | A permission to a global symbol
data GlobalPerm where
  GlobalPerm :: GlobalSymbol -> ValuePerm tp -> GlobalPerm

data PermSet (ctx :: Ctx CrucibleType) =
  PermSet
  { permSetVars :: Ctx.Assignment ValuePerm ctx
  , permSetConsts :: [GlobalPerm] }

-- FIXME: add lifetimes to PermSets


extractCFG :: SharedContext -> AnyCFG (LLVM arch) -> IO Term
extractCFG _sc (AnyCFG _cfg) = error "extractCFG"

crucible_llvm_septypes_extract :: BuiltinContext -> Options -> LLVMModule -> String -> TopLevel TypedTerm
crucible_llvm_septypes_extract bic opts lm fn_name =
  do LLVM_CFG cfg <- crucible_llvm_cfg bic opts lm fn_name
     sc <- getSharedContext
     io (mkTypedTerm sc =<< extractCFG sc cfg)
