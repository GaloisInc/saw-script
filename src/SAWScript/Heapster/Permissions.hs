{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}

module SAWScript.Heapster.Permissions (
  -- * Splitting expressions
  SplittingExpr(..), 
  -- * Splitting coercions
  SplittingCoercion(..), splittingCoercionSource, splittingCoercionTarget,
  coerceSplitting, meetSplittings,
  -- * Permissions and permission sets
  PermExpr(..), ValuePerm(..), LLVMPtrPerm(..), PermSet,
  -- * Permission coercions
  PermCoercion(..), permCoercionSource, permCoercionTarget,
  coercePerm, meetPerms
  ) where

import           Numeric.Natural
import           Data.Kind
import           Data.Parameterized.Ctx
import           Data.Parameterized.Context
import           Data.Parameterized.NatRepr

import           Lang.Crucible.Types
-- import           Lang.Crucible.LLVM.Types
import           Lang.Crucible.LLVM.MemModel
-- import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.CFG.Core


----------------------------------------------------------------------
-- Splittings
----------------------------------------------------------------------

-- | Expressions that represent "fractions" of a write permission
data SplittingExpr ctx
  = SplExpr_All
  | SplExpr_L (SplittingExpr ctx)
  | SplExpr_R (SplittingExpr ctx)
  | SplExpr_Star (SplittingExpr ctx) (SplittingExpr ctx)
  | SplExpr_Var (Index ctx SplittingType)

-- | Crucible type for splitting expressions
type SplittingType = IntrinsicType "Splitting" EmptyCtx

-- | A proof that one 'SplittingExpr' is greater than another
data SplittingCoercion ctx where
  -- | The identity splitting coercion
  SCoerce_Id :: SplittingExpr ctx -> SplittingCoercion ctx

-- FIXME: need more splitting coercions

-- | Extract the source splitting expression of a splitting coercion
splittingCoercionSource :: SplittingCoercion ctx -> SplittingExpr ctx
splittingCoercionSource (SCoerce_Id spl) = spl

-- | Extract the target splitting expression of a splitting coercion
splittingCoercionTarget :: SplittingCoercion ctx -> SplittingExpr ctx
splittingCoercionTarget (SCoerce_Id spl) = spl


-- | Attempt to coerce from one splitting expression to another, returning a
-- coercion proof if this is possible and 'Nothing' otherwise. For the logicians
-- out there, this is attempting to prove an implication.
coerceSplitting :: SplittingExpr ctx -> SplittingExpr ctx ->
                   Maybe (SplittingCoercion ctx)
coerceSplitting = error "coerceSplitting"



-- | Compute the greatest splitting expression that can be coerced to from two
-- input splitting expressions, if one exists
meetSplittings :: SplittingExpr ctx -> SplittingExpr ctx ->
                  (SplittingExpr ctx,
                   SplittingCoercion ctx, SplittingCoercion ctx)
meetSplittings = error "meetSplittings"


----------------------------------------------------------------------
-- Permissions and permission sets
----------------------------------------------------------------------

-- | Expressions that are considered "pure" for use in permissions
data PermExpr (ctx :: Ctx CrucibleType) (a :: CrucibleType) where
  -- Variables
  PExpr_Var :: Index ctx a -> PermExpr ctx a

  -- Natural numbers
  PExpr_NatLit :: Natural -> PermExpr ctx NatType

  -- Bitvector operations
  PExpr_BVLit :: (1 <= w) => NatRepr w -> Integer -> PermExpr ctx (BVType w)

  PExpr_BVAdd :: (1 <= w) => NatRepr w ->
                 PermExpr ctx (BVType w) -> PermExpr ctx (BVType w) ->
                 PermExpr ctx (BVType w)

  -- LLVM pointer constructor and destructors
  PExpr_LLVM_PointerExpr ::
    (1 <= w) => NatRepr w -> PermExpr ctx NatType ->
    PermExpr ctx (BVType w) -> PermExpr ctx (LLVMPointerType w)
  PExpr_LLVM_PointerBlock ::
    (1 <= w) => NatRepr w -> PermExpr ctx (LLVMPointerType w) ->
    PermExpr ctx NatType
  PExpr_LLVM_PointerOffset ::
    (1 <= w) => NatRepr w -> PermExpr ctx (LLVMPointerType w) ->
    PermExpr ctx (BVType w)


-- | Crucible type for value permissions
type ValuePermType a = IntrinsicType "ValuePerm" (EmptyCtx ::> a)


-- | A value permission is a permission to do something with a value, such as
-- use it as a pointer. This also includes a limited set of predicates on values
-- (you can think about this as "permission to assume the value satisfies this
-- predicate" if you like).
data ValuePerm (ctx :: Ctx CrucibleType) (a :: CrucibleType) where
  -- | The trivial value perm
  ValPerm_None :: ValuePerm ctx a

  -- | Says that a value is equal to a known static expression
  ValPerm_Eq :: PermExpr ctx a -> ValuePerm ctx a

  -- | The disjunction of two value permissions
  ValPerm_Or :: ValuePerm ctx a -> ValuePerm ctx a -> ValuePerm ctx a

  -- | An existential binding of a value in a value permission
  ValPerm_Exists :: TypeRepr a -> ValuePerm (ctx ::> a) b -> ValuePerm ctx b

  -- | A recursive / least fixed-point permission
  ValPerm_Mu :: ValuePerm (ctx ::> ValuePermType a) a -> ValuePerm ctx a

  -- | A value permission variable
  ValPerm_Var :: Index ctx (ValuePermType a) -> ValuePerm ctx a

  -- | Says that an LLVM word is a bitvector, i.e., its block = 0
  ValPerm_LLVMWord :: (1 <= w) => NatRepr w -> ValuePerm ctx (LLVMPointerType w)

  -- | Says that an LLVM word is a pointer, i.e., with a non-zero block, where
  -- the memory pointed to has the given shape, and optionally we have
  -- permission to free the memory if we have write perms to @N@ words
  ValPerm_LLVMPtr :: (1 <= w) => NatRepr w ->
                     [LLVMPtrPerm ctx w] -> Maybe (PermExpr ctx (BVType w)) ->
                     ValuePerm ctx (LLVMPointerType w)


data LLVMPtrPerm ctx w
  = LLVMSinglePtr (PermExpr ctx (BVType w)) (SplittingExpr ctx)
    (ValuePerm ctx (LLVMPointerType w))
  | LLVMArrayPtr (PermExpr ctx (BVType w)) (PermExpr ctx (BVType w))
    (SplittingExpr ctx) (ValuePerm ctx (LLVMPointerType w))


-- | A permission set assigns value permissions to the variables in scope
type PermSet ctx = Assignment (ValuePerm ctx) ctx


----------------------------------------------------------------------
-- Permission coercions
----------------------------------------------------------------------

-- | A coercion from one value permission to another. You can coerce a stronger
-- permission to a weaker one, and you can coerce both ways between permissions
-- that are equivalent.
--
-- These should intuitively be typed by the source and destination value
-- permissions, but this would be a little too complex to represent as a Haskell
-- GADT; however, you should /think/ of them as being typed anyway, as they are
-- typed when we convert them to SAW.
data PermCoercion ctx a where
  -- | The identity coercion, marked with its source (and target) perm
  PCoerce_Id :: ValuePerm ctx a -> PermCoercion ctx a

  -- | Map a coercion on the body of a pointer perm to one on the pointer perm
  -- itself
  {-
  PCoerce_LLVMPtr ::
    (1 <= w) => NatRepr w -> PermExpr ctx (BVType w) -> SplittingExpr ctx ->
    PermCoercion ctx (LLVMPointerType w) ->
    PermCoercion ctx (LLVMPointerType w)
-}

-- FIXME: need more perm coercions


-- | Extract the source permission of a permission coercion
permCoercionSource :: PermCoercion ctx a -> ValuePerm ctx a
permCoercionSource (PCoerce_Id p) = p

-- | Extract the target permission of a permission coercion
permCoercionTarget :: PermCoercion ctx a -> ValuePerm ctx a
permCoercionTarget (PCoerce_Id p) = p


-- | Attempt to coerce from one value permission to another, returning a
-- coercion proof if this is possible and 'Nothing' otherwise. For the logicians
-- out there, this is attempting to prove an implication.
coercePerm :: ValuePerm ctx a -> ValuePerm ctx a -> Maybe (PermCoercion ctx a)
coercePerm = error "coercePerm"

meetPerms :: ValuePerm ctx a -> ValuePerm ctx a ->
             Maybe (ValuePerm ctx a, PermCoercion ctx a, PermCoercion ctx a)
meetPerms = error "meetPerms"
