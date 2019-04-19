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

module SAWScript.Heapster.Permissions where

import           Numeric.Natural
import           Data.Kind
import           Data.Parameterized.Ctx
import           Data.Parameterized.Context
import           Data.Parameterized.NatRepr
import           Data.Parameterized.TraversableF

import           Lang.Crucible.Types
-- import           Lang.Crucible.LLVM.Types
import           Lang.Crucible.LLVM.MemModel
-- import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.CFG.Core


----------------------------------------------------------------------
-- * Splittings
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
-- * Permissions and Permission Sets
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
  ValPerm_True :: ValuePerm ctx a

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
                     [LLVMShapePerm ctx w] -> Maybe (PermExpr ctx (BVType w)) ->
                     ValuePerm ctx (LLVMPointerType w)


data LLVMShapePerm ctx w
  = LLVMFieldShapePerm (LLVMFieldPerm ctx w)
  | LLVMArrayShapePerm (LLVMArrayPerm ctx w)

data LLVMFieldPerm ctx w =
  LLVMFieldPerm
  {
    llvmFieldOffset :: PermExpr ctx (BVType w),
    llvmFieldSplitting :: SplittingExpr ctx,
    llvmFieldPerm :: ValuePerm ctx (LLVMPointerType w)
  }

data LLVMArrayPerm ctx w =
  LLVMArrayPerm
  {
    llvmArrayOffset :: PermExpr ctx (BVType w),
    llvmArrayStride :: PermExpr ctx (BVType w),
    llvmArrayLen :: PermExpr ctx (BVType w),
    llvmArrayPtrPerm :: LLVMShapePerm ctx w
  }


-- | A permission set assigns value permissions to the variables in scope
type PermSet ctx = Assignment (ValuePerm ctx) ctx


----------------------------------------------------------------------
-- * Permission Set Eliminations
----------------------------------------------------------------------

-- | An elimination path specififies a path to a subterm in a 'PermSet' at which
-- eliminations are alllowed
data ElimPath ctx a where
  SimpleElimPath :: Index ctx a -> ElimPath ctx a
  -- ^ A "simple" elimination path only allows eliminations at the top level of
  -- a value perm, and so is just given by a variable

  LLVMElimPath ::
    Index ctx (LLVMPointerType w) -> [Int] -> ElimPath ctx (LLVMPointerType w)
  -- ^ For LLVM permissions, eliminations are allowed under 0 or more field
  -- permissions. The path component specifies the numeric position of each
  -- field permission along the way in 'ValPerm_LLVMPtr' permission lists.


-- | Extract the value permission at a given path in a 'PermSet'
permAtElimPath :: PermSet ctx -> ElimPath ctx a -> ValuePerm ctx a
permAtElimPath permSet (SimpleElimPath var) = permSet ! var
permAtElimPath permSet (LLVMElimPath var path) =
  helper path (permSet ! var)
  where
    helper :: [Int] -> ValuePerm ctx (LLVMPointerType w) ->
              ValuePerm ctx (LLVMPointerType w)
    helper [] p = p
    helper (i:is) (ValPerm_LLVMPtr _ ptr_perms _) =
      case ptr_perms!!i of
        LLVMFieldShapePerm (LLVMFieldPerm { llvmFieldPerm = p }) ->
          helper is p
        _ -> error "permAtElimPath"
    helper _ _ = error "permAtElimPath"


-- | A permission elimination decomposes a permission set into some number of
-- disjunctive possibilities; e.g., a permission set with a 'ValPerm_Or' could
-- be decomposed into two permission sets, one with each of the left- and
-- right-hand sides of the 'ValPerm_Or'. This creates a tree of disjunctive
-- possibilities. At each leaf of this tree, an elimination contains an @f@,
-- which in theory is indexed by the permission at that leaf; since we are not
-- lifting the permissions to the type level, however, @f@ is actually only
-- indexed by the context.
data PermElim (f :: Ctx CrucibleType -> *) (ctx :: Ctx CrucibleType) where
  Elim_Leaf :: f ctx -> PermElim f ctx
  -- ^ A leaf node in a permission elimination tree

  Elim_Or :: ElimPath ctx a -> PermElim f ctx -> PermElim f ctx ->
             PermElim f ctx
  -- ^ Eliminate a 'ValPerm_Or', replacing it with the left- and right-hand
  -- sides in the two sub-eliminations

  Elim_Ex :: ElimPath ctx a -> TypeRepr tp -> PermElim f (ctx ::> tp) ->
             PermElim f ctx
  -- ^ Eliminate an existential, i.e., a 'ValPerm_Exists'

  Elim_BindVar :: ElimPath ctx (LLVMPointerType w) ->
                  PermElim f (ctx ::> LLVMPointerType w) -> PermElim f ctx
  -- ^ Eliminate an arbitrary permission and replace it with @'ValPerm_Eq' x@,
  -- where @x@ is a fresh variable that is given the permission that was
  -- eliminated

  Elim_Unroll :: ElimPath ctx a -> PermElim f ctx -> PermElim f ctx
  -- ^ Unroll a recursive 'ValPerm_Mu' permission one time
