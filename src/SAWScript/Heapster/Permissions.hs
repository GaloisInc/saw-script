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

import qualified Control.Lens                     as Lens
import           Data.Kind
import           Data.Parameterized.Context
import           Data.Parameterized.Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.TraversableFC
import           Data.Type.Equality
import           Numeric.Natural

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


instance ExtendContext' PermExpr where
  extendContext' = error "FIXME: extendContext'"

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


instance ExtendContext' ValuePerm where
  extendContext' = error "FIXME: extendContext'"


-- | A permission set assigns value permissions to the variables in scope
type PermSet ctx = Assignment (ValuePerm ctx) ctx

-- | A pair of an expression of some type and a value permission for it
data ExprPerm ctx where
  ExprPerm :: PermExpr ctx a -> ValuePerm ctx a -> ExprPerm ctx

-- | A permission set that assigns value permissions to expressions
type ExprPermSet ctx = [ExprPerm ctx]


----------------------------------------------------------------------
-- * Permission Set Eliminations
----------------------------------------------------------------------

-- | Replace permission @x:(p1 \/ p2)@ with @x:p1@. It is an error if the
-- permission set assigns a non-disjunctive permission to @x@.
elimOrLeftValuePerm :: ValuePerm ctx a -> ValuePerm ctx a
elimOrLeftValuePerm (ValPerm_Or l _) = l
elimOrLeftValuePerm _                = error "elimOrLeftValuePerm"

-- | Replace permission @x:(p1 \/ p2)@ with @x:p2@. It is an error if the
-- permission set assigns a non-disjunctive permission to @x@.
elimOrRightValuePerm :: ValuePerm ctx a -> ValuePerm ctx a
elimOrRightValuePerm (ValPerm_Or _ r) = r
elimOrRightValuePerm _                = error "elimOrRightValuePerm"

-- | Lifts @elimOrLeftValuePerm@ to permissions sets (@PermSet@), targetting the
-- permission at given index.
elimOrLeft :: PermSet ctx -> Index ctx a -> PermSet ctx
elimOrLeft perms x = Lens.over (ixF x) elimOrLeftValuePerm perms

-- | Lifts @elimOrRightValuePerm@ to permission sets (@PermSet@), targetting the
-- permission at given index.
elimOrRight :: PermSet ctx -> Index ctx a -> PermSet ctx
elimOrRight perms x = Lens.over (ixF x) elimOrRightValuePerm perms

-- | Replace permission @x:(exists z:tp.p)@ in a permission set with @x:p@,
-- lifting all other permissions into the extended context @ctx ::> tp@. It is
-- an error if the permission set assigns a non-existential permission to @x@.
elimExists :: PermSet ctx -> Index ctx a -> TypeRepr tp -> PermSet (ctx ::> tp)
elimExists perms x tp =
  case perms ! x of
    ValPerm_Exists tp' p ->
      case testEquality tp tp' of
        Just Refl ->
          flip extend ValPerm_True $ update x p $
          fmapFC (extendContext' (extendRight noDiff)) perms
        Nothing -> error "elimExists"
    _ -> error "elimExists"


-- | A permission elimination decomposes a permission set into some number of
-- disjunctive possibilities; e.g., a permission set with a 'ValPerm_Or' could
-- be decomposed into two permission sets, one with each of the left- and
-- right-hand sides of the 'ValPerm_Or'. This creates a tree of disjunctive
-- possibilities. At each leaf of this tree, an elimination contains an @f@,
-- which in theory is indexed by the permission at that leaf; since we are not
-- lifting the permissions to the type level, however, @f@ is actually only
-- indexed by the context.
data PermElim (f :: Ctx CrucibleType -> *) (ctx :: Ctx CrucibleType) where
  Elim_Done :: f ctx -> PermElim f ctx
  -- ^ No more elimination; i.e., a leaf node in a permission elimination tree

  Elim_Or :: Index ctx a -> PermElim f ctx -> PermElim f ctx -> PermElim f ctx
  -- ^ Eliminate a 'ValPerm_Or' on the given variable, replacing it with the
  -- left- and right-hand sides in the two sub-eliminations

  Elim_Exists :: Index ctx a -> TypeRepr tp -> PermElim f (ctx ::> tp) ->
                 PermElim f ctx
  -- ^ Eliminate an existential, i.e., a 'ValPerm_Exists', on the given variable

  Elim_BindField :: Index ctx (LLVMPointerType w) -> Int ->
                    PermElim f (ctx ::> LLVMPointerType w) ->
                    PermElim f ctx
  -- ^ Bind a fresh variable to contain the contents of a field in a pointer
  -- permission. More specifically, replace an 'LLVMFieldShapePerm' containing
  -- an arbitrary permission @p@ with one containing an @'ValPerm_Eq' x@
  -- permission, where @x@ is a fresh variable that is given the permission @p@.
  -- The 'Int' argument says which 'LLVMFieldShapePerm' of the given variable to
  -- perform this operation on.

  Elim_Copy :: PermElim f ctx -> PermElim f ctx -> PermElim f ctx
  -- ^ Copy the same permissions into two different elimination trees

  Elim_Unroll :: Index ctx a -> PermElim f ctx -> PermElim f ctx
  -- ^ Unroll a recursive 'ValPerm_Mu' permission one time


----------------------------------------------------------------------
-- * Permission Set Introduction Rules
----------------------------------------------------------------------

-- | The permission introduction rules define a judgment of the form
--
-- > Gamma | Pin |- Pout | Prem
--
-- that intuitively proves permission set @Pout@ from @Pin@, with the remainder
-- permission set @Prem@ left over, all of which are relative to context
-- @Gamma@. Note that Pout is an 'ExprPermSet', so it assigns permissions to
-- expressions and not just variables, and it can also be empty. All of the
-- rules are introduction rules, meaning they build up a proof of @Pout@ from
-- smaller permissions. Also, most of the rules have the convention that they
-- operate on the first permission in the 'ExprPermSet'.
data PermIntro (ctx :: Ctx CrucibleType) where
  Intro_Done :: PermIntro ctx
  -- ^ The final step of any introduction proof, of the form
  --
  -- >  --------------------------
  -- >  Gamma | Pin |- empty | Pin

  Intro_Exists :: TypeRepr tp -> PermExpr ctx tp -> ValuePerm (ctx ::> tp) a ->
                  PermIntro ctx -> PermIntro ctx
  -- ^ @Intro_Exists tp e' p pf@ is the existential introduction rule
  --
  -- > pf = Gamma | Pin |- e:[e'/z]p, Pout | Prem
  -- > ---------------------------------------------
  -- > Gamma | Pin |- e:(exists z:tp.p), Pout | Prem

  Intro_OrL :: ValuePerm ctx a -> PermIntro ctx -> PermIntro ctx
  -- ^ @Intro_OrL p2 pf@ is the left disjunction introduction rule
  --
  -- > pf = Gamma | Pin |- e:p1, Pout | Prem
  -- > ---------------------------------------------
  -- > Gamma | Pin |- e:(p1 \/ p2), Pout | Prem

  Intro_OrR :: ValuePerm ctx a -> PermIntro ctx -> PermIntro ctx
  -- ^ @Intro_OrR p1 pf@ is the right disjunction introduction rule
  --
  -- > pf = Gamma | Pin |- e:p2, Pout | Prem
  -- > ---------------------------------------------
  -- > Gamma | Pin |- e:(p1 \/ p2), Pout | Prem

  Intro_True :: PermExpr ctx a -> PermIntro ctx -> PermIntro ctx
  -- ^ Implements the rule
  --
  -- > Gamma | Pin |- Pout | Prem
  -- > ---------------------------------------------
  -- > Gamma | Pin |- e:true, Pout | Prem

  Intro_CastEq :: PermExpr ctx a -> PermIntro ctx -> PermIntro ctx
  -- ^ @Intro_Ptr e pf@ where @e = x+off@ implements the rule
  --
  -- > pf = Gamma | Pin, x:eq(e') |- (e'+off):p, Pout | Prem
  -- > --------------------------------------------------
  -- > Gamma | Pin, x:eq(e') |- e:p, Pout | Prem

  Intro_Eq :: PermExpr ctx a -> PermIntro ctx -> PermIntro ctx
  -- ^ @Intro_Eq e pf@ implements the rule
  --
  -- > pf = Gamma | Pin |- Pout | Prem
  -- > --------------------------------------------------
  -- > Gamma | Pin |- e:eq(e), Pout | Prem

  Intro_LLVMWord ::
    (1 <= w) => NatRepr w -> PermExpr ctx (LLVMPointerType w) ->
    PermIntro ctx -> PermIntro ctx
  -- ^ @Intro_LLVMWord w e pf@ where @e = x+off@ implements the rule
  --
  -- > pf = Gamma | Pin, x:word |- Pout | Prem
  -- > ---------------------------------------------
  -- > Gamma | Pin, x:word |- e:word, Pout | Prem

  Intro_LLVMPtr ::
    (1 <= w) => NatRepr w -> Index ctx (LLVMPointerType w) ->
    PermIntro ctx -> PermIntro ctx
  -- ^ @Intro_LLVMPtr x pf@ implements the rule
  --
  -- > pf = Gamma | Pin, x:ptr(shapes) |- Pout | Prem
  -- > --------------------------------------------------
  -- > Gamma | Pin, x:ptr(shapes) |- x:ptr(), Pout | Prem

  Intro_LLVMPtr_Offset ::
    (1 <= w) => NatRepr w -> Integer -> PermIntro ctx -> PermIntro ctx
  -- ^ @Intro_LLVMPtr_Offset w off pf@ for a static offset @off@ implements
  --
  -- > pf = Gamma | Pin |- x:ptr (shapes + off), Pout | Prem
  -- > --------------------------------------------------
  -- > Gamma | Pin |- (x+off):ptr(shapes), Pout | Prem

  Intro_LLVMField ::
    (1 <= w) => NatRepr w -> Integer -> SplittingExpr ctx ->
    ValuePerm ctx (LLVMPointerType w) ->
    PermIntro ctx -> PermIntro ctx
  -- ^ @Intro_LLVMField w off S p pf@ implements the rule
  --
  -- > pf = Gamma | Pin, x:ptr(shapes) |- e:p, x:ptr(shapes'), Pout | Prem
  -- > --------------------------------------------------------------------
  -- > Gamma | Pin, x:ptr(off |-> (S,eq(e)) * shapes)
  -- >    |- x:ptr(off |-> (S,p) * shapes'), Pout | Prem
