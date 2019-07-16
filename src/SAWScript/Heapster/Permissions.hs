{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}

module SAWScript.Heapster.Permissions where

import Data.Maybe
import Data.Bits
import Data.List
import Data.Proxy
import Data.Reflection
import Data.Binding.Hobbits
import GHC.TypeLits
import Control.Applicative hiding (empty)
import Control.Monad.Identity
import Control.Lens hiding ((:>))

import Data.Binding.Hobbits.NameMap (NameMap)
import qualified Data.Binding.Hobbits.NameMap as NameMap

import Data.Parameterized.Context hiding ((:>), empty, take)
import Data.Parameterized.NatRepr

import Lang.Crucible.Types
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.CFG.Core


----------------------------------------------------------------------
-- * Monads that Support Name-Binding
----------------------------------------------------------------------

-- FIXME HERE: move this to Hobbits!
class Monad m => MonadBind m where
  mbM :: NuMatching a => Mb ctx (m a) -> m (Mb ctx a)

nuM :: (MonadBind m, NuMatching b) => (Name a -> m b) -> m (Binding a b)
nuM = mbM . nu

instance MonadBind Identity where
  mbM = Identity . fmap runIdentity

instance MonadBind Maybe where
  mbM [nuP| Just x |] = return x
  mbM [nuP| Nothing |] = Nothing

-- | A version of 'MonadBind' that does not require a 'NuMatching' instance on
-- the element type of the multi-binding in the monad
class MonadBind m => MonadStrongBind m where
  strongMbM :: Mb ctx (m a) -> m (Mb ctx a)

instance MonadStrongBind Identity where
  strongMbM = Identity . fmap runIdentity


----------------------------------------------------------------------
-- * Contexts of Crucible Types
----------------------------------------------------------------------

-- | Convert a Crucible 'Ctx' to a Hobbits 'RList'
type family CtxToRList (ctx :: Ctx k) :: RList k where
  CtxToRList EmptyCtx = RNil
  CtxToRList (ctx' ::> x) = CtxToRList ctx' :> x

-- | Convert a Hobbits 'RList' to a Crucible 'Ctx'
type family RListToCtx (ctx :: RList k) :: Ctx k where
  RListToCtx RNil = EmptyCtx
  RListToCtx (ctx' :> x) = RListToCtx ctx' ::> x

-- | Convert a Crucible context of contexts to a Hobbits one
type family CtxCtxToRList (ctx :: Ctx (Ctx k)) :: RList (RList k) where
  CtxCtxToRList EmptyCtx = RNil
  CtxCtxToRList (ctx' ::> c) = CtxCtxToRList ctx' :> CtxToRList c

-- | Convert a Hobbits context of contexts to a Crucible one
type family RListToCtxCtx (ctx :: RList (RList k)) :: Ctx (Ctx k) where
  RListToCtxCtx RNil = EmptyCtx
  RListToCtxCtx (ctx' :> c) = RListToCtxCtx ctx' ::> RListToCtx c

withKnownType :: TypeRepr tp -> (KnownRepr TypeRepr tp => r) -> r
withKnownType = error "FIXME HERE: write withKnownType!"

-- | A 'TypeRepr' that has been promoted to a constraint; this is necessary in
-- order to make a 'NuMatching' instance for it, as part of the representation
-- of 'TypeRepr' is hidden (and also this way is faster)
data CruType a where
  CruType :: KnownRepr TypeRepr a => CruType a

-- | A context of Crucible types. NOTE: we do not use 'MapRList' here, because
-- we do not yet have a nice way to define the 'NuMatching' instance we want...
data CruCtx ctx where
  CruCtxNil :: CruCtx RNil
  CruCtxCons :: CruCtx ctx -> CruType a -> CruCtx (ctx :> a)

$(mkNuMatching [t| forall a. CruType a |])
$(mkNuMatching [t| forall ctx. CruCtx ctx |])

-- | Build a 'CruType' from a 'TypeRepr'
mkCruType :: TypeRepr a -> CruType a
mkCruType tp = withKnownType tp CruType

-- | Build a 'CruCtx' from a 'CtxRepr'
mkCruCtx :: CtxRepr ctx -> CruCtx (CtxToRList ctx)
mkCruCtx ctx = case viewAssign ctx of
  AssignEmpty -> CruCtxNil
  AssignExtend ctx' tp -> CruCtxCons (mkCruCtx ctx') (mkCruType tp)

-- | The empty context
emptyCruCtx :: CruCtx RNil
emptyCruCtx = CruCtxNil

-- | Add an element to the end of a context
extCruCtx :: KnownRepr TypeRepr a => CruCtx ctx -> CruCtx (ctx :> a)
extCruCtx ctx = CruCtxCons ctx CruType

-- | Remove an element from the end of a context
unextCruCtx :: CruCtx (ctx :> a) -> CruCtx ctx
unextCruCtx (CruCtxCons ctx _) = ctx


----------------------------------------------------------------------
-- * Expressions for Permissions
----------------------------------------------------------------------

-- | The Haskell type of expression variables
type ExprVar (a :: CrucibleType) = Name a

-- | Map a context of 'CrucibleType's to 'PermExpr' Haskell types
type family ExprVarCtx (as :: RList CrucibleType) :: RList * where
  ExprVarCtx RNil = RNil
  ExprVarCtx (as :> a) = ExprVarCtx as :> PermExpr a

-- | Expressions that represent "fractions" of a write permission
data SplittingExpr
  = SplExpr_All
  | SplExpr_L SplittingExpr
  | SplExpr_R SplittingExpr
  | SplExpr_Star SplittingExpr SplittingExpr
  | SplExpr_Var (ExprVar SplittingType)

-- | Crucible type for splitting expressions; we give them a Crucible type so
-- they can be existentially bound in the same way as other Crucible objects
type SplittingType = IntrinsicType "Splitting" EmptyCtx

-- | The object-level representation of 'SplittingType'
splittingTypeRepr :: TypeRepr SplittingType
splittingTypeRepr = knownRepr


-- | Expressions that are considered "pure" for use in permissions. Note that
-- these are in a normal form, that makes them easier to analyze.
data PermExpr (a :: CrucibleType) where
  PExpr_Var :: ExprVar a -> PermExpr a
  -- ^ A variable of any type

  PExpr_BV :: (1 <= w, KnownNat w) =>
              [BVFactor w] -> Integer -> PermExpr (BVType w)
  -- ^ A bitvector expression is a linear expression in @N@ variables, i.e., sum
  -- of constant times variable factors plus a constant

  PExpr_Struct :: PermExprs args -> PermExpr (StructType args)
  -- ^ A struct expression is an expression for each argument of the struct type

  PExpr_LLVMWord :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                    PermExpr (LLVMPointerType w)
  -- ^ An LLVM value that represents a word, i.e., whose region identifier is 0

  PExpr_LLVMOffset :: (1 <= w, KnownNat w) =>
                      ExprVar (LLVMPointerType w) ->
                      PermExpr (BVType w) ->
                      PermExpr (LLVMPointerType w)
  -- ^ An LLVM value built by adding an offset to an LLVM variable

  PExpr_Spl :: SplittingExpr -> PermExpr SplittingType
  -- ^ An expression that represents a permission splitting


-- | A sequence of permission expressions
data PermExprs (as :: Ctx CrucibleType) where
  PExprs_Nil :: PermExprs EmptyCtx
  PExprs_Cons :: PermExprs as -> PermExpr a -> PermExprs (as ::> a)

-- | A bitvector variable, possibly multiplied by a constant
data BVFactor w where
  BVFactor :: (1 <= w, KnownNat w) => Integer -> ExprVar (BVType w) ->
              BVFactor w
    -- ^ A variable of type @'BVType' w@ multiplied by a constant @i@, which
    -- should be in the range @0 <= i < 2^w@


$(mkNuMatching [t| SplittingExpr |])
$(mkNuMatching [t| forall a . PermExpr a |])
$(mkNuMatching [t| forall a . BVFactor a |])
$(mkNuMatching [t| forall as . PermExprs as |])

instance Eq SplittingExpr where
  SplExpr_All == SplExpr_All = True
  SplExpr_All == _ = False

  (SplExpr_L spl1) == (SplExpr_L spl2) = spl1 == spl2
  (SplExpr_L _) == _ = False

  (SplExpr_R spl1) == (SplExpr_R spl2) = spl1 == spl2
  (SplExpr_R _) == _ = False

  (SplExpr_Star spl1_l spl1_r) == (SplExpr_Star spl2_l spl2_r) =
    spl1_l == spl2_l && spl1_r == spl2_r
  (SplExpr_Star _ _) == _ = False

  (SplExpr_Var x1) == (SplExpr_Var x2) = x1 == x2
  (SplExpr_Var _) == _ = False


instance Eq (PermExpr a) where
  (PExpr_Var x1) == (PExpr_Var x2) = x1 == x2
  (PExpr_Var _) == _ = False

  (PExpr_BV factors1 const1) == (PExpr_BV factors2 const2) =
    const1 == const2 && eqFactors factors1 factors2
    where
      eqFactors :: [BVFactor w] -> [BVFactor w] -> Bool
      eqFactors [] [] = True
      eqFactors (f : factors1) factors2
        | elem f factors2 = eqFactors factors1 (delete f factors2)
      eqFactors _ _ = False
  (PExpr_BV _ _) == _ = False

  (PExpr_Struct args1) == (PExpr_Struct args2) = args1 == args2 where
  (PExpr_Struct _) == _ = False

  (PExpr_LLVMWord e1) == (PExpr_LLVMWord e2) = e1 == e2
  (PExpr_LLVMWord _) == _ = False

  (PExpr_LLVMOffset x1 e1) == (PExpr_LLVMOffset x2 e2) =
    x1 == x2 && e1 == e2
  (PExpr_LLVMOffset _ _) == _ = False

  (PExpr_Spl spl1) == (PExpr_Spl spl2) = spl1 == spl2
  (PExpr_Spl _) == _ = False


instance Eq (PermExprs as) where
  PExprs_Nil == PExprs_Nil = True
  (PExprs_Cons es1 e1) == (PExprs_Cons es2 e2) = es1 == es2 && e1 == e2


instance Eq (BVFactor w) where
  (BVFactor i1 x1) == (BVFactor i2 x2) = i1 == i2 && x1 == x2


-- | Build a "default" expression for a given type
zeroOfType :: TypeRepr tp -> PermExpr tp
zeroOfType (BVRepr w) = withKnownNat w $ PExpr_BV [] 0
zeroOfType (testEquality splittingTypeRepr -> Just Refl) =
  PExpr_Spl SplExpr_All
zeroOfType _ = error "zeroOfType"


----------------------------------------------------------------------
-- * Operations on Bitvector Expressions
----------------------------------------------------------------------

-- | Normalize a factor so that its coefficient is between @0@ and @(2^w)-1@
normalizeFactor :: BVFactor w -> BVFactor w
normalizeFactor f@(BVFactor i x) =
  BVFactor (i `mod` (shiftL 1 $ fromInteger $ natVal f)) x

-- | Smart constructor for 'BVFactor'
bvFactor :: (1 <= w, KnownNat w) => Integer -> ExprVar (BVType w) ->
            BVFactor w
bvFactor i x = normalizeFactor $ BVFactor i x

-- | Build a 'BVFactor' for a variable
varFactor :: (1 <= w, KnownNat w) => ExprVar (BVType w) -> BVFactor w
varFactor = BVFactor 1

-- | Normalize a bitvector expression, so that every variable has at most one
-- factor and the factors are sorted by variable name. NOTE: we shouldn't
-- actually have to call this if we always construct our expressions with the
-- combinators below.
bvNormalize :: PermExpr (BVType w) -> PermExpr (BVType w)
bvNormalize e@(PExpr_Var _) = e
bvNormalize (PExpr_BV factors off) =
  PExpr_BV
  (norm (sortBy (\(BVFactor _ x) (BVFactor _ y) -> compare x y) factors))
  off
  where
    norm [] = []
    norm ((BVFactor 0 _) : factors') = norm factors'
    norm ((BVFactor i1 x1) : (BVFactor i2 x2) : factors')
      | x1 == x2 = norm ((bvFactor (i1+i2) x1) : factors')
    norm (f : factors') = normalizeFactor f : norm factors'

-- | Merge two normalized / sorted lists of 'BVFactor's
bvMergeFactors :: [BVFactor w] -> [BVFactor w] -> [BVFactor w]
bvMergeFactors fs1 fs2 =
  filter (\(BVFactor i _) -> i /= 0) $
  helper fs1 fs2
  where
    helper factors1 [] = factors1
    helper [] factors2 = factors2
    helper ((BVFactor i1 x1):factors1) ((BVFactor i2 x2):factors2)
      | x1 == x2
      = bvFactor (i1+i2) x1 : helper factors1 factors2
    helper (f1@(BVFactor _ x1):factors1) (f2@(BVFactor _ x2):factors2)
      | x1 < x2 = f1 : helper factors1 (f2 : factors2)
    helper (f1@(BVFactor _ x1):factors1) (f2@(BVFactor _ x2):factors2) =
      f2 : helper (f1 : factors1) factors2

-- | Convert a bitvector expression to a sum of factors plus a constant
bvMatch :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
           ([BVFactor w], Integer)
bvMatch (PExpr_Var x) = ([varFactor x], 0)
bvMatch (PExpr_BV factors const) = (factors, const)

-- | Test if a bitvector expression is a constant value
bvMatchConst :: PermExpr (BVType w) -> Maybe Integer
bvMatchConst (PExpr_BV [] const) = Just const
bvMatchConst _ = Nothing

-- | Test whether two bitvector expressions are semantically equal, assuming
-- they are both in normal form
bvEq :: PermExpr (BVType w) -> PermExpr (BVType w) -> Bool
bvEq e1 e2 = toVar e1 == toVar e2 where
  toVar (PExpr_BV [BVFactor 1 x] 0) = (PExpr_Var x)
  toVar e = e

-- | Test whether a bitvector expression is less than another for all
-- substitutions to the free variables. This is an underapproximation, meaning
-- that it could return 'False' in cases where it is actually 'True'. The
-- current algorithm only returns 'True' for constant expressions @k1 < k2@.
bvLt :: PermExpr (BVType w) -> PermExpr (BVType w) -> Bool
bvLt (PExpr_BV [] k1) (PExpr_BV [] k2) = k1 < k2
bvLt _ _ = False

-- | Test whether a bitvector @e@ could equal @0@, i.e., whether the equation
-- @e=0@ has any solutions.
--
-- NOTE: this is an overapproximation, meaning that it may return 'True' for
-- complex expressions that technically cannot unify with @0@.
bvZeroable :: PermExpr (BVType w) -> Bool
bvZeroable (PExpr_Var _) = True
bvZeroable (PExpr_BV _ 0) = True
bvZeroable (PExpr_BV [] _) = False
bvZeroable (PExpr_BV _ _) =
  -- NOTE: there are cases that match this pattern but are still not solvable,
  -- like 8*x + 3 = 0.
  True

-- | Test whether two bitvector expressions are potentially unifiable, i.e.,
-- whether some substitution to the variables could make them equal. This is an
-- overapproximation, meaning that some expressions are marked as "could" equal
-- when they actually cannot.
bvCouldEqual :: PermExpr (BVType w) -> PermExpr (BVType w) -> Bool
bvCouldEqual e1@(PExpr_BV _ _) e2 =
  -- NOTE: we can only call bvSub when at least one side matches PExpr_BV
  bvZeroable (bvSub e1 e2)
bvCouldEqual e1 e2@(PExpr_BV _ _) = bvZeroable (bvSub e1 e2)
bvCouldEqual _ _ = True

-- | Test whether a bitvector expression could potentially be less than another,
-- for some substitution to the free variables. This is an overapproximation,
-- meaning that some expressions are marked as "could" be less than when they
-- actually cannot. The current algorithm returns 'True' in all cases except
-- constant expressions @k1 >= k2@.
bvCouldBeLt :: PermExpr (BVType w) -> PermExpr (BVType w) -> Bool
bvCouldBeLt (PExpr_BV [] k1) (PExpr_BV [] k2) = k1 < k2
bvCouldBeLt _ _ = True

-- | Build a bitvector expression from an integer
bvInt :: (1 <= w, KnownNat w) => Integer -> PermExpr (BVType w)
bvInt i = PExpr_BV [] i

-- | Add two bitvector expressions
bvAdd :: (1 <= w, KnownNat w) => PermExpr (BVType w) -> PermExpr (BVType w) ->
         PermExpr (BVType w)
bvAdd (bvMatch -> (factors1, const1)) (bvMatch -> (factors2, const2)) =
  PExpr_BV (bvMergeFactors factors1 factors2) (const1 + const2)

-- | Multiply a bitvector expression by a constant
bvMult :: (1 <= w, KnownNat w) => Integer -> PermExpr (BVType w) ->
          PermExpr (BVType w)
bvMult i (PExpr_Var x) = PExpr_BV [bvFactor i x] 0
bvMult i (PExpr_BV factors off) =
  PExpr_BV (map (\(BVFactor j x) -> bvFactor (i*j) x) factors) (i*off)

-- | Negate a bitvector expression
bvNegate :: (1 <= w, KnownNat w) => PermExpr (BVType w) -> PermExpr (BVType w)
bvNegate = bvMult (-1)

-- | Subtract one bitvector expression from another
--
-- FIXME: this would be more efficient if we did not use 'bvNegate', which could
-- make very large 'Integer's for negative numbers wrapped around to be positive
bvSub :: (1 <= w, KnownNat w) => PermExpr (BVType w) -> PermExpr (BVType w) ->
         PermExpr (BVType w)
bvSub e1 e2 = bvAdd e1 (bvNegate e2)

-- | Integer division on bitvector expressions, truncating any factors @i*x@
-- where @i@ is not a multiple of the divisor to zero
bvDiv :: (1 <= w, KnownNat w) => PermExpr (BVType w) -> Integer ->
         PermExpr (BVType w)
bvDiv (bvMatch -> (factors, off)) n =
  PExpr_BV (mapMaybe (\(BVFactor i x) ->
                       if mod i n == 0 then
                         -- NOTE: if i is in range then so is i/n, so we do not
                         -- need to normalize the resulting BVFactor
                         Just (BVFactor (div i n) x)
                       else Nothing) factors)
  (div off n)

-- | Integer Modulus on bitvector expressions, where any factors @i*x@ with @i@
-- not a multiple of the divisor are included in the modulus
bvMod :: (1 <= w, KnownNat w) => PermExpr (BVType w) -> Integer ->
         PermExpr (BVType w)
bvMod (bvMatch -> (factors, off)) n =
  PExpr_BV (mapMaybe (\f@(BVFactor i _) ->
                       if mod i n /= 0 then Just f else Nothing) factors)
  (mod off n)

-- | Add a word expression to an LLVM pointer expression
addLLVMOffset :: (1 <= w, KnownNat w) =>
                 PermExpr (LLVMPointerType w) -> PermExpr (BVType w) ->
                 PermExpr (LLVMPointerType w)
addLLVMOffset (PExpr_Var x) off = PExpr_LLVMOffset x off
addLLVMOffset (PExpr_LLVMWord e) off = PExpr_LLVMWord $ bvAdd e off
addLLVMOffset (PExpr_LLVMOffset x e) off =
  PExpr_LLVMOffset x $ bvAdd e off


----------------------------------------------------------------------
-- * Permissions
----------------------------------------------------------------------

-- | The type of variables for use in value permissions. Note that we use names
-- of type 'ValuePerm' and /not/ of type 'PermExpr', so that permission
-- variables cannot be bound as expressions and vice-versa.
type PermVar a = Name (ValuePerm a)

-- | A value permission is a permission to do something with a value, such as
-- use it as a pointer. This also includes a limited set of predicates on values
-- (you can think about this as "permission to assume the value satisfies this
-- predicate" if you like).
data ValuePerm (a :: CrucibleType) where
  -- | The trivial value perm
  ValPerm_True :: ValuePerm a

  -- | Says that a value is equal to a known static expression
  ValPerm_Eq :: PermExpr a -> ValuePerm a

  -- | The disjunction of two value permissions
  ValPerm_Or :: ValuePerm a -> ValuePerm a -> ValuePerm a

  -- | An existential binding of a value in a value permission
  ValPerm_Exists :: KnownRepr TypeRepr a =>
                    Binding a (ValuePerm b) ->
                    ValuePerm b

  -- | A recursive / least fixed-point permission
  ValPerm_Mu :: Binding (ValuePerm a) (ValuePerm a) -> ValuePerm a

  -- | A value permission variable, for use in recursive permissions
  ValPerm_Var :: PermVar a -> ValuePerm a

  -- | Says that an LLVM word is a pointer, i.e., with a non-zero block, where
  -- the memory pointed to has the given shape, and optionally we have
  -- permission to free the memory if we have write perms to @N@ words
  ValPerm_LLVMPtr :: (1 <= w, KnownNat w) =>
                     [LLVMPtrPerm w] -> ValuePerm (LLVMPointerType w)


-- | A permission to the memory referenced by an LLVM pointer
data LLVMPtrPerm w
  = LLVMPP_Field (LLVMFieldPerm w)
  | LLVMPP_Array (LLVMArrayPerm w)
  | LLVMPP_Free (PermExpr (BVType w))
  deriving Eq

data LLVMFieldPerm w =
  LLVMFieldPerm { llvmFieldOffset :: PermExpr (BVType w),
                  llvmFieldSplitting :: SplittingExpr,
                  llvmFieldPerm :: ValuePerm (LLVMPointerType w) }
  deriving Eq

data LLVMArrayPerm w =
  LLVMArrayPerm { llvmArrayOffset :: PermExpr (BVType w),
                  llvmArrayLen :: PermExpr (BVType w),
                  llvmArrayStride :: Integer,
                  llvmArraySplitting :: SplittingExpr,
                  llvmArrayFields :: [LLVMFieldPerm w] }
  deriving Eq


instance (Eq (ValuePerm a)) where
  ValPerm_True == ValPerm_True = True
  ValPerm_True == _ = False
  (ValPerm_Eq e1) == (ValPerm_Eq e2) = e1 == e2
  (ValPerm_Eq _) == _ = False
  (ValPerm_Or p1 p1') == (ValPerm_Or p2 p2') = p1 == p2 && p1' == p2'
  (ValPerm_Or _ _) == _ = False
  (ValPerm_Exists (p1 :: Binding a1 _)) ==
    (ValPerm_Exists (p2 :: Binding a2 _)) =
    case testEquality (knownRepr :: TypeRepr a1) (knownRepr :: TypeRepr a2) of
      Just Refl ->
        mbLift $
        nuWithElim (\_ (_ :>: p1' :>: p2') -> p1' == p2')
        (MNil :>: p1 :>: p2)
  (ValPerm_Exists _) == _ = False
  (ValPerm_Mu p1) == (ValPerm_Mu p2) =
    mbLift $
    nuWithElim (\_ (_ :>: p1' :>: p2') -> p1' == p2') (MNil :>: p1 :>: p2)
  (ValPerm_Mu _) == _ = False
  (ValPerm_Var x1) == (ValPerm_Var x2) = x1 == x2
  (ValPerm_Var _) == _ = False
  (ValPerm_LLVMPtr pps1) == (ValPerm_LLVMPtr pps2) = pps1 == pps2
  (ValPerm_LLVMPtr _) == _ = False

{-
instance (Eq (LLVMPtrPerm w)) where
  (LLVMFieldPerm off1 spl1 p1) == (LLVMFieldPerm off2 spl2 p2) =
    off1 == off2 && spl1 == spl2 && p1 == p2
  (LLVMFieldPerm _ _ _) == _ = False
  (LLVMArrayPerm off1 len1 stride1 spl1 ps1) ==
    (LLVMArrayPerm off2 len2 stride2 spl2 ps2) =
    off1 == off2 && len1 == len2 && stride1 == stride2 &&
    spl1 == spl2 && ps1 == ps2
  (LLVMArrayPerm _ _ _ _ _) == _ = False
  (LLVMPP_Free e1) == (LLVMPP_Free e2) = e1 == e2
  (LLVMPP_Free _) == _ = False
-}


$(mkNuMatching [t| forall a . ValuePerm a |])
$(mkNuMatching [t| forall w . LLVMPtrPerm w |])
$(mkNuMatching [t| forall w . LLVMFieldPerm w |])
$(mkNuMatching [t| forall w . LLVMArrayPerm w |])


-- | Extract @p1@ from a permission of the form @p1 \/ p2@
orPermLeft :: ValuePerm a -> ValuePerm a
orPermLeft (ValPerm_Or p _) = p
orPermLeft _ = error "orPermLeft"

-- | Extract @p2@ from a permission of the form @p1 \/ p2@
orPermRight :: ValuePerm a -> ValuePerm a
orPermRight (ValPerm_Or _ p) = p
orPermRight _ = error "orPermRight"

-- | Extract the body @p@ from a permission of the form @exists (x:tp).p@
exPermBody :: TypeRepr tp -> ValuePerm a -> Binding tp (ValuePerm a)
exPermBody tp (ValPerm_Exists (p :: Binding tp' (ValuePerm a)))
  | Just Refl <- testEquality tp (knownRepr :: TypeRepr tp') = p
exPermBody _ _ = error "exPermBody"

-- | Add an offset to a pointer permission
offsetLLVMPtrPerm :: (1 <= w, KnownNat w) =>
                     PermExpr (BVType w) -> LLVMPtrPerm w -> LLVMPtrPerm w
offsetLLVMPtrPerm off (LLVMPP_Field fp) =
  LLVMPP_Field $ offsetLLVMFieldPerm off fp
offsetLLVMPtrPerm off (LLVMPP_Array ap) =
  LLVMPP_Array $ offsetLLVMArrayPerm off ap
offsetLLVMPtrPerm _ (LLVMPP_Free e) = LLVMPP_Free e

-- | Add an offset to a field permission
offsetLLVMFieldPerm :: (1 <= w, KnownNat w) =>
                     PermExpr (BVType w) -> LLVMFieldPerm w -> LLVMFieldPerm w
offsetLLVMFieldPerm off (LLVMFieldPerm {..}) =
  LLVMFieldPerm { llvmFieldOffset = bvAdd llvmFieldOffset off, ..}

-- | Add an offset to an array permission
offsetLLVMArrayPerm :: (1 <= w, KnownNat w) =>
                     PermExpr (BVType w) -> LLVMArrayPerm w -> LLVMArrayPerm w
offsetLLVMArrayPerm off (LLVMArrayPerm {..}) =
  LLVMArrayPerm { llvmArrayOffset = bvAdd llvmArrayOffset off, ..}

-- | Lens for the pointer permissions of an LLVM pointer permission
llvmPtrPerms :: Lens' (ValuePerm (LLVMPointerType w)) [LLVMPtrPerm w]
llvmPtrPerms =
  lens
  (\p -> case p of
      ValPerm_LLVMPtr pps -> pps
      _ -> error "llvmPtrPerms: not an LLVM pointer permission")
  (\p pps ->
    case p of
      ValPerm_LLVMPtr _ -> ValPerm_LLVMPtr pps
      _ -> error "llvmPtrPerms: not an LLVM pointer permission")

-- | Lens for the @i@th pointer permission of an LLVM pointer permission
llvmPtrPerm :: Int -> Lens' (ValuePerm (LLVMPointerType w)) (LLVMPtrPerm w)
llvmPtrPerm i =
  lens
  (\p -> if i >= length (p ^. llvmPtrPerms) then
           error "llvmPtrPerm: index out of bounds"
         else (p ^. llvmPtrPerms) !! i)
  (\p pp ->
    -- FIXME: there has got to be a nicer, more lens-like way to do this
    let pps = p ^. llvmPtrPerms in
    if i >= length pps then
      error "llvmPtrPerm: index out of bounds"
    else set llvmPtrPerms (take i pps ++ (pp : drop (i+1) pps)) p)

-- | Add a new 'LLVMPtrPerm' to the end of the list of those contained in the
-- 'llvmPtrPerms' of a permission
addLLVMPtrPerm :: LLVMPtrPerm w -> ValuePerm (LLVMPointerType w) ->
                  ValuePerm (LLVMPointerType w)
addLLVMPtrPerm pp = over llvmPtrPerms (++ [pp])

-- | Delete the 'LLVMPtrPerm' at the given index from the list of those
-- contained in the 'llvmPtrPerms' of a permission
deleteLLVMPtrPerm :: Int -> ValuePerm (LLVMPointerType w) ->
                     ValuePerm (LLVMPointerType w)
deleteLLVMPtrPerm i =
  over llvmPtrPerms (\pps ->
                      if i >= length pps then
                        error "deleteLLVMPtrPerm: index out of bounds"
                      else take i pps ++ drop (i+1) pps)

-- | Return the index of the last 'LLVMPtrPerm' of a permission
lastLLVMPtrPermIndex :: ValuePerm (LLVMPointerType w) -> Int
lastLLVMPtrPermIndex p =
  let len = length (p ^. llvmPtrPerms) in
  if len > 0 then len - 1 else error "lastLLVMPtrPerms: no pointer perms!"

{- FIXME: remove
-- | Set the permission inside an 'LLVMFieldPerm'
setLLVMFieldPerm :: ValuePerm (LLVMPointerType w) ->
                    ValuePerm (LLVMPointerType w) ->
                    ValuePerm (LLVMPointerType w)
setLLVMFieldPerm (ValPerm_LLVMPtr (LLVMFieldPerm {..})) p =
  ValPerm_LLVMPtr (LLVMFieldPerm {llvmFieldPerm = p, ..})
-}


----------------------------------------------------------------------
-- * Matching Functions for Inspecting Permissions
----------------------------------------------------------------------

-- | The type of a matcher, that matches on an object of type @a@ and maybe
-- produces a @b@
type Matcher a b = a -> Maybe b

-- | Delete the nth element of a list
deleteNth :: Int -> [a] -> [a]
deleteNth i xs | i >= length xs = error "deleteNth"
deleteNth i xs = take i xs ++ drop (i+1) xs

-- | Find all indices in a list for which the supplied
-- function @f@ returns @'Just' b@ for some @b@, also returning the @b@s
findMatches :: Matcher a b -> [a] -> [(Int, b)]
findMatches f = mapMaybe (\(i,a) -> (i,) <$> f a) . zip [0 ..]

-- | Find the first index in a list of an element for which the supplied
-- function @f@ returns @'Just' b@ for some @b@, also returning @b@
findMatch :: Matcher a b -> [a] -> Maybe (Int, b)
findMatch f = listToMaybe . findMatches f

-- | Test if a pointer permission is a free permission
matchFreePtrPerm :: Matcher (LLVMPtrPerm w) (PermExpr (BVType w))
matchFreePtrPerm (LLVMPP_Free e) = Just e
matchFreePtrPerm _ = Nothing

-- | Test if a pointer permission is a field permission
matchFieldPtrPerm :: Matcher (LLVMPtrPerm w) (LLVMFieldPerm w)
matchFieldPtrPerm (LLVMPP_Field fp) = Just fp
matchFieldPtrPerm _ = Nothing

-- | Test if a pointer permission is a field permission with a specific offset
matchFieldPtrPermOff :: PermExpr (BVType w) ->
                        Matcher (LLVMPtrPerm w) (LLVMFieldPerm w)
matchFieldPtrPermOff off (LLVMPP_Field fp)
  | off == llvmFieldOffset fp = Just fp
matchFieldPtrPermOff _ _ = Nothing

-- | Test if a pointer permission is an array permission
matchArrayPtrPerm :: Matcher (LLVMPtrPerm w) (LLVMArrayPerm w)
matchArrayPtrPerm (LLVMPP_Array ap) = Just ap
matchArrayPtrPerm _ = Nothing

-- | Find the first 'LLVMPP_Free' in a list of pointer permissions, returning
-- its index in the list and the expression it contains if found
findFreePerm :: [LLVMPtrPerm w] -> Maybe (Int, PermExpr (BVType w))
findFreePerm = findMatch matchFreePtrPerm

-- | Find all fields in a list of pointer permissions, returning their contents
-- and their indices
findFieldPerms :: [LLVMPtrPerm w] -> [(Int, LLVMFieldPerm w)]
findFieldPerms = findMatches matchFieldPtrPerm

-- | Find a field in a list of pointer permissions with a specific offset
findFieldPerm :: PermExpr (BVType w) -> [LLVMPtrPerm w] ->
                 Maybe (Int, LLVMFieldPerm w)
findFieldPerm off = findMatch (matchFieldPtrPermOff off)

-- | Find all arrays in a list of pointer permissions, returning their contents
-- and their indices
findArrayPerms :: [LLVMPtrPerm w] -> [(Int, LLVMArrayPerm w)]
findArrayPerms = findMatches matchArrayPtrPerm


-- | A field match represents a pointer permission that could be used to prove a
-- field permission @off |-> (S,p)@.
--
-- In order to be used, each match case (that is, each constructor here) has a
-- constraint on @off@ that must hold. The match case is a /definite/ match if
-- the constraint holds under all possible substitutions for the free variables
-- of the pointer permissions involved (i.e., the one being proved and the one
-- used to prove it), and otherwise is a /potential/ match. The first argument
-- to each constructor is a 'Bool' that is 'True' for a definite match and
-- 'False' for a potential one.
data LLVMFieldMatch w
  = FieldMatchField Bool Int (LLVMFieldPerm w)
    -- ^ Represents another field permission @(off',S') |-> p'@ at the index
    -- given by the 'Int' argument. The constraint for a definite match is that
    -- @off'=off@.
  | FieldMatchArray Bool Int (LLVMArrayPerm w) (PermExpr (BVType w)) Int
    -- ^ Represents an array permission @(off',<len,*stride,S') |-> pps@ at the
    -- given index. The expression argument gives the index @ix@ into the array,
    -- which equals @(off - off')/stride@. The final 'Int' argument gives the
    -- index into the @pps@ list of the individual field in the @ix@ array cell
    -- whose offset equals @(off - off')%stride@, which must be a static
    -- constant. The constraint for a definite match is @ix < len@.

-- | Test if a field match is a definite match
fieldMatchDefinite :: LLVMFieldMatch w -> Bool
fieldMatchDefinite (FieldMatchField b _ _) = b
fieldMatchDefinite (FieldMatchArray b _ _ _ _) = b

-- | Find all field matches for a given offset @off@ in a list of pointer perms
findFieldMatches :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                    [LLVMPtrPerm w] -> [LLVMFieldMatch w]
findFieldMatches off pps =
  flip mapMaybe (zip pps [0..]) $ \(pp, i) ->
  case pp of
    LLVMPP_Field fp
      | bvCouldEqual off (llvmFieldOffset fp) ->
        Just (FieldMatchField (bvEq off $ llvmFieldOffset fp) i fp)
    LLVMPP_Field _ -> Nothing
    LLVMPP_Array ap@(LLVMArrayPerm {..}) ->
      -- In order to index into an array, off must be a multiple of the stride
      -- plus a known, constant offset into the array cell. That is, the value
      -- (off - off')%stride must be a constant.
      do let arr_off = bvSub off llvmArrayOffset -- offset from start of array
         k <- bvMatchConst (bvMod arr_off llvmArrayStride)
         fld_i <- findIndex (\fld ->
                              llvmFieldOffset fld == bvInt k) llvmArrayFields
         let arr_ix = bvDiv arr_off llvmArrayStride -- index into array
         if bvCouldBeLt arr_ix llvmArrayLen then
           return $ FieldMatchArray (bvLt arr_ix llvmArrayLen) i ap arr_ix fld_i
           else Nothing


-- FIXME HERE: remove, or at least reevaluate, these!
{-
-- | Build a matcher that ignores a value
matchIgnore :: Matcher a ()
matchIgnore = const $ return ()

-- | Build a matcher that tests equality
matchEq :: Eq a => a -> Matcher a a
matchEq a1 a2 | a1 == a2 = return a2
matchEq _ _ = Nothing

-- | Test if a permission is an equality permission
matchEqPerm :: Matcher (ValuePerm a) (PermExpr a)
matchEqPerm (ValPerm_Eq e) = Just e
matchEqPerm _ = Nothing

-- | Test is an expression is an LLVM word
matchLLVMWordExpr :: Matcher (PermExpr (LLVMPointerType w)) (PermExpr (BVType w))
matchLLVMWordExpr (PExpr_LLVMWord e) = Just e
matchLLVMWordExpr _ = Nothing

-- | Test if a permission is an equality permission to a @word(e)@ expression
matchEqLLVMWordPerm :: Matcher (ValuePerm (LLVMPointerType w))
                       (PermExpr (BVType w))
matchEqLLVMWordPerm = matchEqPerm >=> matchLLVMWordExpr

-- | Test if a permission satisfies a predicate inside 0 or more existentials or
-- disjunctions
matchInExsOrs :: Liftable r => Matcher (ValuePerm a) r ->
                 Matcher (ValuePerm a) r
matchInExsOrs f p | Just b <- f p = Just b
matchInExsOrs f (ValPerm_Or p1 p2) = matchInExsOrs f p1 <|> matchInExsOrs f p2
matchInExsOrs f (ValPerm_Exists p) = mbLift $ fmap (matchInExsOrs f) p
matchInExsOrs _ _ = Nothing

-- | Test if a permission is an @eq(e)@ inside 0 or more existentials or
-- disjunctions; does not return the contents of the @eq(e)@ perm, as it may be
-- under some number of name-bindings
matchNestedEqPerm :: Matcher (ValuePerm a) ()
matchNestedEqPerm = matchInExsOrs (matchEqPerm >=> matchIgnore)

-- | Test if a permission is an LLVM pointer permission satisfying the given
-- predicate
matchPtrPerm :: Matcher (LLVMPtrPerm w) r ->
                Matcher (ValuePerm (LLVMPointerType w)) r
matchPtrPerm f (ValPerm_LLVMPtr pp) = f pp
matchPtrPerm _ _ = Nothing

-- | Test if a pointer permission satisfies the given predicate inside 0 or more
-- stars
matchInPtrStars :: Matcher (LLVMPtrPerm w) r -> Matcher (LLVMPtrPerm w) r
matchInPtrStars f p | Just b <- f p = Just b
matchInPtrStars f (LLVMStarPerm p1 p2) =
  matchInPtrStars f p1 <|> matchInPtrStars f p2
matchInPtrStars _ _ = Nothing

-- | Test if a permission satisfies a predicate on 'LLVMPtrPerm's inside 0 or
-- more existentials, disjunctions, and stars; does not return the contents, as
-- these may be under name-bindings
matchInExsOrsStars :: Matcher (LLVMPtrPerm w) r ->
                      Matcher (ValuePerm (LLVMPointerType w)) ()
matchInExsOrsStars f =
  matchInExsOrs (matchPtrPerm (matchInPtrStars f) >=> matchIgnore)

-- | Test if a pointer permission is a free permission
matchFreePtrPerm :: Matcher (LLVMPtrPerm w) (PermExpr (BVType w))
matchFreePtrPerm (LLVMPP_Free e) = Just e
matchFreePtrPerm _ = Nothing

-- | Test if a permission is an @x:ptr(free(e))@ inside 0 or more existentials,
-- disjunctions, or LLVM stars
matchNestedFreePerm :: Matcher (ValuePerm (LLVMPointerType w)) ()
matchNestedFreePerm = matchInExsOrsStars (matchFreePtrPerm >=> matchIgnore)

-- | Test if a pointer permission is a field permission
matchFieldPtrPerm :: Matcher (LLVMPtrPerm w)
                     (PermExpr (BVType w),
                      SplittingExpr, ValuePerm (LLVMPointerType w))
matchFieldPtrPerm (LLVMFieldPerm off spl p) = Just (off, spl, p)
matchFieldPtrPerm _ = Nothing

-- | Test if a pointer permission is a field permission with a specific offset
matchFieldPtrPermOff :: PermExpr (BVType w) ->
                        Matcher (LLVMPtrPerm w) (SplittingExpr,
                                                 ValuePerm (LLVMPointerType w))
matchFieldPtrPermOff off (LLVMFieldPerm off' spl p)
  | off == off' = Just (spl, p)
matchFieldPtrPermOff _ _ = Nothing
-}


----------------------------------------------------------------------
-- * Generalized Substitution
----------------------------------------------------------------------

-- | Defines a substitution type @s@ that supports substituting into expression
-- and permission variables in a given monad @m@
class MonadBind m => SubstVar s m | s -> m where
  extSubst :: s ctx -> PermExpr a -> s (ctx :> a)
  substExprVar :: s ctx -> Mb ctx (ExprVar a) -> m (PermExpr a)
  substPermVar :: s ctx -> Mb ctx (PermVar a) -> m (ValuePerm a)

-- | Generalized notion of substitution, which says that substitution type @s@
-- supports substituting into type @a@ in monad @m@
class SubstVar s m => Substable s a m where
  genSubst :: s ctx -> Mb ctx a -> m a

instance (Substable s a m, NuMatching a) => Substable s (Mb ctx a) m where
  genSubst s mbmb = mbM $ fmap (genSubst s) (mbSwap mbmb)

instance SubstVar s m => Substable s SplittingExpr m where
  genSubst s [nuP| SplExpr_All |] = return SplExpr_All
  genSubst s [nuP| SplExpr_L spl |] = SplExpr_L <$> genSubst s spl
  genSubst s [nuP| SplExpr_R spl |] = SplExpr_R <$> genSubst s spl
  genSubst s [nuP| SplExpr_Star spl1 spl2 |] =
    SplExpr_Star <$> genSubst s spl1 <*> genSubst s spl2
  genSubst s [nuP| SplExpr_Var x |] =
    substExprVar s x >>= \e ->
    case e of
      PExpr_Var y -> return $ SplExpr_Var y
      PExpr_Spl spl -> return spl

-- | Helper function to substitute into 'BVFactor's
substBVFactor :: SubstVar s m => s ctx -> Mb ctx (BVFactor w) ->
                 m (PermExpr (BVType w))
substBVFactor s [nuP| BVFactor i x |] =
  bvMult (mbLift i) <$> substExprVar s x

instance SubstVar s m => Substable s (PermExpr a) m where
  genSubst s [nuP| PExpr_Var x |] = substExprVar s x
  genSubst s [nuP| PExpr_BV factors off |] =
    foldr bvAdd (PExpr_BV [] (mbLift off)) <$>
    mapM (substBVFactor s) (mbList factors)
  genSubst s [nuP| PExpr_Struct args |] =
    PExpr_Struct <$> genSubst s args
  genSubst s [nuP| PExpr_LLVMWord e |] =
    PExpr_LLVMWord <$> genSubst s e
  genSubst s [nuP| PExpr_LLVMOffset x off |] =
    addLLVMOffset <$> substExprVar s x <*> genSubst s off
  genSubst s [nuP| PExpr_Spl spl |] =
    PExpr_Spl <$> genSubst s spl

instance SubstVar s m => Substable s (PermExprs as) m where
  genSubst s [nuP| PExprs_Nil |] = return PExprs_Nil
  genSubst s [nuP| PExprs_Cons es e |] =
    PExprs_Cons <$> genSubst s es <*> genSubst s e

instance SubstVar s m => Substable s (ValuePerm a) m where
  genSubst s [nuP| ValPerm_True |] = return ValPerm_True
  genSubst s [nuP| ValPerm_Eq e |] = ValPerm_Eq <$> genSubst s e
  genSubst s [nuP| ValPerm_Or p1 p2 |] =
    ValPerm_Or <$> genSubst s p1 <*> genSubst s p2
  genSubst s [nuP| ValPerm_Exists p |] =
    ValPerm_Exists <$>
    nuM (\x -> genSubst (extSubst s $ PExpr_Var x) $ mbCombine p)
  genSubst s [nuP| ValPerm_Mu p |] =
    ValPerm_Mu <$> mbM (fmap (genSubst s) $ mbSwap p)
  genSubst s [nuP| ValPerm_Var x |] = substPermVar s x
  genSubst s [nuP| ValPerm_LLVMPtr pps |] =
    ValPerm_LLVMPtr <$> mapM (genSubst s) (mbList pps)

instance SubstVar s m => Substable s (LLVMPtrPerm a) m where
  genSubst s [nuP| LLVMPP_Field fp |] = LLVMPP_Field <$> genSubst s fp
  genSubst s [nuP| LLVMPP_Array ap |] = LLVMPP_Array <$> genSubst s ap
  genSubst s [nuP| LLVMPP_Free len |] = LLVMPP_Free <$> genSubst s len

instance SubstVar s m => Substable s (LLVMFieldPerm a) m where
  genSubst s [nuP| LLVMFieldPerm off spl p |] =
    LLVMFieldPerm <$> genSubst s off <*> genSubst s spl <*> genSubst s p

instance SubstVar s m => Substable s (LLVMArrayPerm a) m where
  genSubst s [nuP| LLVMArrayPerm off len stride spl pps |] =
    LLVMArrayPerm <$> genSubst s off <*> genSubst s len <*>
    return (mbLift stride) <*> genSubst s spl <*>
    mapM (genSubst s) (mbList pps)


----------------------------------------------------------------------
-- * Expression Substitutions
----------------------------------------------------------------------

-- | A substitution assigns a permission expression to each bound name in a
-- name-binding context
newtype PermSubst ctx =
  PermSubst { unPermSubst :: MapRList PermExpr ctx }

emptySubst :: PermSubst RNil
emptySubst = PermSubst empty

consSubst :: PermSubst ctx -> PermExpr a -> PermSubst (ctx :> a)
consSubst (PermSubst elems) e = PermSubst (elems :>: e)

singletonSubst :: PermExpr a -> PermSubst (RNil :> a)
singletonSubst e = PermSubst (empty :>: e)

substLookup :: PermSubst ctx -> Member ctx a -> PermExpr a
substLookup (PermSubst m) memb = mapRListLookup memb m

noPermsInCruCtx :: forall (ctx :: RList CrucibleType) (a :: CrucibleType) b.
                   Member ctx (ValuePerm a) -> b
noPermsInCruCtx (Member_Step ctx) = noPermsInCruCtx ctx
-- No case for Member_Base

instance SubstVar PermSubst Identity where
  extSubst (PermSubst elems) e = PermSubst $ elems :>: e
  substExprVar s x =
    case mbNameBoundP x of
      Left memb -> return $ substLookup s memb
      Right y -> return $ PExpr_Var y
  substPermVar s x =
    case mbNameBoundP x of
      Left memb -> noPermsInCruCtx memb
      Right y -> return $ ValPerm_Var y

-- | Wrapper function to apply a substitution to an expression type
subst :: Substable PermSubst a Identity => PermSubst ctx -> Mb ctx a -> a
subst s mb = runIdentity $ genSubst s mb


----------------------------------------------------------------------
-- * Partial Substitutions
----------------------------------------------------------------------

-- | An element of a partial substitution = maybe an expression
newtype PSubstElem a = PSubstElem { unPSubstElem :: Maybe (PermExpr a) }

-- | Partial substitutions assign expressions to some of the bound names in a
-- context
newtype PartialSubst ctx =
  PartialSubst { unPartialSubst :: MapRList PSubstElem ctx }

-- | Build an empty partial substitution for a given set of variables, i.e., the
-- partial substitution that assigns no expressions to those variables
emptyPSubst :: CruCtx ctx -> PartialSubst ctx
emptyPSubst = PartialSubst . helper where
  helper :: CruCtx ctx -> MapRList PSubstElem ctx
  helper CruCtxNil = MNil
  helper (CruCtxCons ctx' _) = helper ctx' :>: PSubstElem Nothing

-- | FIXME: should be in Hobbits!
modifyMapRList :: Member ctx a -> (f a -> f a) ->
                  MapRList f ctx -> MapRList f ctx
modifyMapRList Member_Base f (elems :>: elem) = elems :>: f elem
modifyMapRList (Member_Step memb) f (elems :>: elem) =
  modifyMapRList memb f elems :>: elem

-- | Set the expression associated with a variable in a partial substitution. It
-- is an error if it is already set.
psubstSet :: Member ctx a -> PermExpr a -> PartialSubst ctx ->
             PartialSubst ctx
psubstSet memb e (PartialSubst elems) =
  PartialSubst $
  modifyMapRList memb
  (\pse -> case pse of
      PSubstElem Nothing -> PSubstElem $ Just e
      PSubstElem (Just _) -> error "psubstSet: value already set for variable")
  elems

-- | Extend a partial substitution with an unassigned variable
extPSubst :: PartialSubst ctx -> PartialSubst (ctx :> a)
extPSubst (PartialSubst elems) = PartialSubst $ elems :>: PSubstElem Nothing

-- | Shorten a partial substitution
unextPSubst :: PartialSubst (ctx :> a) -> PartialSubst ctx
unextPSubst (PartialSubst (elems :>: _)) = PartialSubst elems

-- | Complete a partial substitution into a total substitution, filling in zero
-- values using 'zeroOfType' if necessary
completePSubst :: CruCtx vars -> PartialSubst vars -> PermSubst vars
completePSubst ctx (PartialSubst pselems) = PermSubst $ helper ctx pselems where
  helper :: CruCtx vars -> MapRList PSubstElem vars -> MapRList PermExpr vars
  helper _ MNil = MNil
  helper (CruCtxCons ctx' CruType) (pselems' :>: pse) =
    helper ctx' pselems' :>:
    (fromMaybe (zeroOfType knownRepr) (unPSubstElem pse))

-- | Look up an optional expression in a partial substitution
psubstLookup :: PartialSubst ctx -> Member ctx a -> Maybe (PermExpr a)
psubstLookup (PartialSubst m) memb = unPSubstElem $ mapRListLookup memb m

instance SubstVar PartialSubst Maybe where
  extSubst (PartialSubst elems) e =
    PartialSubst $ elems :>: PSubstElem (Just e)
  substExprVar s x =
    case mbNameBoundP x of
      Left memb -> psubstLookup s memb
      Right y -> return $ PExpr_Var y
  substPermVar s x =
    case mbNameBoundP x of
      Left memb -> noPermsInCruCtx memb
      Right y -> return $ ValPerm_Var y

-- | Wrapper function to apply a partial substitution to an expression type
partialSubst :: Substable PartialSubst a Maybe => PartialSubst ctx ->
                Mb ctx a -> Maybe a
partialSubst s mb = genSubst s mb

-- | Apply a partial substitution, raising an error (with the given string) if
-- this fails
partialSubstForce :: Substable PartialSubst a Maybe => PartialSubst ctx ->
                     Mb ctx a -> String -> a
partialSubstForce s mb msg = fromMaybe (error msg) $ partialSubst s mb


----------------------------------------------------------------------
-- * Permission Sets
----------------------------------------------------------------------

-- | A stack of variables and their permissions
data PermStack ps where
  PStackNil :: PermStack RNil
  PStackCons :: PermStack ps -> ExprVar a -> ValuePerm a ->
                PermStack (ps :> a)

-- | Lens for the top permission in a 'PermStack' stack
pstackHead :: ExprVar a -> Lens' (PermStack (ps :> a)) (ValuePerm a)
pstackHead x =
  lens (\(PStackCons _ y p) ->
         if x == y then p else error "pstackHead: incorrect variable name!")
  (\(PStackCons pstk y _) p ->
    if x == y then PStackCons pstk y p else
      error "pstackHead: incorrect variable name!")

-- | The lens for the tail of a 'PermStack' stack
pstackTail :: Lens' (PermStack (ps :> a)) (PermStack ps)
pstackTail =
  lens (\(PStackCons pstk _ _) -> pstk)
  (\(PStackCons _ x p) pstk -> PStackCons pstk x p)

-- | The lens for the nth permission in a 'PermStack' stack
nthVarPerm :: Member ps a -> ExprVar a -> Lens' (PermStack ps) (ValuePerm a)
nthVarPerm Member_Base x = pstackHead x
nthVarPerm (Member_Step memb') x = pstackTail . nthVarPerm memb' x

-- | A permission set associates permissions with expression variables, and also
-- has a stack of "distinguished permissions" that are used for intro rules
data PermSet ps = PermSet { _varPermMap :: NameMap ValuePerm,
                            _distPerms :: PermStack ps }

makeLenses ''PermSet

-- NOTE: these instances would require a NuMatching instance for NameMap...
-- $(mkNuMatching [t| forall ps. PermStack ps |])
-- $(mkNuMatching [t| forall ps. PermSet ps |])

-- | The lens for the permissions associated with a given variable
varPerm :: ExprVar a -> Lens' (PermSet ps) (ValuePerm a)
varPerm x =
  lens
  (\(PermSet nmap _) ->
    case NameMap.lookup x nmap of
      Just p -> p
      Nothing -> ValPerm_True)
  (\(PermSet nmap ps) p -> PermSet (NameMap.insert x p nmap) ps)

-- | The lens for a particular distinguished perm, checking that it is indeed
-- associated with the given variable
distPerm :: Member ps a -> ExprVar a -> Lens' (PermSet ps) (ValuePerm a)
distPerm memb x = distPerms . nthVarPerm memb x

-- | The lens for the distinguished perm at the top of the stack, checking that
-- it has the given variable
topDistPerm :: ExprVar a -> Lens' (PermSet (ps :> a)) (ValuePerm a)
topDistPerm x = distPerms . pstackHead x

-- | Push a new distinguished permission onto the top of the stack
pushPerm :: ExprVar a -> ValuePerm a -> PermSet ps -> PermSet (ps :> a)
pushPerm x p (PermSet nmap ps) = PermSet nmap (PStackCons ps x p)

-- | Pop the top distinguished permission off of the stack
popPerm :: ExprVar a -> PermSet (ps :> a) -> (PermSet ps, ValuePerm a)
popPerm x (PermSet nmap pstk) =
  (PermSet nmap (pstk ^. pstackTail), pstk ^. pstackHead x)

-- | Introduce a proof of @x:true@ onto the top of the stack
introTrue :: ExprVar a -> PermSet ps -> PermSet (ps :> a)
introTrue x = pushPerm x ValPerm_True

-- | Apply the left or-introduction rule to the top of the permission stack,
-- changing it from @x:p1@ to @x:(p1 \/ p2)@
introOrL :: ExprVar a -> ValuePerm a -> PermSet (ps :> a) -> PermSet (ps :> a)
introOrL x p2 = over (topDistPerm x) (\p1 -> ValPerm_Or p1 p2)

-- | Apply the right or-introduction rule to the top of the permission stack,
-- changing it from @x:p2@ to @x:(p1 \/ p2)@
introOrR :: ExprVar a -> ValuePerm a -> PermSet (ps :> a) -> PermSet (ps :> a)
introOrR x p1 = over (topDistPerm x) (\p2 -> ValPerm_Or p1 p2)

-- | Apply existential introduction to the top of the permission stack, changing
-- it from @[e/x]p@ to @exists (x:tp).p@
introExists :: KnownRepr TypeRepr tp => ExprVar a -> PermExpr tp ->
               Binding tp (ValuePerm a) ->
               PermSet (ps :> a) -> PermSet (ps :> a)
introExists x e p_body =
  over (topDistPerm x) $ \p_old ->
  if p_old == subst (singletonSubst e) p_body then ValPerm_Exists p_body else
    error "introExists: permission on the top of the stack does not match"

-- | Replace an or permission for a given variable with its left disjunct
elimOrLeft :: ExprVar a -> PermSet ps -> PermSet ps
elimOrLeft x = over (varPerm x) orPermLeft

-- | Replace an or permission for a given variable with its right disjunct
elimOrRight :: ExprVar a -> PermSet ps -> PermSet ps
elimOrRight x = over (varPerm x) orPermRight

-- | Replace an existential permission for a given variable with its body
elimExists :: ExprVar a -> TypeRepr tp -> PermSet ps -> Binding tp (PermSet ps)
elimExists x tp perms =
  nuWithElim1
  (\_ p_body -> set (varPerm x) p_body perms)
  (exPermBody tp $ perms ^. varPerm x)

-- | Introduce a proof of @x:eq(x)@ onto the top of the stack
introEqRefl :: ExprVar a -> PermSet ps -> PermSet (ps :> a)
introEqRefl x = pushPerm x (ValPerm_Eq (PExpr_Var x))

-- | Copy an @x:eq(e)@ permission to the top of the stack
introEqCopy :: ExprVar a -> PermExpr a -> PermSet ps -> PermSet (ps :> a)
introEqCopy x e perms =
  case perms ^. varPerm x of
    ValPerm_Eq e' | e' == e -> pushPerm x (ValPerm_Eq e) perms
    _ -> error "introEqCopy: unexpected existing permission on variable"

-- | Cast a proof of @x:eq(LLVMWord(e1))@ to @x:eq(LLVMWord(e2))@ on the top of
-- the stack
castLLVMWordEq :: ExprVar (LLVMPointerType w) ->
                  PermExpr (BVType w) -> PermExpr (BVType w) ->
                  PermSet (ps :> LLVMPointerType w) ->
                  PermSet (ps :> LLVMPointerType w)
castLLVMWordEq x e1 e2 =
  over (topDistPerm x) $ \p ->
  case p of
    ValPerm_Eq (PExpr_LLVMWord e1')
      | bvEq e1' e1 -> ValPerm_Eq (PExpr_LLVMWord e2)
    _ -> error "castLLVMWordEq: unexpected existing permission"

-- | Prove an empty @x:ptr()@ permission from any @x:ptr(pps)@ permission
introLLVMPtr :: ExprVar (LLVMPointerType w) -> PermSet ps ->
                PermSet (ps :> LLVMPointerType w)
introLLVMPtr x perms =
  case perms ^. varPerm x of
    ValPerm_LLVMPtr _ -> pushPerm x (ValPerm_LLVMPtr []) perms
    _ -> error "introLLVMPtr: no LLVMptr permission"

-- | Cast a @y:ptr(pps)@ on the top of the stack to @x:ptr(pps - off)@ using a
-- proof of @x:eq(y+off)@ just below it on the stack
castLLVMPtr :: ExprVar (LLVMPointerType w) -> PermExpr (BVType w) ->
               ExprVar (LLVMPointerType w) ->
               PermSet (ps :> LLVMPointerType w :> LLVMPointerType w) ->
               PermSet (ps :> LLVMPointerType w)
castLLVMPtr y off x perms =
  let (perms', y_ptr_perm) = popPerm y perms
      (perms'', x_eq_perm) = popPerm x perms' in
  case (y_ptr_perm, x_eq_perm) of
    (p@(ValPerm_LLVMPtr _), ValPerm_Eq (PExpr_Var y'))
      | y' == y -> pushPerm x p perms''
    (ValPerm_LLVMPtr pps, ValPerm_Eq (PExpr_LLVMOffset y' off))
      | y' == y ->
        pushPerm x (ValPerm_LLVMPtr $ map (offsetLLVMPtrPerm off) pps) perms''
    _ -> error "castLLVMPtr"

-- | Copy an LLVM free permission @free(e)@ from the current
-- @x:ptr(pps1,free(e),pps2)@ permission into the @x:ptr(pps)@ permission on the
-- top of the stack, where the 'Int' index gives the size of @pps1@
introLLVMFree :: ExprVar (LLVMPointerType w) -> Int ->
                 PermSet (ps :> LLVMPointerType w) ->
                 PermSet (ps :> LLVMPointerType w)
introLLVMFree x i perms =
  case perms ^. (varPerm x . llvmPtrPerm i) of
    pp_i@(LLVMPP_Free _) ->
      over (varPerm x) (deleteLLVMPtrPerm i) $
      over (topDistPerm x) (addLLVMPtrPerm pp_i)
      perms
    _ -> error "introLLVMFree"

-- | Cast a proof of @x:ptr(pps1, free(e1), pps2)@ on the top of the stack to
-- one of @x:ptr(pps1, free(e2), pps2)@
castLLVMFree :: ExprVar (LLVMPointerType w) -> Int ->
                PermExpr (BVType w) -> PermExpr (BVType w) ->
                PermSet (ps :> LLVMPointerType w) ->
                PermSet (ps :> LLVMPointerType w)
castLLVMFree x i e1 e2 =
  over (varPerm x . llvmPtrPerm i) $ \pp_i ->
  case pp_i of
    LLVMPP_Free e | e == e1 -> LLVMPP_Free e2
    _ -> error "castLLVMFree"

-- | Move a field permission of the form @(off,All) |-> p@, which should be
-- the @i@th 'LVMPtrPerm' associated with @x@, into the @x:ptr(pps)@ permission
-- on the top of of the stack, resulting in the permission of the form
-- @x:ptr(pps, (off,All) |-> p)@ on the top of the stack.
introLLVMFieldAll :: ExprVar (LLVMPointerType w) -> Int ->
                     PermSet (ps :> LLVMPointerType w) ->
                     PermSet (ps :> LLVMPointerType w)
introLLVMFieldAll x i perms =
  case perms ^. (varPerm x . llvmPtrPerm i) of
    pp_i@(LLVMPP_Field (LLVMFieldPerm _ SplExpr_All _)) ->
      over (varPerm x) (deleteLLVMPtrPerm i) $
      over (topDistPerm x) (addLLVMPtrPerm pp_i)
      perms
    _ -> error "introLLVMFieldAll"

-- | Split a field permission @(off,spl) |-> eq(e)@ into two, leaving the left
-- half in the current permission stack and moving the right half to the top of
-- of the stack
introLLVMFieldSplit :: ExprVar (LLVMPointerType w) -> Int -> SplittingExpr ->
                       PermSet (ps :> LLVMPointerType w) ->
                       PermSet (ps :> LLVMPointerType w)
introLLVMFieldSplit x i spl perms =
  case perms ^. (varPerm x . llvmPtrPerm i) of
    pp_i@(LLVMPP_Field fp)
      | llvmFieldSplitting fp == spl
      , ValPerm_Eq _ <- llvmFieldPerm fp ->
        set (varPerm x . llvmPtrPerm i) (LLVMPP_Field $
                                         fp { llvmFieldSplitting =
                                              SplExpr_L spl }) $
        over (topDistPerm x) (addLLVMPtrPerm $
                              LLVMPP_Field $
                              fp { llvmFieldSplitting = SplExpr_R spl })
        perms
    _ -> error "introLLVMFieldSplit"

-- | Combine proofs of @x:ptr(pps,(off,spl) |-> eq(y))@ and @y:p@ on the top of
-- the permission stack into a proof of @x:ptr(pps,(off,spl |-> p))@
introLLVMFieldContents :: ExprVar (LLVMPointerType w) ->
                          ExprVar (LLVMPointerType w) ->
                          PermSet (ps :> LLVMPointerType w
                                   :> LLVMPointerType w) ->
                          PermSet (ps :> LLVMPointerType w)
introLLVMFieldContents x y perms =
  let (perms', y_perm) = popPerm y perms
      i = lastLLVMPtrPermIndex (perms ^. topDistPerm x) in
  over (topDistPerm x . llvmPtrPerm i)
  (\pp -> case pp of
      LLVMPP_Field fp
        | ValPerm_Eq (PExpr_Var y') <- llvmFieldPerm fp , y' == y ->
            LLVMPP_Field $ fp { llvmFieldPerm = y_perm }
      _ -> error "introLLVMFieldContents")
  perms'

-- | Eliminate a permission @x:ptr(pps1,(off,S) |-> p,pps2)@ into permissions
-- @x:ptr(pps1,(off,S) |-> eq(y),pps2)@ and @y:p@ for a fresh variable @y@. If
-- the permissions for @x@ are already of this form, just return @y@.
elimLLVMFieldContents :: ExprVar (LLVMPointerType w) -> Int -> PermSet ps ->
                         Either (ExprVar (LLVMPointerType w))
                         (Binding (LLVMPointerType w) (PermSet ps))
elimLLVMFieldContents x i perms =
  case perms ^. (varPerm x . llvmPtrPerm i) of
    LLVMPP_Field fp
      | ValPerm_Eq (PExpr_Var y) <- llvmFieldPerm fp -> Left y
    LLVMPP_Field fp ->
      Right $ nu $ \y ->
      set (varPerm y) (llvmFieldPerm fp) $
      set (varPerm x . llvmPtrPerm i)
      (LLVMPP_Field $ fp {llvmFieldPerm = ValPerm_Eq (PExpr_Var y) }) $
      perms
    _ -> error "elimLLVMFieldContents"

-- | Divide an array permission @x:ptr((off,*stride,<len,S) |-> p)@ into two
-- arrays, one of length @e@ starting at @off@ and one of length @len-e@
-- starting at offset @off+e*stride@. The latter permission (at offset
-- @off+e*stride@) stays at the same index, while the former (at the original
-- offset) is moved to the end of the field permissions for @x@.
divideLLVMArray :: ExprVar (LLVMPointerType w) -> Int -> PermExpr (BVType w) ->
                   PermSet ps -> PermSet ps
divideLLVMArray x i e perms =
  case (perms ^. varPerm x, perms ^. (varPerm x . llvmPtrPerm i)) of
    (ValPerm_LLVMPtr _, LLVMPP_Array ap) ->
      -- The match on perms ^. varPerm x is to get the 1 <= w instance
      set (varPerm x . llvmPtrPerm i)
      (LLVMPP_Array $
       ap { llvmArrayLen = bvSub (llvmArrayLen ap) e,
            llvmArrayOffset =
              bvAdd (llvmArrayOffset ap) (bvMult (llvmArrayStride ap) e) }) $
      over (varPerm x) (addLLVMPtrPerm $
                        LLVMPP_Array $ ap { llvmArrayLen = e }) $
      perms
    _ -> error "divideLLVMArray"

-- | Perform an array indexing of the first cell of an array, by separating an
-- array permission @x:ptr((off,*stride,<len,S) |-> pps)@ into one array cell,
-- containing a copy of the pointer permissions @pps@ starting at offset @off@,
-- along with the remaining array @x:ptr((off+1,*stride,<len,S) |-> -- pps)@.
-- Return the new permission set along with the indices of the new @pps@ pointer
-- permissions.
indexLLVMArray :: ExprVar (LLVMPointerType w) -> Int -> PermSet ps ->
                  (PermSet ps, [(Int, LLVMFieldPerm w)])
indexLLVMArray x i perms =
  case (perms ^. varPerm x, perms ^. (varPerm x . llvmPtrPerm i)) of
    (ValPerm_LLVMPtr _, LLVMPP_Array ap) ->
      -- The match on perms ^. varPerm x is to get the 1 <= w instance
      let new_fps =
            map (offsetLLVMFieldPerm (llvmArrayOffset ap)) (llvmArrayFields ap) in
      (set (varPerm x . llvmPtrPerm i)
       (LLVMPP_Array $ ap { llvmArrayOffset =
                            bvAdd (llvmArrayOffset ap) (bvInt 1)}) $
       over (varPerm x . llvmPtrPerms) (++ map LLVMPP_Field new_fps) $
       perms
      ,
      zip [length (perms ^. (varPerm x . llvmPtrPerms)) ..] new_fps)
    _ -> error "indexLLVMArray"

-- | Cast the the offset of the last pointer permission at the top of the stack,
-- going from @(off,S) |-> p@ to @(off',S) |-> p@, assuming that we know (or can
-- assert) that @off=off'.
castLLVMFieldOffset :: ExprVar (LLVMPointerType w) -> PermExpr (BVType w) ->
                       PermExpr (BVType w) ->
                       PermSet (ps :> LLVMPointerType w) ->
                       PermSet (ps :> LLVMPointerType w)
castLLVMFieldOffset x off off' perms =
  let i = lastLLVMPtrPermIndex (perms ^. topDistPerm x) in
  over (topDistPerm x . llvmPtrPerm i)
  (\p -> case p of
      LLVMPP_Field fp
        | llvmFieldOffset fp `bvEq` off ->
            LLVMPP_Field (fp { llvmFieldOffset = off' })
      _ -> error "castLLVMFieldOffset")
  perms
