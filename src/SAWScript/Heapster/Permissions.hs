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
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PartialTypeSignatures #-}

module SAWScript.Heapster.Permissions where

import qualified Control.Lens                     as Lens
import           Data.List
import           Data.Kind
import           Data.Proxy
import           Data.Functor.Const
import           Data.Parameterized.Some
import           Data.Parameterized.Context
import           Data.Parameterized.Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.TraversableFC
import           Data.Type.Equality
import           Data.Functor.Product
import           Numeric.Natural
import qualified Control.Category as Cat
import           Control.Monad.State

import           Lang.Crucible.Types
-- import           Lang.Crucible.LLVM.Types
import           Lang.Crucible.LLVM.MemModel
-- import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.CFG.Core


----------------------------------------------------------------------
-- * Variables and Weakenings
----------------------------------------------------------------------

-- FIXME: these need to go into parameterized-utils

oneDiff :: Diff ctx (ctx ::> tp)
oneDiff = extendRight noDiff

subtractSizeLeft :: Size (ctx1 <+> ctx2) -> Size ctx1 -> p ctx2 -> Size ctx2
subtractSizeLeft = error "FIXME: subtractSizeLeft"

subtractSizeRight :: Size (ctx1 <+> ctx2) -> p ctx1 -> Size ctx2 -> Size ctx1
subtractSizeRight = error "FIXME: subtractSizeRight"

caseIndexAppend :: Size ctx1 -> p ctx2 -> Index (ctx1 <+> ctx2) a ->
                   Either (Index ctx1 a) (Index ctx2 a)
caseIndexAppend = error "FIXME: caseIndexAppend"

extendIndexLeft :: Size ctx1 -> Index ctx2 a -> Index (ctx1 <+> ctx2) a
extendIndexLeft = error "FIXME: extendIndexLeft"


-- | Our variables need to keep the 'Size' of the context around so that we can
-- apply weakenings
data PermVar ctx a = PermVar (Size ctx) (Index ctx a)

nextPermVar :: Size ctx -> PermVar (ctx ::> a) a
nextPermVar sz = PermVar (incSize sz) (nextIndex sz)

instance TestEquality (PermVar ctx) where
  testEquality (PermVar _ x) (PermVar _ y) = testEquality x y

instance Eq (PermVar ctx a) where
  (PermVar _ x) == (PermVar _ y) = x == y

instance ExtendContext' PermVar where
  extendContext' diff (PermVar sz x) =
    PermVar (extSize sz diff) (extendContext' diff x)

caseVarAppend :: Size ctx1 -> Size ctx2 -> PermVar (ctx1 <+> ctx2) a ->
                 Either (PermVar ctx1 a) (PermVar ctx2 a)
caseVarAppend sz1 sz2 (PermVar _ x) =
  case caseIndexAppend sz1 sz2 x of
    Left x1 -> Left $ PermVar sz1 x1
    Right x2 -> Right $ PermVar sz2 x2

-- | Build a lens into an 'Assignment' using a 'PermVar'
pvLens :: PermVar ctx a -> Lens.Lens' (Assignment f ctx) (f a)
pvLens (PermVar _ x) = ixF' x

-- | Look up a 'PermVar' in an 'Assignment'
pvGet :: Assignment f ctx -> PermVar ctx a -> f a
pvGet asgn x = Lens.view (pvLens x) asgn

-- | Modify the value associated with a 'PermVar' in an 'Assignment'
pvModify :: PermVar ctx a -> (f a -> f a) -> Assignment f ctx -> Assignment f ctx
pvModify x f asgn = Lens.over (pvLens x) f asgn

-- | Set the value associated with a 'PermVar' in an 'Assignment'
pvSet :: PermVar ctx a -> f a -> Assignment f ctx -> Assignment f ctx
pvSet x f asgn = Lens.set (pvLens x) f asgn

class FreeVars f where
  freeVars :: f ctx -> [Some (PermVar ctx)]

class FreeVars' f where
  freeVars' :: f ctx a -> [Some (PermVar ctx)]


----------------------------------------------------------------------
-- * Expressions for Use in Permission Sets
----------------------------------------------------------------------

-- | Expressions that represent "fractions" of a write permission
data SplittingExpr ctx
  = SplExpr_All
  | SplExpr_L (SplittingExpr ctx)
  | SplExpr_R (SplittingExpr ctx)
  | SplExpr_Star (SplittingExpr ctx) (SplittingExpr ctx)
  | SplExpr_Var (PermVar ctx SplittingType)

-- | Crucible type for splitting expressions
type SplittingType = IntrinsicType "Splitting" EmptyCtx

splittingTypeRepr :: TypeRepr SplittingType
splittingTypeRepr = knownRepr

-- | Expressions that are considered "pure" for use in permissions. Note that
-- these are in a normal form, that makes them easier to analyze.
data PermExpr (ctx :: Ctx CrucibleType) (a :: CrucibleType) where
  PExpr_Var :: PermVar ctx a -> PermExpr ctx a
  -- ^ A variable of any type

  PExpr_BV :: (1 <= w) => NatRepr w ->
              [BVFactor ctx w] -> Integer -> PermExpr ctx (BVType w)
  -- ^ A bitvector expression is a linear expression in @N@ variables, i.e., sum
  -- of constant times variable factors plus a constant

  PExpr_Struct :: CtxRepr args -> Assignment (PermExpr ctx) args ->
                  PermExpr ctx (StructType args)
  -- ^ A struct expression is an expression for each argument of the struct type

  PExpr_LLVMWord :: (1 <= w) => NatRepr w ->
                    PermExpr ctx (BVType w) ->
                    PermExpr ctx (LLVMPointerType w)
  -- ^ An LLVM value that represents a word, i.e., whose region identifier is 0

  PExpr_LLVMOffset :: (1 <= w) => NatRepr w ->
                      PermVar ctx (LLVMPointerType w) ->
                      PermExpr ctx (BVType w) ->
                      PermExpr ctx (LLVMPointerType w)
  -- ^ An LLVM value built by adding an offset to an LLVM variable

  PExpr_Spl :: SplittingExpr ctx -> PermExpr ctx SplittingType


-- | A bitvector variable, possibly multiplied by a constant
data BVFactor ctx w where
  BVFactor :: (1 <= w) => NatRepr w -> Integer -> PermVar ctx (BVType w) ->
              BVFactor ctx w
    -- ^ A variable of type @'BVType' w@ multiplied by a constant

instance FreeVars SplittingExpr where
  freeVars SplExpr_All = []
  freeVars (SplExpr_L e) = freeVars e
  freeVars (SplExpr_R e) = freeVars e
  freeVars (SplExpr_Star e1 e2) = freeVars e1 ++ freeVars e2
  freeVars (SplExpr_Var x) = [Some x]

instance FreeVars' PermExpr where
  freeVars' (PExpr_Var x) = [Some x]
  freeVars' (PExpr_BV _ factors const) = concatMap freeVars' factors
  freeVars' (PExpr_Struct args_ctx args) = foldMapFC freeVars' args
  freeVars' (PExpr_LLVMWord _ expr) = freeVars' expr
  freeVars' (PExpr_LLVMOffset _ x off) = Some x : freeVars' off
  freeVars' (PExpr_Spl spl) = freeVars spl

instance FreeVars' BVFactor where
  freeVars' (BVFactor _ _ x) = [Some x]

-- | Multiply a 'BVFactor' by a constant
multFactor :: Integer -> BVFactor ctx w -> BVFactor ctx w
multFactor i (BVFactor w j x) = BVFactor w (i*j) x

-- | Convert a bitvector expression to a sum of factors plus a constant
matchBVExpr :: (1 <= w) => NatRepr w -> PermExpr ctx (BVType w) ->
               ([BVFactor ctx w], Integer)
matchBVExpr w (PExpr_Var x) = ([BVFactor w 1 x], 0)
matchBVExpr _ (PExpr_BV _ factors const) = (factors, const)

-- | Add two bitvector expressions
addBVExprs :: (1 <= w) => NatRepr w ->
              PermExpr ctx (BVType w) -> PermExpr ctx (BVType w) ->
              PermExpr ctx (BVType w)
addBVExprs w (matchBVExpr w -> (factors1, const1)) (matchBVExpr w ->
                                                    (factors2, const2)) =
  PExpr_BV w (factors1 ++ factors2) (const1 + const2)

-- | Build a "default" expression for a given type
zeroOfType :: TypeRepr tp -> PermExpr ctx tp
zeroOfType (BVRepr w) = PExpr_BV w [] 0
zeroOfType (testEquality splittingTypeRepr -> Just Refl) =
  PExpr_Spl SplExpr_All
zeroOfType _ = error "zeroOfType"


----------------------------------------------------------------------
-- * Substitutions and Weakenings
----------------------------------------------------------------------

-- | A "generalized substitution" is an object that maps permission variables in
-- one context to permission expressions in some other context, that can also be
-- weakened. This generalizes weakenings, substitutions, and partial
-- substitutions.
data GenSubst ctx1 ctx2
  = GenSubst { genSubstVar :: forall a. PermVar ctx1 a -> PermExpr ctx2 a,
               weakenGenSubst1 :: forall tp. GenSubst (ctx1 ::> tp) (ctx2 ::> tp) }

class GenSubstable f where
  genSubst :: GenSubst ctx1 ctx2 -> f ctx1 -> f ctx2

class GenSubstable' f where
  genSubst' :: GenSubst ctx1 ctx2 -> f ctx1 a -> f ctx2 a

genSubstFactor :: GenSubst ctx1 ctx2 -> BVFactor ctx1 w ->
                  ([BVFactor ctx2 w], Integer)
genSubstFactor s f@(BVFactor w i x) =
  let (factors, const) = matchBVExpr w (genSubstVar s x) in
  (map (multFactor i) factors, const)

instance GenSubstable' PermExpr where
  genSubst' s (PExpr_Var x) = genSubstVar s x
  genSubst' s (PExpr_BV w factors const) =
    let (factorss', consts') = unzip (map (genSubstFactor s) factors) in
    PExpr_BV w (concat factorss') (const + sum consts')
  genSubst' s (PExpr_Struct args_ctx args) =
    PExpr_Struct args_ctx $ fmapFC (genSubst' s) args
  genSubst' s (PExpr_LLVMWord w expr) = PExpr_LLVMWord w $ genSubst' s expr
  genSubst' s (PExpr_LLVMOffset w x off) =
    case genSubstVar s x of
      PExpr_Var x' -> PExpr_LLVMOffset w x' (genSubst' s off)
      PExpr_LLVMWord _ bv -> PExpr_LLVMWord w $ addBVExprs w bv (genSubst' s off)
      PExpr_LLVMOffset _ x' bv ->
        PExpr_LLVMOffset w x' $ addBVExprs w bv (genSubst' s off)
  genSubst' s (PExpr_Spl spl) = PExpr_Spl $ genSubst s spl

{-
instance GenSubstable' BVFactor where
  genSubst' s (BVFactor i x) = BVFactor i $ genSubstVar s expr
-}

instance GenSubstable SplittingExpr where
  genSubst _ SplExpr_All = SplExpr_All
  genSubst s (SplExpr_L e) = SplExpr_L (genSubst s e)
  genSubst s (SplExpr_R e) = SplExpr_R (genSubst s e)
  genSubst s (SplExpr_Star e1 e2) =
    SplExpr_Star (genSubst s e1) (genSubst s e2)
  genSubst s (SplExpr_Var x) =
    case genSubstVar s x of
      PExpr_Var x' -> SplExpr_Var x'
      PExpr_Spl spl -> spl


-- | A weakening is a 'Diff' on a prefix of the context
data Weakening ctx1 ctx2 where
  Weakening :: Diff c1 c2 -> Size c3 -> Weakening (c1 <+> c3) (c2 <+> c3)

identityWeakening :: Weakening ctx ctx
identityWeakening = Weakening noDiff zeroSize

mkWeakening1 :: Weakening ctx (ctx ::> tp)
mkWeakening1 = weakeningOfDiff oneDiff

weakenWeakening1 :: Weakening ctx1 ctx2 -> Weakening (ctx1 ::> tp) (ctx2 ::> tp)
weakenWeakening1 (Weakening diff sz) = Weakening diff $ incSize sz

genSubstOfWeakening :: Weakening ctx1 ctx2 -> GenSubst ctx1 ctx2
genSubstOfWeakening w =
  GenSubst (PExpr_Var . weaken' w) (genSubstOfWeakening $ weakenWeakening1 w)

weakeningOfDiff :: Diff ctx1 ctx2 -> Weakening ctx1 ctx2
weakeningOfDiff diff = Weakening diff zeroSize

genSubstOfDiff :: Diff ctx1 ctx2 -> GenSubst ctx1 ctx2
genSubstOfDiff = genSubstOfWeakening . weakeningOfDiff

class Weakenable (f :: Ctx k -> *) where
  weaken :: Weakening ctx1 ctx2 -> f ctx1 -> f ctx2

class Weakenable' (f :: Ctx k -> k' -> *) where
  weaken' :: Weakening ctx1 ctx2 -> f ctx1 a -> f ctx2 a

instance Weakenable Size where
  weaken (Weakening diff12 sz3) sz =
    addSize (extSize (subtractSizeRight sz Proxy sz3) diff12) sz3

instance Weakenable' PermVar where
  weaken' w@(Weakening diff12 (sz3 :: Size c3)) (PermVar sz13 x) =
    PermVar (weaken w sz13) $
    let sz1 = subtractSizeRight sz13 Proxy sz3 in
    case caseIndexAppend sz1 (Proxy :: Proxy c3) x of
      Left x1 -> extendIndex' (appendDiff sz3 Cat.. diff12) x1
      Right x3 -> extendIndexLeft (extSize sz1 diff12) x3

instance Weakenable' PermExpr where
  weaken' w = genSubst' (genSubstOfWeakening w)

instance Weakenable SplittingExpr where
  weaken w = genSubst (genSubstOfWeakening w)

instance ExtendContext' PermExpr where
  extendContext' diff = weaken' (weakeningOfDiff diff)

instance ExtendContext SplittingExpr where
  extendContext diff = weaken (weakeningOfDiff diff)


-- | A substitution is an assignment of permission expressions relative to
-- @ctx1@ to all variables in @ctx2@. Note that substitutions need the 'Size' of
-- the context in order to weaken them.
data PermSubst ctx1 ctx2 =
  PermSubst (Size ctx2) (Assignment (PermExpr ctx2) ctx1)

substVar :: PermSubst ctx1 ctx2 -> PermVar ctx1 a -> PermExpr ctx2 a
substVar (PermSubst _ asgn) (PermVar _ x) = asgn ! x

idSubst :: Size ctx -> PermSubst ctx ctx
idSubst sz = PermSubst sz $ generate sz $ \x -> PExpr_Var $ PermVar sz x

mkSubst1 :: Size ctx -> PermExpr ctx a -> PermSubst (ctx ::> a) ctx
mkSubst1 sz e = PermSubst sz $ extend (generate sz (PExpr_Var . PermVar sz)) e

weakenSubst1 :: PermSubst ctx1 ctx2 -> PermSubst (ctx1 ::> tp) (ctx2 ::> tp)
weakenSubst1 (PermSubst sz2 asgn) =
  PermSubst (incSize sz2) $
  extend (fmapFC (extendContext' oneDiff) asgn) (PExpr_Var $ nextPermVar sz2)

unconsPermSubst :: PermSubst (ctx1 ::> a) ctx2 ->
                   (PermSubst ctx1 ctx2, PermExpr ctx2 a)
unconsPermSubst (PermSubst sz asgn) =
  case viewAssign asgn of
    AssignExtend asgn' e -> (PermSubst sz asgn', e)

genSubstOfSubst :: PermSubst ctx1 ctx2 -> GenSubst ctx1 ctx2
genSubstOfSubst s = GenSubst (substVar s) (genSubstOfSubst $ weakenSubst1 s)

subst :: GenSubstable f => PermSubst ctx1 ctx2 -> f ctx1 -> f ctx2
subst s = genSubst $ genSubstOfSubst s

subst' :: GenSubstable' f => PermSubst ctx1 ctx2 -> f ctx1 a -> f ctx2 a
subst' s = genSubst' $ genSubstOfSubst s

-- | Replace occurrences of a variable with an expression. Note that this is not
-- quite the same as substitution, which removes the variable from the context
-- of the resulting expression.
replaceVar :: PermVar ctx a -> PermExpr ctx a -> PermExpr ctx b ->
              PermExpr ctx b
replaceVar = error "FIXME: replaceVar"


-- | The range type for a partial substitution
data PSElem ctx a =
  PSElem (Maybe (PermExpr ctx a))

-- | A partial substitution is a substitution for some of the variables
data PartialSubst vars ctx =
  PartialSubst (Assignment (PSElem ctx) vars)

instance Weakenable (PartialSubst vars) where
  weaken w (PartialSubst asgn) =
    PartialSubst $
    fmapFC (\m -> case m of
               PSElem (Just e) -> PSElem $ Just $ weaken' w e
               PSElem Nothing -> PSElem Nothing)
    asgn

instance ExtendContext (PartialSubst vars) where
  extendContext diff ps = weaken (weakeningOfDiff diff) ps

-- | Return the empty partial substitution
emptyPartialSubst :: CtxRepr vars -> PartialSubst vars ctx
emptyPartialSubst vars =
  PartialSubst (fmapFC (\tp -> PSElem Nothing) vars)

-- | Add a new variable with no substitution for it yet to a 'PartialSubst'
consPartialSubst :: PartialSubst vars ctx ->
                    PartialSubst (vars ::> tp) ctx
consPartialSubst (PartialSubst asgn) =
  PartialSubst $ extend asgn $ PSElem Nothing

partialSubstGet :: PartialSubst vars ctx -> PermVar vars a -> PSElem ctx a
partialSubstGet (PartialSubst asgn) pv = pvGet asgn pv

partialSubstGetLast :: PartialSubst (vars ::> a) ctx -> PSElem ctx a
partialSubstGetLast (PartialSubst asgn) = asgn ! lastIndex (size asgn)

partialSubstGetForce :: PartialSubst vars ctx -> PermVar vars a ->
                        Maybe (PermExpr ctx a)
partialSubstGetForce (PartialSubst asgn) pv =
  let (PSElem ret) = pvGet asgn pv in ret

partialSubstSet :: PartialSubst vars ctx -> PermVar vars a ->
                   PermExpr ctx a -> PartialSubst vars ctx
partialSubstSet (PartialSubst asgn) x e =
  PartialSubst $ pvModify x (\(PSElem _) -> PSElem $ Just e) asgn

partialSubstSize :: PartialSubst vars ctx -> Size vars
partialSubstSize (PartialSubst asgn) = size asgn

completePartialSubst :: Size ctx -> CtxRepr vars -> PartialSubst vars ctx ->
                        PermSubst (ctx <+> vars) ctx
completePartialSubst sz vars (PartialSubst asgn) =
  PermSubst sz $
  generate sz (PExpr_Var . PermVar sz) <++>
  generate (size asgn) (\x ->
                         case asgn ! x of
                           PSElem (Just e) -> e
                           PSElem Nothing -> zeroOfType $ vars ! x)

-- | Apply a 'PartialSubst' to a variable
partialSubstVar :: PartialSubst vars ctx -> PermVar (ctx <+> vars) a ->
                   PermExpr (ctx <+> vars) a
partialSubstVar (PartialSubst asgn :: PartialSubst vars ctx) pv@(PermVar sz x) =
  let sz_vars = size asgn in
  let sz_ctx = (subtractSizeRight sz (Proxy :: Proxy ctx) sz_vars) in
  case caseIndexAppend sz_ctx sz_vars x of
    Left _ -> PExpr_Var pv
    Right x' ->
      case asgn ! x' of
        PSElem (Just e) -> extendContext' (appendDiff sz_vars) e
        PSElem Nothing -> PExpr_Var pv

genSubstOfPartialSubst :: PartialSubst vars ctx ->
                          GenSubst (ctx <+> vars) (ctx <+> vars)
genSubstOfPartialSubst ps =
  GenSubst (partialSubstVar ps) $
  genSubstOfPartialSubst $ consPartialSubst ps

-- | Apply a partial substitution, which, because the substitution is partial,
-- does not remove the substituted variables
partialSubst :: GenSubstable f => PartialSubst vars ctx ->
                f (ctx <+> vars) -> f (ctx <+> vars)
partialSubst ps = genSubst (genSubstOfPartialSubst ps)

partialSubst' :: GenSubstable' f => PartialSubst vars ctx ->
                 f (ctx <+> vars) a -> f (ctx <+> vars) a
partialSubst' ps = genSubst' (genSubstOfPartialSubst ps)


----------------------------------------------------------------------
-- * Permissions and Permission Sets
----------------------------------------------------------------------

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
  ValPerm_Var :: PermVar ctx (ValuePermType a) -> ValuePerm ctx a

  -- | Says that a natural number is non-zero
  ValPerm_Nat_Neq0 :: ValuePerm ctx NatType

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
    llvmFieldOffset :: Integer,
    llvmFieldSplitting :: SplittingExpr ctx,
    llvmFieldPerm :: ValuePerm ctx (LLVMPointerType w)
  }

data LLVMArrayPerm ctx w =
  LLVMArrayPerm
  {
    llvmArrayOffset :: Integer,
    llvmArrayStride :: Integer,
    llvmArrayLen :: PermExpr ctx (BVType w),
    llvmArrayPtrPerm :: LLVMShapePerm ctx w
  }

-- | Add a static offset to a pointer shape
shapeAddOffset :: Integer -> LLVMShapePerm ctx w -> LLVMShapePerm ctx w
shapeAddOffset off (LLVMFieldShapePerm shape) =
  LLVMFieldShapePerm $ shape { llvmFieldOffset = off + llvmFieldOffset shape}
shapeAddOffset off (LLVMArrayShapePerm shape) =
  LLVMArrayShapePerm $ shape { llvmArrayOffset = off + llvmArrayOffset shape}

-- | Test if a shape is a field with the given offset
isLLVMFieldAt :: Integer -> LLVMShapePerm ctx w -> Bool
isLLVMFieldAt _ (LLVMArrayShapePerm _) = False
isLLVMFieldAt off (LLVMFieldShapePerm fld) = llvmFieldOffset fld == off

splitLLVMFieldAt :: Integer -> SplittingExpr ctx -> [LLVMShapePerm ctx w] ->
                    [LLVMShapePerm ctx w]
splitLLVMFieldAt = error "FIXME: splitLLVMFieldAt"

instance GenSubstable' ValuePerm where
  genSubst' _ ValPerm_True = ValPerm_True
  genSubst' s (ValPerm_Eq e) = ValPerm_Eq $ genSubst' s e
  genSubst' s (ValPerm_Or p1 p2) = ValPerm_Or (genSubst' s p1) (genSubst' s p2)
  genSubst' s (ValPerm_Exists tp p) =
    ValPerm_Exists tp $ genSubst' (weakenGenSubst1 s) p
  genSubst' s (ValPerm_Mu p) = ValPerm_Mu $ genSubst' (weakenGenSubst1 s) p
  genSubst' s (ValPerm_Var x) =
    case genSubstVar s x of
      PExpr_Var x' -> ValPerm_Var x'
  genSubst' _ ValPerm_Nat_Neq0 = ValPerm_Nat_Neq0
  genSubst' s (ValPerm_LLVMPtr w' shapes (Just freelen)) =
    ValPerm_LLVMPtr w' (map (genSubst' s) shapes) (Just $ genSubst' s freelen)
  genSubst' s (ValPerm_LLVMPtr w' shapes Nothing) =
    ValPerm_LLVMPtr w' (map (genSubst' s) shapes) Nothing

instance GenSubstable' LLVMShapePerm where
  genSubst' s (LLVMFieldShapePerm p) = LLVMFieldShapePerm $ genSubst' s p
  genSubst' s (LLVMArrayShapePerm p) = LLVMArrayShapePerm $ genSubst' s p

instance GenSubstable' LLVMFieldPerm where
  genSubst' s (LLVMFieldPerm off spl p) =
    LLVMFieldPerm off (genSubst s spl) (genSubst' s p)

instance GenSubstable' LLVMArrayPerm where
  genSubst' s (LLVMArrayPerm off stride spl p) =
    LLVMArrayPerm off stride (genSubst' s spl) (genSubst' s p)

instance Weakenable' ValuePerm where
  weaken' w = genSubst' (genSubstOfWeakening w)

instance ExtendContext' ValuePerm where
  extendContext' diff = weaken' (weakeningOfDiff diff)


-- | A permission set assigns value permissions to the variables in scope
type PermSet ctx = Assignment (ValuePerm ctx) ctx

extendPermSet :: PermSet ctx -> ValuePerm (ctx ::> a) a -> PermSet (ctx ::> a)
extendPermSet perms p =
  extend (fmapFC (weaken' mkWeakening1) perms) p


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
elimOrLeft :: PermSet ctx -> PermVar ctx a -> PermSet ctx
elimOrLeft perms x = pvModify x elimOrLeftValuePerm perms

-- | Lifts @elimOrRightValuePerm@ to permission sets (@PermSet@), targetting the
-- permission at given index.
elimOrRight :: PermSet ctx -> PermVar ctx a -> PermSet ctx
elimOrRight perms x = pvModify x elimOrRightValuePerm perms

-- | Replace permission @x:(exists z:tp.p)@ in a permission set with @x:p@,
-- lifting all other permissions into the extended context @ctx ::> tp@. It is
-- an error if the permission set assigns a non-existential permission to @x@.
elimExists :: PermSet ctx -> PermVar ctx a -> TypeRepr tp -> PermSet (ctx ::> tp)
elimExists perms x tp =
  case pvGet perms x of
    ValPerm_Exists tp' p ->
      case testEquality tp tp' of
        Just Refl ->
          flip extend ValPerm_True $ pvSet x p $
          fmapFC (extendContext' oneDiff) perms
        Nothing -> error "elimExists"
    _ -> error "elimExists"


-- | A constraint is a Boolean proposition over (the translations to SAW of)
-- expressions that can be tested dynamically on (the translations of) those
-- expressions
data PermConstr ctx where
  Constr_BVEq :: (1 <= w) => NatRepr w ->
                 PermExpr ctx (BVType w) -> PermExpr ctx (BVType w) ->
                 PermConstr ctx
  -- ^ Constraint stating that two bitvector values are equal

instance Weakenable PermConstr where
  weaken w (Constr_BVEq w' e1 e2) =
    Constr_BVEq w' (weaken' w e1) (weaken' w e2)


-- | A permission elimination decomposes a permission set into some number of
-- disjunctive possibilities; e.g., a permission set with a 'ValPerm_Or' could
-- be decomposed into two permission sets, one with each of the left- and
-- right-hand sides of the 'ValPerm_Or'. This creates a tree of disjunctive
-- possibilities. At each leaf of this tree, an elimination contains an @f@,
-- which in theory is indexed by the permission at that leaf; since we are not
-- lifting the permissions to the type level, however, @f@ is actually only
-- indexed by the context.
--
-- FIXME: explain failures as empty disjunctive trees
data PermElim (f :: Ctx CrucibleType -> *) (ctx :: Ctx CrucibleType) where
  Elim_Done :: f ctx -> PermElim f ctx
  -- ^ No more elimination; i.e., implements the rule
  --
  -- -------------------------------
  -- Gin | Pin |- Pin

  Elim_Fail :: PermElim f ctx
  -- ^ The empty tree, with no disjunctive possibilities; i.e., implements the
  -- rule
  --
  -- ------------------------------
  -- Gin | Pin |- Pany

  Elim_Or :: PermVar ctx a -> PermElim f ctx -> PermElim f ctx -> PermElim f ctx
  -- ^ Eliminate a 'ValPerm_Or' on the given variable, replacing it with the
  -- left- and right-hand sides in the two sub-eliminations
  --
  -- pf1 = Gin | Pin, x:p1 |- GsPs1     pf2 = Gin | Pin, x:p2 |- GsPs2
  -- -----------------------------------------------------------------
  -- Gin | Pin, x:(p1 \/ p2) |- GsPs1, GsPs2

  Elim_Exists :: PermVar ctx a -> TypeRepr tp -> PermElim f (ctx ::> tp) ->
                 PermElim f ctx
  -- ^ Eliminate an existential, i.e., a 'ValPerm_Exists', on the given variable
  --
  -- pf = Gin, z:tp | Pin, x:p, z:true |- rets
  -- ------------------------------------------------------
  -- Gin | x:(exists z:tp. p)  |- rets

  Elim_Assert :: PermConstr ctx -> PermElim f ctx -> PermElim f ctx
  -- ^ Assert that the two bitvector expressions are equal; i.e., this tree
  -- contains those disjunctive possibilities in the given tree when the given
  -- expressions are equal
  --
  -- pf = Gin | Pin, C  |- rets
  -- ---------------------------
  -- Gin | Pin |- rets

  Elim_BindField :: PermVar ctx (LLVMPointerType w) ->
                    Integer -> SplittingExpr ctx ->
                    PermElim f (ctx ::> LLVMPointerType w) ->
                    PermElim f ctx
  -- ^ Bind a fresh variable to contain the contents of a field in a pointer
  -- permission. More specifically, replace an 'LLVMFieldShapePerm' containing
  -- an arbitrary permission @p@ with one containing an @'ValPerm_Eq' x@
  -- permission, where @x@ is a fresh variable that is given the permission @p@.
  -- The 'Integer' and 'SplittingExpr' arguments give the static offset and
  -- splitting for the 'LLVMFieldShapePerm' of the given variable to perform
  -- this operation on.
  --
  -- pf = Gin, y:LLVMPtr | Pin, y:p, x:ptr(off |-> (S, eq(y)) * ps) |- rets
  -- ----------------------------------------------------------------------
  -- Gin | Pin, x:ptr(off |-> (S, p) * ps)  |- rets

  Elim_SplitField :: PermVar ctx (LLVMPointerType w) ->
                     Integer -> SplittingExpr ctx ->
                     PermElim f ctx -> PermElim f ctx
  -- ^ Implements the rule
  --
  -- pf = Gin | Pin, x:ptr(off |-> (Spl_L S, eq(e))
  --                       * off |-> (Spl_R S, eq(e)) * shapes) |- rets
  -- ---------------------------------------------------------------------------
  -- Gin | Pin, x:ptr (off |-> (S, p))

  Elim_Copy :: PermElim f ctx -> PermElim f ctx -> PermElim f ctx
  -- ^ Copy the same permissions into two different elimination trees, where an
  -- 'Elim_Fail' in the first tree "calls" the second tree (sort of like a
  -- try-catch block for exceptions)
  --
  -- pf1 = Gin | Pin |- rets1    pf2 = Gin | Pin |- rets2
  -- ----------------------------------------------------
  -- Gin | Pin |- rets1, rets2

  Elim_Unroll :: PermVar ctx a -> PermElim f ctx -> PermElim f ctx
  -- ^ Unroll a recursive 'ValPerm_Mu' permission one time
  --
  -- pf = Gin | Pin, x:F(mu X.F) |- rets
  -- -----------------------------------
  -- Gin | Pin, x:(mu X.F) |- rets


instance Weakenable f => Weakenable (PermElim f) where
  weaken w (Elim_Done f) = Elim_Done (weaken w f)
  weaken _ Elim_Fail = Elim_Fail
  weaken w (Elim_Or x elim1 elim2) =
    Elim_Or (weaken' w x)
    (weaken w elim1) (weaken w elim2)
  weaken w (Elim_Exists x tp elim) =
    Elim_Exists (weaken' w x) tp
    (weaken (weakenWeakening1 w) elim)
  weaken w (Elim_Assert constr elim) =
    Elim_Assert (weaken w constr) (weaken w elim)
  weaken w (Elim_BindField x off spl elim) =
    Elim_BindField (weaken' w x) off (weaken w spl)
    (weaken (weakenWeakening1 w) elim)
  weaken w (Elim_SplitField x off spl elim) =
    Elim_SplitField (weaken' w x) off (weaken w spl) (weaken w elim)
  weaken w (Elim_Copy elim1 elim2) =
    Elim_Copy (weaken w elim1) (weaken w elim2)
  weaken w (Elim_Unroll x elim) =
    Elim_Unroll (weaken' w x) (weaken w elim)

instance Weakenable f => ExtendContext (PermElim f) where
  extendContext diff = weaken (weakeningOfDiff diff)


----------------------------------------------------------------------
-- * Monads over Contextual Types
----------------------------------------------------------------------

-- | A function that can be applied in any extension of @ctx@
type DiffFun f g ctx = (forall ctx'. Diff ctx ctx' -> f ctx' -> g ctx')

-- | Weaken a 'DiffFun'
weakenDiffFun :: DiffFun f g ctx -> DiffFun f g (ctx ::> tp)
weakenDiffFun f = \diff -> f (diff Cat.. oneDiff)

class CtxMonad m where
  creturn :: f ctx -> m f ctx
  cbind :: m f ctx -> DiffFun f (m g) ctx -> m g ctx

instance CtxMonad PermElim where
  creturn = Elim_Done
  cbind (Elim_Done x) f = f noDiff x
  cbind Elim_Fail f = Elim_Fail
  cbind (Elim_Or x elim1 elim2) f =
    Elim_Or x (cbind elim1 f) (cbind elim2 f)
  cbind (Elim_Exists x tp elim) f =
    Elim_Exists x tp $ cbind elim (weakenDiffFun f)
  cbind (Elim_Assert constr elim) f =
    Elim_Assert constr $ cbind elim f
  cbind (Elim_BindField x off spl elim) f =
    Elim_BindField x off spl $ cbind elim (weakenDiffFun f)
  cbind (Elim_Copy elim1 elim2) f =
    Elim_Copy (cbind elim1 f) (cbind elim2 f)
  cbind (Elim_Unroll x elim) f = Elim_Unroll x $ cbind elim f

-- | More traditional bind syntax for 'cbind'
infixl 1 >>>=
(>>>=) :: CtxMonad m => m f ctx -> DiffFun f (m g) ctx -> m g ctx
(>>>=) = cbind

-- | Like @map@ or @fmap@ for permission eliminations
cmap :: CtxMonad m => DiffFun f g ctx -> m f ctx -> m g ctx
cmap f m = cbind m (\diff -> creturn . f diff)

newtype CStateT s m a ctx =
  CStateT { unCStateT :: s ctx -> m (Product s a) ctx }

instance CtxMonad m => CtxMonad (CStateT s m) where
  creturn x = CStateT $ \s -> creturn (Pair s x)
  cbind (CStateT m) f = CStateT $ \s ->
    cbind (m s) $ \diff (Pair s' x) ->
    unCStateT (f diff x) s'

class CtxMonad m => CtxMonadState s m where
  cget :: m s ctx
  cput :: s ctx -> m (Const ()) ctx

instance CtxMonad m => CtxMonadState s (CStateT s m) where
  cget = CStateT $ \s -> creturn (Pair s s)
  cput s = CStateT $ \_ -> creturn (Pair s (Const ()))

-- FIXME: cbind is going to get really annoying; should use CtxMonad.hs!


----------------------------------------------------------------------
-- * Permission Set Introduction Rules
----------------------------------------------------------------------

-- | The permission introduction rules define a judgment of the form
--
-- > Gamma | Pin |- Pout | Prem
--
-- that intuitively proves permission set @Pout@ from @Pin@, with the remainder
-- permission set @Prem@ left over, all of which are relative to context
-- @Gamma@. Note that Pout is an 'ExprPermSetSpec', so it assigns permissions to
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

  Intro_CastEq :: PermVar ctx a -> PermExpr ctx a -> PermIntro ctx ->
                  PermIntro ctx
  -- ^ @Intro_CastEq x e' pf@ implements the following rule, where the notation
  -- @[x |-> e']e@ denotes a call to 'replaceVar':
  --
  -- > pf = Gamma | Pin, x:eq(e') |- ([x |-> e']e):p, Pout | Prem
  -- > --------------------------------------------------
  -- > Gamma | Pin, x:eq(e') |- e:p, Pout | Prem

  Intro_Eq :: PermExpr ctx a -> PermIntro ctx -> PermIntro ctx
  -- ^ @Intro_Eq e pf@ implements the rule
  --
  -- > pf = Gamma | Pin |- Pout | Prem
  -- > --------------------------------------------------
  -- > Gamma | Pin |- e:eq(e), Pout | Prem

  Intro_LLVMPtr ::
    PermVar ctx (LLVMPointerType w) -> PermIntro ctx -> PermIntro ctx
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
    Integer -> SplittingExpr ctx -> ValuePerm ctx (LLVMPointerType w) ->
    PermIntro ctx -> PermIntro ctx
  -- ^ @Intro_LLVMField off S p pf@ implements the rule
  --
  -- > pf = Gamma | Pin, x:ptr(shapes) |- e:p, x:ptr(shapes'), Pout | Prem
  -- > --------------------------------------------------------------------
  -- > Gamma | Pin, x:ptr(off |-> (S,eq(e)) * shapes)
  -- >    |- x:ptr(off |-> (S,p) * shapes'), Pout | Prem


----------------------------------------------------------------------
-- * Proving Permission Implication
----------------------------------------------------------------------

-- | A pair of an expression and a specifiation of a value permission for it,
-- i.e., a pattern over some free variables that must match this permission
data ExprPermSpec vars ctx where
  ExprPermSpec :: PermExpr ctx a -> ValuePerm (ctx <+> vars) a ->
                  ExprPermSpec vars ctx

weakenPermSpecRight1 :: Proxy tp -> Size vars -> ExprPermSpec vars ctx ->
                        ExprPermSpec vars (ctx ::> tp)
weakenPermSpecRight1 (_ :: Proxy tp) sz (ExprPermSpec (e :: PermExpr ctx a) p) =
  ExprPermSpec (extendContext' oneDiff e)
  (weaken' (Weakening (oneDiff :: Diff ctx (ctx ::> tp)) sz) p)

weakenPermSpec1 :: ExprPermSpec vars ctx -> ExprPermSpec (vars ::> tp) ctx
weakenPermSpec1 (ExprPermSpec e p) =
  ExprPermSpec e $ extendContext' oneDiff p

partialSubstSpec :: PartialSubst vars ctx -> ExprPermSpec vars ctx ->
                    ExprPermSpec vars ctx
partialSubstSpec = error "FIXME: partialSubstSpec"

-- | A specification of a set expression permissions
type ExprPermSetSpec vars ctx = [ExprPermSpec vars ctx]

-- | Return value for 'provePermImpl' and friends
data ImplRet vars ctx =
  ImplRet (Size vars) (PermSet ctx) (PermIntro ctx)
  (PermSubst (ctx <+> vars) ctx)


-- | Helper to test if a permission variable is an existential variable
matchPSVar :: PermSet ctx -> PartialSubst vars ctx -> PermVar (ctx <+> vars) a ->
              Either (PermVar ctx a) (PermVar vars a)
matchPSVar perms s x =
  caseVarAppend (size perms) (partialSubstSize s) x

-- | Apply an introduction rule to an 'ImplRet'
applyIntro :: (DiffFun PermIntro PermIntro ctx) ->
              PermElim (ImplRet vars) ctx ->
              PermElim (ImplRet vars) ctx
applyIntro f =
  cmap (\diff (ImplRet vars perms intro s) ->
         ImplRet vars perms (f diff intro) s)

applyIntroWithSubst :: Size ctx ->
                       (forall ctx'. Diff ctx ctx' ->
                        PermSubst (ctx <+> vars) ctx' ->
                        PermIntro ctx' -> PermIntro ctx') ->
                       PermElim (ImplRet vars) ctx ->
                       PermElim (ImplRet vars) ctx
applyIntroWithSubst sz_ctx f =
  cmap (\diff (ImplRet sz_vars perms intro s@(PermSubst _ asgn)) ->
         let asgn' =
               generate sz_ctx (PExpr_Var . extendContext' diff . PermVar sz_ctx)
               <++>
               generate sz_vars (\x -> asgn ! extendIndexLeft (size perms) x) in
         let s' = PermSubst (extSize sz_ctx diff) asgn' in
         ImplRet sz_vars perms (f diff s' intro) s)

-- | FIXME: documentation
--
-- Invariant: the returned 'PartialSubst' has already been applied to the spec
provePermImplH :: PermSet ctx -> CtxRepr vars -> PartialSubst vars ctx ->
                  ExprPermSetSpec vars ctx ->
                  PermElim (ImplRet vars) ctx

provePermImplH perms vars s [] =
  Elim_Done $ ImplRet (partialSubstSize s) perms Intro_Done $
  completePartialSubst (size perms) vars s

provePermImplH perms vars s (ExprPermSpec e ValPerm_True : specs) =
  -- Prove e:true for any e
  applyIntro (\diff -> Intro_True (extendContext' diff e)) $
  provePermImplH perms vars s specs

provePermImplH perms vars s (ExprPermSpec e
                             (ValPerm_Eq
                              (PExpr_Var
                               (matchPSVar perms s -> Right x))) : specs) =
  -- Prove e:eq(var) by setting var=e
  let s' = partialSubstSet s x e in
  applyIntro (\diff -> Intro_Eq (extendContext' diff e)) $
  provePermImplH perms vars s' $ map (partialSubstSpec s') specs

{- FIXME: figure out how to do this simplification!
provePermImplH perms vars s (ExprPermSpec
                             (PExpr_LLVMWord _ e)
                             (ValPerm_Eq
                              (PExpr_LLVMWord _ e'
                               (matchPSVar perms s -> Right x))) : specs) =
  -- Prove (word e):eq(word e') by proving e:eq(e')
  let s' = partialSubstSet s x e in
  applyIntro (\diff -> Intro_Eq (extendContext' diff e)) $
  provePermImplH perms vars s' $ map (partialSubstSpec s') specs
-}

provePermImplH perms vars s (ExprPermSpec (PExpr_Var x)
                             (ValPerm_Eq
                              (PExpr_Var (matchPSVar perms s -> Left y))) : specs)
  | x == y =
    -- Prove x:eq(x)
    applyIntro (\diff -> Intro_Eq (PExpr_Var $ extendContext' diff x)) $
    provePermImplH perms vars s specs

provePermImplH perms vars s (ExprPermSpec e (ValPerm_Or p1 p2) : specs) =
  -- To prove e:(p1 \/ p2) we try both branches with an Elim_Copy
  Elim_Copy
  (applyIntroWithSubst (size perms) (\diff s' -> Intro_OrL (subst' s' p2)) $
   provePermImplH perms vars s (ExprPermSpec e p1 : specs))
  (applyIntroWithSubst (size perms) (\diff s' -> Intro_OrR (subst' s' p1)) $
   provePermImplH perms vars s (ExprPermSpec e p2 : specs))

provePermImplH perms vars s (ExprPermSpec e (ValPerm_Exists tp p) : specs) =
  -- To prove e:(exists z:tp.p) we prove p in vars::>tp and then get the
  -- substitution for z
  cmap
  (\diff (ImplRet sz_vars perms' intro s') ->
    let (s'', z_val) = unconsPermSubst s' in
    let w = Weakening diff sz_vars in
    ImplRet (decSize sz_vars) perms'
    (Intro_Exists tp z_val (subst' (weakenSubst1 s'') $ weaken' w p) intro)
    s'') $
  provePermImplH perms (extend vars tp) (consPartialSubst s)
  (ExprPermSpec e p : map weakenPermSpec1 specs)

-- case for Pin, x:(p1 \/ p2) |- x:(either eq or LLVMPtr), specs
provePermImplH perms vars s specs@(ExprPermSpec (PExpr_Var x) _ : _)
  | ValPerm_Or _ _ <- pvGet perms x
  = Elim_Or x
    (provePermImplH (elimOrLeft perms x) vars s specs)
    (provePermImplH (elimOrRight perms x) vars s specs)

-- Pin, x:tp |- x:(.. same as below ..), specs
-- ---------------------------------------------------------
-- Pin, x:(exists x:tp.p) |- x:(either eq or LLVMPtr), specs
provePermImplH perms vars s specs@(ExprPermSpec (PExpr_Var x) _ : _)
  | ValPerm_Exists tp _ <- pvGet perms x
  = Elim_Exists x tp $
    provePermImplH (elimExists perms x tp) vars
    (extendContext oneDiff s)
    (map (weakenPermSpecRight1 Proxy $ size vars) specs)

-- Pin |- x:ptr(shapes+off), specs
-- --------------------------------
-- Pin |- (x+off):ptr(shapes), specs
provePermImplH perms vars s (ExprPermSpec
                             (PExpr_LLVMOffset w x (PExpr_BV _ [] off))
                             (ValPerm_LLVMPtr _ shapes _)
                             : specs) =
  applyIntro (\_ -> Intro_LLVMPtr_Offset w off) $
  provePermImplH perms vars s (ExprPermSpec (PExpr_Var x)
                               (ValPerm_LLVMPtr w
                                (map (shapeAddOffset off) shapes) Nothing)
                               : specs)

-- Pin, x:ptr(shapes) |- specs
-- ------------------------------------
-- Pin, x:ptr(shapes) |- x:ptr(), specs
provePermImplH perms vars s (ExprPermSpec
                             (PExpr_Var x) (ValPerm_LLVMPtr _ [] _)
                             : specs)
  | ValPerm_LLVMPtr _ _ _ <- pvGet perms x
  = applyIntro (\diff -> Intro_LLVMPtr (extendContext' diff x)) $
    provePermImplH perms vars s specs

-- Pin, x:ptr(shapes) |- e:p, x:ptr(shapes'), specs
-- ------------------------------------------------------
-- Pin, x:ptr(off |-> (All,eq(e)) * shapes)
--      |- x:ptr(off |-> (All,p) * shapes'), specs

{-
provePermImplH perms vars s (ExprPermSpec
                             (PExpr_Var x)
                             (ValPerm_LLVMPtr w
                              (LLVMFieldShapePerm
                               (LLVMFieldPerm off SplExpr_All p) : shapes)
                              free)
                             : specs)
  | ValPerm_LLVMPtr _ shapes_l free_l <- pvGet perms x
  , Just fld@(LLVMFieldShapePerm
              (LLVMFieldPerm _ SplExpr_All (ValPerm_Eq e))) <-
      find (isLLVMFieldAt off) shapes
  = applyIntro (\diff -> Intro_LLVMField off SplExpr_All $
                         extendContext' diff p) $
    provePermImplH perms vars s specs
    (ExprPermSpec (PExpr_Var x) (ValPerm_LLVMPtr w shapes free) : specs)

-- Pin, x:ptr(off |-> (SplExpr_L S,eq(e)) * shapes)
--      |- e:p, x:ptr(shapes'), specs               (setting z=SplExpr_R S)
-- ------------------------------------------------------------------------
-- Pin, x:ptr(off |-> (S,eq(e)) * shapes)
--      |- x:ptr(off |-> (z,p) * shapes'), specs
provePermImplH perms vars s (ExprPermSpec
                             (PExpr_Var x)
                             (ValPerm_LLVMPtr w
                              (LLVMFieldShapePerm
                               (LLVMFieldPerm off SplExpr_All p) : shapes)
                              free)
                             : specs)
  | ValPerm_LLVMPtr _ shapes_l free_l <- pvGet perms x
  , Just fld@(LLVMFieldShapePerm (LLVMFieldPerm _ spl (ValPerm_Eq e))) <-
      find (isLLVMFieldAt off) shapes
  = applyIntroWithSubst (size perms) (\diff s' ->
                                       Intro_LLVMField off SplExpr_All $
                                       subst' s' p) $
    Elim_SplitField x off spl $
    provePermImplH
    (pvSet x (ValPerm_LLVMPtr w (splitLLVMFieldAt
                                 off spl shapes_l) free_l) perms)
    vars s
    (ExprPermSpec (PExpr_Var x) (ValPerm_LLVMPtr w shapes free) : specs)
-}


-- | FIXME: documentation!
provePermImpl :: PermSet ctx -> CtxRepr vars -> ExprPermSetSpec vars ctx ->
                 PermElim (ImplRet vars) ctx
provePermImpl perms vars specs =
  provePermImplH perms vars (emptyPartialSubst vars) specs
