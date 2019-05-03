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
-- * Variables for Use in Permissions
----------------------------------------------------------------------

oneDiff :: Diff ctx (ctx ::> tp)
oneDiff = extendRight noDiff

-- | Our variables need to keep the 'Size' of the context around so that we can
-- apply weakenings
data PermVar ctx a = PermVar (Size ctx) (Index ctx a)

indexOfPermVar :: PermVar ctx a -> Index ctx a
indexOfPermVar (PermVar _ ix) = ix

nextPermVar :: Size ctx -> PermVar (ctx ::> a) a
nextPermVar sz = PermVar (incSize sz) (nextIndex sz)

weakenPermVar1 :: PermVar ctx a -> PermVar (ctx ::> tp) a
weakenPermVar1 (PermVar sz ix) = PermVar (incSize sz) (skipIndex ix)

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

instance Eq (SplittingExpr ctx) where
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


instance Eq (PermExpr ctx a) where
  (PExpr_Var x1) == (PExpr_Var x2) = x1 == x2
  (PExpr_Var _) == _ = False

  (PExpr_BV _ factors1 const1) == (PExpr_BV _ factors2 const2) =
    const1 == const2 && eqFactors factors1 factors2
    where
      eqFactors :: [BVFactor ctx w] -> [BVFactor ctx w] -> Bool
      eqFactors [] [] = True
      eqFactors (f : factors1) factors2
        | elem f factors2 = eqFactors factors1 (delete f factors2)
      eqFactors _ _ = False
  (PExpr_BV _ _ _) == _ = False

  (PExpr_Struct _ args1) == (PExpr_Struct _ args2) = eqArgs args1 args2 where
    eqArgs :: Assignment (PermExpr ctx) args ->
              Assignment (PermExpr ctx) args -> Bool
    eqArgs (viewAssign -> AssignEmpty) _ = True
    eqArgs (viewAssign ->
            AssignExtend args1' e1) (viewAssign -> AssignExtend args2' e2) =
      eqArgs args1' args2' && e1 == e2
  (PExpr_Struct _ _) == _ = False

  (PExpr_LLVMWord _ e1) == (PExpr_LLVMWord _ e2) = e1 == e2
  (PExpr_LLVMWord _ _) == _ = False

  (PExpr_LLVMOffset _ x1 e1) == (PExpr_LLVMOffset _ x2 e2) =
    x1 == x2 && e1 == e2
  (PExpr_LLVMOffset _ _ _) == _ = False

  (PExpr_Spl spl1) == (PExpr_Spl spl2) = spl1 == spl2
  (PExpr_Spl _) == _ = False


instance Eq (BVFactor ctx w) where
  (BVFactor _ i1 x1) == (BVFactor _ i2 x2) = i1 == i2 && x1 == x2


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
-- FIXME: normalize factors with the same variable!
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

-- | Lowering an expression (or other object) means attempting to move it from
-- extended context @ctx1 <+> ctx2@ to context @ctx1@, returning 'Nothing' if it
-- has any free variables from @ctx2@
class Lowerable f where
  lower :: Size ctx1 -> Size ctx2 -> f (ctx1 <+> ctx2) -> Maybe (f ctx1)

class Lowerable' f where
  lower' :: Size ctx1 -> Size ctx2 -> f (ctx1 <+> ctx2) a -> Maybe (f ctx1 a)

instance Lowerable' PermVar where
  lower' sz1 sz2 x =
    case caseVarAppend sz1 sz2 x of
      Left x' -> Just x'
      Right _ -> Nothing

instance Lowerable SplittingExpr where
  lower _ _ SplExpr_All = Just SplExpr_All
  lower sz1 sz2 (SplExpr_L spl) = SplExpr_L <$> lower sz1 sz2 spl
  lower sz1 sz2 (SplExpr_R spl) = SplExpr_R <$> lower sz1 sz2 spl
  lower sz1 sz2 (SplExpr_Star spl1 spl2) =
    SplExpr_Star <$> lower sz1 sz2 spl1 <*> lower sz1 sz2 spl2
  lower sz1 sz2 (SplExpr_Var x) = SplExpr_Var <$> lower' sz1 sz2 x

instance Lowerable' PermExpr where
  lower' sz1 sz2 (PExpr_Var x) =
    PExpr_Var <$> lower' sz1 sz2 x
  lower' sz1 sz2 (PExpr_BV w factors const) =
    PExpr_BV w <$> mapM (lower' sz1 sz2) factors <*> return const
  lower' sz1 sz2 (PExpr_Struct args_ctx args) =
    PExpr_Struct args_ctx <$> traverseFC (lower' sz1 sz2) args
  lower' sz1 sz2 (PExpr_LLVMWord w e) =
    PExpr_LLVMWord w <$> lower' sz1 sz2 e
  lower' sz1 sz2 (PExpr_LLVMOffset w x off) =
    PExpr_LLVMOffset w <$> lower' sz1 sz2 x <*> lower' sz1 sz2 off
  lower' sz1 sz2 (PExpr_Spl spl) = PExpr_Spl <$> lower sz1 sz2 spl

instance Lowerable' BVFactor where
  lower' sz1 sz2 (BVFactor w i x) = BVFactor w i <$> lower' sz1 sz2 x


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

-- FIXME: there should be a way to do this without traversing all of ctx'
weakenWeakening :: Size ctx' -> Weakening ctx1 ctx2 ->
                   Weakening (ctx1 <+> ctx') (ctx2 <+> ctx')
weakenWeakening (viewSize -> ZeroSize) w = w
weakenWeakening (viewSize -> IncSize sz) w =
  weakenWeakening1 (weakenWeakening sz w)

genSubstOfWeakening :: Weakening ctx1 ctx2 -> GenSubst ctx1 ctx2
genSubstOfWeakening w =
  GenSubst (PExpr_Var . weaken' w) (genSubstOfWeakening $ weakenWeakening1 w)

weakeningOfDiff :: Diff ctx1 ctx2 -> Weakening ctx1 ctx2
weakeningOfDiff diff = Weakening diff zeroSize

genSubstOfDiff :: Diff ctx1 ctx2 -> GenSubst ctx1 ctx2
genSubstOfDiff = genSubstOfWeakening . weakeningOfDiff

embeddingOfWeakening :: Size ctx -> Weakening ctx ctx' -> CtxEmbedding ctx ctx'
embeddingOfWeakening sz w =
  CtxEmbedding (weaken w sz)
  (generate sz (indexOfPermVar . weaken' w . PermVar sz))

weakenAssignment :: (forall a. Index ctx' a -> f a) -> Weakening ctx ctx' ->
                    Assignment f ctx -> Assignment f ctx'
weakenAssignment f w@(Weakening (diff :: Diff ctx1 _) sz3) asgn =
  let sz1 :: Size ctx1 = subtractSize (size asgn) Proxy sz3 in
  case diffIsAppend diff of
    IsAppend sz2 ->
      generate sz1 (\ix -> asgn ! extendContext' (appendDiff sz3) ix)
      <++>
      generate sz2 (\ix ->
                     f (extendContext' (appendDiff sz3) $
                        extendIndexLeft sz1 ix))
      <++>
      generate sz3 (\ix -> asgn ! extendIndexLeft sz1 ix)


class Weakenable (f :: Ctx k -> *) where
  weaken :: Weakening ctx1 ctx2 -> f ctx1 -> f ctx2

class Weakenable' (f :: Ctx k -> k' -> *) where
  weaken' :: Weakening ctx1 ctx2 -> f ctx1 a -> f ctx2 a

class WeakenableWithCtx f where
  weakenWithCtx :: CtxRepr ctx2 -> Weakening ctx1 ctx2 -> f ctx1 -> f ctx2

extendWithCtx :: WeakenableWithCtx f => CtxRepr ctx2 -> Diff ctx1 ctx2 ->
                 f ctx1 -> f ctx2
extendWithCtx ctx diff = weakenWithCtx ctx (weakeningOfDiff diff)

instance Weakenable Size where
  weaken (Weakening diff12 sz3) sz =
    addSize (extSize (subtractSize sz Proxy sz3) diff12) sz3

instance Weakenable' PermVar where
  weaken' w@(Weakening diff12 (sz3 :: Size c3)) (PermVar sz13 x) =
    PermVar (weaken w sz13) $
    let sz1 = subtractSize sz13 Proxy sz3 in
    case caseIndexAppend sz1 sz3 x of
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

weakenSubst :: Size ctx' -> PermSubst ctx1 ctx2 ->
               PermSubst (ctx1 <+> ctx') (ctx2 <+> ctx')
weakenSubst sz' (PermSubst sz2 asgn) =
  PermSubst (addSize sz2 sz') $
  fmapFC (extendContext' (appendDiff sz')) asgn <++>
  generate sz' (\ix -> PExpr_Var $
                       PermVar (addSize sz2 sz') (extendIndexLeft sz2 ix))

combineSubsts :: PermSubst ctx1 ctx -> PermSubst ctx2 ctx ->
                 PermSubst (ctx1 <+> ctx2) ctx
combineSubsts (PermSubst sz asgn1) (PermSubst _ asgn2) =
  PermSubst sz (asgn1 <++> asgn2)

substOfDiff :: Size ctx1 -> Diff ctx1 ctx2 -> PermSubst ctx1 ctx2
substOfDiff sz1 diff =
  let sz2 = extSize sz1 diff in
  PermSubst sz2 $ generate sz1 (PExpr_Var . PermVar sz2 . extendContext' diff)

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
                        PermSubst vars ctx
completePartialSubst sz vars (PartialSubst asgn) =
  PermSubst sz $
  generate (size asgn) (\x ->
                         case asgn ! x of
                           PSElem (Just e) -> e
                           PSElem Nothing -> zeroOfType $ vars ! x)

-- | Apply a 'PartialSubst' to a variable
partialSubstVar :: PartialSubst vars ctx -> PermVar (ctx <+> vars) a ->
                   PermExpr (ctx <+> vars) a
partialSubstVar (PartialSubst asgn :: PartialSubst vars ctx) pv@(PermVar sz x) =
  let sz_vars = size asgn in
  let sz_ctx = (subtractSize sz (Proxy :: Proxy ctx) sz_vars) in
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

  -- | A value permission variable, for use in recursive permissions
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

-- | Find the LLVM field at a given offset and remove it from the list of shapes
remLLVMFieldAt :: Integer -> [LLVMShapePerm ctx w] ->
                  Maybe (SplittingExpr ctx, ValuePerm ctx (LLVMPointerType w),
                         [LLVMShapePerm ctx w])
remLLVMFieldAt off [] = Nothing
remLLVMFieldAt off (LLVMFieldShapePerm (LLVMFieldPerm off' spl p) : shapes)
  | off' == off = Just (spl, p, shapes)
remLLVMFieldAt off (shape : shapes) =
  fmap (\(spl, p, shapes') -> (spl, p, shape:shapes')) $
  remLLVMFieldAt off shapes

-- | Find the LLVM field at a given offset and split it, returning the right
-- half of the split permission and keeping the left in the shapes; that is, it
-- replaces
--
-- > x:ptr(off |-> (S, p) * shapes)
--
-- with
--
-- > x:ptr (off |-> (SplExpr_L S, p) * shapes)
--
-- Note that it is an error to call 'splitLLVMFieldAt' when @p@ is not a
-- permission that can be duplicated, which currently is just an equality
-- permission, but we do not check this condition now.
splitLLVMFieldAt :: Integer -> [LLVMShapePerm ctx w] ->
                    Maybe (SplittingExpr ctx, ValuePerm ctx (LLVMPointerType w),
                           [LLVMShapePerm ctx w])
splitLLVMFieldAt off [] = Nothing
splitLLVMFieldAt off (LLVMFieldShapePerm (LLVMFieldPerm off' spl p) : shapes)
  | off' == off
  = Just (SplExpr_R spl, p,
          LLVMFieldShapePerm (LLVMFieldPerm off' (SplExpr_L spl) p) : shapes)
splitLLVMFieldAt off (shape : shapes) =
  fmap (\(spl, p, shapes') -> (spl, p, shape:shapes')) $
  splitLLVMFieldAt off shapes

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

instance ExtendContext' LLVMShapePerm where
  extendContext' diff = genSubst' (genSubstOfDiff diff)

instance ExtendContext' LLVMFieldPerm where
  extendContext' diff = genSubst' (genSubstOfDiff diff)

instance ExtendContext' LLVMArrayPerm where
  extendContext' diff = genSubst' (genSubstOfDiff diff)

instance ExtendContext' ValuePerm where
  extendContext' diff = weaken' (weakeningOfDiff diff)


-- | A permission set assigns value permissions to the variables in scope, and
-- also knows the types of those variables
data PermSet ctx =
  PermSet { permSetCtx :: CtxRepr ctx,
            permSetAsgn :: Assignment (ValuePerm ctx) ctx }

permSetSize :: PermSet ctx -> Size ctx
permSetSize = size . permSetCtx

getPermIx :: PermSet ctx -> Index ctx a -> ValuePerm ctx a
getPermIx perms ix = permSetAsgn perms ! ix

getPerm :: PermSet ctx -> PermVar ctx a -> ValuePerm ctx a
getPerm perms x = getPermIx perms (indexOfPermVar x)

setPerm :: PermVar ctx a -> ValuePerm ctx a -> PermSet ctx -> PermSet ctx
setPerm x p (PermSet ctx asgn) = PermSet ctx $ pvSet x p asgn

modifyPerm :: PermVar ctx a -> (ValuePerm ctx a -> ValuePerm ctx a) ->
              PermSet ctx -> PermSet ctx
modifyPerm x f (PermSet ctx asgn) = PermSet ctx $ pvModify x f asgn

-- | Add a new variable with the given permission to a 'PermSet'
extendPermSet :: PermSet ctx -> TypeRepr a -> ValuePerm (ctx ::> a) a ->
                 PermSet (ctx ::> a)
extendPermSet (PermSet ctx perms) tp p =
  PermSet (extend ctx tp) $
  extend (fmapFC (weaken' mkWeakening1) perms) p

{-
-- | Extend a permission set with true permissions for the new variables
extPermSet :: Diff ctx ctx' -> PermSet ctx -> PermSet ctx'
extPermSet diff perms =
  case diffIsAppend diff of
    IsAppend sz_app ->
      fmapFC (extendContext' diff) perms <++>
      generate sz_app (\_ -> ValPerm_True)
-}

instance WeakenableWithCtx PermSet where
  weakenWithCtx ctx' w perms =
    PermSet ctx' $
    weakenAssignment (\_ -> ValPerm_True) w $ fmapFC (weaken' w) $
    permSetAsgn perms

-- | A permission on a single variable
data VarPerm ctx where
  VarPerm :: PermVar ctx a -> ValuePerm ctx a -> VarPerm ctx

instance Weakenable VarPerm where
  weaken w (VarPerm x p) = VarPerm (weaken' w x) (weaken' w p)

varPermsOfPermSet :: PermSet ctx -> [VarPerm ctx]
varPermsOfPermSet perms =
  toListFC (\(Const p) -> p) $ generate (permSetSize perms) $ \ix ->
  Const $ VarPerm (PermVar (permSetSize perms) ix) (getPermIx perms ix)


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
elimOrLeft perms x = modifyPerm x elimOrLeftValuePerm perms

-- | Lifts @elimOrRightValuePerm@ to permission sets (@PermSet@), targetting the
-- permission at given index.
elimOrRight :: PermSet ctx -> PermVar ctx a -> PermSet ctx
elimOrRight perms x = modifyPerm x elimOrRightValuePerm perms

-- | Replace permission @x:(exists z:tp.p)@ in a permission set with @x:p@,
-- lifting all other permissions into the extended context @ctx ::> tp@. It is
-- an error if the permission set assigns a non-existential permission to @x@.
elimExists :: PermSet ctx -> PermVar ctx a -> TypeRepr tp -> PermSet (ctx ::> tp)
elimExists perms x tp =
  case getPerm perms x of
    ValPerm_Exists tp' p ->
      case testEquality tp tp' of
        Just Refl ->
          setPerm (extendContext' oneDiff x) p $
          extendPermSet perms tp ValPerm_True
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
  -- Gin | Pin, x:ptr (off |-> (S, eq(e))) |- rets

  Elim_Catch :: PermElim f ctx -> PermElim f ctx -> PermElim f ctx
  -- ^ Copy the same permissions into two different elimination trees, where an
  -- 'Elim_Fail' in the first tree "calls" the second tree, just like a
  -- try-catch block for exceptions. This implements the rule:
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
  weaken w (Elim_Catch elim1 elim2) =
    Elim_Catch (weaken w elim1) (weaken w elim2)
  weaken w (Elim_Unroll x elim) =
    Elim_Unroll (weaken' w x) (weaken w elim)

instance Weakenable f => ExtendContext (PermElim f) where
  extendContext diff = weaken (weakeningOfDiff diff)

-- | Eliminate any disjunctions or existentials on a variable, returning the
-- resulting permission set
elimDisjuncts :: PermSet ctx -> PermVar ctx a ->
                 PermElim PermSet ctx
elimDisjuncts perms x = helper perms x (getPerm perms x) where
  helper :: PermSet ctx -> PermVar ctx a -> ValuePerm ctx a ->
            PermElim PermSet ctx
  helper perms x (ValPerm_Or p1 p2) =
    Elim_Or x (helper (elimOrLeft perms x) x p1)
    (helper (elimOrRight perms x) x p2)
  helper perms x (ValPerm_Exists tp p) =
    Elim_Exists x tp $
    helper (extendPermSet perms tp ValPerm_True) (weakenPermVar1 x) p
  helper perms _ _ = Elim_Done perms

-- | Like 'traverse' but for 'PermElim's
traverseElim :: Applicative m =>
                (forall ctx'. Diff ctx ctx' -> f ctx' -> m (g ctx')) ->
                PermElim f ctx -> m (PermElim g ctx)
traverseElim f (Elim_Done x) = Elim_Done <$> f noDiff x
traverseElim f Elim_Fail = pure Elim_Fail
traverseElim f (Elim_Or x elim1 elim2) =
  Elim_Or x <$> traverseElim f elim1 <*> traverseElim f elim2
traverseElim f (Elim_Exists x tp elim) =
  Elim_Exists x tp <$> traverseElim (\diff -> f (diff Cat.. oneDiff)) elim
traverseElim f (Elim_Assert constr elim) =
  Elim_Assert constr <$> traverseElim f elim
traverseElim f (Elim_BindField x off spl elim) =
  Elim_BindField x off spl <$>
  traverseElim (\diff -> f (diff Cat.. oneDiff)) elim
traverseElim f (Elim_Catch elim1 elim2) =
  Elim_Catch <$> traverseElim f elim1 <*> traverseElim f elim2
traverseElim f (Elim_Unroll x elim) = Elim_Unroll x <$> traverseElim f elim


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
  cbind (Elim_Catch elim1 elim2) f =
    Elim_Catch (cbind elim1 f) (cbind elim2 f)
  cbind (Elim_Unroll x elim) f = Elim_Unroll x $ cbind elim f

-- | More traditional bind syntax for 'cbind'
infixl 1 >>>=
(>>>=) :: CtxMonad m => m f ctx -> DiffFun f (m g) ctx -> m g ctx
(>>>=) = cbind

-- | Like @map@ or @fmap@ for permission eliminations
cmap :: CtxMonad m => DiffFun f g ctx -> m f ctx -> m g ctx
cmap f m = cbind m (\diff -> creturn . f diff)

cjoin :: CtxMonad m => m (m f) ctx -> m f ctx
cjoin m = cbind m (\_ -> id)

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
-- * Permission Specifications
----------------------------------------------------------------------

-- | A pair of an expression and a specifiation of a value permission for it,
-- i.e., a pattern over some free variables that must match this permission
data PermSpec vars ctx where
  PermSpec :: Size vars -> PermExpr ctx a -> ValuePerm (ctx <+> vars) a ->
              PermSpec vars ctx

instance Weakenable (PermSpec vars) where
  weaken w (PermSpec sz_vars (e :: PermExpr ctx a) p) =
    PermSpec sz_vars (weaken' w e) (weaken' (weakenWeakening sz_vars w) p)

instance ExtendContext (PermSpec vars) where
  extendContext diff (PermSpec sz_vars (e :: PermExpr ctx a) p) =
    PermSpec sz_vars (extendContext' diff e) (weaken' (Weakening diff sz_vars) p)

extPermSpecVars :: PermSpec vars ctx -> PermSpec (vars ::> tp) ctx
extPermSpecVars (PermSpec sz_vars e p) =
  PermSpec (incSize sz_vars) e $ extendContext' oneDiff p

substPermSpec :: PermSubst args ctx -> PermSpec vars args -> PermSpec vars ctx
substPermSpec s (PermSpec sz_vars e p) =
  PermSpec sz_vars (subst' s e) (subst' (weakenSubst sz_vars s) p)

-- | Instantiate the existential variables in a 'PermSpec'
instPermSpecVars :: PermSubst vars ctx -> PermSpec vars ctx ->
                    PermSpec EmptyCtx ctx
instPermSpecVars s@(PermSubst sz_ctx _) (PermSpec _ e p) =
  PermSpec zeroSize e $
  subst' (combineSubsts (idSubst sz_ctx) s) p

-- | A specification of a set expression permissions
type PermSetSpec vars ctx = [PermSpec vars ctx]

permSpecOfPerms :: Size vars -> Assignment (ValuePerm (ctx <+> vars)) ctx ->
                   PermSetSpec vars ctx
permSpecOfPerms sz_vars asgn =
  let sz_ctx = size asgn in
  toListFC (\(Const spec) -> spec) $
  generate sz_ctx $ \ix ->
  Const $ PermSpec sz_vars (PExpr_Var $ PermVar sz_ctx ix) (asgn ! ix)


----------------------------------------------------------------------
-- * Permission Set Introduction Rules
----------------------------------------------------------------------

-- | A proof that two expressions are equal, assuming any constraints in an
-- input permission set; i.e., a judgment of the form
--
-- > Gamma | Pin |- e1 = e2
data EqProof ctx a where
  EqProof_Refl :: PermExpr ctx a -> EqProof ctx a
  -- ^ A proof that any expression equals itself

  EqProof_CastEq :: PermVar ctx a -> PermExpr ctx a -> EqProof ctx a ->
                    EqProof ctx a
  -- ^ @EqProof_CastEq x e1 pf@ implements the following rule:
  --
  -- > pf = Gamma | Pin, x:eq(e1) |- e1 = e2
  -- > --------------------------------------------------
  -- > Gamma | Pin, x:eq(e1) |- x = e2

  EqProof_LLVMWord :: (1 <= w) => NatRepr w -> EqProof ctx (BVType w) ->
                      EqProof ctx (LLVMPointerType w)
  -- ^ The proof rule
  --
  -- Gamma | Pin |- e1 = e2
  -- -------------------------
  -- Gamma | Pin |- LLVMWord e1 = LLVMWord e2

instance Weakenable' EqProof where
  weaken' w (EqProof_Refl e) = EqProof_Refl $ weaken' w e
  weaken' w (EqProof_CastEq x e pf) =
    EqProof_CastEq (weaken' w x) (weaken' w e) (weaken' w pf)
  weaken' w (EqProof_LLVMWord w' pf) = EqProof_LLVMWord w' $ weaken' w pf

instance ExtendContext' EqProof where
  extendContext' diff = weaken' (weakeningOfDiff diff)

-- | Extract @e1@ from a proof that @e1 = e2@
eqProofLHS :: EqProof ctx a -> PermExpr ctx a
eqProofLHS (EqProof_Refl e) = e
eqProofLHS (EqProof_CastEq x _ _) = PExpr_Var x
eqProofLHS (EqProof_LLVMWord w pf) = PExpr_LLVMWord w $ eqProofLHS pf

-- | Extract @e2@ from a proof that @e1 = e2@
eqProofRHS :: EqProof ctx a -> PermExpr ctx a
eqProofRHS (EqProof_Refl e) = e
eqProofRHS (EqProof_CastEq _ _ pf) = eqProofRHS pf
eqProofRHS (EqProof_LLVMWord w pf) = PExpr_LLVMWord w $ eqProofRHS pf


-- | The permission introduction rules define a judgment of the form
--
-- > Gamma | Pin |- Pout
--
-- that intuitively proves permission set @Pout@ from @Pin@, both of which are
-- relative to context @Gamma@. Note that Pout is an 'PermSetSpec', so it
-- assigns permissions to expressions and not just variables, and is also a list
-- that can have multiple copies of the same variable or be empty. All of the
-- rules are introduction rules, meaning they build up a proof of @Pout@ from
-- smaller permissions. Also, most of the rules have the convention that they
-- operate on the first permission in the 'ExprPermSet'.
data PermIntro (ctx :: Ctx CrucibleType) where
  Intro_Id :: [VarPerm ctx] -> PermIntro ctx
  -- ^ The final step of any introduction proof, of the following form, where
  -- each @x@ can occur at most once:
  --
  -- >  ---------------------------------------------------
  -- >  Gamma | x1:p1, ..., xn:pn, Pin |- x1:p1, ..., xn:pn

  Intro_Exists :: TypeRepr tp -> PermExpr ctx tp -> ValuePerm (ctx ::> tp) a ->
                  PermIntro ctx -> PermIntro ctx
  -- ^ @Intro_Exists tp e' p pf@ is the existential introduction rule
  --
  -- > pf = Gamma | Pin |- e:[e'/z]p, Pout
  -- > --------------------------------------
  -- > Gamma | Pin |- e:(exists z:tp.p), Pout

  Intro_OrL :: ValuePerm ctx a -> PermIntro ctx -> PermIntro ctx
  -- ^ @Intro_OrL p2 pf@ is the left disjunction introduction rule
  --
  -- > pf = Gamma | Pin |- e:p1, Pout
  -- > ---------------------------------
  -- > Gamma | Pin |- e:(p1 \/ p2), Pout

  Intro_OrR :: ValuePerm ctx a -> PermIntro ctx -> PermIntro ctx
  -- ^ @Intro_OrR p1 pf@ is the right disjunction introduction rule
  --
  -- > pf = Gamma | Pin |- e:p2, Pout
  -- > ---------------------------------
  -- > Gamma | Pin |- e:(p1 \/ p2), Pout

  Intro_True :: PermExpr ctx a -> PermIntro ctx -> PermIntro ctx
  -- ^ Implements the rule
  --
  -- > Gamma | Pin |- Pout
  -- > ---------------------------
  -- > Gamma | Pin |- e:true, Pout

  Intro_CastEq :: PermVar ctx a -> PermExpr ctx a -> PermIntro ctx ->
                  PermIntro ctx
  -- ^ @Intro_CastEq x e' pf@ implements the following rule:
  --
  -- > pf = Gamma | Pin, x:eq(e) |- e:p, Pout
  -- > --------------------------------------
  -- > Gamma | Pin, x:eq(e) |- x:p, Pout

  Intro_Eq :: EqProof ctx a -> PermIntro ctx -> PermIntro ctx
  -- ^ @Intro_Eq eq_pf pf@ for @eq_pf :: e1 = e2@ implements the rule
  --
  -- > pf = Gamma | Pin |- Pout
  -- > ------------------------------
  -- > Gamma | Pin |- e1:eq(e2), Pout

  Intro_LLVMPtr ::
    PermVar ctx (LLVMPointerType w) -> PermIntro ctx -> PermIntro ctx
  -- ^ @Intro_LLVMPtr x pf@ implements the rule
  --
  -- > pf = Gamma | Pin, x:ptr(shapes) |- Pout
  -- > -------------------------------------------
  -- > Gamma | Pin, x:ptr(shapes) |- x:ptr(), Pout
  --
  -- FIXME: this needs to handle the free length!

  Intro_LLVMPtr_Offset ::
    (1 <= w) => NatRepr w -> Integer -> PermIntro ctx -> PermIntro ctx
  -- ^ @Intro_LLVMPtr_Offset w off pf@ for a static offset @off@ implements
  --
  -- > pf = Gamma | Pin |- x:ptr (shapes + off), Pout
  -- > ----------------------------------------------
  -- > Gamma | Pin |- (x+off):ptr(shapes), Pout

  Intro_LLVMField ::
    Integer -> SplittingExpr ctx -> ValuePerm ctx (LLVMPointerType w) ->
    PermIntro ctx -> PermIntro ctx
  -- ^ @Intro_LLVMField off S p pf@ implements the rule
  --
  -- > pf = Gamma | Pin, x:ptr(shapes) |- e:p, x:ptr(shapes'), Pout
  -- > ------------------------------------------------------------
  -- > Gamma | Pin, x:ptr(off |-> (S,eq(e)) * shapes)
  -- >    |- x:ptr(off |-> (S,p) * shapes'), Pout


instance Weakenable PermIntro where
  weaken w (Intro_Id perms) =
    Intro_Id $ map (weaken w) perms
  weaken w (Intro_Exists tp e p intro) =
    Intro_Exists tp (weaken' w e) (weaken' (weakenWeakening1 w) p)
    (weaken w intro)
  weaken w (Intro_OrL p2 intro) = Intro_OrL (weaken' w p2) (weaken w intro)
  weaken w (Intro_OrR p1 intro) = Intro_OrR (weaken' w p1) (weaken w intro)
  weaken w (Intro_True e intro) = Intro_True (weaken' w e) (weaken w intro)
  weaken w (Intro_CastEq x e intro) =
    Intro_CastEq (weaken' w x) (weaken' w e) (weaken w intro)
  weaken w (Intro_Eq eq_pf intro) =
    Intro_Eq (weaken' w eq_pf) (weaken w intro)
  weaken w (Intro_LLVMPtr x intro) =
    Intro_LLVMPtr (weaken' w x) (weaken w intro)
  weaken w (Intro_LLVMPtr_Offset w' off intro) =
    Intro_LLVMPtr_Offset w' off (weaken w intro)
  weaken w (Intro_LLVMField off spl p intro) =
    Intro_LLVMField off (weaken w spl) (weaken' w p) (weaken w intro)

instance ExtendContext PermIntro where
  extendContext diff = weaken (Weakening diff zeroSize)

-- | An introduction rule annotated with the input permission set and output
-- permission specs
data AnnotIntro ctx =
  AnnotIntro { introInPerms :: PermSet ctx,
               introOutPerms :: PermSetSpec EmptyCtx ctx,
               introProof :: PermIntro ctx }

instance WeakenableWithCtx AnnotIntro where
  weakenWithCtx ctx w (AnnotIntro perms perms' pf) =
    AnnotIntro (weakenWithCtx ctx w perms) (map (weaken w) perms') (weaken w pf)

{-
instance Weakenable AnnotIntro where
  weaken w (AnnotIntro perms_in perms_out intro) =
    AnnotIntro (weakenPermSet w perms_in)
    (map (weaken w) perms_out) (weaken w intro)

instance ExtendContext AnnotIntro where
  extendContext diff = weaken (Weakening diff zeroSize)
-}


----------------------------------------------------------------------
-- * Proving Equality of Permission Expressions
----------------------------------------------------------------------

-- | Test if a variable in an 'PermSpec' is an existential variable
matchSpecEVar :: PermSet ctx -> PartialSubst vars ctx ->
                 PermVar (ctx <+> vars) a -> Maybe (PermVar vars a)
matchSpecEVar perms s x =
  case caseVarAppend (permSetSize perms) (partialSubstSize s) x of
    Left _ -> Nothing
    Right z -> Just z

-- | Test if an expression in an 'PermSpec' is constant, i.e., has no
-- existential variables
matchSpecConst :: PermSet ctx -> PartialSubst vars ctx ->
                  PermExpr (ctx <+> vars) a -> Maybe (PermExpr ctx a)
matchSpecConst perms s = lower' (permSetSize perms) (partialSubstSize s)

-- | Return type for 'proveEq'
data EqRet vars a ctx =
  EqRet (PermSet ctx) (PartialSubst vars ctx) (EqProof ctx a)

-- | Apply an 'EqProof' rule to an 'EqRet'
applyEqProof :: (forall ctx'. Diff ctx ctx' ->
                 EqProof ctx' a -> EqProof ctx' b) ->
                PermElim (EqRet vars a) ctx ->
                PermElim (EqRet vars b) ctx
applyEqProof f =
  cmap (\diff (EqRet perms s eq_pf) -> EqRet perms s (f diff eq_pf))

-- | Build a proof that two expressions are equal, where the right-hand one can
-- have free variables listed in @vars@
proveEq :: PermSet ctx -> CtxRepr vars -> PartialSubst vars ctx ->
           PermExpr ctx a -> PermExpr (ctx <+> vars) a ->
           PermElim (EqRet vars a) ctx
proveEq perms vars s e1 e2 =
  proveEqH perms vars s e1 $ partialSubst' s e2

-- | Helper for 'proveEq' that assumes the given partial substitution has
-- already been applied
proveEqH :: PermSet ctx -> CtxRepr vars -> PartialSubst vars ctx ->
            PermExpr ctx a -> PermExpr (ctx <+> vars) a ->
            PermElim (EqRet vars a) ctx

-- Prove e=z by setting z=e
proveEqH perms vars s e (PExpr_Var (matchSpecEVar perms s -> Just x)) =
  Elim_Done $ EqRet perms (partialSubstSet s x e) (EqProof_Refl e)

-- Prove LLVMWord w1=LLVMWord w2 by proving w1 = w2
proveEqH perms vars s (PExpr_LLVMWord w e1) (PExpr_LLVMWord _ e2) =
  applyEqProof (\_ -> EqProof_LLVMWord w) $
  proveEqH perms vars s e1 e2

-- Prove e=e by reflexivity
proveEqH perms _vars s e1 (matchSpecConst perms s -> Just e2)
  | e1 == e2 =
    Elim_Done $ EqRet perms s $ EqProof_Refl e1

-- Prove x=e2 when x:eq(e1) is in the context by proving e1=e2
proveEqH perms vars s (PExpr_Var x) e2
  | ValPerm_Eq e1 <- getPerm perms x
  = applyEqProof (\diff -> EqProof_CastEq (extendContext' diff x)
                           (extendContext' diff e1)) $
    proveEq perms vars s e1 e2

-- Prove x=e2 when x:(p1 \/ p2) is in perms by eliminating the disjunct
proveEqH perms vars s (PExpr_Var x) e2
  | ValPerm_Or _ _ <- getPerm perms x
  = elimDisjuncts perms x >>>= \diff perms' ->
    proveEqH perms' vars (extendContext diff s)
    (PExpr_Var $ extendContext' diff x)
    (weaken' (Weakening diff (size vars)) e2)

-- Prove x=e2 when x:exists z.p is in perms by eliminating the existential
proveEqH perms vars s (PExpr_Var x) e2
  | ValPerm_Exists _ _ <- getPerm perms x
  = elimDisjuncts perms x >>>= \diff perms' ->
    proveEqH perms' vars (extendContext diff s)
    (PExpr_Var $ extendContext' diff x)
    (weaken' (Weakening diff (size vars)) e2)

-- FIXME: need more rules!
proveEqH _perms _vars _s _e1 _e2 =
  Elim_Fail


----------------------------------------------------------------------
-- * Proving Permission Implication
----------------------------------------------------------------------

-- FIXME: double-check that we have applied our PartialSubst everywhere we need
-- to before pattern-matching in provePermImplH

-- | Helper type for building an 'ImplRet', but without annotations on the
-- returned introduction proof; used by 'provePermImplH'
data ImplHRet vars ctx =
  ImplHRet (PermSet ctx) (PermSubst vars ctx) (PermIntro ctx)

-- | Apply an introduction rule to an 'ImplRet'
applyIntro :: (DiffFun PermIntro PermIntro ctx) ->
              PermElim (ImplHRet vars) ctx ->
              PermElim (ImplHRet vars) ctx
applyIntro f =
  cmap (\diff (ImplHRet perms s intro) ->
         ImplHRet perms s (f diff intro))

-- | Apply an introduction rule to an 'ImplHRet', also passing a helpful
-- substitution for expressions in the original 'PermSpec'
applyIntroWithSubst :: Size ctx ->
                       (forall ctx'. Diff ctx ctx' ->
                        PermSubst (ctx <+> vars) ctx' ->
                        PermIntro ctx' -> PermIntro ctx') ->
                       PermElim (ImplHRet vars) ctx ->
                       PermElim (ImplHRet vars) ctx
applyIntroWithSubst sz_ctx f =
  cmap (\diff (ImplHRet permsRem s intro) ->
         let s' = combineSubsts (substOfDiff sz_ctx diff) s in
         ImplHRet permsRem s (f diff s' intro))

-- | FIXME: documentation
--
-- Invariant: the returned 'PartialSubst' has already been applied to the spec
provePermImplH :: PermSet ctx -> CtxRepr vars -> PartialSubst vars ctx ->
                  PermSetSpec vars ctx ->
                  PermElim (ImplHRet vars) ctx

provePermImplH perms vars s [] =
  Elim_Done $ ImplHRet perms (completePartialSubst (permSetSize perms) vars s) $
  Intro_Id $ varPermsOfPermSet perms

provePermImplH perms vars s (PermSpec _ e ValPerm_True : specs) =
  -- Prove e:true for any e
  applyIntro (\diff -> Intro_True (extendContext' diff e)) $
  provePermImplH perms vars s specs

provePermImplH perms vars s (PermSpec _ e1 (ValPerm_Eq e2) : specs) =
  -- Prove e:eq(var) by setting var=e
  proveEq perms vars s e1 e2 >>>= \diff (EqRet perms' s' eq_pf) ->
  applyIntro (\diff' -> Intro_Eq (extendContext' diff' eq_pf)) $
  provePermImplH perms' vars s' $
  map (extendContext diff) specs

provePermImplH perms vars s (PermSpec sz_vars e (ValPerm_Or p1 p2) : specs) =
  -- To prove e:(p1 \/ p2) we try both branches with an Elim_Catch
  Elim_Catch
  (applyIntroWithSubst (permSetSize perms) (\diff s' -> Intro_OrL (subst' s' p2)) $
   provePermImplH perms vars s (PermSpec sz_vars e p1 : specs))
  (applyIntroWithSubst (permSetSize perms) (\diff s' -> Intro_OrR (subst' s' p1)) $
   provePermImplH perms vars s (PermSpec sz_vars e p2 : specs))

provePermImplH perms vars s (PermSpec sz_vars e (ValPerm_Exists tp p) : specs) =
  -- To prove e:(exists z:tp.p) we prove p in vars::>tp and then get the
  -- substitution for z
  cmap
  (\diff (ImplHRet perms' s' intro) ->
    let (s'', z_val) = unconsPermSubst s' in
    let s_p =
          combineSubsts (substOfDiff (permSetSize perms) (extendRight diff))
          (weakenSubst1 s'') in
    let p' = subst' s_p p in
    ImplHRet perms' s'' (Intro_Exists tp z_val p' intro)) $
  provePermImplH perms (extend vars tp) (consPartialSubst s)
  (PermSpec (incSize sz_vars) e p : map extPermSpecVars specs)

-- case for Pin, x:(p1 \/ p2) |- x:(either eq or LLVMPtr), specs
provePermImplH perms vars s specs@(PermSpec _ (PExpr_Var x) _ : _)
  | ValPerm_Or _ _ <- getPerm perms x
  = Elim_Or x
    (provePermImplH (elimOrLeft perms x) vars s specs)
    (provePermImplH (elimOrRight perms x) vars s specs)

-- Pin, x:tp |- x:(.. same as below ..), specs
-- ---------------------------------------------------------
-- Pin, x:(exists x:tp.p) |- x:(either eq or LLVMPtr), specs
provePermImplH perms vars s specs@(PermSpec _ (PExpr_Var x) _ : _)
  | ValPerm_Exists tp _ <- getPerm perms x
  = Elim_Exists x tp $
    provePermImplH (elimExists perms x tp) vars
    (extendContext oneDiff s)
    (map (extendContext oneDiff) specs)

-- Pin |- x:ptr(shapes+off), specs
-- --------------------------------
-- Pin |- (x+off):ptr(shapes), specs
provePermImplH perms vars s (PermSpec sz_vars
                             (PExpr_LLVMOffset w x (PExpr_BV _ [] off))
                             (ValPerm_LLVMPtr _ shapes _)
                             : specs) =
  applyIntro (\_ -> Intro_LLVMPtr_Offset w off) $
  provePermImplH perms vars s (PermSpec sz_vars (PExpr_Var x)
                               (ValPerm_LLVMPtr w
                                (map (shapeAddOffset off) shapes) Nothing)
                               : specs)

-- Pin, x:ptr(shapes) |- specs
-- ------------------------------------
-- Pin, x:ptr(shapes) |- x:ptr(), specs
provePermImplH perms vars s (PermSpec _
                             (PExpr_Var x) (ValPerm_LLVMPtr w [] free)
                             : specs)
  | ValPerm_LLVMPtr _ _ free_l <- getPerm perms x
  = (case (free_l, free) of
        (_, Nothing) -> id
        (Just freelen_l, Just freelen) ->
          error "provePermImplH: cannot yet prove free perms"
          -- FIXME: need to match the free vars of freelen to freelen_l;
          -- maybe add a function
          -- proveEq :: PermExpr ctx a -> PermExpr (ctx <+> vars) a ->
          --            Elim (Product (PartialSubst vars) (PermExprFlip a))
          -- that adds the necessary elims and returns the new partial subst and
          -- the result of substituting into the right-hand expr
          --
          --Elim_Assert $ Constr_BVEq w freelen_l freelen
    ) $
    applyIntro (\diff -> Intro_LLVMPtr (extendContext' diff x)) $
    provePermImplH perms vars s specs

-- Pin, x:ptr(shapes) |- e:p, x:ptr(shapes'), specs
-- ------------------------------------------------------
-- Pin, x:ptr(off |-> (All,eq(e)) * shapes)
--      |- x:ptr(off |-> (All,p) * shapes'), specs
provePermImplH perms vars s (PermSpec sz_vars
                             (PExpr_Var x)
                             (ValPerm_LLVMPtr w
                              (LLVMFieldShapePerm
                               (LLVMFieldPerm off SplExpr_All p) : shapes)
                              free)
                             : specs)
  | ValPerm_LLVMPtr _ shapes_l free_l <- getPerm perms x
  , Just (SplExpr_All, ValPerm_Eq e, shapes_l') <- remLLVMFieldAt off shapes_l
  = applyIntroWithSubst (permSetSize perms) (\diff s' ->
                                              Intro_LLVMField off SplExpr_All $
                                              subst' s' p) $
    provePermImplH
    (setPerm x (ValPerm_LLVMPtr w shapes_l' free_l) perms)
    vars s
    (PermSpec sz_vars e p :
     PermSpec sz_vars (PExpr_Var x) (ValPerm_LLVMPtr w shapes free) : specs)

-- Pin, x:ptr(off |-> (SplExpr_L S,eq(e)) * shapes)
--      |- e:p, x:ptr(shapes'), specs               (setting z=SplExpr_R S)
-- ------------------------------------------------------------------------
-- Pin, x:ptr(off |-> (S,eq(e)) * shapes)
--      |- x:ptr(off |-> (z,p) * shapes'), specs
provePermImplH perms vars s (PermSpec sz_vars
                             (PExpr_Var x)
                             (ValPerm_LLVMPtr w
                              (LLVMFieldShapePerm
                               (LLVMFieldPerm off
                                (SplExpr_Var
                                 (matchSpecEVar perms s -> Just z)) p) : shapes)
                              free)
                             : specs)
  | ValPerm_LLVMPtr _ shapes_l free_l <- getPerm perms x
  , Just (spl, ValPerm_Eq e, shapes_l') <- splitLLVMFieldAt off shapes_l
  = applyIntroWithSubst (permSetSize perms) (\diff s' ->
                                              Intro_LLVMField off
                                              (extendContext diff spl)
                                              (subst' s' p)) $
    Elim_SplitField x off spl $
    provePermImplH
    (setPerm x (ValPerm_LLVMPtr w shapes_l' free_l) perms)
    vars
    (partialSubstSet s z (PExpr_Spl spl))
    (PermSpec sz_vars e p :
     PermSpec sz_vars (PExpr_Var x) (ValPerm_LLVMPtr w shapes free) : specs)

-- Pin, x:ptr(off |-> (S_l,eq(y)) * shapes), y:p_l
--      |- x:ptr(off |-> (S,p) * shapes'), specs
-- ------------------------------------------------------------------------
-- Pin, x:ptr(off |-> (S_l,p_l) * shapes)
--      |- x:ptr(off |-> (S,p) * shapes'), specs
provePermImplH perms vars s specs@(PermSpec _
                                   (PExpr_Var x)
                                   (ValPerm_LLVMPtr w
                                    (LLVMFieldShapePerm
                                     (LLVMFieldPerm off _ _) : _) _) : _)
  | ValPerm_LLVMPtr _ shapes_l free_l <- getPerm perms x
  , Just (spl, p, shapes_l') <- remLLVMFieldAt off shapes_l
  = Elim_BindField x off spl $
    provePermImplH
    (extendPermSet (setPerm x (ValPerm_LLVMPtr w shapes_l' free_l) perms)
     (LLVMPointerRepr w)
     (weaken' mkWeakening1 p))
    vars
    (extendContext oneDiff s)
    (map (extendContext oneDiff) specs)

provePermImplH _perms _vars _s _specs =
  Elim_Fail


-- | Return value for 'provePermImpl'
data ImplRet vars ctx =
  ImplRet { implPermsRem :: PermSet ctx,
            -- ^ The permissions that remain after proving the implication;
            -- i.e., if we asked for a proof of @Pin |- Pout@ we actually got a
            -- proof of @Pin |- Pout * Prem@

            implSubst :: PermSubst vars ctx,
            -- ^ The values of the existential variables that were in @Pout@

            implIntro :: AnnotIntro ctx
            -- ^ The introduction proof itself
          }

-- | FIXME: documentation!
provePermImpl :: PermSet ctx -> CtxRepr vars -> PermSetSpec vars ctx ->
                 PermElim (ImplRet vars) ctx
provePermImpl perms vars specs =
  cmap (\diff (ImplHRet permsRem s intro) ->
         ImplRet permsRem s $
         AnnotIntro (extendWithCtx (permSetCtx permsRem) diff perms)
         (map (instPermSpecVars s . extendContext diff) specs)
         intro) $
  provePermImplH perms vars (emptyPartialSubst vars) specs
