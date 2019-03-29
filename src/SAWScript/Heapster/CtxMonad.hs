{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ViewPatterns #-}

module SAWScript.Heapster.CtxMonad where

import           Control.Monad.Except
import qualified Control.Category as Cat
import           Data.Type.Equality
import           Data.Kind
import           Data.Proxy
import           Data.Reflection

import           Data.Parameterized.Ctx
import           Data.Parameterized.Context


----------------------------------------------------------------------
-- * The standard backtracking monad
----------------------------------------------------------------------

-- | Backtracking search monad
newtype BackM err a =
  BackM { unBackM :: forall r. (a -> (err -> r) -> r) -> (err -> r) -> r }

instance Functor (BackM err) where
  fmap f m = m >>= return . f

instance Applicative (BackM err) where
  pure = return
  (<*>) = ap

instance Monad (BackM err) where
  return a = BackM $ \ks kf -> ks a kf
  m >>= f = BackM $ \ks kf -> unBackM m (\a kf' -> unBackM (f a) ks kf') kf

instance MonadError err (BackM err) where
  throwError err = BackM $ \_ kf -> kf err
  catchError m f = BackM $ \ks kf -> unBackM m ks (\err -> unBackM (f err) ks kf)


----------------------------------------------------------------------
-- * Contextual types: types that are relative to a type context
----------------------------------------------------------------------

-- | A context-dependent type is a type that depends on a context
type CType k = Ctx k -> *

-- | A valid contextual type is one that can be mapped via context extensions
class ValidCType a where
  mapContext :: Diff ctx ctx' -> a ctx -> a ctx'

-- | A valid unary contextual type function is one that maps valid contextual
-- types to valid contextual types
class ValidCType1 (f :: CType k -> CType k) where
  mapContext1 :: ValidCType a => Diff ctx ctx' -> f a ctx -> f a ctx'

instance {-# INCOHERENT #-} (ValidCType1 f, ValidCType a) => ValidCType (f a) where
  mapContext = mapContext1

-- | A valid binary contextual type function is one that maps pairs of valid
-- contextual types to a valid contextual types
class ValidCType2 (f :: CType k -> CType k -> CType k) where
  mapContext2 :: (ValidCType a, ValidCType b) =>
                 Diff ctx ctx' -> f a b ctx -> f a b ctx'

instance {-# INCOHERENT #-} (ValidCType2 f, ValidCType a) => ValidCType1 (f a) where
  mapContext1 = mapContext2

-- | Apply a type function to a contextual type
infixl 2 :@:
newtype (:@:) (f :: * -> *) (b :: CType k) ctx =
  CApplyF { unCApplyF :: f (b ctx) }

instance Functor f => ValidCType1 ((:@:) f) where
  mapContext1 diff = CApplyF . fmap (mapContext diff) . unCApplyF

-- | The pair type-in-context
infixr 1 :*:
data (:*:) a b (ctx :: Ctx k) = CPair (a ctx) (b ctx)

instance ValidCType2 (:*:) where
  mapContext2 diff (CPair a b) =
    CPair (mapContext diff a) (mapContext diff b)

-- | The unit type-in-context
data CUnit (ctx :: Ctx k) = CUnit

instance ValidCType CUnit where
  mapContext _ _ = CUnit

-- | Lift a standard type to a contextual type that ignores its context
newtype CConst a (ctx :: Ctx k) = CConst { unCConst :: a }

instance ValidCType (CConst a) where
  mapContext _ (CConst a) = CConst a

-- | The function type-in-context, that can be applied in any extension of the
-- current context
infixr 0 :->:
newtype (:->:) a b (ctx :: Ctx k) =
  CFun { unCFun :: forall ctx'. Diff ctx ctx' -> a ctx' -> b ctx' }

instance ValidCType2 (:->:) where
  mapContext2 diff (CFun f) = CFun $ \diff' -> f (diff' Cat.. diff)

-- | The contextual type for a variable in the context
newtype CVar (tp :: k) (ctx :: Ctx k) = CVar { unCVar :: Index ctx tp }

instance ValidCType (CVar tp) where
  mapContext diff (CVar i) = CVar $ extendIndex' diff i

instance ValidCType Size where
  mapContext diff sz = extSize sz diff

-- | Represents a contextual type inside a binding for another variable
newtype CBind (tp :: k) (a :: CType k) (ctx :: Ctx k) =
  CBind { unCBind :: forall ctx'.
                     Diff ctx ctx' -> Size ctx' -> a (ctx' ::> tp) }

instance ValidCType1 (CBind tp) where
  mapContext1 diff (CBind b) =
    CBind $ \diff' sz -> b (diff' Cat.. diff) sz


----------------------------------------------------------------------
-- * Contextual expressions: expressions over contextual types
----------------------------------------------------------------------

-- | An "expression context" is a sequence
--
-- > BaseCtx ctx0 :<+>: '(ctx1, sz1) :<+>: ... :<+>: '(ctxn, szn)
--
-- of contexts bound at each contextual lambda (see 'clam') containing the
-- current expression. That is, the above expression context is used for the
-- body of a contextual lambda that is nested @n@ levels deep. This expression
-- context is used to represent (using 'CtxOfExprCtx') the @n@-ary append
--
-- > ctx0 <+> ctx1 <+> ... <+> ctxn
--
-- of the contexts contained in it. Intuitively, this is because each contextual
-- lambda could be called in an extension of the previous context.
--
-- Each @szi@ is a type-level variable that 'Reifies' a 'Diff' from @ctx(i-1)@
-- to @ctxi@. This gives GHC enough information to automatically derive a 'Diff'
-- (using the 'WeakensTo' class, below) from any previous context to any later
-- context in the list, which in turn allows us to weaken expressions without
-- having to manually put in all the coercions.
data ExprCtx k1 k2
  = BaseCtx (Ctx k1)
  | ExprCtx k1 k2 :<+>: (Ctx k1, k2)

-- | Defines the constraint required for type variable @sz@ in the expression
-- context @ectx :<+>: (ctx, sz)@
type SzConstr (ectx :: ExprCtx k *) (ctx :: Ctx k) (sz :: *) =
  Reifies sz (Size ctx)

-- | Convert an expression context to the context it reprsents
type family CtxOfExprCtx (ctx :: ExprCtx k *) :: Ctx k where
  CtxOfExprCtx (BaseCtx ctx) = ctx
  CtxOfExprCtx (ectx :<+>: '(ctx, _)) = CtxOfExprCtx ectx <+> ctx

-- | A "weakening" of expression contexts is a 'Diff' from the 'CtxOfExprCtx' of
-- one to that of the other
newtype Weakening ectx1 ectx2 =
  Weakening (Diff (CtxOfExprCtx ectx1) (CtxOfExprCtx ectx2))

-- | Any expression context weakens to itself
weakeningRefl :: Weakening ectx ectx
weakeningRefl = Weakening noDiff

-- | Add a context to the right of an existing weakening
weakeningCons :: SzConstr ectx ctx sz => Weakening ectx1 ectx2 -> Proxy sz ->
                 Weakening ectx1 (ectx2 :<+>: '(ctx, sz))
weakeningCons (Weakening diff) sz =
  Weakening $ appendDiff (reflect sz) Cat.. diff

-- | Typeclass version of 'Weakening'
class WeakensTo ectx1 ectx2 where
  weakensTo :: Weakening ectx1 ectx2

instance WeakensTo ectx ectx where
  weakensTo = weakeningRefl

instance {-# INCOHERENT #-} (WeakensTo ectx1 ectx2, SzConstr ectx2 ctx sz) =>
                            WeakensTo ectx1 (ectx2 :<+>: '(ctx, sz)) where
  weakensTo = weakeningCons weakensTo Proxy

-- | A contextual expression of contextual type @a@ in expression context @ectx@
newtype CExpr (a :: CType k) (ectx :: ExprCtx k *) =
  CExpr { unCExpr :: (a (CtxOfExprCtx ectx)) }

-- | Extract a contextual value from a top-level contextual expression
runCExpr :: CExpr a (BaseCtx ctx) -> a ctx
runCExpr = unCExpr

-- | Weaken the context of a contextual expression
cweakenPf :: ValidCType a => Weakening ectx1 ectx2 ->
             CExpr a ectx1 -> CExpr a ectx2
cweakenPf (Weakening diff) (CExpr a) = CExpr $ mapContext diff a

-- | Weaken the context of a contextual expression using 'WeakensTo'
cweaken :: (ValidCType a, WeakensTo ectx1 ectx2) =>
           CExpr a ectx1 -> CExpr a ectx2
cweaken = cweakenPf weakensTo

-- | Helper function for 'clam'
clamH :: (forall ctx sz. SzConstr ectx ctx sz =>
          CExpr a (ectx :<+>: '(ctx, sz)) -> CExpr b (ectx :<+>: '(ctx, sz))) ->
         CExpr (a :->: b) ectx
clamH f =
  CExpr $ CFun $ \diff a ->
  case diffIsAppend diff of
    IsAppend (sz :: Size ctx'') ->
      reify sz $ \(p :: Proxy s) ->
      unCExpr $ f @ctx'' @s (CExpr a)

-- | The type of a binding expression
type CExprBinder a b ectx =
  (forall ctx sz. SzConstr ectx ctx sz =>
   (forall ectx'.
    WeakensTo (ectx :<+>: '(ctx, sz)) ectx' => CExpr a ectx') ->
   CExpr b (ectx :<+>: '(ctx, sz)))

-- | Build an expression for a contextual function 
clam :: ValidCType a => CExprBinder a b ectx -> CExpr (a :->: b) ectx
clam f = clamH (\a -> f $ cweaken a)

-- | Apply a contextual function expression
(@@) :: CExpr (a :->: b) ectx -> CExpr a ectx -> CExpr b ectx
(CExpr f) @@ (CExpr arg) = CExpr $ unCFun f Cat.id arg

-- | A version of '(@@)' with low precedence, to work like '($)'
infixr 0 $$
($$) :: CExpr (a :->: b) ectx -> CExpr a ectx -> CExpr b ectx
($$) = (@@)

-- | Lift a unary operation between contextual types to one on expressions
cOp1 :: (forall ctx. a ctx -> b ctx) -> CExpr a ectx -> CExpr b ectx
cOp1 f (CExpr a) = CExpr $ f a

-- | Lift a binary operation between contextual types to one on expressions
cOp2 :: (forall ctx. a ctx -> b ctx -> c ctx) ->
        CExpr a ectx -> CExpr b ectx -> CExpr c ectx
cOp2 f (CExpr a) (CExpr b) = CExpr $ f a b

-- | Build a contextual expression for a pair
cpair :: CExpr a ectx -> CExpr b ectx -> CExpr (a :*: b) ectx
cpair = cOp2 CPair

-- | Pattern-match a contextual expression for a pair
cunpair :: CExpr (a :*: b) ectx -> (CExpr a ectx, CExpr b ectx)
cunpair (CExpr (CPair a b)) = (CExpr a, CExpr b)

-- | Build a contextual unit expression
cunit :: CExpr CUnit ectx
cunit = CExpr CUnit

-- | Lift an element of a standard type to a contextual expression
cconst :: a -> CExpr (CConst a) ectx
cconst = CExpr . CConst

-- | Un-lift a contextual expression of lifted type to a normal value
cunconst :: CExpr (CConst a) ectx -> a
cunconst (CExpr (CConst a)) = a

cbindH :: (CVar tp :->: a) ctx -> CBind tp a ctx
cbindH f =
  CBind $ \diff sz -> unCFun f (extendRight diff) (CVar $ nextIndex sz)

-- | Bind a variable in the context of an expression
cbind :: CExprBinder (CVar tp) a ectx -> CExpr (CBind tp a) ectx
cbind f = cOp1 cbindH (clam f)

uncbind :: CExpr Size ectx -> CExpr (CBind tp a) ectx ->
           a (CtxOfExprCtx ectx ::> tp)
uncbind (CExpr sz) (CExpr b) = unCBind b noDiff sz

test1 :: ValidCType a => CExpr (a :->: a) ectx
test1 = clam $ \x -> x

test2 :: (ValidCType a, ValidCType b) =>
         CExpr (a :->: b :->: a) ectx
test2 = clam $ \x -> clam $ \y -> x


----------------------------------------------------------------------
-- * Contextual monads
----------------------------------------------------------------------

-- | Monads over contextual types
class ValidCType1 m => CMonad (m :: CType k -> CType k) where
  creturnFun :: ValidCType a => (a :->: m a) ctx
  cbindFun :: (ValidCType a, ValidCType b) =>
              (m a :->: (a :->: m b) :->: m b) ctx

-- | Lift 'creturnFun' to an operation on expressions
creturn :: (CMonad m, ValidCType a) => CExpr a ectx -> CExpr (m a) ectx
creturn = (@@) (CExpr creturnFun)

-- | Lift 'cbindFun' to an operation on expressions
infixl 1 >>>=
(>>>=) :: (CMonad m, ValidCType a, ValidCType b) =>
          CExpr (m a) ectx ->
          CExprBinder a (m b) ectx ->
          CExpr (m b) ectx
m >>>= f = CExpr cbindFun @@ m @@ clam f


-- | Contextual monad transformers
class CMonadTrans (t :: (CType k -> CType k) -> CType k -> CType k) where
  cliftFun :: (CMonad m, ValidCType a) => (m a :->: t m a) ectx

-- | Lift 'cliftFun' to an operation on expressions
clift :: (CMonadTrans t, CMonad m, ValidCType a) =>
         CExpr (m a) ectx -> CExpr (t m a) ectx
clift = (@@) (CExpr cliftFun)

instance Monad m => CMonad ((:@:) m) where
  creturnFun = runCExpr $ clam $ \x -> cOp1 (CApplyF . return) x
  cbindFun = runCExpr $ clam $ \m -> clam $ \f ->
    cOp2 (\m' f' ->
           CApplyF (unCApplyF m' >>= unCApplyF . unCFun f' Cat.id)) m f


-- | The contextual continuation transformer
newtype CContT res m a (ctx :: Ctx k) =
  CContT { unCContT :: ((a :->: m res) :->: m res) ctx }

instance (ValidCType1 m, ValidCType res) =>
         ValidCType1 (CContT res m) where
  mapContext1 diff (CContT m) = CContT $ mapContext diff m

instance (CMonad m, ValidCType res) => CMonad (CContT res m) where
  creturnFun =
    runCExpr $ clam $ \a -> cOp1 CContT $ clam $ \k -> k @@ a
  cbindFun =
    runCExpr $ clam $ \m -> clam $ \f ->
    cOp1 CContT $ clam $ \k ->
    (cOp1 unCContT m) $$ clam $ \a ->
    cOp1 unCContT (f @@ a) @@ k

instance ValidCType res => CMonadTrans (CContT res) where
  cliftFun =
    runCExpr $ clam $ \m -> cOp1 CContT $ clam $ \k -> m >>>= \a -> k @@ a

-- | Contextual monads that support shift and reset
class (ValidCType res, CMonad m) => CMonadShiftReset res m | m -> res where
  cshiftFun :: ValidCType a => (((a :->: m res) :->: m res) :->: m a) ctx
  cresetFun :: (m res :->: m res) ctx

-- | Lift 'cshiftFun' to an operation on expressions
cshift :: (CMonadShiftReset res m, ValidCType a) =>
          CExpr ((a :->: m res) :->: m res) ectx -> CExpr (m a) ectx
cshift = (@@) $ CExpr cshiftFun

-- | Lift 'cresetFun' to an operation on expressions
creset :: CMonadShiftReset res m => CExpr (m res) ectx -> CExpr (m res) ectx
creset = (@@) $ CExpr cresetFun

instance (CMonad m, ValidCType res) => CMonadShiftReset res (CContT res m) where
  cshiftFun =
    runCExpr $ clam $ \f ->
    cOp1 CContT $ clam $ \k ->
    cOp1 unCContT (f @@ (clam $ \a -> clift $ k @@ a)) @@
    (clam $ \res -> creturn res)
  cresetFun =
    runCExpr $ clam $ \m ->
    cOp1 CContT $ clam $ \k ->
    cOp1 unCContT m @@ (clam $ \res -> creturn res) >>>= \a -> k @@ a


-- | The contextual state transformer
newtype CStateT s m a (ctx :: Ctx k) =
  CStateT { unCStateT :: (s :->: m (s :*: a)) ctx }

instance (ValidCType1 m, ValidCType s) =>
         ValidCType1 (CStateT s m) where
  mapContext1 diff (CStateT m) = CStateT $ mapContext diff m

instance (CMonad m, ValidCType s) => CMonad (CStateT s m) where
  creturnFun =
    runCExpr $ clam $ \a ->
    cOp1 CStateT $ clam $ \s -> creturn (cpair s a)
  cbindFun =
    runCExpr $ clam $ \m -> clam $ \f ->
    cOp1 CStateT $ clam $ \s ->
    cOp1 unCStateT m @@ s >>>= \(cunpair -> (s',a)) ->
    (cOp1 unCStateT $ f @@ a) @@ s'

instance ValidCType s => CMonadTrans (CStateT s) where
  cliftFun =
    runCExpr $ clam $ \m ->
    cOp1 CStateT $ clam $ \s ->
    m >>>= \a -> creturn (cpair s a)

-- | Contextual state monads
class CMonad m => CMonadState s m where
  cgetFun :: (m s) ectx
  cputFun :: (s :->: m CUnit) ectx

-- | Lift 'cget' to an operation on expressions
cget :: CMonadState s m => CExpr (m s) ectx
cget = CExpr cgetFun

-- | Lift 'cput' to an operation on expressions
cput :: CMonadState s m => CExpr s ectx -> CExpr (m CUnit) ectx
cput = (@@) $ CExpr cputFun

instance (CMonad m, ValidCType s) => CMonadState s (CStateT s m) where
  cgetFun =
    runCExpr $ cOp1 CStateT $ clam $ \s -> creturn (cpair s s)
  cputFun =
    runCExpr $ clam $ \s ->
    cOp1 CStateT $ clam $ \_ -> creturn (cpair s cunit)

instance (ValidCType s, CMonadShiftReset res m) =>
         CMonadShiftReset res (CStateT s m) where
  -- FIXME: understand what shift does to the state...
  cshiftFun =
    runCExpr $ clam $ \f ->
    cOp1 CStateT $ clam $ \s ->
    cshift $ clam $ \k ->
    (cOp1 unCStateT $ f $$ clam $ \a ->
      cget >>>= \s' ->
      clift (k @@ (cpair s' a))) @@ s >>>= \(cunpair -> (_, res)) ->
    creturn res

  -- NOTE: reset throws away the inner state
  cresetFun =
    runCExpr $ clam $ \m ->
    cOp1 CStateT $ clam $ \s ->
    creset (cOp1 unCStateT m @@ s >>>= \(cunpair -> (_, res)) ->
             creturn res) >>>= \res ->
    creturn (cpair s res)
