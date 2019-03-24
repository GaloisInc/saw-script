{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

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
type CtxType k = Ctx k -> *

-- | Map a functor over a contextual type
newtype CtxMapF (f :: * -> *) (b :: CtxType k) ctx =
  CtxMapF { unCtxMapF :: f (b ctx) }

instance (Functor f, ExtendContext b) => ExtendContext (CtxMapF f b) where
  extendContext diff = CtxMapF . fmap (extendContext diff) . unCtxMapF

-- | The pair type-in-context
data CtxPair a b (ctx :: Ctx k) = CtxPair (a ctx) (b ctx)

instance (ExtendContext a, ExtendContext b) => ExtendContext (CtxPair a b) where
  extendContext diff (CtxPair a b) =
    CtxPair (extendContext diff a) (extendContext diff b)

-- | The unit type-in-context
data CtxUnit (ctx :: Ctx k) = CtxUnit

instance ExtendContext CtxUnit where
  extendContext _ _ = CtxUnit

-- | The function type-in-context, that can be applied in any extension of the
-- current context
newtype CtxFun a b (ctx :: Ctx k) =
  CtxFun { unCtxFun :: forall ctx'. Diff ctx ctx' -> a ctx' -> b ctx' }

instance ExtendContext (CtxFun a b) where
  extendContext diff (CtxFun f) = CtxFun $ \diff' -> f (diff' Cat.. diff)


----------------------------------------------------------------------
-- * Contextual expressions: expressions over contextual types
----------------------------------------------------------------------

-- | An "expression context" is a representation of contexts as sequences of
-- contexts that are to be appended. That is, the expression context
--
-- > BaseCtx ctx :<+>: '(ctx1, sz1) :<+>: ... :<+>: '(ctxn, szn)
--
-- represents the context
--
-- > ctx <+> ctx1 <+> ... <+> ctxn
--
-- This expression context is used to represent the context inside @n@
-- contextual lambdas (see 'lambdaC'), each of which builds a function body that
-- can be called in an extension @cur_ctx <+> ctx@ of the current context
-- @cur_ctx@. By using type-level constructors in a representation, rather than
-- using the @n@-fold context append explicitly, we make things easier for GHC
-- (and so also for us).
--
-- The @sz@ type is a type-level variable that 'Reifies' a 'Size' object for
-- each context using type-level reflection. That is, an expression context is
-- intuitively a sequence of pairs of a context and its 'Size'.
--
-- Note that there are multiple different expression
-- contexts that represent the same underlying context, but that will not
-- actually be an issue here.
data ExprCtx k1 k2
  = BaseCtx (Ctx k1)
  | ExprCtx k1 k2 :<+>: (Ctx k1, k2)

-- | Convert an expression context to the context it reprsents
type family CtxOfExprCtx (ctx :: ExprCtx k *) :: Ctx k where
  CtxOfExprCtx (BaseCtx ctx) = ctx
  CtxOfExprCtx (ectx :<+>: '(ctx, _)) = CtxOfExprCtx ectx <+> ctx

-- NOTE: cannot write this in the Unsafe representation of contexts; this is why
-- we need WeakensTo, below
-- flattenDiff :: Diff ectx1 ectx2 -> Diff (CtxOfExprCtx ectx1) (CtxOfExprCtx ectx2)

-- | Proof that @ectx1@ can be extended to @ectx2@
newtype WeakensToPf ectx1 ectx2 =
  WeakensToPf (Diff (CtxOfExprCtx ectx1) (CtxOfExprCtx ectx2))

-- | Any expression context weakens to itself
weakensRefl :: WeakensToPf ectx ectx
weakensRefl = WeakensToPf noDiff

-- | Add an extra context to the right of an existing weakening proof
weakensCons :: Reifies s (Size ctx) => WeakensToPf ectx1 ectx2 -> Proxy s ->
               WeakensToPf ectx1 (ectx2 :<+>: '(ctx, s))
weakensCons (WeakensToPf diff) sz =
  WeakensToPf $ appendDiff (reflect sz) Cat.. diff

-- | Typeclass version of 'WeakensToPf'
class WeakensTo ectx1 ectx2 where
  weakensTo :: WeakensToPf ectx1 ectx2

instance WeakensTo ectx ectx where
  weakensTo = weakensRefl

instance {-# INCOHERENT #-} (WeakensTo ectx1 ectx2, Reifies s (Size ctx)) =>
                            WeakensTo ectx1 (ectx2 :<+>: '(ctx, s)) where
  weakensTo = weakensCons weakensTo Proxy

-- | FIXME: documentation
newtype CExpr (a :: CtxType k) (ectx :: ExprCtx k *) =
  CExpr { unCExpr :: (a (CtxOfExprCtx ectx)) }

weakenExpr :: ExtendContext a => WeakensToPf ectx1 ectx2 ->
              CExpr a ectx1 -> CExpr a ectx2
weakenExpr (WeakensToPf diff) (CExpr a) = CExpr $ extendContext diff a

lambdaC' :: (forall ctx s. Reifies s (Size ctx) =>
             CExpr a (ectx :<+>: '(ctx, s)) -> CExpr b (ectx :<+>: '(ctx, s))) ->
            CExpr (CtxFun a b) ectx
lambdaC' f =
  CExpr $ CtxFun $ \diff a ->
  case diffIsAppend diff of
    IsAppend (sz :: Size ctx'') ->
      reify sz $ \(p :: Proxy s) ->
      unCExpr $ f @ctx'' @s (CExpr a)

lambdaC :: ExtendContext a =>
           (forall ctx s. Reifies s (Size ctx) =>
            (forall ectx'.
             WeakensTo (ectx :<+>: '(ctx, s)) ectx' => CExpr a ectx') ->
            CExpr b (ectx :<+>: '(ctx, s))) ->
           CExpr (CtxFun a b) ectx
lambdaC f = lambdaC' (\a -> f $ weakenExpr weakensTo a)

(@@) :: CExpr (CtxFun a b) ectx -> CExpr a ectx -> CExpr b ectx
(CExpr f) @@ (CExpr arg) = CExpr $ unCtxFun f noDiff arg


test1 :: CExpr (CtxFun CtxUnit CtxUnit) ectx
test1 = lambdaC $ \x -> x

test2 :: (ExtendContext a, ExtendContext b) =>
         CExpr (CtxFun a (CtxFun b a)) ectx
test2 = lambdaC $ \x -> lambdaC $ \y -> x


----------------------------------------------------------------------
-- * Contextual monads
----------------------------------------------------------------------

{-

-- | Monads over contextual types
class CtxMonad (m :: (Ctx k -> *) -> Ctx k -> *) where
  returnC :: a ctx -> m a ctx
  (>>>=) :: m a ctx ->
            (forall ctx'. Diff ctx ctx' -> a ctx' -> m b ctx') ->
            m b ctx

-- | Contextual monad transformers
class CtxMonadTrans (t :: ((Ctx k -> *) -> Ctx k -> *) ->
                          ((Ctx k -> *) -> Ctx k -> *)) where
  liftC :: CtxMonad m => m a ctx -> t m a ctx


----------------------------------------------------------------------
-- * The contextual continuation monad
----------------------------------------------------------------------

-- | The continuation transformer from ordinary to contextual monads
newtype CtxContM res (m :: * -> *) a (ctx :: Ctx k) =
  CtxContM { unCtxContM :: CtxFun a (CtxMapF m res) ctx -> CtxMapF m res ctx }

instance Monad m => CtxMonad (CtxContM res m) where
  returnC a = CtxContM $ \k -> applyCtxFun k noDiff a
  m >>>= f =
    CtxContM $ \k ->
    unCtxContM m (CtxFun $ \diff a ->
                   unCtxContM (f diff a) (extendContext diff k))

-- | Lift a computation in @m@ into one in 'CtxContM res m'
liftCtxContM :: Monad m => m (a ctx) -> CtxContM res m a ctx
liftCtxContM m = CtxContM $ \k -> CtxMapF (m >>= unCtxMapF . applyCtxFun k noDiff)

-- | Contextual monads that support shift and reset
class CtxMonad m => CtxMonadShiftReset res m | m -> res where
  shiftC :: ((forall ctx'. Diff ctx ctx' ->
              a ctx' -> m res ctx') -> m res ctx) -> m a ctx
  resetC :: m res ctx -> m res ctx

instance Monad m => CtxMonadShiftReset res (CtxContM res m) where
  shiftC f =
    CtxContM $ \k ->
    unCtxContM (f (\diff a -> liftCtxContM $ unCtxMapF $ applyCtxFun k diff a))
    (CtxFun $ \diff a -> CtxMapF $ return a)
  resetC m =
    CtxContM $ \k ->
    CtxMapF $
    (unCtxMapF $ unCtxContM m (CtxFun $ \_ -> CtxMapF . return)) >>=
    (unCtxMapF . applyCtxFun k noDiff)


----------------------------------------------------------------------
-- * The contextual state monad
----------------------------------------------------------------------

-- | The contextual state monad
newtype CtxStateT s m a (ctx :: Ctx k) =
  CtxStateT { unCtxStateT :: s ctx -> m (CtxPair s a) ctx }

instance CtxMonad m => CtxMonad (CtxStateT s m) where
  returnC a = CtxStateT $ \s -> returnC (CtxPair s a)
  m >>>= f =
    CtxStateT $ \s -> unCtxStateT m s >>>= \diff (CtxPair s' a) ->
    unCtxStateT (f diff a) s'

instance ExtendContext s => CtxMonadTrans (CtxStateT s) where
  liftC m =
    CtxStateT $ \s -> m >>>= \diff a ->
    returnC (CtxPair (extendContext diff s) a)

-- | Contextual monads with state
class CtxMonadState s m | m -> s where
  getC :: m s ctx
  putC :: s ctx -> m CtxUnit ctx

instance CtxMonad m => CtxMonadState s (CtxStateT s m) where
  getC = CtxStateT $ \s -> returnC (CtxPair s s)
  putC s = CtxStateT $ \_ -> returnC (CtxPair s CtxUnit)

instance (ExtendContext s, CtxMonadShiftReset res m) =>
         CtxMonadShiftReset res (CtxStateT s m) where
  -- FIXME: understand what shift does to the state...
  shiftC f = CtxStateT $ \s -> 
    shiftC $ \k ->
    unCtxStateT (f $ \diff a ->
                  CtxStateT $ \s' ->
                  k diff (CtxPair s' a) >>>= \diff res ->
                  returnC (CtxPair (extendContext diff s') res)) s
    >>>= \diff (CtxPair _ res) ->
    returnC res

  -- NOTE: reset throws away the inner state
  resetC m =
    CtxStateT $ \s ->
    resetC (unCtxStateT m s >>>= \diff (CtxPair _ res) ->
             returnC res) >>>= \diff res ->
    returnC (CtxPair (extendContext diff s) res)
-}
