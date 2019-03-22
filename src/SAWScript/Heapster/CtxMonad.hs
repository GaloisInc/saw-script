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

module SAWScript.Heapster.CtxMonad where

import           Data.Parameterized.Ctx
import           Data.Parameterized.Context

import           Control.Monad.Except
import qualified Control.Category as Cat


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

-- | Map a type function over a contextual type
newtype CtxMapF (f :: * -> *) b (ctx :: Ctx k) =
  CtxMapF { unCtxMapF :: f (b ctx) }

-- | The pair type-in-context
data CtxPair a b (ctx :: Ctx k) = CtxPair (a ctx) (b ctx)

-- | The unit type-in-context
data CtxUnit (ctx :: Ctx k) = CtxUnit

-- | The function type-in-context, that can be applied in any extension of the
-- current context
newtype CtxFun a b (ctx :: Ctx k) =
  CtxFun { applyCtxFun :: forall ctx'. Diff ctx ctx' -> a ctx' -> b ctx' }

instance ExtendContext (CtxFun a b) where
  extendContext diff (CtxFun k) = CtxFun $ \diff' -> k (diff' Cat.. diff)

-- | Extend the context of a contextual continuation
{-
extendCtxFun :: Diff ctx ctx' -> CtxFun ctx a b -> CtxFun ctx' a b
extendCtxFun diff (CtxFun k) = CtxFun $ \diff' -> k (diff' Cat.. diff)
-}


----------------------------------------------------------------------
-- * Contextual monads
----------------------------------------------------------------------

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
