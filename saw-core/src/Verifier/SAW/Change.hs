{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

{- |
Module      : Verifier.SAW.Change
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Change
  ( ChangeMonad(..)
  , Change(..)
  , ChangeT(..)
  , change
  , changeList
  , commitChange
  , commitChangeT
  , preserveChangeT
  , flatten
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import Control.Monad (liftM, liftM2)
import Control.Monad.Trans

----------------------------------------------------------------------
-- Monads for tracking whether values have changed

class (Monad m, Applicative m) => ChangeMonad m where
  preserve :: a -> m a -> m a
  taint :: m a -> m a
  taint m = m >>= modified
  modified :: a -> m a
  modified x = taint (pure x)
  -- Laws (not a minimal set):
  -- taint (taint m) = taint m
  -- taint (pure x) = modified x
  -- fmap f (taint m) = taint (fmap f m)
  -- taint m1 <*> m2 = taint (m1 <*> m2)
  -- m1 <*> taint m2 = taint (m1 <*> m2)
  -- fmap f (modified x) = modified (f x)
  -- modified x >>= k = taint (k x)
  -- m >>= modified = taint m
  -- taint (modified x) = modified x
  -- taint (return x) = modified x
  -- taint (m >>= k) = taint m >>= k
  -- taint (m >>= k) = m >>= (taint . k)
  -- preserve x (pure _) = pure x
  -- preserve _ (modified y) = modified y
  -- preserve _ (taint m) = taint m

change :: ChangeMonad m => (a -> Maybe a) -> a -> m a
change f a =
  case f a of
    Nothing -> pure a
    Just x  -> modified x

changeList :: ChangeMonad m => (a -> m a) -> [a] -> m [a]
changeList f xs =
  preserve xs $
    case xs of
      [] -> pure []
      y : ys -> (:) <$> f y <*> changeList f ys

----------------------------------------------------------------------
-- Change monad

data Change a = Original a | Modified a
  deriving (Show, Functor)

instance Applicative Change where
  pure x = Original x
  Original f <*> Original x = Original (f x)
  Original f <*> Modified x = Modified (f x)
  Modified f <*> Original x = Modified (f x)
  Modified f <*> Modified x = Modified (f x)

instance Monad Change where
  return x = Original x
  Original x >>= k = k x
  Modified x >>= k = taint (k x)

instance ChangeMonad Change where
  preserve x (Original _) = Original x
  preserve _ c@(Modified _) = c
  taint (Original x) = Modified x
  taint c@(Modified _) = c
  modified x = Modified x

commitChange :: Change a -> a
commitChange (Original x) = x
commitChange (Modified x) = x
-- ^ Satisfies the following laws:
-- @commitChange (fmap f m) = f (commitChange m)@
-- @commitChange (taint m) = commitChange m@
-- @commitChange (m >>= k) = commitChange (k (commitChange m))@

----------------------------------------------------------------------
-- Change monad transformer

newtype ChangeT m a = ChangeT { runChangeT :: m (Change a) }

instance Monad m => Functor (ChangeT m) where
  fmap f (ChangeT m) = ChangeT (liftM (fmap f) m)

instance Monad m => Applicative (ChangeT m) where
  pure x = ChangeT (return (Original x))
  ChangeT m1 <*> ChangeT m2 = ChangeT (liftM2 (<*>) m1 m2)

instance Monad m => Monad (ChangeT m) where
  return x = ChangeT (return (Original x))
  ChangeT m >>= k = ChangeT (m >>= f)
    where f (Original x) = runChangeT (k x)
          f (Modified x) = runChangeT (k x) >>= (return . taint)

instance MonadTrans ChangeT where
  lift m = ChangeT (liftM Original m)

instance MonadIO m => MonadIO (ChangeT m) where
  liftIO m = lift (liftIO m)

instance Monad m => ChangeMonad (ChangeT m) where
  preserve x (ChangeT m) = ChangeT (liftM (preserve x) m)
  taint (ChangeT m) = ChangeT (liftM taint m)
  modified x = ChangeT (return (modified x))

commitChangeT :: Monad m => ChangeT m a -> m a
commitChangeT (ChangeT m) = liftM commitChange m
-- ^ Is a natural transformation from @ChangeT m@ to @m@:
-- @commitChangeT (fmap f m) = fmap f (commitChangeT m)@
-- @commitChangeT (lift m) = m@
-- @commitChangeT (m >>= k) = commitChangeT m >>= (commitChangeT . k)@
-- @commitChangeT (return x) = return x@
-- @commitChangeT (taint m) = commitChangeT m@

preserveChangeT :: Monad m => a -> ChangeT m (m a) -> ChangeT m a
preserveChangeT x (ChangeT c) = ChangeT (c >>= k)
  where k (Original _) = return (Original x)
        k (Modified m) = liftM Modified m
-- ^ Satisfies @preserveChangeT x (return _) = return x@ and
-- @preserveChangeT _ (modified m) = taint (lift m)@.

flatten :: Monad m => (a -> ChangeT m (m a)) -> a -> ChangeT m a
flatten f x = ChangeT (runChangeT (f x) >>= k)
  where k (Original _) = return (Original x)
        k (Modified m) = liftM Modified m
-- ^ @flatten f x = preserveChangeT x (f x)@
