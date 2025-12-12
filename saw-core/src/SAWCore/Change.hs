{- |
Module      : SAWCore.Change
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Change
  ( Change
  , ChangeT
  , changeT
  , runChangeT
  , preserve
  , taint
  , modified
  , change
  , changeList
  , commitChange
  , commitChangeT
  , preserveChangeT
  , flatten
  ) where

import Control.Monad.Trans
import Control.Monad.Writer
import Data.Monoid

----------------------------------------------------------------------
-- Monads for tracking whether values have changed

--class (Monad m, Applicative m) => ChangeMonad m where
--  preserve :: a -> m a -> m a
--  taint :: m a -> m a
--  taint m = m >>= modified
--  modified :: a -> m a
--  modified x = taint (pure x)
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

change :: Monad m => (a -> Maybe a) -> a -> ChangeT m a
change f a =
  case f a of
    Nothing -> pure a
    Just x  -> modified x

changeList :: Monad m => (a -> ChangeT m a) -> [a] -> ChangeT m [a]
changeList f xs =
  preserve xs $
    case xs of
      [] -> pure []
      y : ys -> (:) <$> f y <*> changeList f ys

----------------------------------------------------------------------
-- Change monad

type Change = Writer Any

--data Change a = Original a | Modified a
--  deriving (Show, Functor)

--instance Applicative Change where
--  pure x = Original x
--  Original f <*> Original x = Original (f x)
--  Original f <*> Modified x = Modified (f x)
--  Modified f <*> Original x = Modified (f x)
--  Modified f <*> Modified x = Modified (f x)

--instance Monad Change where
--  return = pure
--  Original x >>= k = k x
--  Modified x >>= k = taint (k x)

--instance ChangeMonad Change where
--  preserve x (Original _) = Original x
--  preserve _ c@(Modified _) = c
--  taint (Original x) = Modified x
--  taint c@(Modified _) = c
--  modified x = Modified x

commitChange :: Change a -> a
commitChange m = fst (runWriter m)
--commitChange (Original x) = x
--commitChange (Modified x) = x
-- ^ Satisfies the following laws:
-- @commitChange (fmap f m) = f (commitChange m)@
-- @commitChange (taint m) = commitChange m@
-- @commitChange (m >>= k) = commitChange (k (commitChange m))@

----------------------------------------------------------------------
-- Change monad transformer

--newtype ChangeT m a = ChangeT { runChangeT :: m (Change a) }
type ChangeT = WriterT Any

changeT :: Functor m => m (Change a) -> ChangeT m a
changeT m = WriterT (fmap runWriter m)

runChangeT :: Monad m => ChangeT m a -> m (Change a)
runChangeT m = writer <$> runWriterT m

--instance Functor m => Functor (ChangeT m) where
--  fmap f (ChangeT m) = ChangeT (fmap (fmap f) m)

--instance Applicative m => Applicative (ChangeT m) where
--  pure x = ChangeT (pure (Original x))
--  ChangeT m1 <*> ChangeT m2 = ChangeT (App.liftA2 (<*>) m1 m2)

--instance Monad m => Monad (ChangeT m) where
--  return = pure
--  ChangeT m >>= k = ChangeT (m >>= f)
--    where f (Original x) = runChangeT (k x)
--          f (Modified x) = runChangeT (k x) >>= (return . taint)

--instance MonadTrans ChangeT where
--  lift m = ChangeT (liftM Original m)

--instance MonadIO m => MonadIO (ChangeT m) where
--  liftIO m = lift (liftIO m)

preserve :: Monad m => a -> ChangeT m a -> ChangeT m a
preserve x m =
  do (y, Any w) <- listen m
     pure (if w then y else x)
  -- preserve x (pure _) = pure x
  -- preserve _ (modified y) = modified y
  -- preserve _ (taint m) = taint m

taint :: Monad m => ChangeT m a -> ChangeT m a
taint m = m >>= modified

modified :: Monad m => a -> ChangeT m a
modified x = tell (Any True) >> pure x

--instance Monad m => ChangeMonad (ChangeT m) where
--  preserve x (ChangeT m) = ChangeT (liftM (preserve x) m)
--  taint (ChangeT m) = ChangeT (liftM taint m)
--  modified x = ChangeT (return (modified x))

commitChangeT :: Monad m => ChangeT m a -> m a
commitChangeT m = fst <$> runWriterT m
-- commitChangeT (ChangeT m) = liftM commitChange m
-- ^ Is a natural transformation from @ChangeT m@ to @m@:
-- @commitChangeT (fmap f m) = fmap f (commitChangeT m)@
-- @commitChangeT (lift m) = m@
-- @commitChangeT (m >>= k) = commitChangeT m >>= (commitChangeT . k)@
-- @commitChangeT (return x) = return x@
-- @commitChangeT (taint m) = commitChangeT m@

preserveChangeT :: Monad m => a -> ChangeT m (m a) -> ChangeT m a
preserveChangeT x m =
  do (m', w) <- listen m
     if getAny w then pure x else lift m'

--preserveChangeT x (ChangeT c) = ChangeT (c >>= k)
--  where k (Original _) = return (Original x)
--        k (Modified m) = liftM Modified m
-- ^ Satisfies @preserveChangeT x (return _) = return x@ and
-- @preserveChangeT _ (modified m) = taint (lift m)@.

flatten :: Monad m => (a -> ChangeT m (m a)) -> a -> ChangeT m a
flatten f x = preserveChangeT x (f x)
