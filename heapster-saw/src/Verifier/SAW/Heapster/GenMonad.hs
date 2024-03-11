{-# Language BlockArguments #-}
{-# Language DeriveFunctor #-}
{-# Language FlexibleInstances, MultiParamTypeClasses #-} -- MonadState
{-# Language PolyKinds #-} -- gopenBinding
{-# Language TypeFamilies #-} -- Equality constraints
{-# Language TypeOperators #-} -- Equality constraints
{-# Language RankNTypes #-}
module Verifier.SAW.Heapster.GenMonad (
  -- * Core definitions
  GenStateContT(..), (>>>=), (>>>),
  -- * Continuation operations
  gcaptureCC, gmapRet, gabortM, gparallel, startBinding,
  startNamedBinding, gopenBinding, gopenNamedBinding,
  -- * State operations
  gmodify, gput,
  -- * Transformations
  addReader,
  ) where

import Data.Binding.Hobbits ( nuMulti, nuMultiWithElim1, Mb, Name, RAssign )
import Control.Monad ( ap )
import Control.Monad.State ( MonadState(get, put) )
import Control.Monad.Trans.Class ( MonadTrans(lift) )
import Control.Monad.Trans.Reader
import Data.Proxy
import Verifier.SAW.Heapster.NamedMb

-- | The generalized state-continuation monad
newtype GenStateContT s1 r1 s2 r2 m a = GenStateContT {
  runGenStateContT :: s2 -> (s1 -> a -> m r1) -> m r2
  } deriving Functor

-- | Sequence two 'GenStateCont' values. Type-changing analogue of '>>='
(>>>=) :: GenStateContT s2 r2 s1 r1 m a -> (a -> GenStateContT s3 r3 s2 r2 m b) -> GenStateContT s3 r3 s1 r1 m b
x >>>= y = GenStateContT \s1 z -> runGenStateContT x s1 \s2 a -> runGenStateContT (y a) s2 z

-- | Sequence two 'GenStateCont' values ignoring the return value. Type-changing analogue of '>>'
(>>>) :: GenStateContT s2 r2 s1 r1 m a -> GenStateContT s3 r3 s2 r2 m b -> GenStateContT s3 r3 s1 r1 m b
m1 >>> m2 = m1 >>>= \_ -> m2

infixl 1 >>>=, >>>

-- NB. These instance must be specified as
-- instance (s1 ~ s2, r1 ~ r2) => Applicative (GenStateContT s1 r1 s2 r2) where
-- instead of
-- instance Applicative (GenStateContT s r s r) where
-- in order to ensure they are quickly selected by GHC even when it's not
-- immediately obvious that the types are equal.

instance (s1 ~ s2, r1 ~ r2) => Applicative (GenStateContT s1 r1 s2 r2 m) where
  pure x = GenStateContT \s k -> k s x
  (<*>) = ap

instance (s1 ~ s2, r1 ~ r2) => Monad (GenStateContT s1 r1 s2 r2 m) where
  (>>=) = (>>>=)

instance (s1 ~ s2, r1 ~ r2) => MonadTrans (GenStateContT s1 r1 s2 r2) where
  lift m = gcaptureCC (m >>=)

-----------------------------------------------------------------------
-- Continuation operations
-----------------------------------------------------------------------

-- | Capture the current continuation while preserving the state.
gcaptureCC :: ((a -> m r1) -> m r2) -> GenStateContT s r1 s r2 m a
gcaptureCC f = GenStateContT \s k -> f (k s)

-- | Run two generalized monad computations \"in parallel\" and combine their
-- results
gparallel ::
  (m r1 -> m r2 -> m r3) ->
  GenStateContT s1 r s2 r1 m a ->
  GenStateContT s1 r s2 r2 m a ->
  GenStateContT s1 r s2 r3 m a
gparallel f (GenStateContT m1) (GenStateContT m2) = GenStateContT \s k -> f (m1 s k) (m2 s k)

-- | Abort the current state-continuation computation and just return an @r2@
gabortM :: m r2 -> GenStateContT s1 r1 s2 r2 m a
gabortM ret = GenStateContT \_ _ -> ret

-----------------------------------------------------------------------
-- State operations
-----------------------------------------------------------------------

instance (s1 ~ s2, r1 ~ r2) => MonadState s1 (GenStateContT s1 r1 s2 r2 m) where
  get = GenStateContT \s k -> k s s
  put = gput

-- | Overwrite the previous state value (with the ability to change its type)
gput :: s -> GenStateContT s r s_ r m ()
gput s = GenStateContT \_ k -> k s ()

-----------------------------------------------------------------------
-- Derived operations
-----------------------------------------------------------------------

-- | Apply a function to the state to update it.
gmodify :: (s -> t) -> GenStateContT t r s r m ()
gmodify f = get >>>= gput . f

-- | Map a function over the final return value.
gmapRet :: (m r1 -> m r2) -> GenStateContT s r1 s r2 m ()
gmapRet f_ret = gcaptureCC \k -> f_ret (k ())

-- | Name-binding in the generalized continuation monad (FIXME: explain)
gopenBinding ::
  (Mb ctx (m b1) -> m r2) ->
  Mb ctx b2 ->
  GenStateContT s b1 s r2 m (RAssign Name ctx, b2)
gopenBinding f_ret mb_a =
  gcaptureCC \k ->
  f_ret $ flip nuMultiWithElim1 mb_a $ \names a ->
  k (names, a)

-- | Name-binding in the generalized continuation monad (FIXME: explain)
gopenNamedBinding ::
  (NamedMb ctx (m b1) -> m r2) ->
  NamedMb ctx b2 ->
  GenStateContT s b1 s r2 m (RAssign Name ctx, b2)
gopenNamedBinding f_ret mb_a =
  gcaptureCC \k ->
  f_ret $ flip nuMultiWithElim1Named mb_a $ \names a ->
  k (names, a)

-- | Name-binding in the generalized continuation monad (FIXME: explain)
startBinding ::
  RAssign Proxy ctx ->
  (Mb ctx (m r1) -> m r2) ->
  GenStateContT s r1 s r2 m (RAssign Name ctx)
startBinding tps f_ret = gcaptureCC (f_ret . nuMulti tps)

-- | Name-binding in the generalized continuation monad (FIXME: explain)
startNamedBinding ::
  RAssign StringF ctx ->
  (NamedMb ctx (m r1) -> m r2) ->
  GenStateContT s r1 s r2 m (RAssign Name ctx)
startNamedBinding tps f_ret = gcaptureCC (f_ret . nuMultiNamed tps)

addReader :: GenStateContT s1 r1 s2 r2 m a -> GenStateContT s1 r1 s2 r2 (ReaderT e m) a
addReader (GenStateContT m) =
  GenStateContT \s2 k ->
  ReaderT \e ->
  m s2 \s1 a ->
  runReaderT (k s1 a) e
