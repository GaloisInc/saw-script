{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
module Verifier.SAW.Heapster.NamedMb where

import Data.Binding.Hobbits
import Data.Binding.Hobbits.MonadBind
import Data.Type.RList
import Control.Lens

newtype StringF a = StringF { unStringF :: String }

type Binding' c = Mb' (RNil :> c)

data Mb' ctx a = Mb'
  { _mbNames :: RAssign StringF ctx
  , _mbBinding :: Mb ctx a
  }
  deriving Functor

mkNuMatching [t| forall a. StringF a |]

instance Liftable (StringF a) where
    mbLift (mbMatch -> [nuMP| StringF x |]) = StringF (mbLift x)

instance LiftableAny1 StringF where
    mbLiftAny1 = mbLift

mkNuMatching [t| forall ctx a. NuMatching a => Mb' ctx a |]

mbMap2' :: (a -> b -> c) -> Mb' ctx a -> Mb' ctx b -> Mb' ctx c
mbMap2' f mb1 mb2 =
  Mb' (_mbNames mb1) (mbMap2 f (_mbBinding mb1) (_mbBinding mb2))

mbBinding :: Lens (Mb' ctx a) (Mb' ctx b) (Mb ctx a) (Mb ctx b)
mbBinding f x = Mb' (_mbNames x) <$> f (_mbBinding x)

nuMulti' :: RAssign StringF ctx -> (RAssign Name ctx -> b) -> Mb' ctx b
nuMulti' tps f = Mb'
  { _mbNames = tps
  , _mbBinding = nuMulti (mapRAssign (const Proxy) tps) f
  }

nuMultiWithElim1' :: (RAssign Name ctx -> arg -> b) -> Mb' ctx arg -> Mb' ctx b
nuMultiWithElim1' k = over mbBinding (nuMultiWithElim1 k)


strongMbM' :: MonadStrongBind m => Mb' ctx (m a) -> m (Mb' ctx a)
strongMbM' = traverseOf mbBinding strongMbM

mbM' :: (MonadBind m, NuMatching a) => Mb' ctx (m a) -> m (Mb' ctx a)
mbM' = traverseOf mbBinding mbM

mbSwap' :: RAssign Proxy ctx -> Mb' ctx' (Mb' ctx a) -> Mb' ctx (Mb' ctx' a)
mbSwap' p (Mb' names' body') =
    Mb'
    { _mbNames = mbLift (_mbNames <$> body')
    , _mbBinding = Mb' names' <$> mbSwap p (_mbBinding <$> body')
    }

mbSink :: RAssign Proxy ctx -> Mb ctx' (Mb' ctx a) -> Mb' ctx (Mb ctx' a)
mbSink p m =
    Mb'
    { _mbNames = mbLift (_mbNames <$> m)
    , _mbBinding = mbSwap p (_mbBinding <$> m)
    }

mbLift' :: Liftable a => Mb' ctx a -> a
mbLift' = views mbBinding mbLift

elimEmptyMb' :: Mb' RNil a -> a
elimEmptyMb' = views mbBinding elimEmptyMb

emptyMb' :: a -> Mb' RNil a
emptyMb' = Mb' MNil . emptyMb
