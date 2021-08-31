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

type Binding' c = NMb (RNil :> c)

data NMb ctx a = NMb
  { _mbNames :: RAssign StringF ctx
  , _mbBinding :: Mb ctx a
  }
  deriving Functor

mbBinding :: Lens (NMb ctx a) (NMb ctx b) (Mb ctx a) (Mb ctx b)
mbBinding f x = NMb (_mbNames x) <$> f (_mbBinding x)

nuMultiN :: RAssign StringF ctx -> (RAssign Name ctx -> b) -> NMb ctx b
nuMultiN tps f = NMb
  { _mbNames = tps
  , _mbBinding = nuMulti (mapRAssign (const Proxy) tps) f
  }

nuMultiWithElim1N :: (RAssign Name ctx -> arg -> b) -> NMb ctx arg -> NMb ctx b
nuMultiWithElim1N = over mbBinding . nuMultiWithElim1

strongNMbM :: MonadStrongBind m => NMb ctx (m a) -> m (NMb ctx a)
strongNMbM = traverseOf mbBinding strongMbM

nmbM :: (MonadBind m, NuMatching a) => NMb ctx (m a) -> m (NMb ctx a)
nmbM = traverseOf mbBinding mbM

nmbSwap :: RAssign Proxy ctx -> NMb ctx' (NMb ctx a) -> NMb ctx (NMb ctx' a)
nmbSwap p (NMb names' body') = NMb names' <$> nmbSink p body'

nmbSink :: RAssign Proxy ctx -> Mb ctx' (NMb ctx a) -> NMb ctx (Mb ctx' a)
nmbSink p m =
    NMb
    { _mbNames = mbLift (_mbNames <$> m)
    , _mbBinding = mbSwap p (_mbBinding <$> m)
    }

nmbLift :: Liftable a => NMb ctx a -> a
nmbLift = views mbBinding mbLift

elimEmptyNMb :: NMb RNil a -> a
elimEmptyNMb = views mbBinding elimEmptyMb

emptyNMb :: a -> NMb RNil a
emptyNMb = NMb MNil . emptyMb

mkNuMatching [t| forall a. StringF a |]
instance NuMatchingAny1 StringF where
    nuMatchingAny1Proof = nuMatchingProof

instance Liftable (StringF a) where
    mbLift (mbMatch -> [nuMP| StringF x |]) = StringF (mbLift x)

instance LiftableAny1 StringF where
    mbLiftAny1 = mbLift

mkNuMatching [t| forall ctx a. NuMatching a => NMb ctx a |]
