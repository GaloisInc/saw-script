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

-- | A constant type functor for 'String's
newtype StringF a = StringF { unStringF :: String }

mkNuMatching [t| forall a. StringF a |]

-- | An 'Mb' multi-binding where each bound 'Name' has an associated 'String'
-- for parsing and printing it
data NamedMb ctx a = NamedMb
  { _mbNames :: RAssign StringF ctx
  , _mbBinding :: Mb ctx a
  }
  deriving Functor

-- | A 'Binding' of a single 'Name' with a 'String'
type NamedBinding c = NamedMb (RNil :> c)

instance Liftable (StringF a) where
    mbLift (mbMatch -> [nuMP| StringF x |]) = StringF (mbLift x)

instance LiftableAny1 StringF where
    mbLiftAny1 = mbLift

mkNuMatching [t| forall ctx a. NuMatching a => NamedMb ctx a |]

-- | Apply a binary function to the body of a 'NamedMb'; similar to 'mbMap2'
mbMap2Named :: (a -> b -> c) -> NamedMb ctx a -> NamedMb ctx b -> NamedMb ctx c
mbMap2Named f mb1 mb2 =
  NamedMb (_mbNames mb1) (mbMap2 f (_mbBinding mb1) (_mbBinding mb2))

-- | A 'Lens' to get the binding ouf of a 'NamedMb'
mbBinding :: Lens (NamedMb ctx a) (NamedMb ctx b) (Mb ctx a) (Mb ctx b)
mbBinding f x = NamedMb (_mbNames x) <$> f (_mbBinding x)

-- | Build a 'NamedMb' that binds multiple 'Name's with the given 'String's
nuMultiNamed :: RAssign StringF ctx -> (RAssign Name ctx -> b) -> NamedMb ctx b
nuMultiNamed tps f = NamedMb
  { _mbNames = tps
  , _mbBinding = nuMulti (mapRAssign (const Proxy) tps) f
  }

-- | A version of 'nuMultiWithElim1' for 'NamedMb'
nuMultiWithElim1Named :: (RAssign Name ctx -> arg -> b) ->
                         NamedMb ctx arg -> NamedMb ctx b
nuMultiWithElim1Named k = over mbBinding (nuMultiWithElim1 k)

-- | Commute a 'NamedMb' inside a strong binding monad
strongMbMNamed :: MonadStrongBind m => NamedMb ctx (m a) -> m (NamedMb ctx a)
strongMbMNamed = traverseOf mbBinding strongMbM

-- | Commute a 'NamedMb' inside a binding monad
mbMNamed :: (MonadBind m, NuMatching a) => NamedMb ctx (m a) -> m (NamedMb ctx a)
mbMNamed = traverseOf mbBinding mbM

-- | Swap the order of two nested named bindings
mbSwapNamed :: RAssign Proxy ctx -> NamedMb ctx' (NamedMb ctx a) ->
               NamedMb ctx (NamedMb ctx' a)
mbSwapNamed p (NamedMb names' body') =
    NamedMb
    { _mbNames = mbLift (_mbNames <$> body')
    , _mbBinding = NamedMb names' <$> mbSwap p (_mbBinding <$> body')
    }

-- | Swap the order of a binding with 'String' names with one without
mbSink :: RAssign Proxy ctx -> Mb ctx' (NamedMb ctx a) -> NamedMb ctx (Mb ctx' a)
mbSink p m =
    NamedMb
    { _mbNames = mbLift (_mbNames <$> m)
    , _mbBinding = mbSwap p (_mbBinding <$> m)
    }

-- | Lift a 'Liftable' value out of a 'NamedMb'
mbLiftNamed :: Liftable a => NamedMb ctx a -> a
mbLiftNamed = views mbBinding mbLift

-- | Eliminate a 'NamedMb' that binds zero names
elimEmptyNamedMb :: NamedMb RNil a -> a
elimEmptyNamedMb = views mbBinding elimEmptyMb

-- | Create a 'NamedMb' that binds zero names
emptyNamedMb :: a -> NamedMb RNil a
emptyNamedMb = NamedMb MNil . emptyMb
