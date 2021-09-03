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

type NBinding c = NMb (RNil :> c)

-- | Named version of 'Mb'
data NMb ctx a = NMb
  { _nmbNames :: RAssign StringF ctx
  , _nmbBinding :: Mb ctx a
  }
  deriving Functor

-- | Lens for accessing 'NMb' underlying 'Mb'
nmbBinding :: Lens (NMb ctx a) (NMb ctx b) (Mb ctx a) (Mb ctx b)
nmbBinding f x = NMb (_nmbNames x) <$> f (_nmbBinding x)

-- | 'Lens' for accessing 'NMb' debug names.
nmbNames :: Lens' (NMb ctx a) (RAssign StringF ctx)
nmbNames f x = (\n -> NMb n (_nmbBinding x)) <$> f (_nmbNames x)

-- | Named version of 'nuMulti'
nuMultiN :: RAssign StringF ctx -> (RAssign Name ctx -> b) -> NMb ctx b
nuMultiN tps f = NMb
  { _nmbNames = tps
  , _nmbBinding = nuMulti (mapRAssign (const Proxy) tps) f
  }

-- | Named version of 'nuMultiWithElem1'
nuMultiWithElim1N :: (RAssign Name ctx -> arg -> b) -> NMb ctx arg -> NMb ctx b
nuMultiWithElim1N = over nmbBinding . nuMultiWithElim1

-- | Named version of 'strongMbM'
strongNMbM :: MonadStrongBind m => NMb ctx (m a) -> m (NMb ctx a)
strongNMbM = traverseOf nmbBinding strongMbM

-- | Named version of 'mbM'
nmbM :: (MonadBind m, NuMatching a) => NMb ctx (m a) -> m (NMb ctx a)
nmbM = traverseOf nmbBinding mbM

-- | Named version of 'mbSwap'
nmbSwap :: RAssign Proxy ctx -> NMb ctx' (NMb ctx a) -> NMb ctx (NMb ctx' a)
nmbSwap p (NMb names' body') = NMb names' <$> nmbSink p body'

-- | Variant of 'mbSwap' that works with a mix of 'NMb' and 'Mb'
nmbSink :: RAssign Proxy ctx -> Mb ctx' (NMb ctx a) -> NMb ctx (Mb ctx' a)
nmbSink p m =
    NMb
    { _nmbNames = mbLift (_nmbNames <$> m)
    , _nmbBinding = mbSwap p (_nmbBinding <$> m)
    }

-- | Named version of 'mbLift'
nmbLift :: Liftable a => NMb ctx a -> a
nmbLift = views nmbBinding mbLift

-- | Named version of 'elimEmptyMb'
elimEmptyNMb :: NMb RNil a -> a
elimEmptyNMb = views nmbBinding elimEmptyMb

-- | Named version of 'emptyMb'
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
