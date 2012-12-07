{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}

module SAWScript.Unify.Fresh where

import SAWScript.Unify.Fix
import SAWScript.Unify.Goal
import SAWScript.Unify.Unification

import Control.Monad

class Freshable s t | s -> t where
  fresh :: s -> Goal t

instance (Unifiable f) => Freshable (Goal (Mu f)) (Mu f) where
  fresh = id

instance (Unifiable f, Freshable s (Mu f)) => Freshable (Mu f -> s) (Mu f) where
  fresh f = newLVar >>= fresh . f

