{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module Unify.Ops where

import Unify.Fix
import Unify.Goal
import Unify.Unify
import Unify.Fresh

import Control.Monad
import Control.Monad.Trans.State
import Control.Monad.Trans.Either
import qualified Data.Foldable as F
import qualified Data.Traversable as T

import GHC.TypeLits

conj :: [Goal t] -> Goal t
conj = sequence_

disj :: [Goal t] -> Goal t
disj = msum

anyo :: Unifiable f => Goal (Mu f) -> Goal (Mu f)
anyo g = disj [ g , anyo g ]

onceo :: Unifiable f => Goal (Mu f) -> Goal (Mu f)
onceo g = GoalM $ StateT $ \s ->
  let (EitherT (Interleave ss)) = runStateT (runGoalM g) s in
    case ss of
      [] -> EitherT $ Interleave []
      a:_ -> EitherT $ Interleave [a]

(===) :: Unifiable f => Mu f -> Mu f -> Goal (Mu f)
(===) = unify

