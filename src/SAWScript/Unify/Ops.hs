{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module SAWScript.Unify.Ops where

import SAWScript.Unify.Fix
import SAWScript.Unify.Goal
import SAWScript.Unify.Unification

import Control.Monad
import Control.Monad.State
import Control.Monad.Trans.Either

conj :: [Goal t] -> Goal t
conj = sequence_

disj :: [Goal t] -> Goal t
disj = msum

anyo :: Unifiable f => Goal (Mu f) -> Goal (Mu f)
anyo g = disj [ g , anyo g ]

(===) :: Unifiable f => Mu f -> Mu f -> Goal (Mu f)
(===) = unify

onceo :: Unifiable f => Goal (Mu f) -> Goal (Mu f)
onceo g = GoalM $ StateT $ \s ->
  case firstAnswer $ runStateT (runGoalM g) s of
    Nothing -> EitherT $ mzero
    Just a  -> EitherT $ return (Right a)

