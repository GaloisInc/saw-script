{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}

module SAWScript.LiftPoly where

import SAWScript.AST
import SAWScript.Unify

import Prelude hiding (mapM)
import Control.Applicative
import Control.Arrow
import Control.Monad
import Control.Monad.Trans.State

import Data.Foldable
import Data.Traversable

type LS = StateT [(Name,LType)] (GoalM LType)

runLS = runStateT

liftState :: (Monad m) => m a -> StateT s m a
liftState m = StateT $ \s -> m >>= \a -> return (a,s)

evalLS :: Show a => LS a -> (a,Int)
evalLS m = case stream of
  [a] -> a
  _   -> error ("what happened? evalLS got " ++ show stream)
  where
    goal = runStateT m []
    res = runGoalM goal initGState
    stream = takeInterleave Nothing $ fmap ((fst >>> fst) &&& (snd >>> fst)) res

type ModuleGen = (Module LType,Int)

liftPoly :: Module MPType -> ModuleGen
liftPoly m = evalLS (lPoly m)

fillHoles :: MPType -> LS LType
fillHoles mpt = case mpt of
  Nothing -> liftState newLVar
  Just pt -> assignVar pt

class (Functor f, Traversable f) => LiftPoly f where
  lPoly :: f MPType -> LS (f LType)
  lPoly  = traverse fillHoles

instance LiftPoly Module where
  lPoly = traverse (saveEnv . fillHoles)
instance LiftPoly TopStmt
instance LiftPoly (BlockStmt Context)
instance LiftPoly Expr

class (Functor f, Traversable f) => Assignable f where
  assign :: f LType -> LS LType

instance (Assignable f, Assignable g) => Assignable (f :+: g) where
  assign cp = case cp of
   Inl e -> assign e 
   Inr e -> assign e 
instance Assignable Type where
  assign = return . inject
instance Assignable Poly where
  assign (Poly n) = do
    mi <- gets (lookup n)
    case mi of
      Just x  -> return x
      Nothing -> do
        x <- liftState newLVar
        extendEnv n x
        return x

assignVar :: PType -> LS LType
assignVar = foldMuM assign

extendEnv :: Name -> LType -> LS ()
extendEnv n x = modify ((n,x):)

saveEnv :: LS r -> LS r
saveEnv m = do
  s <- get
  a <- m
  put s
  return a

