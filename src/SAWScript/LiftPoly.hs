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

import Data.List
import Data.Foldable
import Data.Traversable

type LS = StateT [(Name,LType)] (GoalM LType)
runLS = runStateT

type ModuleGen = (Module LType,Int)

liftPoly :: Module MPType -> Err ModuleGen
liftPoly m = case stream of
  Left es   -> Left (intercalate "\n" ("LiftPoly: No possible lifting:" : es))
  Right [r] -> Right r
  Right rs  -> Left (intercalate "\n" ("LiftPoly: Ambiguous lifting:\n" : map show rs))
  where
    goal = runStateT (lPoly m) []
    res = runStateT (runGoalM goal) initGState
    stream = fromStream Nothing Nothing $ fmap ((fst >>> fst) &&& (snd >>> fst)) res

class (Traversable f) => LiftPoly f where
  lPoly :: f MPType -> LS (f LType)
  lPoly  = traverse fillHoles

instance LiftPoly Module where
  lPoly = traverse (saveEnv . fillHoles)
instance LiftPoly TopStmt
instance LiftPoly BlockStmt
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
        x <- newLVarLS
        extendEnv n x
        return x
instance Assignable I where
  assign = return . inject

fillHoles :: MPType -> LS LType
fillHoles mpt = case mpt of
  Nothing -> newLVarLS
  Just pt -> assignVar pt

assignVar :: PType -> LS LType
assignVar = foldMuM assign

newLVarLS :: LS LType
newLVarLS = StateT $ \s -> newLVar >>= \a -> return (a,s)

extendEnv :: Name -> LType -> LS ()
extendEnv n x = modify ((n,x):)

saveEnv :: LS r -> LS r
saveEnv m = do
  s <- get
  a <- m
  put s
  return a

