{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}

module SAWScript.LiftPoly where

import SAWScript.Compiler

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

import qualified Text.Show.Pretty as PP

type LS = StateT [(Name,LType)] (GoalM LType)
runLS = runStateT

liftPoly :: Compiler (Module MPType) (Module LType,Int)
liftPoly = compiler "LiftPoly" $ \input ->
  case getStream $ runGoal $ getGoal input of
    Left es   -> fail "No possible lifting"
    Right [r] -> return r
    Right rs  -> fail ("Ambiguous lifting:" ++ PP.ppShow rs)
  where
  getGoal = flip runStateT [] . lPoly
  runGoal = flip runStateT initGState . runGoalM
  getStream = fromStream Nothing Nothing . fmap getModuleGen
  getModuleGen = (fst >>> fst) &&& (snd >>> fst)

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
instance Assignable TypeF where
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

