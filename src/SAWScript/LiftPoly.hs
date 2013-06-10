{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}

module SAWScript.LiftPoly where

import SAWScript.Compiler

import SAWScript.AST
import SAWScript.Unify

import Prelude hiding (mapM)
import Control.Applicative
import Control.Monad.Trans.State

import Data.Monoid
import Data.Traversable

import qualified Text.Show.Pretty as PP

-- LSEnv {{{

data LSEnv = LSEnv
  { polyEnv :: [(Name,GoalM TCheckT TCheckT)]
  , monoEnv :: [(Name,TCheckT)]
  } deriving (Show)

polyPair :: Name -> GoalM TCheckT TCheckT -> LSEnv
polyPair n g = LSEnv [(n,g)] []

monoPair :: Name -> TCheckT -> LSEnv
monoPair n t = LSEnv [] [(n,t)]

initLSEnv :: LSEnv
initLSEnv = LSEnv [] []

instance Monoid LSEnv where
  mempty = initLSEnv
  mappend e1 e2 = LSEnv (polyEnv e1 <> polyEnv e2) (monoEnv e1 <> monoEnv e2)

-- }}}

type LS = StateT LSEnv (GoalM TCheckT)

evalLS :: LS a -> GoalM TCheckT (a, LSEnv)
evalLS = flip runStateT initLSEnv

data Lifted = Lifted
  { liftedModule :: ModuleSimple TCheckT TCheckT
  , liftedGen    :: Int
  , liftedEnv    :: [(Name,GoalM TCheckT TCheckT)]
  } deriving (Show)

liftPoly :: Compiler (ModuleSimple ResolvedT ResolvedT) Lifted
liftPoly = compiler "LiftPoly" $ \input ->
  case evalStream $ getStream input of
    Left es   -> fail "No possible lifting"
    Right [r] -> return r
    Right rs  -> fail ("Ambiguous lifting:" ++ PP.ppShow rs)

getStream :: ModuleSimple ResolvedT ResolvedT -> Stream ((ModuleSimple TCheckT TCheckT, LSEnv), (Int, Subst TCheckT))
getStream (Module nm ee te ds) = flip runGoal initGState $ evalLS $
  Module nm <$> traverse saveLPoly ee <*> saveLPoly te <*> pure ds

evalStream :: Stream ((ModuleSimple TCheckT TCheckT, LSEnv), (Int, Subst TCheckT)) -> Either [String] [Lifted]
evalStream = fromStream Nothing Nothing . fmap getModuleGen

getModuleGen :: ((ModuleSimple TCheckT TCheckT, LSEnv), (Int, Subst TCheckT)) -> Lifted
getModuleGen ((m,e),(g,_)) = Lifted m g $ polyEnv e

saveLPoly :: Traversable f => f ResolvedT -> LS (f TCheckT)
saveLPoly = traverse (saveEnv . fillHoles)

fromAll :: Monoid m => (a -> m) -> [a] -> m
fromAll f = mconcat . map f

join2 :: (c -> d -> e) -> (a -> c) -> (b -> d) -> a -> b -> e
join2 op f g x y = (f x) `op` (g y)

class (Traversable f) => LiftPoly f where
  lPoly :: f ResolvedT -> LS (f TCheckT)
  lPoly  = traverse fillHoles

--instance LiftPoly ModuleSimple where
--  lPoly = traverse (saveEnv . fillHoles)
instance LiftPoly TopStmtSimple
instance LiftPoly BlockStmtSimple
instance LiftPoly ExprSimple

class (Functor f, Traversable f) => Assignable f where
  assign :: f TCheckT -> LS TCheckT

instance (Assignable f, Assignable g) => Assignable (f :+: g) where
  assign cp = case cp of
   Inl e -> assign e 
   Inr e -> assign e 

instance Assignable Poly where
  assign p = case p of
    PVar n -> do
      mt <- gets (lookup n . monoEnv)
      case mt of
        Just t  -> return t
        Nothing -> do
          x <- newLVarLS
          extendEnv n x
          return x
    PAbs ns t -> return $ pAbs ns t

instance Assignable TypeF where
  assign = return . inject

instance Assignable I where
  assign = return . inject

instance Assignable ContextF where
  assign = return . inject

fillHoles :: ResolvedT -> LS TCheckT
fillHoles mpt = case mpt of
  Nothing -> newLVarLS
  Just pt -> assignVar pt

assignVar :: FullT -> LS TCheckT
assignVar = foldMuM assign

newLVarLS :: LS TCheckT
newLVarLS = StateT $ \s -> newLVar >>= \a -> return (a,s)

extendEnv :: Name -> TCheckT -> LS ()
extendEnv n t = modify (monoPair n t <>)

saveEnv :: LS r -> LS r
saveEnv m = do
  s <- get
  a <- m
  put s
  return a

