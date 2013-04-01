{-# LANGUAGE TypeOperators #-}
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
import Control.Monad.Trans.Either

import Data.List
import Data.Monoid
import Data.Foldable
import Data.Traversable

import qualified Text.Show.Pretty as PP

-- LSEnv {{{

data LSEnv = LSEnv
  { polyEnv :: [(Name,GoalM LType LType)]
  , monoEnv :: [(Name,LType)]
  } deriving (Show)

polyPair :: Name -> GoalM LType LType -> LSEnv
polyPair n g = LSEnv [(n,g)] []

monoPair :: Name -> LType -> LSEnv
monoPair n t = LSEnv [] [(n,t)]

initLSEnv :: LSEnv
initLSEnv = LSEnv [] []

instance Monoid LSEnv where
  mempty = initLSEnv
  mappend e1 e2 = LSEnv (polyEnv e1 <> polyEnv e2) (monoEnv e1 <> monoEnv e2)

-- }}}

type LS = StateT LSEnv (GoalM LType)
evalLS = flip runStateT initLSEnv

data Lifted = Lifted
  { liftedModule :: Module LType
  , liftedGen    :: Int
  , liftedEnv    :: [(Name,GoalM LType LType)]
  } deriving (Show)

liftPoly :: Compiler (Module MPType) Lifted
liftPoly = compiler "LiftPoly" $ \input ->
  case evalStream $ getStream input of
    Left es   -> fail "No possible lifting"
    Right [r] -> return r
    Right rs  -> fail ("Ambiguous lifting:" ++ PP.ppShow rs)

getStream :: Module MPType -> Stream ((Module LType, LSEnv), (Int, Subst LType))
getStream (Module mname ds mn) = flip runGoal initGState $ evalLS $
  Module mname <$> traverse saveLPoly ds <*> saveLPoly mn

evalStream :: Stream ((Module LType, LSEnv), (Int, Subst LType)) -> Either [String] [Lifted]
evalStream = fromStream Nothing Nothing . fmap getModuleGen

getModuleGen ((m,e),(g,_)) = Lifted m g $ polyEnv e

buildEnv :: TopStmt MPType -> LSEnv
buildEnv t = case t of
  TopTypeDecl n t -> polyPair n $ instantiateType t
  TopBind n e     -> polyPair n $ instantiateExpr e
  _               -> mempty

saveLPoly :: Traversable f => f MPType -> LS (f LType)
saveLPoly = traverse (saveEnv . fillHoles)

fromAll :: Monoid m => (a -> m) -> [a] -> m
fromAll f = mconcat . map f

join2 :: (c -> d -> e) -> (a -> c) -> (b -> d) -> a -> b -> e
join2 op f g x y = (f x) `op` (g y)

class (Traversable f) => LiftPoly f where
  lPoly :: f MPType -> LS (f LType)
  lPoly  = traverse fillHoles

--instance LiftPoly Module where
--  lPoly = traverse (saveEnv . fillHoles)
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
    mt <- gets (lookup n . monoEnv)
    case mt of
      Just t  -> return t
      Nothing -> do
        x <- newLVarLS
        extendEnv n x
        return x
instance Assignable I where
  assign = return . inject

instantiateType :: PType -> GoalM LType LType
instantiateType = fmap fst . evalLS . assignVar

instantiateExpr :: Expr MPType -> GoalM LType LType
instantiateExpr = fmap (typeOf . fst) . evalLS . traverse fillHoles

fillHoles :: MPType -> LS LType
fillHoles mpt = case mpt of
  Nothing -> newLVarLS
  Just pt -> assignVar pt

assignVar :: PType -> LS LType
assignVar = foldMuM assign

newLVarLS :: LS LType
newLVarLS = StateT $ \s -> newLVar >>= \a -> return (a,s)

extendEnv :: Name -> LType -> LS ()
extendEnv n t = modify (monoPair n t <>)

saveEnv :: LS r -> LS r
saveEnv m = do
  s <- get
  a <- m
  put s
  return a

