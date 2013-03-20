{-# LANGUAGE DeriveFunctor,DeriveFoldable,DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module SAWScript.Unify.Goal where

import Control.Applicative
import Control.Arrow
import Control.Monad
import Control.Monad.State
import Control.Monad.Trans.Either
import Data.Monoid
import qualified Data.Foldable as F
import qualified Data.Traversable as T

type Subst t = [(t,t)]
type GState t = (Int,Subst t)

-- Interleave {{{

newtype Interleave a = Interleave
  { runInterleave :: [a]
  } deriving (Show,Functor,F.Foldable,T.Traversable)

instance Monad Interleave where
  return a = Interleave [a]
  m >>= f  = case runInterleave m of
    []    -> mzero
    a:as' -> f a `mplus` (Interleave as' >>= f)

instance MonadPlus Interleave where
  mzero         = Interleave []
  m1 `mplus` m2 = case runInterleave m1 of
    []    -> m2
    a:as' -> Interleave (a : runInterleave rest)
      where rest = m2 `mplus` Interleave as'

fromStream :: Maybe Int -> Maybe Int -> Stream a -> Either [String] [a]
fromStream en rn s = fS en rn $ runInterleave $ runStream s
  where
    fS en rn as = case (en,rn,as) of
      (Just 0,_,_)            -> Left []  -- convention here?
      (_,Just 0,_)            -> Right [] -- if we need zero more results, than we've succeeded (trivially)?
      (_,_,[])                -> Left []  -- if we're out of results, then we've failed, trivially.
      (_,_,e@(Left _) : as')  -> orEither e (fS (pr en) rn as')
      (_,_,e@(Right _) : as') -> orEither e (fS en (pr rn) as')
    pr = fmap pred

orEither :: Either a b -> Either [a] [b] -> Either [a] [b]
orEither x re = case (x,re) of
  (Left e,Left es)   -> Left (e:es)
  (Left e,Right rs)  -> Right rs
  (Right r,Left es)  -> Right [r]
  (Right r,Right rs) -> Right (r:rs)

headInterleave :: Interleave a -> Maybe a
headInterleave i = case runInterleave i of
  []  -> Nothing
  a:_ -> Just a

tailInterleave :: Interleave a -> Maybe (Interleave a)
tailInterleave i = case runInterleave i of
  []    -> Nothing
  _:as' -> Just (Interleave as')

-- }}}

-- Stream {{{

type Stream = EitherT String Interleave
runStream :: Stream a -> Interleave (Either String a)
runStream = runEitherT

instance MonadPlus m => MonadPlus (EitherT e m) where
  mzero = EitherT $ mzero
  (EitherT m1) `mplus` (EitherT m2) = EitherT (m1 `mplus` m2)

firstAnswer :: Stream a -> Maybe a
firstAnswer = fstAns . runInterleave . runEitherT
  where
  fstAns :: [Either String a] -> Maybe a
  fstAns es = case es of
    (Right a):_   -> Just a
    (Left _):rest -> fstAns $ tail rest
    [] -> Nothing

-- }}}

-- Goal {{{

evalGoal :: GoalM t a -> GState t -> Stream a
evalGoal m s = evalStateT (runGoalM m) s

runGoal :: GoalM t a -> GState t -> Stream (a,GState t)
runGoal m s = runStateT (runGoalM m) s

newtype GoalM t a = GoalM { runGoalM :: StateT (GState t) Stream a } deriving (Functor)
type Goal t = GoalM t ()

instance Show (GoalM t a) where
  show g = "<goal>"

instance Monad (GoalM t) where
  return a = GoalM $ return a
  (GoalM m) >>= f = GoalM $ (m >>= runGoalM . f)

  ---- Branch trimming failure
  --fail err = GoalM mzero

  -- Message collecting failure
  fail err = GoalM $ StateT $ const $ EitherT $ Interleave [Left err]

instance MonadPlus (GoalM t) where
  mzero = GoalM $ mzero
  (GoalM m1) `mplus` (GoalM m2) = GoalM (m1 `mplus` m2)

instance Applicative (GoalM t) where
  pure = return
  (<*>) = ap

getsG :: (GState t -> a) -> GoalM t a
getsG = GoalM . gets
getG = GoalM get

putG :: GState t -> Goal t
putG = GoalM . put

modifyG :: (GState t -> GState t) -> Goal t
modifyG = GoalM . modify

-- }}}

