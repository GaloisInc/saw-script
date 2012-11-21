{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}

module SAWScript.TypeCheck where

import SAWScript.AST
import SAWScript.FixFunctor

import Control.Monad
import Data.Maybe (fromMaybe)

type Subst a = [(a,a)]
type Unify f = Subst f -> FL (Subst f)

-- Goal {{{

newtype GoalM f a = GoalM { runGoalM :: Subst f -> FL (a,Subst f) }
type Goal f = GoalM f ()

instance Functor (GoalM f) where
  fmap f g = GoalM $ \s ->
    let (as,ss) = unzipList $ runGoalM g s in
      zipList (map f as) ss

instance Monad (GoalM f) where
  return a = GoalM $ \s -> return (a,s)
  m >>= f  = GoalM $ \s ->
    let (as,ss) = unzipList $ runGoalM m s in
      msum $ zipWith (runGoalM . f) as ss

instance MonadPlus (GoalM f) where
  mzero = GoalM $ \s -> mzero
  mplus m1 m2 = GoalM $ \s ->
    let p1 = runGoalM m1 s
        p2 = runGoalM m2 s in
      mplus p1 p2

-- }}}

-- Fair List Interleaving {{{

newtype FL a = FL [a] deriving Show

instance Functor FL where
  fmap f (FL as) = FL $ map f as

instance Monad FL where
  return a = FL [a]
  (>>=)    = (>>-)

instance MonadPlus FL where
  mzero = FL []
  mplus = interleave

interleave :: FL a -> FL a -> FL a
interleave (FL xs) m2 = case xs of
  []    -> m2
  a:xs' -> FL (a : rest)
    where
      (FL rest) = interleave m2 (FL xs')

(>>-) :: FL a -> (a -> FL b) -> FL b
(FL as) >>- f = case as of
  []   -> FL []
  a:as' -> interleave (f a) (FL as' >>- f)

unzipList :: FL (a,b) -> ([a],[b])
unzipList (FL l) = unzip l

zipList :: [a] -> [b] -> FL (a,b)
zipList as bs = FL $ zip as bs

-- }}}
        
-- Unifiable Class {{{

class Eq f => Unifiable f where
  unify :: f -> f -> Unify f

instance (Logic :<: f, Equal f, Uni f) => Unifiable (Mu f) where
  unify u v s = mcond $
    [ guard (u' == v')     :|:        return s
    , isVar u'             :>: \ui -> occursCheck ui v' s
    , isVar v'             :>: \vi -> occursCheck vi u' s
    , Else $                          uni u'' v'' s
    ]
    where
      u'@(In u'') = walk u s
      v'@(In v'') = walk v s

-- Base instances
class Uni f where
  uni :: (Equal g, Logic :<: g, Uni g) => f (Mu g) -> f (Mu g) -> Unify (Mu g)
instance (Uni f, Uni g) => Uni (f :+: g) where
  uni cp1 cp2 s = case (cp1,cp2) of
    (Inl e1,Inl e2) -> uni e1 e2 s
    (Inr e1,Inr e2) -> uni e1 e2 s
    _               -> mzero
instance Uni Logic where
  uni (LVar x) (LVar y) = error "unreachable"

-- User instances
instance Uni Val where
  uni (Val x) (Val y) s = guard (x == y) >> return s
instance Uni Add where
  uni (Add x1 y1) (Add x2 y2) = unify x1 x2 >=> unify y1 y2
instance Uni Mul where
  uni (Mul x1 y1) (Mul x2 y2) = unify x1 x2 >=> unify y1 y2

-- }}}

-- Unification Helpers {{{

runL :: Maybe Int -> GoalM f a -> [Subst f]
runL mn g = let (FL l) = runGoalM g emptyS
                (_,ss) = unzip l in
  case mn of
    Nothing -> ss
    Just n  -> take n ss

occursCheck :: (Logic :<: f, Equal f) => Int -> Mu f -> Unify (Mu f)
occursCheck ui v s = mcond $
  [ isVar v      :>: \vi -> do guard (ui /= vi)
                               extendS ui v s
  , Else          $         extendS ui v s
  ]

--walk :: (Logic :<: f, Equal f) => Mu f -> Subst (Mu f) -> Mu f
walk :: (Unifiable f) => f -> Subst f -> f
walk x s = fromMaybe x $ do
  v <- lookup x s
  return $ walk v s

isVar :: (Logic :<: f) => Mu f -> Maybe Int
isVar x = do
  LVar i <- match x
  return i

extendS :: (Logic :<: f) => Int -> Mu f -> Unify (Mu f)
extendS ui v s = return $ (lVar ui,v):s

emptyS :: Subst f
emptyS = []

reify :: Unifiable f => f -> Subst f -> [f]
reify x s = return $ walk x s

-- }}}

-- mcond {{{

mcond :: (MonadPlus m) => [Case (m a)] -> m a
mcond ms = case ms of
  []              -> mzero
  (Else        m) : _   -> m
  (Just _  :|: m) : _   -> m
  (Nothing :|: m) : ms' -> mcond ms'
  (Just a  :>: f) : _   -> f a
  (Nothing :>: f) : ms' -> mcond ms'

data Case a where
  (:|:) :: Maybe b -> a -> Case a
  (:>:) :: Maybe b -> (b -> a) -> Case a
  Else  :: a -> Case a

-- }}}

-- Tests {{{

type LExpr = Mu (Logic :+: Val :+: Add :+: Mul)

e1,e2 :: LExpr
e1 = lVar 0
e2 = val 5

e3,e4,e5 :: LExpr
e3 = add (lVar 0) (lVar 1)
e4 = add (val 1) (lVar 2)
e5 = mul (val 2) (val 3)

--arr1,arr2 :: LType
--arr1 = array (lVar 0) 4
--arr2 = array z 4
--
--tup1,tup2 :: LType
--tup1 = tuple [lVar 0,bit]
--tup2 = tuple [z,lVar 1]
--
--testArr = unify arr1 arr2 []
--testTup = unify tup1 tup2 []
--testAT1 = unify arr1 tup1 []
--testAT2 = unify arr2 tup2 []
--testAT3 = unify arr1 tup2 []
--testAT4 = unify arr2 tup1 []

-- }}}

-- Goals {{{

(===) :: (Unifiable f) => f -> f -> Goal f
e1 === e2 = mkGoal $ unify e1 e2

conj :: [Goal f] -> Goal f
conj = sequence_

disj :: [Goal f] -> Goal f
disj = msum

mkGoal :: Unify f -> Goal f
mkGoal u = GoalM $ \s -> 
  let ss = u s in
    fmap (\s->((),s)) ss

-- }}}

lpTest1 :: LExpr -> [LExpr]
lpTest1 x = reify x =<<
  (runL Nothing $ conj
     [ lVar 0 === lVar 1
     , lVar 0 === (add (val 1) (lVar 2))
     , lVar 1 === (add (lVar 3) (val 2))
     ])
