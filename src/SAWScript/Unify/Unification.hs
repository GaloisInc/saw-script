{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module SAWScript.Unify.Unification where

import SAWScript.Unify.Fix
import SAWScript.Unify.Goal

import Control.Arrow
import Control.Applicative
import Control.Monad
import Data.Monoid
import qualified Data.Foldable as F
import qualified Data.Traversable as T

type Index = Int

type Results a = Either [String] [a]

-- Logic {{{

data Logic a = LV Index deriving (Functor,F.Foldable,T.Traversable)

instance Render Logic where
  render (LV i) = "_." ++ show i

instance Equal Logic where
  equal (LV x) (LV y) = x == y

instance Uni Logic where
  uni _u _v = error "unreachable uni"
  wkS u = return u
  occ ui (LV vi) = return (ui == vi)
  clLV (LV ui) = return [lVar ui]

lVar :: (Logic :<: f) => Index -> Mu f
lVar i = inject $ LV i

newLVar :: Unifiable f => GoalM (Mu f) (Mu f)
newLVar = do
  i <- getGen
  modifyGen (+1)
  return (lVar i)

-- }}}

-- Uni{,fiable} {{{

class (Uni f, Logic :<: f) => Unifiable f
instance (Uni f, Logic :<: f) => Unifiable f

unify :: (Unifiable f) => Mu f -> Mu f -> Goal (Mu f)
unify u v = do
  u'@(In ue) <- walk u
  v'@(In ve) <- walk v
  mcond $
    [ guard (u' == v') :|:        succeed
    , isVar u'         :>: \ui -> occursCheck ui v' >>= \b -> assert (not b) (cycleErr (show u') (show v')) >> extendS ui v'
    , isVar v'         :>: \vi -> occursCheck vi u' >>= \b -> assert (not b) (cycleErr (show v') (show u')) >> extendS vi u'
    , Else              $         uni ue ve
    ] 

cycleErr :: String -> String -> String
cycleErr u v = concat [ "Unification of " , u, " and ", v, " causes infinite cycle." ]

walkStar :: (Unifiable f) => Mu f -> GoalM (Mu f) (Mu f)
walkStar u = out <$> walk u >>= (In <$>) . wkS

occursCheck :: (Unifiable f) => Index -> Mu f -> GoalM (Mu f) Bool
occursCheck ui v = out <$> walk v >>= occ ui

collectLVars :: (Unifiable f) => Mu f -> GoalM (Mu f) [Mu f]
collectLVars u = out <$> walk u >>= clLV

class (Render f, F.Foldable f, T.Traversable f, Equal f) => Uni f where
  uni :: (Unifiable g) => f (Mu g) -> f (Mu g) -> Goal (Mu g)

  wkS     :: (Unifiable g) => f (Mu g) -> GoalM (Mu g) (f (Mu g))
  wkS     = T.traverse walkStar
  
  occ     :: (Unifiable g) => Index -> f (Mu g) -> GoalM (Mu g) Bool
  occ ui = foldOrM (occursCheck ui)

  clLV    :: (Unifiable g) => f (Mu g) -> GoalM (Mu g) [Mu g]
  clLV e  = foldMapM collectLVars e

instance (Uni f, Uni g) => Uni (f :+: g) where
  uni u v = case (u,v) of
    (Inl e1,Inl e2) -> uni e1 e2
    (Inr e1,Inr e2) -> uni e1 e2
    _               -> fail ("Type mismatch: " ++ render u ++ " =/= " ++ render v)
  wkS cp = case cp of
    Inl e -> Inl <$> wkS e
    Inr e -> Inr <$> wkS e
  occ ui cp = case cp of
    Inl e -> occ ui e
    Inr e -> occ ui e
  clLV cp = case cp of
    Inl e -> clLV e
    Inr e -> clLV e

-- }}}

-- Run abstractions {{{

initGState :: GState (Mu f)
initGState = (0,emptyS)

runS :: (Unifiable f) => Maybe Int -> Maybe Int -> (Mu f -> Goal (Mu f)) -> Results (Subst (Mu f))
runS en rn f = runG en rn $ do
  x <- newLVar
  f x
  getSubst

run :: (Unifiable f) => Maybe Int -> Maybe Int -> (Mu f -> Goal (Mu f)) -> Results (Mu f)
run en rn f = runG en rn $ do
  x <- newLVar
  f x
  walkStar x

runG :: (Unifiable f) => Maybe Int -> Maybe Int -> GoalM (Mu f) a -> Results a
runG en rn g = fromStream en rn $ evalGoal g initGState

-- }}}

-- Substitution abstractions {{{

emptyS :: Subst (Mu f)
emptyS = []

extendS :: Unifiable f => Index -> Mu f -> Goal (Mu f)
extendS ui v = modifySubst ((lVar ui,v):)

-- }}}

-- mcond {{{

mcond :: MonadPlus m => [Case m a] -> m a
mcond cs = case cs of
  [] -> (fail "Ran off the end of mcond expression")
  (Else m) : _          -> m
  (Just _  :|: m) : _   -> m
  (Nothing :|: _) : cs' -> mcond cs'
  (Just a  :>: f) : _   -> f a
  (Nothing :>: _) : cs' -> mcond cs'

data Case m a
  = forall b . (Maybe b) :|: m a
  | forall b . (Maybe b) :>: (b -> m a)
  | Else (m a)

-- }}}

-- Framework {{{

assert :: Unifiable f => Bool -> String -> Goal (Mu f)
assert p err = if p then succeed else fail err

--succeed :: Unifiable f => Goal (Mu f)
succeed :: MonadPlus m => m ()
succeed = return ()

isVar :: Unifiable f => Mu f -> Maybe Index
isVar x = do
  LV i <- match x
  return i

walk :: Unifiable f => Mu f -> GoalM (Mu f) (Mu f)
walk x = do
  mv <- getsSubst $ lookup x
  case mv of
    Just v  -> walk v
    Nothing -> return x

getsGen :: Unifiable f => (Index -> a) -> GoalM (Mu f) a
getsGen f = f <$> getsG fst

getGen :: Unifiable f => GoalM (Mu f) Index
getGen = getsGen id

modifyGen :: Unifiable f => (Index -> Index) -> Goal (Mu f)
modifyGen = modifyG . first

getsSubst :: Unifiable f => (Subst (Mu f) -> a) -> GoalM (Mu f) a
getsSubst f = f <$> getsG snd

getSubst :: Unifiable f => GoalM (Mu f) (Subst (Mu f))
getSubst = getsSubst id

modifySubst :: Unifiable f => (Subst (Mu f) -> Subst (Mu f)) -> Goal (Mu f)
modifySubst = modifyG . second

-- }}}

-- Helpers {{{

foldMapM :: (F.Foldable t, Monad m, Monoid n) => (a -> m n) -> t a -> m n
foldMapM f = F.foldrM (\a n -> f a >>= return . mappend n) mempty

foldOrM :: (F.Foldable t, Monad m) => (a -> m Bool) -> t a -> m Bool
foldOrM f = F.foldrM (\a n -> f a >>= return . (||) n) False

zipWithMP :: (MonadPlus m, Show a, Show b) => (a -> b -> m c) -> [a] -> [b] -> m [c]
zipWithMP f as bs = case (as,bs) of
  ([],[])       -> return []
  ([],_)        -> fail ("Length mismatch: " ++ show as ++ " and " ++ show bs)
  (_,[])        -> fail ("Length mismatch: " ++ show as ++ " and " ++ show bs)
  (a:as',b:bs') -> do c <- f a b
                      rest <- zipWithMP f as' bs'
                      return (c:rest)

zipWithMP_ :: (MonadPlus m, Show a, Show b) => (a -> b -> m c) -> [a] -> [b] -> m ()
zipWithMP_ f as bs = zipWithMP f as bs >> return ()

-- }}}

