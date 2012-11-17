{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module SAWScript.FixFunctor where

import Data.List (intercalate)
import Control.Arrow
import Control.Applicative
import Control.Monad
import Data.Foldable
import Data.Traversable
import Data.Monoid

-- Mu & Coproduct {{{1

data Mu f = In (f (Mu f))

foldMu :: Functor f => (f a -> a) -> Mu f -> a
foldMu f (In t) = f (fmap (foldMu f) t)

foldMuM :: (Applicative m, Monad m, Traversable f) => (f a -> m a) -> Mu f -> m a
foldMuM f (In t) = do
  res <- traverse (foldMuM f) t
  f res

test1 :: Mu (Val :+: Add :+: Mul)
test1 = val 1 `add` val 2 `mul` val 3 `add` val 4

infixr 5 `add`
infixr 6 `mul`

infixr :+:

data (f :+: g) e = Inl (f e) | Inr (g e)
  deriving (Eq,Show)

instance (Functor f, Functor g) => Functor (f :+: g) where
  fmap f e = case e of
    Inl a -> Inl $ fmap f a
    Inr a -> Inr $ fmap f a

-- Eval {{{1

class Functor f => Eval f where
  evalAlgebra :: f Int -> Int

instance (Eval f, Eval g) => Eval (f :+: g) where
  evalAlgebra cp = case cp of
    Inl e -> evalAlgebra e
    Inr e -> evalAlgebra e

instance Eval Val where
  evalAlgebra (Val i) = i
instance Eval Add where
  evalAlgebra (Add x y) = x + y
instance Eval Mul where
  evalAlgebra (Mul x y) = x * y

eval :: Eval f => Mu f -> Int
eval = foldMu evalAlgebra

-- EvalM {{{1

class (Monad m, Functor f) => EvalM m f where
  evalAlgM :: f Int -> m Int

instance (Monad m, EvalM m f, EvalM m g) => EvalM m (f :+: g) where
  evalAlgM cp = case cp of
    Inl e -> evalAlgM e
    Inr e -> evalAlgM e

instance (Foldable f, Foldable g) => Foldable (f :+: g) where
  foldMap f cp = case cp of
    Inl e -> foldMap f e
    Inr e -> foldMap f e
instance (Traversable f, Traversable g) => Traversable (f :+: g) where
  traverse f cp = case cp of
    Inl e -> Inl <$> traverse f e
    Inr e -> Inr <$> traverse f e

-- Count {{{1

newtype Count a = Count { runCount :: Int -> (a,Int) }
instance Functor Count where
  fmap f c = Count $ \i -> let (a,i') = runCount c i in (f a,i')
instance Monad Count where
  return a = Count $ \i -> (a,i)
  m >>= f  = Count $ \i -> let (a,i') = runCount m i in runCount (f a) i'
instance Applicative Count where
  pure = return
  (<*>) = ap

tick :: Count ()
tick = Count $ \i -> ((),i+1)

instance EvalM Count Val where
  evalAlgM (Val i) = tick >> return i
instance EvalM Count Add where
  evalAlgM (Add x y) = return (x + y)
instance EvalM Count Mul where
  evalAlgM (Mul x y) = return (x * y)

evalMCount :: (Traversable f, EvalM Count f) => Mu f -> (Int,Int)
evalMCount e = runCount (foldMuM evalAlgM e) 0

-- Wr {{{1

newtype Wr a = Wr (a,String)
instance Functor Wr where
  fmap f (Wr (a,w)) = Wr (f a,w)
instance Monad Wr where
  return a = Wr (a,"")
  (Wr (a,w)) >>= f = let Wr (a',w') = f a in Wr (a',w++w')
instance Applicative Wr where
  pure = return
  (<*>) = ap

tell :: String -> Wr ()
tell s = Wr ((),s)

instance EvalM Wr Val where
  evalAlgM (Val i) = tell ("saw " ++ show i ++ "\n") >> return i
instance EvalM Wr Add where
  evalAlgM (Add x y) = tell ("adding " ++ show x ++ " and " ++ show y ++ "\n") >> return (x + y)
instance EvalM Wr Mul where
  evalAlgM (Mul x y) = tell ("multiplying " ++ show x ++ " and " ++ show y ++ "\n") >> return (x * y)

evalMWr :: (Traversable f, EvalM Wr f) => Mu f -> IO Int
evalMWr e = do
  let Wr (a,w) = foldMuM evalAlgM e
  putStrLn w
  return a

-- }}}
-- Arith {{{1

data Val a = Val Int deriving Show
data Add a = Add a a deriving Show
data Mul a = Mul a a deriving Show

instance Functor Val where
  fmap f (Val i) = Val i
instance Functor Add where
  fmap f (Add x y) = Add (f x) (f y)
instance Functor Mul where
  fmap f (Mul x y) = Mul (f x) (f y)

-- Required for Traversable
instance Foldable Val where
  foldMap f (Val i) = mempty
instance Foldable Add where
  foldMap f (Add x y) = f x <> f y
instance Foldable Mul where
  foldMap f (Mul x y) = f x <> f y

instance Traversable Val where
  traverse f (Val i) = pure $ Val i
instance Traversable Add where
  traverse f (Add x y) = Add <$> f x <*> f y
instance Traversable Mul where
  traverse f (Mul x y) = Mul <$> f x <*> f y

-- Injection {{{1

class (Functor sub, Functor sup) => sub :<: sup where
  inj :: sub a -> sup a
  prj :: sup a -> Maybe (sub a)

    -- Reflexive case
instance Functor f => f :<: f where
  inj = id
  prj = Just

-- Base case, f is at head
instance (Functor f, Functor g) => f :<: (f :+: g) where
  inj = Inl
  prj cp = case cp of
    Inl e -> Just e
    Inr _ -> Nothing

-- Inductive case, f is somewhere in tail
instance (Functor f, Functor g, Functor h, f :<: g) =>  f :<: (h :+: g) where
  inj = Inr . inj
  prj cp = case cp of
    Inl _ -> Nothing
    Inr e -> prj e

inject :: (g :<: f) => g (Mu f) -> Mu f
inject = In . inj

{-

class (Functor f, Functor g) => f :=>: g where
  reinject :: Mu f -> Mu g

instance (Functor f) => f :=>: f where
  reinject = id

instance (f :<: g) => f :=>: g where
  reinject = foldMu inject

instance (f :<: h, g :=>: h) => (f :+: g) :=>: h where
  reinject (In cp) = case cp of
    Inl e -> inject $ fmap reinject e
    Inr e -> reinject e

-}

-- Render {{{1

instance Render Val where
  render (Val i) = show i
instance Render Add where
  render (Add x y) = "(" ++ show x ++ " + " ++ show y ++ ")"
instance Render Mul where
  render (Mul x y) = "(" ++ show x ++ " * " ++ show y ++ ")"

class Render f where
  render :: Render g => f (Mu g) -> String

instance (Render f, Render g) => Render (f :+: g) where
  render cp = case cp of
    Inl x -> render x
    Inr y -> render y

instance Render f => Show (Mu f) where
  show (In t) = render t

-- Operators {{{1

val :: (Val :<: f) => Int -> Mu f
val x = inject $ Val x
add :: (Add :<: f) => Mu f -> Mu f -> Mu f
add x y = inject $ Add x y
mul :: (Mul :<: f) => Mu f -> Mu f -> Mu f
mul x y = inject $ Mul x y

-- }}}

