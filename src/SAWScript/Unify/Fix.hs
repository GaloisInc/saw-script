{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module Unify.Fix where

import Data.Foldable
import Data.Traversable

-- Base {{{

newtype Mu f = In (f (Mu f))

out :: Mu f -> f (Mu f)
out (In e) = e

data (f :+: g) e = Inl (f e) | Inr (g e) deriving (Show,Functor,Foldable,Traversable)

infixr :+:

class (Functor sub, Functor sup) => sub :<: sup where
  inj :: sub a -> sup a
  prj :: sup a -> Maybe (sub a)

instance (Functor f) => f :<: f where
  inj = id
  prj = Just

instance (Functor f, Functor g) => f :<: (f :+: g) where
  inj = Inl
  prj cp = case cp of
    Inl e -> Just e
    Inr _ -> Nothing

instance (Functor f, Functor g, Functor h, f :<: g) => f :<: (h :+: g) where
  inj = Inr . inj
  prj cp = case cp of
    Inl e -> Nothing
    Inr e -> prj e

inject :: (f :<: g) => f (Mu g) -> Mu g
inject = In . inj

match :: (g :<: f) => Mu f -> Maybe (g (Mu f))
match (In e) = prj e

foldMu :: Functor f => (f a -> a) -> Mu f -> a
foldMu f (In e) = f (fmap (foldMu f) e)

-- }}}

-- Render {{{

class (Functor f) => Render f where
  render :: Render g => f (Mu g) -> String

instance (Render f, Render g) => Render (f :+: g) where
  render cp = case cp of
    Inl e -> render e
    Inr e -> render e

pretty :: (Render f) => Mu f -> String
pretty (In e) = render e

instance Render f => Show (Mu f) where
  show (In e) = render e

-- }}}

-- Equal {{{

class Equal f where
  equal :: Equal g => f (Mu g) -> f (Mu g) -> Bool

instance (Equal f, Equal g) => Equal (f :+: g) where
  equal cp1 cp2 = case (cp1,cp2) of
    (Inl e1,Inl e2) -> equal e1 e2
    (Inr e1,Inr e2) -> equal e1 e2
    _               -> False

instance (Equal f) => Eq (Mu f) where
  (In e1) == (In e2) = equal e1 e2

-- }}}

