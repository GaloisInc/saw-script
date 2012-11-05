module Unification where

import qualified Data.List as List
import Data.Foldable
import Data.Traversable
import Data.Monoid      ( mempty, mappend )
import Control.Applicative

import SAWScript.AST

instance Foldable Expr where
  foldMap f (Var _ a) =
    f a

  foldMap f (Pattern _ a) =
    f a

  foldMap f (Func _ _ e a) =
    (foldMap f e) `mappend` (f a)

  foldMap f (App e1 e2 a) =
    (foldMap f e1) `mappend` (foldMap f e2) `mappend` (f a)

  foldMap f (Switch e es a) =
    (foldMap f e) `mappend` (List.foldl foldCase mempty es) `mappend` (f a)
    where
      foldCase acc (guard, expr) = acc `mappend` (foldMap f guard) `mappend` (foldMap f expr)

  foldMap f (DM es a) =
    (List.foldl foldElem mempty es) `mappend` (f a)
    where
      foldElem acc (_,expr) = acc `mappend` (foldMap f expr)

module Unification2 where

import SAWScript.AST
import Data.Map

data SAWType =
  | TypeVariable String
  | Atom Name SAWType
  | BitField [Integer]
  | DirectedMultiset (Set SAWType)
  | Arrow ArrowType [SAWType] SAWType

type Context = Map String SAWType

freshTypeVariable :: Context -> 
frashTypeVariable ctxt = 
  let names = "'":[name++[c] | name <- names, c <- ['A'..'Z']]
      taken = snd . unzip . assocs $ ctxt
  take . (dropWhile (\v -> elem v taken)) . (drop 1) $ names

appendTypes :: Expr TypeAnnotation -> Expr SAWType
appendTypes