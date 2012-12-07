{-# LANGUAGE TypeOperators #-}

module SAWScript.GroundType where

import SAWScript.AST
import SAWScript.Unify

import Data.List
import Data.Traversable

groundType :: Module LType -> Either String (Module CType)
groundType m = case traverse (foldMuM gType) m of
  Left e   -> Left (intercalate "\n" ["GroundType:" , ("  " ++ e) , show m])
  Right m' -> Right m'

class Functor f => Groundable f where
  gType :: f CType -> Either String CType

instance (Groundable f, Groundable g) => Groundable (f :+: g) where
  gType cp = case cp of
    Inl e -> gType e
    Inr e -> gType e

instance Groundable Logic where
  gType x = Left ("non-ground type: " ++ render x)

instance Groundable Type where
  gType = Right . inject

