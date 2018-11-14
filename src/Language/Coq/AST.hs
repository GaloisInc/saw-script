{- |
Module      : Language.Coq.AST
Copyright   : Galois, Inc. 2018
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable
-}

module Language.Coq.AST where

type Ident = String

data Sort
  = Prop
  | Set
  | Type
    deriving (Show)

data Term
  = Lambda [Binder] Term
  | Pi [PiBinder] Term
  | Let Ident [Binder] (Maybe Type) Term Term
  | If Term Term Term
  | App Term [Term]
  | Sort Sort
  | Var Ident
  | NatLit Integer
  | List [Term]
    deriving (Show)

-- | Type synonym useful for indicating when a term is used as a type.
type Type = Term

data Binder
  = Binder Ident (Maybe Type)
    deriving (Show)

data PiBinder
  = PiBinder (Maybe Ident) Type
    deriving (Show)

data Decl
  = Definition Ident [Binder] (Maybe Type) Term
  deriving (Show)
