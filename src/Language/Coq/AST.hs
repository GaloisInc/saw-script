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
  | Fix Ident [Binder] Term Term
  | Pi [PiBinder] Term
  | Let Ident [Binder] (Maybe Type) Term Term
  | If Term Term Term
  | App Term [Term]
  | Sort Sort
  | Var Ident
  | NatLit Integer
  | ZLit Integer
  | List [Term]
  | StringLit String
  | Scope Term String
  | Ltac String
  deriving (Show)

-- | Type synonym useful for indicating when a term is used as a type.
type Type = Term

data Binder
  = Binder Ident (Maybe Type)
    deriving (Show)

data PiBinder
  = PiBinder (Maybe Ident) Type
    deriving (Show)

-- Because saw-core does not give very helpful access to the parameters and
-- indices, we just follow their style and define the constructor by its fully
-- applied return type.
data Constructor = Constructor
  { constructorName    :: Ident
  , constructorType    :: Term
  }
  deriving (Show)

data Inductive = Inductive
  { inductiveName         :: Ident
  , inductiveParameters   :: [Binder]
  , inductiveIndices      :: [PiBinder]
  , inductiveSort         :: Sort
  , inductiveConstructors :: [Constructor]
  }
  deriving (Show)

data Decl
  = Axiom Ident Type
  | Comment String
  | Definition Ident [Binder] (Maybe Type) Term
  | InductiveDecl Inductive
  | Snippet String
  deriving (Show)
