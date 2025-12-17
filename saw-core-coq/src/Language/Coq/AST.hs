{- |
Module      : Language.Coq.AST
Copyright   : Galois, Inc. 2018
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable
-}

module Language.Coq.AST where

import Data.String (IsString(..))

-- | An 'Ident' is a Coq qualified identifier represented as a string,
-- with the invariant that it is lexically valid.
-- A valid Coq identifier is a sequence of letters, digits,
-- underscores and primes that starts with a letter or underscore.
-- A /qualified/ identifier is a sequence of one or more identifiers
-- separated by periods.
newtype Ident = Ident String
  deriving (Eq, Ord)

instance Show Ident where
  show (Ident s) = show s

instance IsString Ident where
  fromString s = Ident s

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
    -- | A variable that needs to be printed with a leading at sign in order to
    -- make all arguments explicit
  | ExplVar Ident
    -- | A ascription @tm : tp@ of a type to a term
  | Ascription Term Term
  | NatLit Integer
  | ZLit Integer
  | List [Term]
  | StringLit String
  | Scope Term String
  | Ltac String
  deriving (Show)

-- | Type synonym useful for indicating when a term is used as a type.
type Type = Term

-- | Is this a maximally-inserted implicit ("{}") or explicit binder?
data BinderImplicity
  = Implicit
  | Explicit
    deriving (Show)

-- | An 'Ident' with an optional 'Type', which may be explicit or implicit.
-- For use representing the bound variables in 'Lambda's, 'Let's, etc.
data Binder
  = Binder BinderImplicity Ident (Maybe Type)
    deriving (Show)

-- | An 'Type' with an optional 'Ident', which may be explicit or implicit.
-- For use representing arguments in 'Pi' types.
data PiBinder
  = PiBinder BinderImplicity (Maybe Ident) Type
    deriving (Show)

-- Because saw-core does not give very helpful access to the parameters and
-- indices, we just follow their style and define the constructor by its fully
-- applied return type.
data Constructor = Constructor
  { constructorName    :: Ident
  -- ^ NOTE: The constructor name must be an /unqualified/ identifier.
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
  | Parameter Ident Type
  | Variable Ident Type
  | InductiveDecl Inductive
  | Section Ident [Decl]
  | Snippet String
  deriving (Show)
