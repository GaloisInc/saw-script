
{- |
Module      : Language.Rocq.AST
Description : AST definition for Rocq exporter
License     : BSD3
Maintainer  : saw@galois.com

This module declares a (simplified) Rocq/Gallina AST for the back end
of the Rocq exporter.
-}

module Language.Rocq.AST (
    Ident(..),
    Sort(..),
    Term(..),
    Type,
    BinderImplicity(..),
    Binder(..),
    PiBinder(..),
    Constructor(..),
    Inductive(..),
    Decl(..)
  ) where

import Data.String (IsString(..))

-- | An 'Ident' is a Rocq qualified identifier represented as a
--   string, with the invariant that it is lexically valid.
--
--   A valid Rocq identifier is a sequence of letters, digits,
--   underscores and primes that starts with a letter or underscore.
--
--   A /qualified/ identifier is a sequence of one or more identifiers
--   separated by periods.
--
--   We don't enforce the distinction between qualified and unqualified
--   identifiers in this representation.
--
newtype Ident = Ident String
  deriving (Eq, Ord)

instance Show Ident where
  show (Ident s) = show s

instance IsString Ident where
  fromString s = Ident s

-- | Type to hold universes
--
data Sort
  = Prop
  | Set
  | Type
  deriving (Show)

-- | Type to hold Gallina expressions
--
data Term

    -- | fun x => e
  = Lambda [Binder] Term

    -- | Fix f x : ty := e
  | Fix Ident [Binder] Type Term

    -- | forall x, e
  | Pi [PiBinder] Term

    -- | let f arg [: ty] := e in e
  | Let Ident [Binder] (Maybe Type) Term Term

    -- | if e then e else e
  | If Term Term Term

    -- | f args
  | App Term [Term]

    -- | Prop or Type
  | Sort Sort

   -- | x
  | Var Ident
  
    -- | @x, that is, Var with @ in order to explicitly apply implicit
    --   arguments.
  | ExplVar Ident

    -- | Type annotation e: ty
  | Ascription Term Type

    -- | integer constant in nat
  | NatLit Integer
  
    -- | integer constant in Z
  | ZLit Integer

    -- | [e1; e2; ...]
  | List [Term]

    -- | "foo"
  | StringLit String

    -- | e%scope
  | Scope Term String

    -- | Expression-level ltac invocation ltac:(text)
  | Ltac String

  deriving (Show)

-- | Type synonym useful for indicating when a term is used as a type.
type Type = Term

-- | Is this a maximally-inserted implicit ("{}") or explicit binder?
data BinderImplicity
  = Implicit
  | Explicit
    deriving (Show)

-- | Bound variable in a `Lambda` or `Let`, optionally with type
data Binder
  = Binder BinderImplicity Ident (Maybe Type)
    deriving (Show)

-- | Bound variable in a `Pi` (forall), optionally with a name
data PiBinder
  = PiBinder BinderImplicity (Maybe Ident) Type
    deriving (Show)

-- | Single constructor declaration in an inductive type declaration.
--
--   Because saw-core does not give very helpful access to the parameters and
--   indices, we just follow that style and define the constructor by its fully
--   applied return type.
--
--   NOTE: constructor names must be unqualified.
--
data Constructor = Constructor
  { constructorName    :: Ident
  , constructorType    :: Type
  }
  deriving (Show)

-- | Inductive type declaration
--
data Inductive = Inductive
  { inductiveName         :: Ident
  , inductiveParameters   :: [Binder]
  , inductiveIndices      :: [PiBinder]
  , inductiveSort         :: Sort
  , inductiveConstructors :: [Constructor]
  }
  deriving (Show)

-- | Arbitrary top-level declaration.
--
--   Does not support modules or functors.
--
--   `Snippet` inserts raw text, presumably for things this AST can't
--   represent. XXX: probably shouldn't need that
--
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
