{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

{- |
Module      : Language.Lean.AST
Copyright   : Galois, Inc. 2026
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable

Surface-syntax AST for Lean 4. Structured as a near-mirror of
"Language.Rocq.AST"; intentional departures are noted per type.
-}

module Language.Lean.AST where

import Data.String (IsString(..))

-- | An 'Ident' is a Lean qualified identifier represented as a string,
-- with the invariant that it is lexically valid.
-- A valid Lean identifier is a sequence of letters, digits,
-- underscores and primes that starts with a letter or underscore
-- (Unicode letters are also permitted).
-- A /qualified/ identifier is a sequence of one or more identifiers
-- separated by periods.
newtype Ident = Ident String
  deriving (Eq, Ord)

instance Show Ident where
  show (Ident s) = show s

instance IsString Ident where
  fromString s = Ident s

-- | Lean 4 has 'Prop', universe-polymorphic 'Sort u', and 'Type n'
-- for concrete level @n@. The pretty-printer emits:
--
-- * @Prop@ for 'Prop'
-- * @Sort <ident>@ for 'SortVar'
-- * @Type@ for @TypeLvl 0@
-- * @Type n@ for @TypeLvl n@, n > 0
-- * @Sort (max 1 <ident>)@ for 'SortMax1Var' — used as an inductive
--   /result/ sort when the parameters use @Sort <ident>@, to
--   guarantee the inductive lives strictly above @Prop@ regardless
--   of what the parameter is instantiated to.
data Sort
  = Prop
  | TypeLvl Integer
  | SortVar String
    -- ^ A universe-polymorphic @Sort u@. The 'String' is the
    -- universe-variable name (e.g. @\"u\"@). The surrounding 'Decl'
    -- is expected to declare the variable via its universe-binder
    -- list.
  | SortMax1Var String
    -- ^ @Sort (max 1 u)@ — like 'SortVar' but guaranteed to be at
    -- least @Type 0@, never @Prop@.
  deriving (Show)

-- | Convenience synonym for @TypeLvl 0@ so existing call sites can
-- write 'Lean.Type'.
pattern Type :: Sort
pattern Type = TypeLvl 0

-- | Differences from "Language.Rocq.AST.Term":
--
-- * @Fix@ is omitted. Recursive SAWCore terms are rejected by the
--   translator (mirroring Rocq); a future pass will emit
--   @termination_by@ clauses.
-- * @Scope@ (Rocq notation scopes like @(e)%bits@) is omitted. Lean has
--   no direct analog; user-supplied notation remaps happen via 'Ident'
--   rewriting in the translator.
-- * @ZLit@ is renamed 'IntLit' (Lean calls the type @Int@, not @Z@).
-- * @Ltac@ is renamed 'Tactic' and prints as @by <script>@.
data Term
  = Lambda [Binder] Term
  | Pi [PiBinder] Term
  | Let Ident [Binder] (Maybe Type) Term Term
  | If Term Term Term
  | App Term [Term]
  | Sort Sort
  | Var Ident
    -- | A variable printed with a leading @\@@ to force all implicit
    -- arguments to be supplied explicitly.
  | ExplVar Ident
    -- | An ascription @(tm : tp)@ of a type to a term.
  | Ascription Term Term
  | NatLit Integer
  | IntLit Integer
  | List [Term]
  | StringLit String
  | Tactic String
  deriving (Show)

-- | Type synonym useful for indicating when a term is used as a type.
type Type = Term

-- | Binder flavor. Lean 4 distinguishes @(x : A)@, @{x : A}@, and
-- @[x : A]@: the last drives typeclass instance search. Strict-
-- implicit @⦃x : A⦄@ can be added when the translator needs it.
data BinderImplicity
  = Implicit
  | Explicit
  | Instance
    -- ^ Square-bracket binder @[x : A]@, triggers instance search at
    -- use sites. Needed when the translator injects 'Inhabited'
    -- hypotheses for SAWCore @isort@ binders.
    deriving (Show)

-- | An 'Ident' with an optional 'Type', which may be explicit or implicit.
-- For use representing the bound variables in 'Lambda's, 'Let's, etc.
data Binder
  = Binder BinderImplicity Ident (Maybe Type)
    deriving (Show)

-- | A 'Type' with an optional 'Ident', which may be explicit or implicit.
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
  { inductiveUniverses    :: [String]
    -- ^ Universe-variable names the inductive parameterizes over.
    -- Empty means monomorphic in @Type 0@.
  , inductiveName         :: Ident
  , inductiveParameters   :: [Binder]
  , inductiveIndices      :: [PiBinder]
  , inductiveSort         :: Sort
  , inductiveConstructors :: [Constructor]
  }
  deriving (Show)

-- | A 'Definition' carries a 'Noncomputable' flag that controls
-- whether the Lean keyword @noncomputable@ is emitted. Lean forbids
-- non-@noncomputable@ defs from invoking an auto-generated
-- @Foo.rec@ recursor, so definitions produced by the SAWCore
-- prelude walker are marked @Noncomputable@ conservatively.
data Noncomputable = Noncomputable | Computable
  deriving (Show, Eq)

-- | Differences from "Language.Rocq.AST.Decl":
--
-- * Rocq @Section@ becomes 'Namespace'. Lean 'section's hoist
--   @variable@s but do not qualify names; Cryptol modules want
--   qualified names, so @namespace@ is the right target.
-- * Rocq @Parameter@ is omitted; use 'Axiom' for unimplemented
--   constants in Lean.
-- * 'Definition' carries a 'Noncomputable' flag (see above).
-- * 'Definition' and 'Axiom' take a list of universe-variable names
--   that the declaration parameterizes over. Empty means
--   monomorphic in @Type 0@ / @Prop@. Non-empty produces Lean's
--   @def foo.{u v} ...@ form.
data Decl
  = Axiom [String] Ident Type
  | Comment String
  | Definition Noncomputable [String] Ident [Binder] (Maybe Type) Term
  | Variable Ident Type
  | InductiveDecl Inductive
  | Namespace Ident [Decl]
  | Snippet String
  deriving (Show)
