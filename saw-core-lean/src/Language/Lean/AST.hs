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
import Numeric.Natural (Natural)

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
data Sort
  = Prop
  | TypeLvl Integer
  | TypeVar String
    -- ^ A universe-polymorphic @Type u@. This is syntactic sugar
    -- for @Sort (u+1)@ and is used when the translator deliberately
    -- restricts a SAWCore carrier binder to Lean's value universe so
    -- @Except String α@ is well-formed.
  | SortVar String
    -- ^ A universe-polymorphic @Sort u@. The 'String' is the
    -- universe-variable name (e.g. @\"u\"@). The surrounding 'Decl'
    -- is expected to declare the variable via its universe-binder
    -- list.
  deriving (Show)

-- | Convenience synonym for @TypeLvl 0@ so existing call sites can
-- write 'Lean.Type'.
pattern Type :: Sort
pattern Type = TypeLvl 0

-- | A universe level — emitted explicitly at call sites for
-- universe-polymorphic targets (@\@Foo.{u, v}@). Per the
-- 'mathport' pattern, we never emit bare @\@Foo@ for a
-- universe-poly target and rely on Lean inference; explicit
-- levels sidestep Lean issue #2297 and the universe-unification
-- gaps that motivated the parked P4 work.
data UnivLevel
  = LevelVar String      -- ^ A universe variable name in scope: @u@
  | LevelLit Natural     -- ^ A concrete level: @0@, @1@, …
  | LevelSucc UnivLevel  -- ^ @u + 1@
  | LevelMax [UnivLevel] -- ^ @max u v w@; used for inductive return
                         --   sorts and any callsite where a level
                         --   comes from a join
  deriving (Show)

-- | Differences from "Language.Rocq.AST.Term":
--
-- * @Fix@ is omitted. Recursive SAWCore terms are rejected by the
--   translator (mirroring Rocq); a future pass will emit
--   @termination_by@ clauses.
-- * @Scope@ (Rocq notation scopes like @(e)%bits@) is omitted. Lean has
--   no direct analog; user-supplied notation remaps happen via 'Ident'
--   rewriting in the translator.
-- * @ZLit@ is renamed 'IntLit' (Lean calls the type @Int@, not @Z@).
data Term
  = Lambda [Binder] Term
  | Pi [PiBinder] Term
  | Let Ident [Binder] (Maybe Type) Term Term
  | App Term [Term]
  | Sort Sort
  | Var Ident
    -- | A variable printed with a leading @\@@ to force all implicit
    -- arguments to be supplied explicitly.
  | ExplVar Ident
    -- | A reference to a universe-polymorphic constant with its
    -- universe levels supplied explicitly: @\@Foo.{u, v}@.
    -- Per-binder fresh universes + explicit-call-site levels are
    -- the post-P4 emission strategy that makes the auto-emitted
    -- prelude elaborate without depending on Lean's universe
    -- unifier (Lean issue #2297). The list order matches the
    -- callee's declared universe-binder order.
  | ExplVarUniv Ident [UnivLevel]
    -- | An ascription @(tm : tp)@ of a type to a term.
  | Ascription Term Term
  | NatLit Integer
  | IntLit Integer
  | List [Term]
  | StringLit String
    -- | A Lean tactic expression: pretty-prints as @(by \<s\>)@,
    -- where @s@ is the verbatim tactic source. Used for generated
    -- proof placeholders and optional proof attempts in emitted
    -- obligations. Mirrors Rocq's @Ltac@ constructor.
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
  | Definition Noncomputable [String] Ident [Binder] (Maybe Type) Term
  | InductiveDecl Inductive
  | Namespace Ident [Decl]
  deriving (Show)
