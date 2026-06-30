{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

{- |
Module      : SAWCoreLean.Monad
Copyright   : Galois, Inc. 2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : portable

Near-mirror of "SAWCoreRocq.Monad". Drops Rocq-specific config fields
(@vectorModule@, @monadicTranslation@, @postPreamble@) since Lean has
native 'BitVec'/'Vector' and no free-monad encoding is needed yet.
-}

module SAWCoreLean.Monad
  ( TranslationConfiguration(..)
  , TranslationConfigurationMonad
  , TranslationMonad
  , TranslationError(..)
  , WithTranslationConfiguration(..)
  , runTranslationMonad
  , ppTranslationError
  ) where

import qualified Control.Monad.Except as Except
import Control.Monad.Reader (MonadReader, ReaderT(..))
import Control.Monad.State (MonadState, StateT(..))
import Data.Text (Text)
import Prelude hiding (fail)

import Prettyprinter ((<+>))

import qualified Data.Text as Text
import qualified SAWSupport.Pretty as PPS
import SAWCore.SharedTerm

data TranslationError
    -- | A SAWCore term form the translator does not yet handle
    --   (typically: a hand-constructed @parse_core@ term using a
    --   primitive without dispatch coverage). User-visible.
  = NotSupported Term
    -- | Expected an expression-level term, got a type-level one.
    --   Translator-internal contract violation; no live emission
    --   path produces this on user input.
  | NotExpr Term
    -- | Expected a type-level term, got an expression-level one.
    --   Translator-internal contract violation; no live emission
    --   path produces this on user input.
  | NotType Term
    -- | Free SAWCore Variable not bound by any Pi/Lambda in scope.
    --   Triggered by 'llvm_verify'-style goals if 'writeLeanProp'
    --   misses the abstraction step (Exporter.hs). Hard to provoke
    --   from a focused test without reproducing the full Crucible
    --   pipeline.
  | LocalVarOutOfBounds Term
    -- | A SAWCore structural invariant the translator depends on
    --   was violated. Translator-internal; no live user input
    --   produces this — SAWCore's typechecker rejects upstream.
  | BadTerm Term
    -- | Couldn't synthesize an Inhabited witness for a type that
    --   reaches the L-17 'error.{u}' inhabitedness emitter.
    --   Triggerable in principle by exotic types but no live
    --   driver currently exercises it.
  | CannotCreateDefaultValue Term
    -- | A 'UseMacro' treatment for the given identifier expected at
    --   least @n@ arguments but was supplied with fewer.
    --
    --   This is reachable for the small set of near-syntactic macro
    --   entries that consume raw constructor/index arguments (for
    --   example Nat/Pos helper constructors). Surfacing the arity
    --   error is preferable to emitting a partial macro application
    --   whose shape would be meaningless.
  | UnderAppliedMacro Text Int
    -- | A SAWCore @<dt>#rec@ occurrence survived normalization for
    --   a datatype the translator deliberately refuses (Nat, Pos,
    --   Z, AccessibleNat, AccessiblePos). The 'Text' is the
    --   datatype name. Pinned by saw-boundary/{natrec, zrec,
    --   accessible_nat_rec, accessible_pos_rec}.
  | UnsoundRecursor Text
    -- | A SAWCore primitive the translator deliberately rejects
    --   (e.g. 'Prelude.fix', for which we have no sound Lean
    --   transposition under the current arc). The first 'Text' is
    --   the SAWCore identifier; the second is the rejection reason
    --   surfaced to the user. Throwing this at SAW-translation time
    --   is preferable to letting an unmapped reference reach Lean
    --   and surface as an opaque "unknown identifier" error there.
  | RejectedPrimitive Text Text

ppTranslationError :: SharedContext -> TranslationError -> IO Text
ppTranslationError sc err = case err of
  UnderAppliedMacro name n ->
    pure $
      "Under-applied macro: identifier " <> name <>
      " was given fewer arguments than its macro\n" <>
      "treatment requires (needs at least " <> Text.pack (show n) <>
      ").\n" <>
      "\n" <>
      "What this means: a SpecialTreatment 'mapsToMacro' entry for " <> name <>
      " expects the\n" <>
      "term to have at least " <> Text.pack (show n) <>
      " arguments at translation time so it can\n" <>
      "rewrite the call into its Lean form, but the term reached the\n" <>
      "translator partially applied.\n" <>
      "\n" <>
      "Likely causes:\n" <>
      "  - The term was not fully eta-expanded by scNormalizeForLean (rare).\n" <>
      "  - A user wrote a term that mentions " <> name <>
      " in a non-application\n" <>
      "    position (e.g. as an argument).\n" <>
      "\n" <>
      "Workaround: eta-expand the use site, or remove the macro treatment\n" <>
      "(in SAWCoreLean.SpecialTreatment) and bind " <> name <>
      " to a regular Lean def\n" <>
      "instead. The macro form is an optimization for common shapes; the\n" <>
      "regular def form is always available as a fallback."
  UnsoundRecursor dt ->
    pure $
      "Refusing to emit a Lean equivalent of SAWCore's " <> dt <>
      "#rec.\n" <>
      "\n" <>
      "What this means for your Cryptol code:\n" <>
      "  Your term, after specialization, contains a recursor over " <> dt <>
      ".\n" <>
      "  Two failure modes share this gate:\n" <>
      "  * Nat / Pos / Bool — translator maps to Lean's native equivalent,\n" <>
      "    but constructor order differs and emitting the recursor would\n" <>
      "    silently swap branches.\n" <>
      "  * Z / AccessibleNat / AccessiblePos — no Lean-side analog at all;\n" <>
      "    emission would produce an unmapped reference.\n" <>
      "  Translation is refused rather than mistranslate or emit junk.\n" <>
      "\n" <>
      "Likely causes:\n" <>
      "  - A Cryptol def used " <> dt <>
      "-arithmetic in a way that didn't fully specialize\n" <>
      "    (typically: a symbolic Nat / Pos / Z value reaching " <> dt <>
      "#rec).\n" <>
      "  - You called a SAW primitive that uses " <> dt <>
      "-recursion in its body without\n" <>
      "    a SpecialTreatment entry to keep it opaque.\n" <>
      "\n" <>
      "Workarounds:\n" <>
      "  - Refactor to a concrete length / value where possible.\n" <>
      "  - Run dump_lean_residual_primitives on your term to see which " <>
      "SAWCore name reached\n" <>
      "    " <> dt <> "#rec; if it has no SpecialTreatment yet, that's " <>
      "the entry to add.\n" <>
      "  - Contributor-side: extend leanOpaqueBuiltins (in " <>
      "SAWCentral.Prover.Exporter) so the\n" <>
      "    referring definition stays opaque, or supply a handwritten " <>
      "recursor wrapper."
  RejectedPrimitive name reason ->
    pure $
      "Refusing to translate primitive " <> name <> ".\n" <>
      "\n" <>
      "Reason: " <> reason <> "\n" <>
      "\n" <>
      "This is a deliberate translator-level rejection — the Lean " <>
      "backend doesn't have a sound\n" <>
      "transposition for this primitive yet. If your Cryptol code " <>
      "specialised down to it,\n" <>
      "you've hit one of the open cases tracked in the long-term " <>
      "plan.\n" <>
      "\n" <>
      "Workaround: refactor to avoid the primitive (e.g. recursion " <>
      "via `fix` can sometimes\n" <>
      "be expressed as a bounded fold instead). Run " <>
      "dump_lean_residual_primitives on your\n" <>
      "term to see all surviving names — " <> name <>
      " will be one of them."
  NotSupported t -> ppWithTerm
    ("Translator hit a SAWCore term form it does not yet handle.\n" <>
     "\n" <>
     "What this means: the translator has dispatch arms for every\n" <>
     "SAWCore primitive shape we've seen in real Cryptol. Reaching\n" <>
     "this constructor means a new shape surfaced — typically from a\n" <>
     "hand-constructed `parse_core` term, an SMT-style residual that\n" <>
     "wasn't normalized away, or a recently-added Cryptol primitive.\n" <>
     "\n" <>
     "Workaround: extend SAWCoreLean.Term.translateFTermF (or the\n" <>
     "appropriate sibling) with a case for the offending shape, OR\n" <>
     "skip the term via the `skips` argument to write_lean_term so\n" <>
     "it stays opaque on the Lean side.\n" <>
     "\n" <>
     "The unsupported term:") t
  NotExpr t      -> ppWithTerm
    ("Translator wanted an expression-level term but got a type-level\n" <>
     "one. Should not happen on user input — investigate as a translator\n" <>
     "bug.\n" <>
     "\n" <>
     "The offending term:") t
  NotType t      -> ppWithTerm
    ("Translator wanted a type-level term but got an expression-level\n" <>
     "one. Should not happen on user input — investigate as a translator\n" <>
     "bug.\n" <>
     "\n" <>
     "The offending term:") t
  LocalVarOutOfBounds t -> ppWithTerm
    ("Local variable reference is out of bounds — the term references a\n" <>
     "Variable that no Pi/Lambda in scope binds.\n" <>
     "\n" <>
     "Most common cause: a `llvm_verify` (or other Crucible-driven)\n" <>
     "goal containing free SAWCore Variables introduced by\n" <>
     "`llvm_fresh_var` etc. `writeLeanProp` abstracts those into outer\n" <>
     "Pi binders before translation, so this constructor surfacing on\n" <>
     "an `llvm_verify` goal is a translator bug — please file with the\n" <>
     "term below.\n" <>
     "\n" <>
     "On a `prove_print` over a closed Cryptol lambda, this would mean\n" <>
     "the user term genuinely has free Variables; refactor to bind them\n" <>
     "with `\\x -> ...`.\n" <>
     "\n" <>
     "The offending term:") t
  BadTerm t      -> ppWithTerm
    ("Malformed SAWCore term — a structural invariant the translator\n" <>
     "depends on (e.g. a recognizer pattern matched but the constituent\n" <>
     "shapes were unexpected) was violated.\n" <>
     "\n" <>
     "This is almost always a translator bug: SAWCore's typechecker\n" <>
     "would have rejected an actually-malformed user term upstream.\n" <>
     "Please file with the term below.\n" <>
     "\n" <>
     "The offending term:") t
  CannotCreateDefaultValue t -> ppWithTerm
    ("Translator needed an Inhabited witness for the given type but\n" <>
     "could not synthesize one.\n" <>
     "\n" <>
     "What this means: a translator transformation (typically the\n" <>
     "L-17 `error.{u}` handling, which routes through Lean's\n" <>
     "[Inhabited α] type class) needs a default value for `α`. The\n" <>
     "translator handles common cases (Bool, Nat, Vec, …) directly and\n" <>
     "delegates the rest to Lean's instance search. Reaching this\n" <>
     "error means neither path produced a witness.\n" <>
     "\n" <>
     "Workaround: wrap the type in a sufficiently-monomorphic skeleton\n" <>
     "before translation, or extend the inhabitedness emitter\n" <>
     "(SAWCoreLean.Term, Inhabited-evidence path) to cover the new shape.\n" <>
     "\n" <>
     "The offending type:") t
  where
    ppWithTerm msg tm = do
      ppopts <- scGetPPOpts sc
      tm' <- prettyTerm sc tm
      pure $ PPS.renderText ppopts $ msg <+> tm'

data TranslationConfiguration = TranslationConfiguration
  { constantRenaming :: [(String, String)]
  -- ^ A map from 'ImportedName's of constants to names that should be used to
  -- realize them in Lean; primarily used to map Cryptol operators (@||@, @&&@,
  -- etc.) to nicer names on the Lean side, but works on any imported name.
  , constantSkips :: [String]
  -- ^ A list of 'ImportedName's to skip — not translate when encountered. The
  -- consumer is expected to supply their own Lean definitions.
  }

-- | The functional dependency of 'MonadReader' makes it not compositional, so
-- we have to jam together different structures that want to be in the 'Reader'
-- into a single datatype.  This type allows adding extra configuration on top
-- of the translation configuration.
data WithTranslationConfiguration r = WithTranslationConfiguration
  { translationConfiguration :: TranslationConfiguration
  , otherConfiguration :: r
  }

-- | Some computations rely solely on access to the configuration, so we
-- provide it separately.
type TranslationConfigurationMonad r m =
  ( MonadReader (WithTranslationConfiguration r) m
  )

type TranslationMonad r s m =
  ( Except.MonadError TranslationError  m
  , TranslationConfigurationMonad r m
  , MonadState s m
  )

runTranslationMonad ::
  TranslationConfiguration ->
  r ->
  s ->
  (forall m. TranslationMonad r s m => m a) ->
  Either TranslationError (a, s)
runTranslationMonad configuration r s m =
  runStateT (runReaderT m (WithTranslationConfiguration configuration r)) s
