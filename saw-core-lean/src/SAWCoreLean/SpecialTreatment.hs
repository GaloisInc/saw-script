{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : SAWCoreLean.SpecialTreatment
Copyright   : Galois, Inc. 2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : portable

Per-identifier treatment table: how to translate specific SAWCore
constants when they appear at a definition site or a use site.

Near-mirror of "SAWCoreRocq.SpecialTreatment", with Lean-target names.
The table itself (see 'specialTreatmentMap') starts empty and fills
incrementally as the Phase-1 Lean-side support library grows.
-}

module SAWCoreLean.SpecialTreatment
  ( DefSiteTreatment(..)
  , UseSiteTreatment(..)
  , IdentSpecialTreatment(..)
  , translateModuleName
  , findSpecialTreatment'
  , findSpecialTreatment
  , escapeIdent
    -- * Combinators for building 'IdentSpecialTreatment' values
  , mapsTo
  , mapsToExpl
  , mapsToCore
  , mapsToCoreExpl
  , rename
  , realize
  , replace
  , replaceDropArgs
  , skip
    -- * Named target modules on the Lean side
  , sawScaffoldingModule
  , sawVectorsModule
  , sawBitvectorsModule
  , sawCorePreludeExtraModule
  , sawCorePrimitivesModule
    -- * Output-shape predicates
  , implicitlyOpenedModules
  , isImplicitlyOpened
  ) where

import           Control.Lens            (_1, _2, over)
import           Control.Monad.Reader    (asks)
import           Data.Char               (isAlphaNum)
import qualified Data.Map                as Map
import           Data.Map                (Map)
import           Data.Text               (Text)
import           Prelude                 hiding (fail)
import           Text.Encoding.Z         (zEncodeString)

import qualified Language.Lean.AST       as Lean

import           SAWCore.Name

import           SAWCoreLean.Monad

-- | How to handle a SAWCore identifier at its definition site.
data DefSiteTreatment
  = -- | Translate the identifier unchanged, and directly translate the
    --   associated SAWCore declaration.
    DefPreserve
  | -- | Translate the identifier into the given Lean identifier, and
    --   otherwise directly translate the associated SAWCore declaration.
    DefRename Lean.Ident
  | -- | Replace the declaration of the identifier with the given text
    --   verbatim (emitted as a 'Lean.Snippet').
    DefReplace String
  | -- | Skip the declaration of the identifier altogether (the Lean side
    --   is expected to define it independently).
    DefSkip

-- | How to translate a SAWCore identifier at its use sites.
data UseSiteTreatment
  = -- | Translate the identifier unchanged.
    UsePreserve
    -- | Rename the identifier to the given (optionally qualified) Lean
    --   identifier. When the 'Bool' is 'True' the use site is emitted
    --   with a leading @\@@, forcing all implicit arguments to be
    --   supplied explicitly.
  | UseRename (Maybe ModuleName) Lean.Ident Bool
    -- | Apply a macro function to the translations of the first @n@
    --   SAWCore arguments of this identifier. Used for things like
    --   collapsing Cryptol's binary numeric encoding (@TCNum (NatPos
    --   (Bit0 (Bit0 One)))@) into a plain 'Lean.NatLit' at translation
    --   time. If fewer than @n@ arguments are supplied, the
    --   translator throws 'UnderAppliedMacro' — use 'UseMacroOrVar'
    --   if the identifier might appear under-applied.
  | UseMacro Int ([Lean.Term] -> Lean.Term)
    -- | Like 'UseMacro' but with a fallback. Under-applied uses
    --   emit the given 'Lean.Term' applied to whatever arguments
    --   are present; fully-applied uses run the macro. The macro
    --   itself can pattern-match on its arguments and fall back to
    --   a wrapper-call if a collapse target isn't reachable —
    --   typically by returning @'Lean.App' fallback args@ when the
    --   args don't match the literal-collapse shape.
    --
    --   Used for Cryptol's 'NatPos' / 'Bit0' / 'Bit1' constructors,
    --   which:
    --     - collapse to 'Lean.NatLit' when applied to a literal arg;
    --     - emit a wrapper-function call when applied to a symbolic
    --       arg (the macro detects this and produces 'App fallback
    --       [arg]');
    --     - emit a bare 'Lean.Var' reference when used un-applied
    --       (e.g. as a higher-order argument).
  | UseMacroOrVar Int Lean.Term ([Lean.Term] -> Lean.Term)
    -- | Reject this identifier at every use site. Throws
    --   'RejectedPrimitive' with the given rejection reason. Used
    --   for SAWCore primitives whose Lean transposition would be
    --   unsound under the current arc (e.g. 'Prelude.fix'); makes
    --   failure surface at SAW-translation time rather than as an
    --   "unknown identifier" at Lean-elaboration time.
  | UseReject Text

data IdentSpecialTreatment = IdentSpecialTreatment
  { atDefSite :: DefSiteTreatment
  , atUseSite :: UseSiteTreatment
  }

-- | SAWCore module names get remapped to their Lean-support-library
-- counterparts.
moduleRenamingMap :: Map ModuleName ModuleName
moduleRenamingMap = Map.fromList $
  over _1 (mkModuleName . (: [])) <$>
  over _2 mkModuleName <$>
  [ ("Cryptol", ["CryptolToLean", "CryptolPrimitivesForSAWCore"])
  , ("Prelude", ["CryptolToLean", "SAWCorePrelude"])
  ]

translateModuleName :: ModuleName -> ModuleName
translateModuleName mn =
  Map.findWithDefault mn mn moduleRenamingMap

findSpecialTreatment' ::
  TranslationConfigurationMonad r m =>
  NameInfo -> m IdentSpecialTreatment
findSpecialTreatment' nmi =
  case nmi of
    ModuleIdentifier ident -> findSpecialTreatment ident
    ImportedName{} -> pure (IdentSpecialTreatment DefPreserve UsePreserve)

findSpecialTreatment ::
  TranslationConfigurationMonad r m =>
  Ident -> m IdentSpecialTreatment
findSpecialTreatment ident = do
  configuration <- asks translationConfiguration
  let moduleMap = Map.findWithDefault Map.empty (identModule ident)
                    (specialTreatmentMap configuration)
  let defaultTreatment = IdentSpecialTreatment
        { atDefSite = DefPreserve
        , atUseSite = UsePreserve
        }
  pure $ Map.findWithDefault defaultTreatment (identName ident) moduleMap

-- | Use 'mapsTo' for identifiers whose definition has a matching
-- definition already on the Lean side. Skips the SAWCore-side
-- definition; use sites are rewritten to point at the provided target.
mapsTo :: ModuleName -> Lean.Ident -> IdentSpecialTreatment
mapsTo targetModule targetName = IdentSpecialTreatment
  { atDefSite = DefSkip
  , atUseSite = UseRename (Just targetModule) targetName False
  }

-- | Like 'mapsTo' but emits @\@name@ at use sites, forcing all
-- implicit arguments to be supplied explicitly.
mapsToExpl :: ModuleName -> Lean.Ident -> IdentSpecialTreatment
mapsToExpl targetModule targetName = IdentSpecialTreatment
  { atDefSite = DefSkip
  , atUseSite = UseRename (Just targetModule) targetName True
  }

-- | Maps a SAWCore identifier to a Lean-core name (no module prefix).
-- Used for primitives that resolve directly in Lean's prelude
-- (@Bool@, @Nat@, @Int@, …).
mapsToCore :: Lean.Ident -> IdentSpecialTreatment
mapsToCore targetName = IdentSpecialTreatment
  { atDefSite = DefSkip
  , atUseSite = UseRename Nothing targetName False
  }

-- | Like 'mapsToCore' but emits @\@name@ at use sites, forcing all
-- implicit arguments to be supplied explicitly. Needed for names like
-- Lean's @Eq@ where the type parameter is implicit in Lean but
-- SAWCore supplies it explicitly.
mapsToCoreExpl :: Lean.Ident -> IdentSpecialTreatment
mapsToCoreExpl targetName = IdentSpecialTreatment
  { atDefSite = DefSkip
  , atUseSite = UseRename Nothing targetName True
  }

-- | Use 'realize' for axioms or primitives that must be realized
-- where they were originally declared. Emits the supplied verbatim
-- Lean text at the def site; use sites are left unchanged.
realize :: String -> IdentSpecialTreatment
realize code = IdentSpecialTreatment
  { atDefSite = DefReplace code
  , atUseSite = UsePreserve
  }

-- | Rename a SAWCore identifier whose definition can be translated
-- but whose name clashes with Lean's. (For example, SAWCore's @at@
-- would collide with Lean-idiomatic uses; Rocq also uses this
-- combinator for exactly this case.)
rename :: Lean.Ident -> IdentSpecialTreatment
rename ident = IdentSpecialTreatment
  { atDefSite = DefRename ident
  , atUseSite = UseRename Nothing ident False
  }

-- | Replace any occurrence of the identifier applied to @n@ arguments
-- with the supplied Lean term.
replaceDropArgs :: Int -> Lean.Term -> IdentSpecialTreatment
replaceDropArgs n term = IdentSpecialTreatment
  { atDefSite = DefSkip
  , atUseSite = UseMacro n (const term)
  }

-- | A version of 'replaceDropArgs' that drops no arguments.
replace :: Lean.Term -> IdentSpecialTreatment
replace = replaceDropArgs 0

-- | For identifiers that are already defined in the Lean-side support
-- library under the same name — skip the SAWCore-side definition and
-- emit the short name unchanged at use sites.
skip :: IdentSpecialTreatment
skip = IdentSpecialTreatment
  { atDefSite = DefSkip
  , atUseSite = UsePreserve
  }

-- | Reject this identifier at every use site, throwing
-- 'RejectedPrimitive' with the supplied reason. Use for SAWCore
-- primitives we deliberately refuse to translate (e.g. 'fix',
-- pending the Phase 5 recursion design). Loud at SAW-translation
-- time, mirroring Rocq's @badTerm@ on @Prelude.fix@.
reject :: Text -> IdentSpecialTreatment
reject reason = IdentSpecialTreatment
  { atDefSite = DefSkip
  , atUseSite = UseReject reason
  }

-- | The handwritten Lean-side support modules. Use these as the
-- 'ModuleName' argument to 'mapsTo' / 'mapsToExpl'.
sawScaffoldingModule, sawVectorsModule, sawBitvectorsModule,
  sawCorePreludeExtraModule, sawCorePrimitivesModule :: ModuleName
sawScaffoldingModule      = mkModuleName ["CryptolToLean", "SAWCoreScaffolding"]
sawVectorsModule          = mkModuleName ["CryptolToLean", "SAWCoreVectors"]
sawBitvectorsModule       = mkModuleName ["CryptolToLean", "SAWCoreBitvectors"]
sawCorePreludeExtraModule = mkModuleName ["CryptolToLean", "SAWCorePreludeExtra"]
sawCorePrimitivesModule   = mkModuleName ["CryptolToLean", "SAWCorePrimitives"]

-- | Lean-side modules that the emitted preamble brings into scope
-- via @open ...@. References that target one of these modules are
-- emitted as bare short names rather than fully-qualified paths,
-- shrinking the output and matching how a hand-written user proof
-- would refer to the same primitives.
--
-- Currently only 'CryptolToLean.SAWCorePrimitives' is opened: it's
-- the dominant target module (every SAW primitive routes through
-- it) and its short names ('bvAdd', 'gen', 'foldr', 'coerce', …)
-- don't collide with anything else the translator emits. Other
-- support modules ('SAWCoreScaffolding', 'SAWCoreVectors',
-- 'SAWCorePreludeExtra') stay fully-qualified for now — their
-- short names are common ('Bit', 'Vec', 'ite') and could shadow
-- user-supplied names downstream.
implicitlyOpenedModules :: [ModuleName]
implicitlyOpenedModules = [sawCorePrimitivesModule]

isImplicitlyOpened :: ModuleName -> Bool
isImplicitlyOpened m = m `elem` implicitlyOpenedModules

-- | The per-SAWCore-module treatment tables. Starts empty; entries
-- accumulate here as the Lean-side support library grows. Compare
-- 'SAWCoreRocq.SpecialTreatment.specialTreatmentMap' (which is
-- ~500 lines) — the Lean-side analog fills in gradually over Phase 1.
specialTreatmentMap :: TranslationConfiguration ->
                       Map ModuleName (Map String IdentSpecialTreatment)
specialTreatmentMap _configuration = Map.fromList $
  over _1 (mkModuleName . (: [])) <$>
  [ ("Cryptol", cryptolPreludeSpecialTreatmentMap)
  , ("Prelude", sawCorePreludeSpecialTreatmentMap)
  ]

-- | Cryptol-side treatment entries. The Cryptol @Num@ inductive and
-- its constructors are declared in 'CryptolToLean.SAWCorePrimitives'
-- so translated output has something to reference.
cryptolPreludeSpecialTreatmentMap :: Map String IdentSpecialTreatment
cryptolPreludeSpecialTreatmentMap = Map.fromList
  [ ("Num",   mapsTo sawCorePrimitivesModule "Num")
  , ("TCNum", mapsTo sawCorePrimitivesModule "Num.TCNum")
  , ("TCInf", mapsTo sawCorePrimitivesModule "Num.TCInf")
  ]

-- | Seed entries for 'Prelude.*' primitives whose Lean realisation is
-- already in scope (via Lean's core or the handwritten support lib).
-- Every entry here replaces an otherwise-unresolvable qualified
-- reference like @CryptolToLean.SAWCorePrelude.Bool@.
sawCorePreludeSpecialTreatmentMap :: Map String IdentSpecialTreatment
sawCorePreludeSpecialTreatmentMap = Map.fromList
  -- Lean core
  [ ("Bool",    mapsToCore "Bool")
    -- Under specialization, SAWCore's 'Nat' ('Zero | NatPos Pos',
    -- binary-positive) is mapped to Lean's native 'Nat' ('zero |
    -- succ Nat', unary). The constructor-level UseMacro entries
    -- below collapse @NatPos (Bit0 (Bit0 One))@ chains to numeric
    -- literals at translation time, giving clean Lean-side output.
    -- This would silently change the semantics of a 'Nat#rec'
    -- elimination — but 'scNormalize' reduces concrete 'Nat#rec'
    -- calls away before the translator sees them. Residual 'Nat#rec'
    -- on a symbolic argument would still be unsound; if that ever
    -- surfaces we'll need a handwritten 'Nat#rec' wrapper with the
    -- SAW-matching argument order. The polymorphism-residual check
    -- in 'writeLeanTerm' will catch most such cases upstream.
  , ("Nat",     mapsToCore "Nat")
  , ("Integer", mapsToCore "Int")
  , ("String",  mapsToCore "String")
  , ("True",    mapsToCore "Bool.true")
  , ("False",   mapsToCore "Bool.false")
  , ("Eq",      mapsToCoreExpl "Eq")
    -- SAWCore's Eq takes the type explicitly; Lean's Eq takes it
    -- implicitly, so we need @Eq to force the application through.

    -- SAWCore's UnitType is a singleton inductive with constructor
    -- @Unit@. We provide a Lean-side @UnitType@ inductive in
    -- 'CryptolToLean.SAWCorePrimitives' (Lean core @Unit@ is an
    -- abbrev for @PUnit.{1}@ and lacks the @.rec@ shape SAWCore
    -- expects), so route both the type and constructor there.
  , ("UnitType", mapsTo sawCorePrimitivesModule "UnitType")
  , ("Unit",     mapsTo sawCorePrimitivesModule "UnitType.Unit")
    -- SAWCore's PairType: similar story; the Lean-side inductive
    -- with constructor 'PairValue' lives in SAWCorePrimitives.
  , ("PairType",  mapsTo sawCorePrimitivesModule "PairType")
  , ("PairValue", mapsToExpl sawCorePrimitivesModule "PairType.PairValue")
  , ("Pair_fst",  mapsTo sawCorePrimitivesModule "Pair_fst")
  , ("Pair_snd",  mapsTo sawCorePrimitivesModule "Pair_snd")

  -- SAWCore capitalizes constructor names; Lean's core @Eq@ uses
  -- lower-case @Eq.refl@. The 'mapsToCoreExpl' flag forces @\@Eq.refl@
  -- to be emitted so all implicit parameters are supplied positionally
  -- — SAWCore always gives them explicitly.
  , ("Refl", mapsToCoreExpl "Eq.refl")

    -- SAWCore's Bool eliminator primitives (iteDep, ite, and their
    -- reduction rules) have the True case before the False case;
    -- Lean's Bool.rec is the opposite. Routing through handwritten
    -- wrappers in SAWCorePreludeExtra permutes the arguments so the
    -- elimination stays faithful to SAW semantics. (Using a direct
    -- mapsTo to Lean's Bool.rec would silently swap the cases at
    -- every use site.)
  , ("iteDep",        mapsTo sawCorePreludeExtraModule "iteDep")
  , ("iteDep_True",   mapsTo sawCorePreludeExtraModule "iteDep_True")
  , ("iteDep_False",  mapsTo sawCorePreludeExtraModule "iteDep_False")
  , ("ite",           mapsTo sawCorePreludeExtraModule "ite")
  , ("ite_eq_iteDep", mapsTo sawCorePreludeExtraModule "ite_eq_iteDep")

  -- Support lib
  , ("Bit",       mapsTo sawScaffoldingModule "Bit")
  , ("Vec",       mapsTo sawVectorsModule     "Vec")
  , ("bitvector", mapsTo sawBitvectorsModule  "bitvector")

    -- Nat / Pos constructors — collapse binary-positive chains to
    -- Lean numeric literals when fully applied to a 'NatLit'.
    -- Otherwise emit the wrapper-function call (Bit0/Bit1) or
    -- identity (NatPos), with a bare-reference fallback when the
    -- constructor itself is used un-applied. This lets a type like
    -- @[4]Bit@ render as @Vec 4 Bool@ rather than the verbose
    -- @Vec (id (bit0_macro (bit0_macro 1))) Bool@ chain.
  , ("Zero",   replaceDropArgs 0 (Lean.NatLit 0))
  , ("One",    replaceDropArgs 0 (Lean.NatLit 1))
  , ("Succ",   replace (Lean.Var (Lean.Ident "Nat.succ")))
  , ("Bit0",   IdentSpecialTreatment DefSkip
                 (UseMacroOrVar 1 (Lean.Var bit0MacroIdent)
                    (collapseOrApply bit0MacroIdent (\n -> 2 * n))))
  , ("Bit1",   IdentSpecialTreatment DefSkip
                 (UseMacroOrVar 1 (Lean.Var bit1MacroIdent)
                    (collapseOrApply bit1MacroIdent (\n -> 2 * n + 1))))
    -- NatPos wraps a 'Pos' into a 'Nat'; under our Pos-as-Nat
    -- collapse it's the identity. Pass through the literal when
    -- the arg is already a 'NatLit'; otherwise fall back to 'id'.
  , ("NatPos", IdentSpecialTreatment DefSkip
                 (UseMacroOrVar 1 (Lean.Var (Lean.Ident "id"))
                    (\xs -> case xs of
                       [Lean.NatLit n] -> Lean.NatLit n
                       _ -> Lean.App (Lean.Var (Lean.Ident "id")) xs)))

    -- SAWCorePrimitives — axioms, inductives, and recursors that
    -- survive 'scNormalize' and for which the handwritten
    -- CryptolToLean.SAWCorePrimitives provides a realisation.
  , ("Either",        mapsTo sawCorePrimitivesModule "Either")
    -- Constructors: SAWCore supplies both type parameters explicitly
    -- at every use site; Lean makes them implicit. Force the @-form
    -- so the two positional arguments resolve correctly.
  , ("Left",          mapsToExpl sawCorePrimitivesModule "Either.Left")
  , ("Right",         mapsToExpl sawCorePrimitivesModule "Either.Right")
  , ("Stream",        mapsTo sawCorePrimitivesModule "Stream")
  , ("MkStream",      mapsToExpl sawCorePrimitivesModule "Stream.MkStream")
  , ("EmptyType",     mapsTo sawCorePrimitivesModule "EmptyType")
  , ("Empty",         mapsTo sawCorePrimitivesModule "EmptyType.Empty")
  , ("RecordType",    mapsTo sawCorePrimitivesModule "RecordType")
  , ("RecordValue",   mapsToExpl sawCorePrimitivesModule "RecordType.RecordValue")
  , ("subNat",        mapsTo sawCorePrimitivesModule "subNat")
  , ("addNat",        mapsTo sawCorePrimitivesModule "addNat")
  , ("intAdd",        mapsTo sawCorePrimitivesModule "intAdd")
  , ("intSub",        mapsTo sawCorePrimitivesModule "intSub")
  , ("intMul",        mapsTo sawCorePrimitivesModule "intMul")
  , ("intDiv",        mapsTo sawCorePrimitivesModule "intDiv")
  , ("intMod",        mapsTo sawCorePrimitivesModule "intMod")
  , ("intNeg",        mapsTo sawCorePrimitivesModule "intNeg")
  , ("intEq",         mapsTo sawCorePrimitivesModule "intEq")
  , ("intLe",         mapsTo sawCorePrimitivesModule "intLe")
  , ("intLt",         mapsTo sawCorePrimitivesModule "intLt")
  , ("natToInt",      mapsTo sawCorePrimitivesModule "natToInt")
  , ("intToNat",      mapsTo sawCorePrimitivesModule "intToNat")
  , ("gen",           mapsTo sawCorePrimitivesModule "gen")
  , ("atWithDefault", mapsTo sawCorePrimitivesModule "atWithDefault")
  , ("shiftL",        mapsTo sawCorePrimitivesModule "shiftL")
  , ("shiftR",        mapsTo sawCorePrimitivesModule "shiftR")
  , ("rotateL",       mapsTo sawCorePrimitivesModule "rotateL")
  , ("rotateR",       mapsTo sawCorePrimitivesModule "rotateR")
  , ("equalNat",      mapsTo sawCorePrimitivesModule "equalNat")
  , ("ltNat",         mapsTo sawCorePrimitivesModule "ltNat")
  , ("leNat",         mapsTo sawCorePrimitivesModule "leNat")
  , ("foldr",         mapsTo sawCorePrimitivesModule "foldr")
  , ("foldl",         mapsTo sawCorePrimitivesModule "foldl")
  , ("coerce",        mapsTo sawCorePrimitivesModule "coerce")
  , ("unsafeAssert",  mapsTo sawCorePrimitivesModule "unsafeAssert")
  , ("error",         mapsTo sawCorePrimitivesModule "error")

    -- Recursion primitives — deliberately rejected at the SAW
    -- translation boundary (loud failure, mirrors Rocq's @badTerm@
    -- on @Prelude.fix@). The Phase 5 recursion design (was Arc 4.4)
    -- will replace this with a proper transposition; until then,
    -- any term reaching `fix` after specialization throws cleanly
    -- here rather than emitting an unmapped reference that surfaces
    -- as "unknown identifier" at Lean elaboration. L-5 lockdown.
  , ("fix", reject "Prelude.fix is recursion on streams. \
                   \saw-core-lean does not yet have a sound Lean \
                   \transposition for it (tracked as Phase 5 \
                   \recursion design in saw-core-lean/doc/2026-05-02_post-audit-plan.md). \
                   \If your Cryptol program survives normalization with \
                   \a `fix` residual, you've hit one of the open \
                   \cases — Merkle-Damgard hashing, [inf]-stream \
                   \definitions, etc. Re-export the residual to \
                   \dump_lean_residual_primitives for diagnostics.")
  , ("fix_unfold", reject "fix_unfold is the unfolding lemma for \
                          \Prelude.fix; same recursion-design \
                          \blocker as `fix` itself.")

    -- Bitvector primitives — see CryptolToLean.SAWCorePrimitives's
    -- "## Bitvector primitives" block. Both SAW-Prelude primitives
    -- (bvNat, bvAdd, …) and SAW-Prelude defs we keep opaque
    -- (bvNot, bvAnd, bvOr, bvXor, bvEq) route here. The opaque set
    -- is enforced by `leanOpaqueBuiltins` in
    -- `SAWCentral.Prover.Exporter`.
  , ("bvNat",   mapsTo sawCorePrimitivesModule "bvNat")
  , ("bvToNat", mapsTo sawCorePrimitivesModule "bvToNat")
  , ("bvToInt", mapsTo sawCorePrimitivesModule "bvToInt")
  , ("intToBv", mapsTo sawCorePrimitivesModule "intToBv")
  , ("sbvToInt",mapsTo sawCorePrimitivesModule "sbvToInt")
  , ("bvAdd",   mapsTo sawCorePrimitivesModule "bvAdd")
  , ("bvSub",   mapsTo sawCorePrimitivesModule "bvSub")
  , ("bvMul",   mapsTo sawCorePrimitivesModule "bvMul")
  , ("bvNeg",   mapsTo sawCorePrimitivesModule "bvNeg")
  , ("bvUDiv",  mapsTo sawCorePrimitivesModule "bvUDiv")
  , ("bvURem",  mapsTo sawCorePrimitivesModule "bvURem")
  , ("bvSDiv",  mapsTo sawCorePrimitivesModule "bvSDiv")
  , ("bvSRem",  mapsTo sawCorePrimitivesModule "bvSRem")
  , ("bvShl",   mapsTo sawCorePrimitivesModule "bvShl")
  , ("bvShr",   mapsTo sawCorePrimitivesModule "bvShr")
  , ("bvSShr",  mapsTo sawCorePrimitivesModule "bvSShr")
  , ("bvNot",   mapsTo sawCorePrimitivesModule "bvNot")
  , ("bvAnd",   mapsTo sawCorePrimitivesModule "bvAnd")
  , ("bvOr",    mapsTo sawCorePrimitivesModule "bvOr")
  , ("bvXor",   mapsTo sawCorePrimitivesModule "bvXor")
  , ("bvEq",    mapsTo sawCorePrimitivesModule "bvEq")
  , ("bvult",   mapsTo sawCorePrimitivesModule "bvult")
  , ("bvule",   mapsTo sawCorePrimitivesModule "bvule")
  , ("bvugt",   mapsTo sawCorePrimitivesModule "bvugt")
  , ("bvuge",   mapsTo sawCorePrimitivesModule "bvuge")
  , ("bvslt",   mapsTo sawCorePrimitivesModule "bvslt")
  , ("bvsle",   mapsTo sawCorePrimitivesModule "bvsle")
  , ("bvsgt",   mapsTo sawCorePrimitivesModule "bvsgt")
  , ("bvsge",   mapsTo sawCorePrimitivesModule "bvsge")
  , ("bvUExt",  mapsTo sawCorePrimitivesModule "bvUExt")
  , ("bvSExt",  mapsTo sawCorePrimitivesModule "bvSExt")
  , ("bvPopcount",            mapsTo sawCorePrimitivesModule "bvPopcount")
  , ("bvCountLeadingZeros",   mapsTo sawCorePrimitivesModule "bvCountLeadingZeros")
  , ("bvCountTrailingZeros",  mapsTo sawCorePrimitivesModule "bvCountTrailingZeros")
  , ("bvLg2",                 mapsTo sawCorePrimitivesModule "bvLg2")
  ]

-- | The two Lean-side helpers that back 'Bit0' / 'Bit1' when the
-- argument isn't a literal we can collapse. Defined in
-- 'CryptolToLean.SAWCorePrimitives'.
bit0MacroIdent, bit1MacroIdent :: Lean.Ident
bit0MacroIdent = Lean.Ident "CryptolToLean.SAWCorePrimitives.bit0_macro"
bit1MacroIdent = Lean.Ident "CryptolToLean.SAWCorePrimitives.bit1_macro"

-- | Macro body for 'Bit0' / 'Bit1': if the argument translates to a
-- 'Lean.NatLit', collapse to a single literal computed via @f@;
-- otherwise emit the wrapper-function call.
collapseOrApply ::
  Lean.Ident -> (Integer -> Integer) -> [Lean.Term] -> Lean.Term
collapseOrApply _ f [Lean.NatLit n] = Lean.NatLit (f n)
collapseOrApply wrap _ args         = Lean.App (Lean.Var wrap) args

-- | Escape a Lean identifier so it's lexically valid. Any non-alnum,
-- non-@_@, non-@'@ character causes the whole identifier to be
-- Z-encoded with an @Op_@ prefix (same scheme the Rocq backend uses,
-- since Z-encoding is purely textual).
escapeIdent :: Lean.Ident -> Lean.Ident
escapeIdent (Lean.Ident str)
  | all okChar str = Lean.Ident str
  | otherwise      = Lean.Ident ("Op_" ++ zEncodeString str)
 where
   okChar x = isAlphaNum x || x `elem` ("_'" :: String)
