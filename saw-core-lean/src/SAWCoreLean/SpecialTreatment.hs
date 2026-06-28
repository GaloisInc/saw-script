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
  , UseArgShape(..)
  , UseResultShape(..)
  , UseSiteTreatment(..)
  , IdentSpecialTreatment(..)
  , translateModuleName
  , findSpecialTreatment'
  , findSpecialTreatment
  , specialTreatmentMap
  , escapeIdent
  , unsupportedFixReason
    -- * Combinators for building 'IdentSpecialTreatment' values
  , mapsTo
  , mapsToExpl
  , mapsToCore
  , mapsToCoreExpl
  , mapsToCoreUniv
  , replace
  , replaceDropArgs
  , skip
  , autoEmit
  , liftRawValue
    -- * Named target modules on the Lean side
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
import qualified Data.List
import qualified Data.Map                as Map
import           Data.Map                (Map)
import qualified Data.Set                as Set
import           Data.Set                (Set)
import qualified Data.Text               as Text
import           Data.Text               (Text)
import           Prelude                 hiding (fail)
import           Text.Encoding.Z         (zEncodeString)

import qualified Language.Lean.AST       as Lean

import           SAWCore.Name

import           SAWCoreLean.Monad

-- | How to translate a SAWCore identifier at its definition site
-- (i.e. when the auto-emit prelude walker encounters its 'DataType'
-- or 'Def' in the SAWCore module). Mirrors Rocq's 'DefSiteTreatment'.
data DefSiteTreatment
  = -- | Translate the declaration in place, preserving its name.
    DefPreserve
    -- | Translate the declaration in raw SAWCore mode, preserving its
    --   name. This keeps proof/type infrastructure universe-polymorphic
    --   over @Sort u@ instead of applying the Phase-beta @Except String@
    --   value-domain convention.
  | DefPreserveRaw
    -- | Translate the declaration, renaming the identifier to the
    --   given Lean ident.
  | DefRename Lean.Ident
    -- | Replace the declaration with the supplied verbatim Lean
    --   source. Used for prelude entries whose semantics are
    --   transposed to a hand-rolled Lean shape inside the
    --   auto-emitted module.
  | DefReplace String
    -- | Skip the declaration altogether — the SAWCore identifier
    --   resolves at use sites to a name in the hand-written support
    --   library, so re-emitting its body would either be redundant
    --   or actively wrong.
  | DefSkip

data UseResultShape
  = UseResultRaw
  | UseResultWrapped
  | UseResultFunction
  deriving (Eq, Show)

data UseArgShape
  = UseArgRaw
  | UseArgWrapped
  | UseArgFunction
  deriving (Eq, Show)

-- | How to translate a SAWCore identifier at its use sites.
data UseSiteTreatment
  = -- | Translate the identifier unchanged.
    UsePreserve
    -- | Rename the identifier to the given (optionally qualified) Lean
    --   identifier. When the 'Bool' is 'True' the use site is emitted
    --   with a leading @\@@, forcing all implicit arguments to be
    --   supplied explicitly.
  | UseRename (Maybe ModuleName) Lean.Ident Bool
    -- | Like 'UseRename' with the @\@@ flag implicitly set, plus
    --   universe-level inference. The @[Int]@ lists SAWCore-argument
    --   indices whose types' universes are supplied at the Lean
    --   use site in the @\.{u₀, u₁, …}@ position. Bypasses Lean's
    --   universe unifier (motivating regression: Lean issue #2297
    --   and the @Eq.rec@-shape elaboration gaps from the parked
    --   P4/P6 work). Index 0 is the first SAWCore argument.
    --
    --   Levels are resolved by 'levelOfArg' from the current
    --   'boundUniverses' map; if a referenced index is out of
    --   range or doesn't resolve to a known universe, the call
    --   site falls back to bare @\@name@ and lets Lean infer.
    --   This keeps the change safe: at worst, behavior matches
    --   the pre-universe-polymorphism translator.
  | UseRenameUniv (Maybe ModuleName) Lean.Ident [Int]
    -- | Apply a macro function to the translations of the first @n@
    --   SAWCore arguments of this identifier. Used for things like
    --   collapsing Cryptol's binary numeric encoding (@TCNum (NatPos
    --   (Bit0 (Bit0 One)))@) into a plain 'Lean.NatLit' at translation
    --   time. If fewer than @n@ arguments are supplied, the
    --   translator throws 'UnderAppliedMacro' — use 'UseMacroOrVar'
    --   if the identifier might appear under-applied.
  | UseMacro Int UseResultShape ([Lean.Term] -> Lean.Term)
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
  | UseMacroOrVar Int UseResultShape Lean.Term ([Lean.Term] -> Lean.Term)
    -- | Route a SAWCore primitive to a wrapped-signature Lean target.
    --   The list records the Lean helper's expected convention for
    --   each consumed SAWCore argument. Under-applied calls adapt the
    --   supplied prefix with the same conventions before returning a
    --   function-shaped partial application. Index 0 is the first
    --   SAWCore argument.
  | UseMapsToWrapped [UseArgShape] Lean.Ident
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
  pure $ Map.findWithDefault (defaultTreatmentFor ident) (identName ident) moduleMap

-- | Default treatment when an identifier has no explicit
-- 'SpecialTreatment' entry. Always 'UseReject'.
--
-- Design principle: NEVER drop errors. An unmapped
-- 'ModuleIdentifier' reaching the translator is *always* a
-- bug-shaped situation:
--
--   * If Cryptol's `scNormalizeForLean` was supposed to unfold it,
--     it's a translator/normaliser gap.
--   * If the primitive is genuinely unsupported, the responsible
--     thing is to fail at SAW time with a documented reason, not
--     to silently emit a dangling @CryptolToLean.Foo.bar@
--     reference that surfaces later as a confusing Lean
--     "unknown identifier" error.
--
-- Every primitive that we deliberately don't support yet must be
-- catalogued as a 'reject' entry in the per-module
-- 'specialTreatmentMap'. The 'reject' constructor produces a
-- 'UseReject' with a workflow-specific reason, so the user sees
-- exactly why the translator refuses. Truly-unmapped idents
-- (forgotten by both the contributor and this default) still
-- reject loudly via the message below — no escape hatch.
--
-- Documented in audit `doc/audit/2026-05-06_cryptol-coverage-gaps.md`
-- as the highest-leverage UX change.
defaultTreatmentFor :: Ident -> IdentSpecialTreatment
defaultTreatmentFor ident =
  IdentSpecialTreatment DefSkip $ UseReject $ Text.pack $
    "No SAW-core-lean mapping for `" ++
    show (identModule ident) ++ "." ++ identName ident ++ "`. Either:\n" ++
    "  * Cryptol's `scNormalizeForLean` was supposed to unfold this " ++
    "primitive before translation but didn't (translator gap; report it);\n" ++
    "  * The primitive is genuinely unsupported and should be " ++
    "catalogued as a `reject` entry in " ++
    "`SAWCoreLean.SpecialTreatment.specialTreatmentMap` with a " ++
    "documented reason; or\n" ++
    "  * It needs a real mapping (use `mapsTo` / `replace` / etc).\n" ++
    "Workaround: monomorphize / specialize at the SAWScript call site " ++
    "so the primitive is unfolded; or refactor the Cryptol code to " ++
    "avoid the construct."

-- | Use 'mapsTo' for identifiers whose definition has a matching
-- definition already on the Lean side. Use sites are rewritten to
-- point at the provided target, and the auto-emit walker skips
-- the def site.
mapsTo :: ModuleName -> Lean.Ident -> IdentSpecialTreatment
mapsTo targetModule targetName =
  IdentSpecialTreatment DefSkip
    (UseRename (Just targetModule) targetName False)

-- | Like 'mapsTo' but emits @\@name@ at use sites, forcing all
-- implicit arguments to be supplied explicitly.
mapsToExpl :: ModuleName -> Lean.Ident -> IdentSpecialTreatment
mapsToExpl targetModule targetName =
  IdentSpecialTreatment DefSkip
    (UseRename (Just targetModule) targetName True)

-- | Maps a SAWCore identifier to a Lean-core name (no module prefix).
-- Used for primitives that resolve directly in Lean's prelude
-- (@Bool@, @Nat@, @Int@, …).
mapsToCore :: Lean.Ident -> IdentSpecialTreatment
mapsToCore targetName =
  IdentSpecialTreatment DefSkip (UseRename Nothing targetName False)

-- | Like 'mapsToCore' but emits @\@name@ at use sites, forcing all
-- implicit arguments to be supplied explicitly. Needed for names like
-- Lean's @Eq@ where the type parameter is implicit in Lean but
-- SAWCore supplies it explicitly.
mapsToCoreExpl :: Lean.Ident -> IdentSpecialTreatment
mapsToCoreExpl targetName =
  IdentSpecialTreatment DefSkip (UseRename Nothing targetName True)

-- | Like 'mapsToCoreExpl' but also supplies explicit universe levels
-- at the call site, by inferring them from the SAWCore arguments
-- at the given indices. Each indexed argument must resolve to a
-- bound variable carrying a 'boundUniverses' entry; otherwise the
-- emission falls back to bare @\@name@. See 'UseRenameUniv' for
-- the full contract and motivation.
mapsToCoreUniv :: Lean.Ident -> [Int] -> IdentSpecialTreatment
mapsToCoreUniv targetName argIndices =
  IdentSpecialTreatment DefSkip
    (UseRenameUniv Nothing targetName argIndices)

-- | Lift a syntactically-raw Lean value (number/string literal,
-- bare constructor reference) into the 'Except String' monad via
-- 'Pure.pure'. Already-wrapped translations (a 'Var' bound by
-- 'translateBinder'' under the Phase-β wrap rule, an 'App' headed
-- by a lifted call) flow through unchanged. Used by macro entries
-- that target Lean primitives with wrapped formals (e.g. 'iteM')
-- so raw-value SAWCore arguments (Bool ctors, NatLit) become
-- well-typed Except values at the call site.
liftRawValue :: Lean.Term -> Lean.Term
liftRawValue t = case t of
  Lean.NatLit _                  -> wrap t
  Lean.IntLit _                  -> wrap t
  Lean.StringLit _               -> wrap t
  Lean.Var (Lean.Ident s)
    | s `elem` rawCtorNames      -> wrap t
  Lean.ExplVar (Lean.Ident s)
    | s `elem` rawCtorNames      -> wrap t
  -- Empty Vec literal '#v[]' is unambiguously a raw value: no
  -- elements means no wrap/raw mismatch on element types. The
  -- non-empty case is handled separately at translation time
  -- (each element flows through the wrap rules; the surrounding
  -- ArrayValue emit would need a coordinated lift).
  Lean.List []                   -> wrap t
  _                              -> t
  where
    wrap u = Lean.App (Lean.Var (Lean.Ident "Pure.pure")) [u]
    -- Nullary constructor references emitted by the translator at
    -- 'mapsTo' targets. These name-pieces correspond to entries in
    -- 'specialTreatmentMap' that route to Lean stdlib / support-lib
    -- inductives. Extend as new mappings appear; the rule is "any
    -- 'Lean.Ident' that names a 0-arity constructor and arrives at
    -- a wrapped-formal position needs a 'Pure.pure' lift to match".
    rawCtorNames =
      [ "Bool.true", "Bool.false"
      , "UnitType.Unit"
      , "EmptyType.Empty"
      ]

-- | Replace any occurrence of the identifier applied to @n@ arguments
-- with the supplied Lean term.
replaceDropArgs :: Int -> Lean.Term -> IdentSpecialTreatment
replaceDropArgs n term =
  IdentSpecialTreatment DefSkip (UseMacro n UseResultRaw (const term))

-- | Route a SAWCore primitive to an Except-wrapped Lean variant
-- without going through the generic 'mapsTo' lift. The translator's
-- 'applied' path inserts a 'Pure.pure' around a 'mapsTo'-target's
-- result whenever the source SAW return type is value-domain; the
-- wrapped variant on the Lean side already returns 'Except String τ',
-- so that extra 'Pure.pure' would double-wrap. The per-argument shape
-- list declares exactly which helper formals expect wrapped values.
mapsToWrapped :: [UseArgShape] -> Lean.Ident -> IdentSpecialTreatment
mapsToWrapped argShapes target =
  IdentSpecialTreatment DefSkip
    (UseMapsToWrapped argShapes target)

-- | A version of 'replaceDropArgs' that drops no arguments.
replace :: Lean.Term -> IdentSpecialTreatment
replace = replaceDropArgs 0

-- | For identifiers that are already defined in the Lean-side support
-- library under the same name — emit the short name unchanged at use
-- sites; skip the def site (the support library supplies it).
skip :: IdentSpecialTreatment
skip = IdentSpecialTreatment DefSkip UsePreserve

-- | Auto-emit the SAWCore body into the prelude output. The use
-- site preserves the short name (Lean's namespace machinery picks
-- it up from the @namespace SAWCorePrelude@ block). For identifiers
-- whose Lean target name should differ from the SAWCore short name,
-- use 'rename' instead (todo).
autoEmit :: IdentSpecialTreatment
autoEmit = IdentSpecialTreatment DefPreserve UsePreserve

-- | Auto-emit a SAWCore definition using the raw/logical convention.
-- This is for Prelude proof/type infrastructure. Value-domain Prelude
-- facades use 'autoEmit' so their binders/results carry the Phase-beta
-- @Except String@ semantics.
autoEmitRaw :: IdentSpecialTreatment
autoEmitRaw = IdentSpecialTreatment DefPreserveRaw UsePreserve

replaceDef :: String -> IdentSpecialTreatment
replaceDef s = IdentSpecialTreatment (DefReplace s) UsePreserve

-- | Reject this identifier at every use site, throwing
-- 'RejectedPrimitive' with the supplied reason. Use for SAWCore
-- primitives we deliberately refuse to translate (e.g. residual
-- 'fix_unfold', or malformed/under-applied uses that did not go
-- through the proof-carrying fix path). Loud at SAW-translation time.
-- The auto-emit walker skips the def site — there is no Lean
-- translation to emit.
reject :: Text -> IdentSpecialTreatment
reject reason = IdentSpecialTreatment DefSkip (UseReject reason)

unsupportedFixReason :: Text
unsupportedFixReason =
  "Prelude.fix must be translated by the proof-carrying fix path, \
  \which emits an explicit Lean fixed-point obligation. This occurrence \
  \did not have a supported application shape. See \
  \saw-core-lean/doc/2026-06-26_proof-carrying-soundness-contracts.md."

-- | The handwritten Lean-side support modules. Use these as the
-- 'ModuleName' argument to 'mapsTo' / 'mapsToExpl'.
sawVectorsModule, sawBitvectorsModule,
  sawCorePreludeExtraModule, sawCorePrimitivesModule :: ModuleName
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
-- Open list:
--
-- * 'CryptolToLean.SAWCorePrimitives' — dominant target module
--   (every SAW primitive routes through it). Its short names
--   ('bvAdd', 'gen', 'foldr', 'coerce', …) don't collide with
--   anything else the translator emits.
--
-- * 'CryptolToLean.SAWCoreVectors' — emitted modules use 'Vec n α'
--   pervasively; opening this collapses
--   'CryptolToLean.SAWCoreVectors.Vec' (32 chars) to 'Vec' (3 chars)
--   at every occurrence. Tier-1 readability fix per
--   @doc/2026-05-09_readability-review.md@. 'Vec' does not shadow
--   anything in Lean's stdlib (which uses 'Vector', not 'Vec').
--
-- 'SAWCorePreludeExtra' stays fully-qualified: its short name 'ite'
-- would shadow Lean's built-in non-dependent 'ite', causing
-- elaboration mismatches in user proofs that mix the two.
implicitlyOpenedModules :: [ModuleName]
implicitlyOpenedModules = [sawCorePrimitivesModule, sawVectorsModule]

isImplicitlyOpened :: ModuleName -> Bool
isImplicitlyOpened m = m `elem` implicitlyOpenedModules

-- | The per-SAWCore-module treatment tables. Compare
-- 'SAWCoreRocq.SpecialTreatment.specialTreatmentMap' (~500 lines) —
-- the Lean-side analog covers a similar surface; coverage grows as
-- new Cryptol primitives surface in case studies.
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
  [
    -- Phase 3 auto-emit entries. These translate the SAWCore body
    -- into the emitted prelude file (under namespace
    -- @CryptolToLean.SAWCorePrelude@). Use-site references resolve
    -- via 'UsePreserve' + the namespace block in the emitted output.
    ("id",          autoEmit)
  , ("sawLet",      replaceDef $
      "noncomputable def sawLet.{u0, u1} (a : Type u0) (b : Type u1) \
      \(x : Except String a) (f : a -> Except String b) : Except String b :=\n\
      \  match x with\n\
      \  | Except.ok v => f v\n\
      \  | Except.error msg => Except.error msg")
  , ("Eq__rec",     autoEmitRaw)
  , ("sym",         autoEmitRaw)
  , ("trans",       autoEmitRaw)
  , ("eq_cong",     autoEmitRaw)
    -- Phase 3 stage 4 expansion. Each entry validates the
    -- machinery on an additional shape — soundness gates per
    -- 'Phase 0 / Phase 2.6' apply.
  , ("trans2",      autoEmitRaw)
  , ("trans4",      autoEmitRaw)
  , ("eq_inv_map",  autoEmitRaw)
  , ("coerce__def", autoEmitRaw)
    -- 'coerce_same' and 'coerce_trans' reference @coerce__eq@,
    -- a SAW-internal axiom we 'reject'. Leave them skipped
    -- until @coerce__eq@ has a Lean transposition (likely a
    -- propositional-equality axiom).
  , ("coerce__def_trans", autoEmitRaw)
  , ("rcoerce",     autoEmitRaw)
    -- Bool-arithmetic primitives. Bodies reference @ite@ which
    -- routes via SpecialTreatment to the hand-library wrapper.
  , ("not",         autoEmit)
  , ("and",         autoEmit)
  , ("or",          autoEmit)
  , ("xor",         replaceDef $
      "noncomputable def xor (b1 : Except String Bool) (b2 : Except String Bool) : \
      \Except String Bool :=\n\
      \  CryptolToLean.SAWCorePreludeExtra.iteM Bool b1\n\
      \    (Bind.bind b2 (fun v => Pure.pure (!v))) b2")
  , ("boolEq",      replaceDef $
      "noncomputable def boolEq (b1 : Except String Bool) (b2 : Except String Bool) : \
      \Except String Bool :=\n\
      \  CryptolToLean.SAWCorePreludeExtra.iteM Bool b1 b2\n\
      \    (Bind.bind b2 (fun v => Pure.pure (!v)))")
    -- Equality-style proofs whose bodies are uses of @Refl@.
  , ("not__eq",     skip)
  , ("and__eq",     skip)
  , ("iteDep_True",  autoEmit)
  , ("iteDep_False", autoEmit)
  , ("ite_eq_iteDep", skip)
    -- 'headRecord_RecordValue' / 'tailRecord_RecordValue' depend
    -- on 'headRecord' / 'tailRecord' / 'RecordValue' (all skipped
    -- — RecordType machinery lives in the hand library).
    -- More universe-arithmetic coverage.
    -- 'unsafeCoerce' body is @coerce a b (unsafeAssert (sort 0) a b)@.
    -- Translating @unsafeAssert (sort 0) a b@ requires @unsafeAssert@
    -- at universe 2 (since @(sort 0) = Type : Sort 2@). SAW's
    -- @unsafeAssert@ is at @sort 1@ by SAWCore cumulativity, but
    -- Lean's stand-in is monomorphic at @(α : Type) = Sort 1@ — a
    -- broader Lean axiom would *postulate more than SAW does*
    -- (broader admission than SAW's sort-1 binder), which is an
    -- unsound trust expansion. So @unsafeCoerce@ stays skipped
    -- until we have a sound mechanism (e.g. specialise the
    -- SAW-prelude bodies that use it, or rework
    -- @unsafeAssert@'s shape to admit @α := Type@ without
    -- generalising further).
  , ("piCong0",     autoEmitRaw)
  , ("piCong1",     autoEmitRaw)
  , ("inverse_eta_rule", autoEmitRaw)
    -- DELIBERATELY NOT auto-emitted: 'coerce__eq', 'uip', and the
    -- downstream defs that depend on them ('coerce_same',
    -- 'coerce_trans', 'rcoerce_same', 'unsafeCoerce_same').
    --
    -- SAW declares 'uip' and 'coerce__eq' as @axiom@; naively
    -- transcribing them as Lean @axiom@s adds trusted assumptions
    -- to the verification kernel. But:
    --   * 'uip' is provable in Lean from proof irrelevance — Lean's
    --     'Eq' lives in 'Prop', so any two proofs unify by 'rfl'.
    --   * 'coerce__eq' is (probably) provable: both 'coerce' (=
    --     'cast') and 'coerce__def' (= 'Eq.rec' with motive
    --     @fun b' _ => b'@) reduce via the same elimination shape,
    --     so 'funext' + 'rfl' likely closes the goal.
    --
    -- Naively auto-emitting these as @axiom@s weakens soundness:
    -- every additional Lean axiom is a trusted assumption a
    -- discharge could exploit. Until we have a 'DefReplace'-style
    -- mechanism (or hand-library theorem entries) that emits a
    -- *proof* rather than a postulate, leave them rejected.

  -- Lean core
  , ("Bool",    mapsToCore "Bool")
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
  , ("Eq",      mapsToCoreUniv "Eq" [0])
    -- SAWCore's @Eq t x y@ — type arg is explicit (SAW position 0).
    -- Supply the explicit @\.{u}@ from the universe of @t@ so the
    -- emission becomes @\@Eq.{u_t} t x y@, bypassing Lean's universe
    -- inference (the Phase 0 probe pattern). Falls back to bare
    -- @\@Eq@ if @t@'s universe doesn't resolve, matching pre-Phase-2
    -- behavior in the worst case.

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
    -- PairType1 / PairValue1 are SAWCore's @sort 1@ pair (carrier of
    -- mutual stream-corec fix shapes). Universe-polymorphism makes
    -- our Lean-side 'PairType' fit either; the recognizer in
    -- 'SAWCoreLean.FixShapes' relies on this mapping to see through
    -- the @PairType1#rec1@ projections at lowering time.
  , ("PairType1",  mapsTo sawCorePrimitivesModule "PairType")
  , ("PairValue1", mapsToExpl sawCorePrimitivesModule "PairType.PairValue")

  -- SAWCore capitalizes constructor names; Lean's core @Eq@ uses
  -- lower-case @Eq.refl@. Same universe treatment as @Eq@: pull the
  -- level from the type argument (SAW position 0).
  , ("Refl", mapsToCoreUniv "Eq.refl" [0])

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
    -- Under Phase β, every value-domain SAW term translates at
    -- type @Except String τ@, so a use of @ite α b x y@ arrives
    -- with branches @x y : Except String α@. The Lean target
    -- 'iteM' expects wrapped branches. SAW's @ite@ signature is
    -- @(α : Sort u) → Bool → α → α → α@ — the formal types of @x@
    -- and @y@ are bare type variables, which keeps the generic
    -- 'applied' lift from inserting a 'Pure.pure' around
    -- raw-value branches (e.g. @Bool.true@/@Bool.false@). The
    -- macro fixes that: it wraps any arg-position translation
    -- that is syntactically a raw value (literal or constructor
    -- reference) so the call to 'iteM' typechecks. Branches that
    -- are already-wrapped Lean terms (a 'Var' bound by
    -- 'translateBinder'' under the wrap rule) flow through
    -- unchanged.
    --
    -- Uses 'UseMacroOrVar' (not 'UseMacro') so partial applications
    -- are allowed. The translator still runs this macro's lifting on
    -- any supplied prefix — @ite α True@ must become @iteM α
    -- (Pure.pure True)@ — and falls back to the bare 'iteM' only for
    -- the zero-argument higher-order reference. Lean's elaborator
    -- handles eta-expansion at the use site.
  , ("ite",
      IdentSpecialTreatment DefSkip
        (UseMacroOrVar 4
          UseResultWrapped
          (Lean.Var (Lean.Ident
            "CryptolToLean.SAWCorePreludeExtra.iteM"))
          (\args ->
            Lean.App
              (Lean.Var (Lean.Ident
                "CryptolToLean.SAWCorePreludeExtra.iteM"))
              (map liftRawValue args))))
    -- streamScanl is handwritten in SAWCorePreludeExtra (mirrors
    -- Rocq's hand-rewrite). The corresponding entry in
    -- 'leanOpaqueBuiltins' keeps scNormalize from unfolding it.
  , ("streamScanl",   mapsTo sawCorePreludeExtraModule "streamScanl")

  -- Support lib
  -- Bit was a one-line abbrev for Bool in SAWCoreScaffolding.lean
  -- (deleted Phase 1.4). Map directly to Lean's Bool.
  , ("Bit",       replace (Lean.Var (Lean.Ident "Bool")))
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
                 (UseMacroOrVar 1 UseResultRaw (Lean.Var bit0MacroIdent)
                    (collapseOrApply bit0MacroIdent (\n -> 2 * n))))
  , ("Bit1",   IdentSpecialTreatment DefSkip
                 (UseMacroOrVar 1 UseResultRaw (Lean.Var bit1MacroIdent)
                    (collapseOrApply bit1MacroIdent (\n -> 2 * n + 1))))
    -- NatPos wraps a 'Pos' into a 'Nat'; under our Pos-as-Nat
    -- collapse it's the identity. Pass through the literal when
    -- the arg is already a 'NatLit'; otherwise fall back to 'id'.
  , ("NatPos", IdentSpecialTreatment DefSkip
                 (UseMacroOrVar 1 UseResultRaw (Lean.Var (Lean.Ident "id"))
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
  , ("mulNat",        mapsTo sawCorePrimitivesModule "mulNat")
  , ("divNat",        mapsTo sawCorePrimitivesModule "divNat")
  , ("modNat",        mapsTo sawCorePrimitivesModule "modNat")
  , ("divModNat",     mapsTo sawCorePrimitivesModule "divModNat")
  , ("expNat",        mapsTo sawCorePrimitivesModule "expNat")
  , ("doubleNat",     mapsTo sawCorePrimitivesModule "doubleNat")
  , ("pred",          mapsTo sawCorePrimitivesModule "pred")
  , ("widthNat",      mapsTo sawCorePrimitivesModule "widthNat")
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
    -- Phase β polymorphic-helper routing: SAW 'gen' / 'atWithDefault'
    -- accept value-domain elements; under Phase β those arrive
    -- 'Except String'-wrapped. Route to the 'genM' / 'atWithDefaultM'
    -- wrappers in 'SAWCorePrimitives.lean' via 'mapsToWrapped' so the
    -- generic call-site lift doesn't double-wrap the already-Except
    -- result. SAW signatures: 'gen' takes 3 args (n, α, f);
    -- 'atWithDefault' takes 5 (n, α, d, v, i).
  , ("gen",           mapsToWrapped
                        [UseArgRaw, UseArgRaw, UseArgFunction]
                        (Lean.Ident "genM"))
  , ("atWithDefault", mapsToWrapped
                        [ UseArgRaw, UseArgRaw, UseArgWrapped
                        , UseArgWrapped, UseArgRaw
                        ]
                        (Lean.Ident "atWithDefaultM"))
  , ("shiftL",        mapsTo sawCorePrimitivesModule "shiftL")
  , ("shiftR",        mapsTo sawCorePrimitivesModule "shiftR")
  , ("rotateL",       mapsTo sawCorePrimitivesModule "rotateL")
  , ("rotateR",       mapsTo sawCorePrimitivesModule "rotateR")
  , ("equalNat",      mapsTo sawCorePrimitivesModule "equalNat")
  , ("ltNat",         mapsTo sawCorePrimitivesModule "ltNat")
  , ("leNat",         mapsTo sawCorePrimitivesModule "leNat")
    -- Phase β: 'foldr' / 'foldl' over wrapped vectors with wrapped
    -- folding functions. SAW 'foldr' / 'foldl' both take 6 args
    -- (α, β, n, f, z, v). The Lean target 'foldrM' / 'foldlM' have
    -- matching arity; the wrapped-helper convention records which
    -- positions are raw, function-shaped, and wrapped.
  , ("foldr",         mapsToWrapped
                        [ UseArgRaw, UseArgRaw, UseArgRaw, UseArgFunction
                        , UseArgWrapped, UseArgWrapped
                        ]
                        (Lean.Ident "foldrM"))
  , ("foldl",         mapsToWrapped
                        [ UseArgRaw, UseArgRaw, UseArgRaw, UseArgFunction
                        , UseArgWrapped, UseArgWrapped
                        ]
                        (Lean.Ident "foldlM"))
  , ("zip",           mapsTo sawCorePrimitivesModule "zip")
  , ("minNat",        mapsTo sawCorePrimitivesModule "minNat")
  , ("maxNat",        mapsTo sawCorePrimitivesModule "maxNat")
    -- IntMod (Cryptol's `Z n` quotient type) routed to Lean axioms
    -- in SAWCorePrimitives. Faithful to SAW's primitive
    -- declarations.
  , ("IntMod",        mapsTo sawCorePrimitivesModule "IntMod")
  , ("toIntMod",      mapsTo sawCorePrimitivesModule "toIntMod")
  , ("fromIntMod",    mapsTo sawCorePrimitivesModule "fromIntMod")
  , ("intModEq",      mapsTo sawCorePrimitivesModule "intModEq")
  , ("intModAdd",     mapsTo sawCorePrimitivesModule "intModAdd")
  , ("intModSub",     mapsTo sawCorePrimitivesModule "intModSub")
  , ("intModMul",     mapsTo sawCorePrimitivesModule "intModMul")
  , ("intModNeg",     mapsTo sawCorePrimitivesModule "intModNeg")
    -- Rational primitive bindings (Prelude.sawcore 2513-2550).
  , ("Rational",      mapsTo sawCorePrimitivesModule "Rational")
  , ("ratio",         mapsTo sawCorePrimitivesModule "ratio")
  , ("rationalEq",    mapsTo sawCorePrimitivesModule "rationalEq")
  , ("rationalLe",    mapsTo sawCorePrimitivesModule "rationalLe")
  , ("rationalLt",    mapsTo sawCorePrimitivesModule "rationalLt")
  , ("rationalAdd",   mapsTo sawCorePrimitivesModule "rationalAdd")
  , ("rationalSub",   mapsTo sawCorePrimitivesModule "rationalSub")
  , ("rationalMul",   mapsTo sawCorePrimitivesModule "rationalMul")
  , ("rationalNeg",   mapsTo sawCorePrimitivesModule "rationalNeg")
  , ("rationalRecip", mapsTo sawCorePrimitivesModule "rationalRecip")
  , ("rationalFloor", mapsTo sawCorePrimitivesModule "rationalFloor")
    -- Float / Double primitive bindings (Prelude.sawcore 2153-2165).
  , ("Float",         mapsTo sawCorePrimitivesModule "Float")
  , ("mkFloat",       mapsTo sawCorePrimitivesModule "mkFloat")
  , ("Double",        mapsTo sawCorePrimitivesModule "Double")
  , ("mkDouble",      mapsTo sawCorePrimitivesModule "mkDouble")
  , ("coerce",        mapsTo sawCorePrimitivesModule "coerce")
    -- SAW's `unsafeAssert α x y` is an assertion-without-proof:
    -- SAW claims @Eq α x y@ but never proves it. Translating as
    -- an axiom would import SAW's unsoundness; translating as a
    -- def that fabricates a proof would be the same mistake.
    --
    -- Correct: emit a proof obligation at the call site, paired
    -- with a sound discharge tactic that mirrors Rocq's
    -- `solveUnsafeAssert`. We drop SAW's 3 args (α, x, y) and
    -- replace the whole application with `(by saw_unsafeAssert)`;
    -- Lean's elaborator infers the expected type @Eq α x y@ from
    -- context and runs the tactic to discharge. Sound tactics
    -- only (rfl/decide/omega/proven simp); if it fails to
    -- discharge, elaboration errors loud — the open obligation
    -- becomes visible to the user.
  , ("unsafeAssert",
      replaceDropArgs 3 (Lean.Tactic "saw_unsafeAssert"))
    -- SAW's `Prelude.error : (a : isort 1) → String → a` produces
    -- a witness of any type "on error". `Term.translateIdentWithArgs`
    -- first gates this primitive with `shouldWrapBinder`: only wrapped
    -- value-domain result types may reach this macro. Raw Nat/Num
    -- indices, types, propositions/proofs, and function results reject
    -- before Lean emission.
    --
    -- For supported value-domain results, @error α msg@ becomes
    -- @saw_throw_error α msg@, which binds the (possibly wrapped)
    -- message argument before constructing the error. The msg is
    -- typically an @appendString …@ chain from Cryptol's @ecError@, so
    -- it arrives at type @Except String String@, not raw @String@.
    -- 'saw_throw_error' handles either case via 'Bind.bind'. Sound:
    -- no axiom.
  , ("error",
      IdentSpecialTreatment DefSkip
        (UseMacro 2 UseResultWrapped (\args ->
          case args of
            [α, msg] ->
              Lean.App (Lean.Var (Lean.Ident "saw_throw_error"))
                -- 'saw_throw_error' expects @msg : Except String
                -- String@. If the SAW msg arrived as a raw
                -- StringLit (e.g. @"at: index out of bounds"@,
                -- not the @appendString@ chain Cryptol uses for
                -- substitutions), lift with 'Pure.pure'.
                [α, liftRawValue msg]
            _ ->
              Lean.App (Lean.Var (Lean.Ident "saw_throw_error")) args)))

    -- Recursion primitives. Fully-applied `Prelude.fix` is intercepted before
    -- this table and emitted through either checked helper obligations or the
    -- generic unique-fixed-point obligation. Residual `fix_unfold` remains a
    -- rejected primitive proof principle.
  , ("fix", reject unsupportedFixReason)
  , ("fix_unfold", reject "fix_unfold is the unfolding lemma for \
                          \Prelude.fix. The Lean backend emits \
                          \proof-carrying fix terms instead of trusting \
                          \this primitive proof principle directly.")

    -- Inductive data types whose Lean side has no analog. These
    -- complement the explicit UnsoundRecursor throws in
    -- 'SAWCoreLean.Term.translateFTermF' (which catch direct
    -- `<DT>#rec` references); rejecting the data-type-name itself
    -- catches *value-level* uses too — e.g. a Cryptol value of
    -- type `Z` reaching the translator without normalization.
  , ("Z",              reject "SAWCore's `Z` (signed integer with \
                                \positives) has no Lean-side analog. \
                                \Z values and `Z#rec` are both refused; \
                                \refactor to a Cryptol shape that \
                                \specializes away `Z` (typically: use \
                                \`Integer` with explicit width or work \
                                \in bitvectors).")
  , ("AccessibleNat",  reject "SAWCore's `AccessibleNat` is the \
                                \well-foundedness witness for strong \
                                \induction; it has no Lean analog. \
                                \Refactor to bounded recursion via \
                                \`Vec n` / `gen` / `atWithDefault`.")
  , ("AccessiblePos",  reject "SAWCore's `AccessiblePos` is the \
                                \well-foundedness witness for strong \
                                \induction over `Pos`; same shape as \
                                \`AccessibleNat`. Refactor to bounded \
                                \recursion.")

    -- ListSort / FunsTo are SAW's internal encoding of Cryptol's
    -- algebraic enum types (`enum Color = Red | Green | Blue` and
    -- friends — anything beyond numeric ranges). Audit (2026-05-07):
    -- the translator-side discovery `discoverEnumEncodingReachers`
    -- in saw-central marks any def whose body uses these as opaque
    -- under `scNormalizeForLean` (otherwise scNormalize crashes
    -- with a SAWCore typing-context panic on the unfolded body).
    -- The opaque-marking lets the surface ListSort / FunsTo /
    -- recursor refs survive into the translator, where these
    -- entries fire — giving the user a clear "algebraic enums
    -- aren't yet supported" message instead of the generic
    -- unmapped-primitive default.
  , ("ListSort", reject "Cryptol algebraic enum types (`enum Color = Red \
                         \| Green | Blue` etc.) elaborate through SAW's \
                         \internal `ListSort` / `FunsTo` encoding, which \
                         \has no Lean-side realisation yet (CG-5 in \
                         \long-term-plan.md). Workaround: refactor to a \
                         \bitvector tag (`type Color = [2]; Red = 0; \
                         \Green = 1; Blue = 2`) — bitvector-based \
                         \enumerations translate cleanly today.")
  , ("ListSort__rec", reject "Cryptol algebraic enum case-analysis. See \
                              \`ListSort` reject entry for context and \
                              \workaround.")
  , ("LS_Nil", reject "Cryptol algebraic enum encoding (`ListSort` \
                       \nil-constructor). See `ListSort` reject entry.")
  , ("LS_Cons", reject "Cryptol algebraic enum encoding (`ListSort` \
                        \cons-constructor). See `ListSort` reject entry.")
  , ("FunsTo", reject "Cryptol algebraic enum case-analysis (the \
                       \variant-eliminator carrier). See `ListSort` \
                       \reject entry for context and workaround.")
  , ("FunsTo__rec", reject "Cryptol algebraic enum case-analysis. See \
                            \`ListSort` reject entry.")
  , ("FunsTo_Nil", reject "Cryptol algebraic enum eliminator. See \
                           \`ListSort` reject entry.")
  , ("FunsTo_Cons", reject "Cryptol algebraic enum eliminator. See \
                            \`ListSort` reject entry.")
  , ("FunsToIns", reject "Cryptol algebraic enum eliminator. See \
                          \`ListSort` reject entry.")

    -- ###########################################################
    -- Deliberately-unmapped Prelude primitives. Each must have a
    -- `reject` entry with a documented reason — the default
    -- treatment (in 'defaultTreatmentFor') already rejects, so the
    -- reasons here are what surface to the user. The audit
    -- 'auditPreludePrimitivesForLean' verifies this list stays
    -- exhaustive: any new Prelude addition without a matching
    -- entry here trips the smoketest.
    -- ###########################################################

    -- SMT-array primitives. Used by Crucible-driven extracts that
    -- touch memory; see CG-3 in the long-term plan.
  , ("Array",         reject "SMT-array primitives are not yet \
                              \mapped; needed for crucible_array-style \
                              \extracts. See CG-3 in long-term-plan.md.")
  , ("arrayConstant", reject "SMT-array primitives are not yet \
                              \mapped; needed for crucible_array-style \
                              \extracts. See CG-3 in long-term-plan.md.")
  , ("arrayLookup",   reject "SMT-array primitives are not yet \
                              \mapped; needed for crucible_array-style \
                              \extracts. See CG-3 in long-term-plan.md.")
  , ("arraySet",      reject "SMT-array primitives are not yet \
                              \mapped; needed for crucible_array-style \
                              \extracts. See CG-3 in long-term-plan.md.")
  , ("arrayCopy",     reject "SMT-array primitives are not yet \
                              \mapped; needed for crucible_array-style \
                              \extracts. See CG-3 in long-term-plan.md.")
  , ("arrayEq",       reject "SMT-array primitives are not yet \
                              \mapped; needed for crucible_array-style \
                              \extracts. See CG-3 in long-term-plan.md.")
  , ("arrayUpdate",   reject "SMT-array primitives are not yet \
                              \mapped; needed for crucible_array-style \
                              \extracts. See CG-3 in long-term-plan.md.")
  , ("arrayRangeEq",  reject "SMT-array primitives are not yet \
                              \mapped; needed for crucible_array-style \
                              \extracts. See CG-3 in long-term-plan.md.")

    -- String primitives. CG-4 (2026-05-07): mapped via Lean
    -- equivalents in CryptolToLean.SAWCorePrimitives. Surfaces in
    -- every real Cryptol workflow that uses `error "msg"` —
    -- Cryptol's `ecError` builds the SAW-side error string via
    -- `appendString` + `bytesToString`.
  , ("appendString",  mapsTo sawCorePrimitivesModule "appendString")
  , ("equalString",   mapsTo sawCorePrimitivesModule "equalString")
  , ("bytesToString", mapsTo sawCorePrimitivesModule "bytesToString")

    -- Vector with-proof variants — replace with atWithDefault /
    -- gen / etc. when Lean lacks the proof obligation we need.
  , ("atWithProof",       reject "with-proof Vec variants not mapped; \
                                   \use atWithDefault instead, or refactor \
                                   \to thread the proof manually.")
  , ("genWithProof",      reject "with-proof Vec variants not mapped; \
                                   \use gen instead, or refactor to thread \
                                   \the proof manually.")
  , ("updWithProof",      reject "with-proof Vec variants not mapped; \
                                   \use upd instead, or refactor.")
  , ("sliceWithProof",    reject "with-proof Vec variants not mapped; \
                                   \use slice instead, or refactor.")
  , ("updSliceWithProof", reject "with-proof Vec variants not mapped; \
                                   \use updSlice instead, or refactor.")

    -- SAW-internal Nat / Int / bv lemma primitives. These have type
    -- 'Eq ...' / 'IsLeNat ...' / similar; they're SAW-side proof
    -- obligations, not translator-emitted Cryptol code. Mapping
    -- each requires writing the equivalent Lean proof.
  , ("bvForall",        reject "SAW-internal proof primitive (bvForall); \
                                 \mapping requires a Lean realization. \
                                 \Not currently used in Cryptol-emission paths.")
  , ("bvEqToEq",        reject "SAW-internal proof primitive (bvEqToEq); \
                                 \use bvEq_iff in CryptolToLean.SAWCoreBitvectorsProofs.")
  , ("bvEqToEqNat",     reject "SAW-internal proof primitive (bvEqToEqNat); \
                                 \mapping requires a Lean realization.")
  , ("bvultToIsLtNat",  reject "SAW-internal proof primitive; mapping requires \
                                 \a Lean realization.")
  , ("equalNatToEqNat", reject "SAW-internal proof primitive; mapping requires \
                                 \a Lean realization.")
  , ("expByNat",        reject "SAW-internal proof primitive; mapping requires \
                                 \a Lean realization.")
  , ("proveLeNat",      reject "SAW-internal proof primitive; mapping requires \
                                 \a Lean realization.")
  , ("natCompareLe",    reject "SAW-internal proof primitive; mapping requires \
                                 \a Lean realization.")
  , ("intAbs",          reject "Int primitive (intAbs) not mapped; needs Lean \
                                 \realization.")
  , ("intMin",          reject "Int primitive (intMin) not mapped; needs Lean \
                                 \realization.")
  , ("intMax",          reject "Int primitive (intMax) not mapped; needs Lean \
                                 \realization.")

    -- Vector primitives we use atWithDefault / gen for.
  , ("head",     reject "Vec.head is replaced by atWithDefault on the Lean side; \
                         \refactor or supply a wrapper.")
  , ("tail",     reject "Vec.tail is not yet mapped; use atWithDefault / gen \
                         \patterns instead.")
  , ("EmptyVec", reject "EmptyVec not mapped; emit Vector.nil-shaped output \
                         \through gen instead.")
  , ("scanl",    reject "Prelude.scanl not mapped on bounded vectors yet; \
                         \streamScanl covers the stream case.")

    -- SAW-internal proof primitives / lemma axioms. SAW-Prelude
    -- lemmas used during SAW-side proof obligations, not in
    -- translator-emitted Cryptol code paths.
  , ("uip",                  reject "SAW-internal proof axiom. \
                                     \Will surface as a Lean theorem once \
                                     \we have a DefReplace path for SAW \
                                     \axioms that are provable in Lean.")
  , ("coerce__eq",           reject "SAW-internal coerce-equality axiom. \
                                    \Will surface as a Lean theorem once \
                                    \we have a DefReplace path for SAW \
                                    \axioms that are provable in Lean.")
  , ("ite_bit",              reject "SAW-internal proof primitive (ite_bit).")
  , ("ite_split_cong",       reject "SAW-internal proof primitive (ite_split_cong).")
  , ("ite_join_cong",        reject "SAW-internal proof primitive (ite_join_cong).")
  , ("eqNatPrec",            reject "SAW-internal proof primitive (eqNatPrec).")
  , ("eqNatAdd0",            reject "SAW-internal proof primitive (eqNatAdd0).")
  , ("eqNatAddS",            reject "SAW-internal proof primitive (eqNatAddS).")
  , ("eqNatAddComm",         reject "SAW-internal proof primitive (eqNatAddComm).")
  , ("addNat_assoc",         reject "SAW-internal proof primitive (addNat_assoc).")
  , ("IsLtNat_Zero_absurd",  reject "SAW-internal proof primitive (IsLtNat_Zero_absurd).")
  , ("IsLeNat_SuccSucc",     reject "SAW-internal proof primitive (IsLeNat_SuccSucc).")
  , ("IsLtNat_to_bvult",     reject "SAW-internal proof primitive (IsLtNat_to_bvult).")
  , ("bvult_to_IsLtNat",     reject "SAW-internal proof primitive (bvult_to_IsLtNat).")
  , ("head_gen",             reject "SAW-internal proof primitive (head_gen).")
  , ("tail_gen",             reject "SAW-internal proof primitive (tail_gen).")
  , ("at_single",            reject "SAW-internal proof primitive (at_single).")
  , ("foldr_nil",            reject "SAW-internal proof primitive (foldr_nil).")
  , ("foldr_cons",           reject "SAW-internal proof primitive (foldr_cons).")
  , ("foldl_nil",            reject "SAW-internal proof primitive (foldl_nil).")
  , ("foldl_cons",           reject "SAW-internal proof primitive (foldl_cons).")
  , ("vecEq_refl",           reject "SAW-internal proof primitive (vecEq_refl).")
  , ("take0",                reject "SAW-internal proof primitive (take0).")
  , ("drop0",                reject "SAW-internal proof primitive (drop0).")
  , ("map_map",              reject "SAW-internal proof primitive (map_map).")

    -- bv-equation lemmas.
  , ("bvNat_bvToNat",         reject "SAW-internal bv lemma (bvNat_bvToNat).")
  , ("bvAddZeroL",            reject "SAW-internal bv lemma (bvAddZeroL); \
                                       \use bvAdd_id_l in SAWCoreBitvectorsProofs.")
  , ("bvAddZeroR",            reject "SAW-internal bv lemma (bvAddZeroR); \
                                       \use bvAdd_id_r in SAWCoreBitvectorsProofs.")
  , ("bvShiftL_bvShl",        reject "SAW-internal bv lemma (bvShiftL_bvShl).")
  , ("bvShiftR_bvShr",        reject "SAW-internal bv lemma (bvShiftR_bvShr).")
  , ("bvEq_refl",             reject "SAW-internal bv lemma; use bvEq_refl in \
                                       \SAWCoreBitvectorsProofs.")
  , ("equalNat_bv",           reject "SAW-internal bv lemma (equalNat_bv).")
  , ("bveq_sameL",            reject "SAW-internal bv lemma (bveq_sameL).")
  , ("bveq_sameR",            reject "SAW-internal bv lemma (bveq_sameR).")
  , ("bveq_same2",            reject "SAW-internal bv lemma (bveq_same2).")
  , ("not_bvult_zero",        reject "SAW-internal bv lemma; use isBvult_n_zero.")
  , ("trans_bvult_bvule",     reject "SAW-internal bv lemma (trans_bvult_bvule).")
  , ("bvult_sub_add_bvult",   reject "SAW-internal bv lemma (bvult_sub_add_bvult).")
  , ("bvult_sum_bvult_sub",   reject "SAW-internal bv lemma (bvult_sum_bvult_sub).")

    -- bv-bound assertions. SAW threads Cryptol size proofs through
    -- these; under Lean specialization the size obligations are
    -- always concrete-Nat so the assertion isn't surfaced.
  , ("unsafeAssertBVULt", reject "Cryptol size-bound assertion; under Lean \
                                   \specialization sizes are concrete and the \
                                   \assertion shouldn't surface.")
  , ("unsafeAssertBVULe", reject "Cryptol size-bound assertion; under Lean \
                                   \specialization sizes are concrete and the \
                                   \assertion shouldn't surface.")

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
  | all okChar str
  , not (str `Set.member` leanReservedWords)
  , not (escapePrefix `Data.List.isPrefixOf` str) =
      Lean.Ident str
  | otherwise = Lean.Ident (escapePrefix ++ zEncodeString str)
 where
   okChar x = isAlphaNum x || x `elem` ("_'" :: String)
   -- The escape namespace is disjoint from the passthrough
   -- namespace by reserving the @Op_@ prefix entirely. A SAW name
   -- that happens to begin with @Op_@ (e.g. a literal @Op_foo@)
   -- gets re-escaped to @Op_Opzufoo@ rather than passed through —
   -- otherwise it would collide with the escaped form of @foo!@,
   -- @match@, etc. Z-encoding's @_@ → @zu@ rule makes the two
   -- namespaces disjoint.
   escapePrefix = "Op_"

-- | Conservative list of Lean 4 reserved words and elaborator-
-- significant identifiers that could realistically collide with
-- Cryptol or SAWCore identifiers. A SAW name in this set gets
-- Z-encoded with an @Op_@ prefix even if it's otherwise
-- alphanumeric — so a Cryptol function called @match@ or @do@
-- doesn't fail elaboration with a parse error.
--
-- L-11 lockdown: this is the irreducible "names that look fine but
-- aren't" list. We err on the side of conservatism — false positives
-- (a name we escape that wouldn't have collided) make output
-- slightly uglier; false negatives leak as Lean elaboration
-- failures. The set is enumerated rather than auto-derived because
-- Lean's keyword set is internal to its parser and shifts between
-- versions; if a future Lean release adds a keyword Cryptol code
-- happens to use, this list catches it without a Lean upgrade
-- breaking SAW.
leanReservedWords :: Set String
leanReservedWords = Set.fromList
  [ "def", "theorem", "lemma", "example", "axiom", "class", "instance"
  , "structure", "inductive", "open", "import", "namespace", "end"
  , "match", "with", "fun", "let", "have", "show", "if", "then", "else"
  , "do", "for", "while", "where", "mutual", "partial", "noncomputable"
  , "private", "protected", "unsafe", "inline", "attribute", "notation"
  , "prefix", "infix", "infixl", "infixr", "postfix", "macro", "elab"
  , "syntax", "section", "variable", "universe", "abbrev"
  , "Type", "Sort", "Prop"
  ]
