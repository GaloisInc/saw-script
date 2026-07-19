{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

{- |
Module      : SAWCoreLean.Convention
Copyright   : Galois, Inc. 2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : portable

The position/callee calculus vocabulary and the term-translation
monad: every convention type the calculus assigns (positions, arg
modes, result modes, binding shapes, recursor/motive/Eq.rec
conventions), the translation Γ ('TranslationReader' /
'TranslationState') expressed over that vocabulary, and the basic
identifier/shape helpers with no translator recursion. Extracted
from "SAWCoreLean.Term" in the 2026-07-17 module split (SWE review
finding 2); the recursive translator and every @lower*@ obligation
emitter stay in "SAWCoreLean.Term". Rocq keeps the analogous
(much smaller) monad inline in @SAWCoreRocq.Term@ — the split is a
documented Lean-backend divergence earned by the calculus scope.
-}

module SAWCoreLean.Convention
  ( -- generated vocabulary + Γ + helpers (see module doc)
    module SAWCoreLean.Convention
  ) where
import           Control.Lens                 (makeLenses, over, set, view)
import           Control.Monad.Reader         (MonadReader(local), asks)
import           Control.Monad.State          (gets, modify)
import           Data.IntMap.Strict           (IntMap)
import           Data.Maybe                   (mapMaybe)
import qualified Data.Map                     as Map
import           Data.Map                     (Map)
import qualified Data.Set                     as Set
import           Data.Set                     (Set)
import qualified Data.Text                    as Text
import           Prelude                      hiding (fail)

import qualified Language.Lean.AST            as Lean

import           SAWCore.Module               (ModuleMap)
import           SAWCore.Name
import           SAWCore.Recognizer
import           SAWCore.SharedTerm
import           SAWCore.Term.Functor

import           SAWCoreLean.Monad
import           SAWCoreLean.SpecialTreatment


-- | A Lean identifier introduced for a shared subterm via let-binding.
-- Audit P-1 (2026-05-06) revealed that without sharing, the translator
-- re-translates each shared subterm 2^N times for N nested aliases —
-- ate ~100 GB on Salsa20. Mirrors @SAWCoreRocq.Term.SharedName@.
newtype SharedName = SharedName { sharedNameIdent :: Lean.Ident }
  deriving Show

-- | Expected-shape migration state for Lean identifiers in scope. This
-- replaces the old one-bit "wrapped variable" set: a variable can be an
-- outer 'Except' value, a function-shaped value, or a raw/type-like
-- value. Only 'BindingWrapped' should be unwrapped with 'Bind.bind'.
data BindingShape
  = BindingRaw
  | BindingWrapped
  | BindingFunction
  deriving (Eq, Show)

data RawReason
  = RawValuePosition
  | RawTypePosition
  | RawIndexPosition
  | RawPropositionPosition
  | RawProofPosition
  | RawMotivePosition
  | RawLogicalPosition
  | StructuralRecursorFieldPosition
  deriving (Eq, Show)

data ExpectedPosition
  = ExpectRuntimeValue
  | ExpectRaw RawReason
  | ExpectFunctionPosition (Maybe FunctionConvention)
    -- ^ A function position. @'Just' c@ carries the declared
    -- convention that drives binder/result positions. 'Nothing' is a
    -- PERMANENT production, not a migration bridge: some surrounds
    -- (e.g. Eq.rec branch/carrier transport) legitimately demand "a
    -- function delivered structurally" without constraining its
    -- binder positions — Lean's typechecker guards the arity.
  deriving (Eq, Show)

-- | Calculus §Positions: a function position recursively assigns a
-- position to each binder and to the result. 'fcArgPositions' is
-- outermost-first and must cover every binder of the lambda it is
-- applied to (translation rejects otherwise — no silent padding).
data FunctionConvention = FunctionConvention
  { fcArgPositions   :: [ExpectedPosition]
  , fcResultPosition :: ExpectedPosition
  }
  deriving (Eq, Show)

-- | What a recursor motive's body computes (plan Slice 3c; calculus
-- §Recursors — "motive result position" is a declared convention
-- field). This is deliberately NOT a 'FunctionConvention' result
-- position: a motive's body is a TYPE-level expression, and a
-- value-computing motive wraps its body type in @Except String@
-- ('wrapExcept') — never a 'Pure.pure' value lift.
data MotiveResultMode
  = MotiveComputesRuntimeValueType
    -- ^ Phase-β value motive: the body type wraps
    -- (@… → Except String T@).
  | MotiveComputesRawType
    -- ^ Type/proof/function motive: the body type stays raw.
  | MotiveComputesTypeImage
    -- ^ Type-subject transport motive (calculus §Raw Logical Callees,
    -- type-subject sub-case, 2026-07-19): the motive body is
    -- type/prop-level content translated in the CURRENT mode with no
    -- mode flip — the subject images fix the type interpretation, so
    -- in ambient Phase-β content embedded value-domain Pis wrap to
    -- their T-images (matching the branch and the consuming value
    -- transport), and inside raw logical mode everything stays raw.
  deriving (Eq, Show)

-- | Declared convention for a recursor motive: per-binder positions
-- (datatype indices, then the eliminated scrutinee) and the result
-- mode. Produced by the recursor dispatch, consumed by
-- 'translateMotiveAtConvention'.
data MotiveConvention = MotiveConvention
  { mcBinderPositions :: [ExpectedPosition]
  , mcResultMode      :: MotiveResultMode
  }
  deriving (Eq, Show)

-- | Calculus §Callee Conventions: the explicit per-argument mode of a
-- callee convention (plan Slice 4a). An 'ArgMode' declares what the
-- callee's formal IS, and the convention interpreter derives from it
-- both the actual's expected position and the allowed adaptation:
--
--   * 'RuntimeArg' actuals adapt to runtime values ('Pure.pure' lift
--     of raws);
--   * 'IndexArg' actuals must arrive raw; a *wrapped* runtime-computed
--     index is sequenced through an error-preserving 'Bind.bind'
--     ahead of the application (never opened, never defaulted), and a
--     function-shaped actual is forbidden;
--   * 'TypeArg' / 'RawValueArg' / proof-family actuals must arrive
--     raw; anything else is forbidden;
--   * 'ProofArg' marks a source proof argument that is dropped at
--     emission and re-proved as a Lean obligation;
--   * 'FunctionWithNatLtArg' is the PERMANENT convention for
--     proof-carrying generator functions whose index is bounded by
--     the helper argument at the given (post-drop) position (e.g.
--     'genWithBoundsM' callbacks receiving @i < n@ evidence). A
--     once-planned fold into 'FunctionArg' never proved necessary —
--     the evidence-threading slot is what distinguishes it.
data ArgMode
  = TypeArg
  | IndexArg
  | RuntimeArg
  | RawValueArg
  | ProofArg
  | PropositionArg
  | MotiveArg
  | StructuralFieldArg
  | FunctionArg (Maybe FunctionConvention)
  | FunctionWithNatLtArg Int
  deriving (Eq, Show)

-- | Calculus §Callee Conventions: a convention's declared result mode.
-- Today every checked-application contract declares 'RuntimeResult';
-- the 'RawResult'/'FunctionResult' arms are the calculus's declared
-- vocabulary, kept so a future contract with a raw or function result
-- states its mode in the table rather than growing a side channel
-- (release audit 2026-07-14: declared-but-unproduced, deliberate).
data ResultMode
  = RuntimeResult
  | RawResult RawReason
  | FunctionResult FunctionConvention
  deriving (Eq, Show)

data EqualitySubjectRep
  = EqualitySubjectRuntimeValue
  | EqualitySubjectRaw RawReason
  | EqualitySubjectRawFunction
    -- ^ Function-carrier equality (plan Slice 5c): the subjects are
    -- function-shaped and the carrier is the CURRENT-mode translation
    -- of the source function type — in raw logical content (e.g. the
    -- auto-emitted Prelude's @inverse_eta_rule@) that is the raw
    -- @a -> b@ the lemma quantifies over; in Phase-β value content it
    -- is the translated effectful type. Never a rawified value-level
    -- signature: the carrier compares the functions SAW actually
    -- denotes in that mode. Subjects deliver structurally (a function
    -- undergoes no representation change); a wrapped operand mixed
    -- with a function subject rejects — the carrier would not be
    -- uniquely determined.
  | EqualitySubjectTypeImage
    -- ^ Type-subject equality (2026-07-19; calculus §Raw Logical
    -- Callees, type-subject sub-case): the carrier @a@ is a SORT, so
    -- the subjects are TYPES — decided by D (@asSort@ on the carrier),
    -- never by operand production shapes. The whole spine translates
    -- MODE-UNIFORMLY in the current mode's type translation: T-images
    -- in ambient Phase-β content (wrapped value arrows — what a value
    -- transport at T-carriers consumes), raw inside raw logical mode
    -- (where current-mode and raw coincide by construction). A
    -- type-level congruence spine is parametric in the type
    -- interpretation, so leaves re-check at the chosen images: a Refl
    -- leaf needs the images Lean-defeq and an unsafeAssert leaf states
    -- its obligation at the images — divergence is a loud failed
    -- elaboration or an unprovable obligation, never silent.
  deriving (Eq, Show)

data RawLogicalCallee
  = RawLogicalEq
  | RawLogicalRefl
  | RawLogicalEqRec
  deriving (Eq, Show)

-- | The full @Eq.rec@ field set the calculus requires (§Raw Logical
-- Callees, plan Slice 5b): every position a proof transport touches
-- is a declared field, so the operands, the motive's binders and
-- result, the branch, the proof, and the final result are consistent
-- BY CONSTRUCTION — never by translation-mode coincidence.
--
-- All fields derive from the declared subject representation ρ_eq at
-- convention-construction time ('eqRecConventionForStandalone'); the
-- lowering consumes only the record and never re-inspects operands.
data EqRecConvention = EqRecConvention
  { ercSubjectRep    :: EqualitySubjectRep
    -- ^ Operand position ρ_eq: the representation @x@ and @y@ stand at.
  , ercCarrierLevel  :: Maybe Lean.UnivLevel
    -- ^ Universe class of the carrier @SubjectRep(a, ρ_eq)@. Recorded
    -- for the trace/audit record; @Eq.rec@ itself is emitted without
    -- explicit universes (Lean elaborates them from the motive), and
    -- the motive's inner equality proposition emits its own @.{k}@
    -- through the standalone path.
  , ercMotive        :: MotiveConvention
    -- ^ Motive binder positions (@y@ at ρ_eq, the equality proof at a
    -- raw proof position) and the motive result mode.
  , ercBranchPosition :: ExpectedPosition
    -- ^ Branch position: the motive result at @y := x@.
  , ercProofPosition :: RawReason
    -- ^ Proof position (always a raw proof; its interpreter follows
    -- ρ_eq so equality nodes INSIDE the proof term classify their
    -- subjects consistently with the declared carrier).
  , ercResultShape   :: BindingShape
    -- ^ Final result position, as the shape the surround adapts.
  }
  deriving (Show)

-- NOTE (plan Slice 4c): the old 'CalleeConvention' enum — including
-- its 'CalleeTransitional' constructor — is DELETED, not filled in.
-- Only its raw-logical arm was ever consumed; the dispatch's real
-- classifier is the declarative guard chain over the contract tables
-- ('translateIdentWithArgsWithShape') with declared 'ArgMode' slots.
-- 'CalleeTransitional' count: zero, permanently.

data RecursorScrutineeMode
  = RecursorScrutineeRaw
  | RecursorScrutineeWrapped
  deriving (Eq, Show)

data RecursorResultMode
  = RecursorReturnsWrappedValue
  | RecursorReturnsRawTypeOrProof
  | RecursorReturnsFunction
  deriving (Eq, Show)

data RecursorConvention = RecursorConvention
  { recScrutineeMode :: RecursorScrutineeMode
  , recResultMode    :: RecursorResultMode
  , recMotiveResultPosition :: ExpectedPosition
    -- ^ The declared motive result position (plan Slice 6.1;
    -- calculus §Recursors): the single source
    -- 'recursorMotiveResultPosition' computes and from which
    -- 'recResultMode' and 'recFinalShape' DERIVE. Consumed directly
    -- by 'motiveConventionFor' for the motive's result mode.
  , recFinalShape    :: BindingShape
  }
  deriving (Eq, Show)

-- | A translated term plus its Phase-β representation. Expected
-- positions are DEMANDED, not stored: ρ flows through the explicit
-- parameter of 'translateSharedAt' / 'translateAt' and the declared
-- conventions, and consistency is checked at production time
-- ('tracePositionAt' / 'shapeConsistentWithPosition'). A stored
-- produced-at stamp existed during the position-directed migration
-- but was a write-only ghost — nothing ever branched on it — and was
-- removed by the 2026-07-14 release audit.
data TranslatedTerm = TranslatedTerm
  { ttLean  :: Lean.Term
  , ttShape :: BindingShape
  }
  deriving Show

translatedTermLean :: TranslatedTerm -> Lean.Term
translatedTermLean = ttLean

-- | Per-binding record for the calculus's Γ. Today its payload is
-- the binder's Phase-β representation — the one thing every
-- adaptation use site consults. The Slice-1 migration provisionally
-- carried richer fields (bound position, source type, emitted Lean
-- type) as a landing pad for consumers that were expected in
-- Slices 2/5; those consumers were ultimately served by declared
-- conventions instead and the write-only fields were removed by the
-- 2026-07-14 release audit. Re-enrich this record (rather than
-- adding side tables) if a future consumer genuinely needs more of
-- Γ per binder.
newtype BindingInfo = BindingInfo
  { biRepr :: BindingShape
    -- ^ Phase-β representation of the bound Lean identifier.
  }

data ValueTranslationMode
  = WrappedValueMode
  | RawValueMode
  deriving (Eq, Show)

data SortBinderMode
  = SortBinderAsSort
  | SortBinderAsType
  deriving (Eq, Show)

-- | Read-only state for translating terms.
data TranslationReader = TranslationReader
  { _namedEnvironment  :: Map VarName Lean.Ident
    -- ^ SAWCore variable names in scope, paired with the Lean identifier
    -- they translate to.
  , _skipBinderWrap    :: Bool
    -- ^ When True, 'translateBinder'' emits binder types without
    -- the 'Except String' wrap. Set in two situations:
    --
    --   * Motive abstractions whose body is type-level (a
    --     'Lambda' with 'isTypeProducing' body, or a 'Pi' whose
    --     return is 'Sort'/'Pi'). The binders are scrutinees for
    --     recursor elimination and must arrive at the inductive's
    --     raw type. Set blanket-True for the whole binder list.
    --
    --   * Individual *type-arg* binders inside a value-level
    --     abstraction — variables that appear in subsequent
    --     binder types or the return type as indices (the @n@ in
    --     @bvAdd : (n : Nat) → Vec n Bool → …@). Set transiently
    --     per-binder by 'translateBindersSelective'.
    --
    -- The flag does not propagate into 'f' continuations of
    -- 'translateBinder'': the wrap decision is one-shot per
    -- binder, surrounding bindings re-assert their own value.
  , _inRecursorCaseBinder :: Bool
    -- ^ True during translation of a recursor case-handler's
    -- binder types (NOT during the case body). Inhibits both the
    -- 'translateBinder'' outer wrap AND the Pi case's body-wrap,
    -- so case-handler binder types stay raw and match Lean's
    -- @Foo.rec@ signature. Set transiently by 'translateRecursorApp'
    -- when descending into a case-handler argument's Lambda binders;
    -- cleared by the 'Lambda' case before translating the body.
  , _bindingEnv :: Map Lean.Ident BindingInfo
    -- ^ Γ: Lean identifiers in scope paired with everything their
    -- introduction site knew about them ('BindingInfo'). The
    -- 'biRepr' projection is used at application and recursor-app
    -- sites to decide whether a variable is an outer 'Except' value
    -- that must be 'Bind.bind'-ed, a function-shaped value that
    -- should be passed directly, or raw. The remaining fields
    -- (bound position, source type, exact Lean type) are the
    -- calculus's binding record (plan Slice 1); they are recorded
    -- but not yet consulted — Slices 2–5 make them the authority
    -- for adaptation and proof transport.
  , _natBoundsEnv :: Map Lean.Ident Lean.Term
    -- ^ Exclusive Nat upper-bound facts in scope: binder identifiers
    -- introduced with an @h_gen_bounds_ : i < n@ hypothesis, mapped
    -- to their bound term @n@. Consulted by the @at@ contract's
    -- interval-entailment decision (OP-2,
    -- doc/2026-07-12_obligation-placement-design.md): the
    -- proof-carrying lowering fires only when these facts entail the
    -- emitted bound; otherwise the runtime-checked accessor is the
    -- honest form.
  , _boundUniverses    :: Map VarName Lean.UnivLevel
    -- ^ For SAWCore variables whose binder type is @sort k@ at @k ≥ 1@,
    -- the universe variable that 'translateSort' allocated for the
    -- binder. Looked up at use sites by 'levelOfArg' so the translator
    -- can supply explicit @\.{u_n}@ universes to polymorphic Lean
    -- targets (mathport pattern). Variables not in this map have a
    -- non-sort binder type and contribute no universe at use sites.
  , _unavailableIdents :: Set Lean.Ident
    -- ^ Lean identifiers already reserved or in use. Used to pick fresh
    -- names that don't shadow.
  , _sawModuleMap      :: ModuleMap
    -- ^ The environment of SAWCore global definitions, used to resolve
    -- 'Constant' references to their bodies for inline translation.
  , _currentModule     :: Maybe ModuleName
    -- ^ The SAWCore module currently being translated. When a
    -- 'UsePreserve' reference targets this module, emit the short
    -- name unqualified — Lean's namespace scoping already provides
    -- the prefix.
  , _sharedNames       :: IntMap SharedName
    -- ^ Index of identifiers for repeated subterms that have been
    -- lifted into a top-level @let@. Populated by 'translateTermLet'
    -- before recursive descent; consulted by 'translateTerm' on
    -- 'STApp' so a hash-consed subterm with multiple occurrences
    -- emits as a 'Lean.Var' reference instead of being re-translated.
  , _nextSharedName    :: Lean.Ident
    -- ^ Counter used to mint fresh names for shared subterms.
    -- 'freshVariant' threads it through 'unavailableIdents' so the
    -- chosen names don't collide with anything else in scope.
  , _valueTranslationMode :: ValueTranslationMode
    -- ^ Whether this translation pass applies Phase-beta's wrapped
    -- value-domain convention. Auto-emitted proof/type Prelude
    -- infrastructure uses 'RawValueMode'; user terms and value-domain
    -- Prelude facades use 'WrappedValueMode'.
  , _sortBinderMode :: SortBinderMode
    -- ^ How a bare SAWCore sort binder should be emitted. Normal raw
    -- logical binders use @Sort u@. Wrapped value facades can bind
    -- carrier types as @Type u@ so terms like @Except String α@ are
    -- well-formed in Lean.
  }

makeLenses ''TranslationReader

-- | Mutable state collected during translation.
data TranslationState = TranslationState
  { _globalDeclarations   :: [Lean.Ident]
    -- ^ Lean names for SAWCore constants we should /not/ re-emit
    -- (either already translated or explicitly skipped by the caller).
  , _topLevelDeclarations :: [Lean.Decl]
    -- ^ Auxiliary Lean declarations discovered while translating a
    -- term — the bodies of the SAWCore constants it references.
    -- Stored most-recently-added first, reversed on output.
  , _universeVars         :: [String]
    -- ^ Universe-variable names allocated during translation of
    -- the current declaration, in *binder-introduction order* —
    -- most-recently-allocated last. Used to populate the def's
    -- universe list (@def foo.{u0 u1} …@) in the order Lean
    -- expects (mathport convention: introduction order).
    -- A 'Set' lookup would lose order; we maintain order
    -- explicitly because call-site emission threads positional
    -- references back through this list.
  , _universeVarCount     :: Int
    -- ^ Counter for generating fresh @u0@, @u1@, … names. Bumped
    -- once per 'BinderPos' allocation in 'translateSort'.
  , _universeBinderAssignments :: Map VarName String
    -- ^ Memoization of universe-name allocations by SAWCore
    -- 'VarName'. 'translateDefDoc' walks the body and type
    -- *separately*, but both may encounter the same SAWCore
    -- binder (lambda body, pi type) which carries the same
    -- 'vnIndex'. Without memoization each walk would allocate a
    -- fresh universe, producing inconsistent 'Sort u_n' / 'Sort u_m'
    -- emissions for what is logically one binder. The map keys
    -- compare by 'VarIndex' (the global uniqueness invariant),
    -- so body-side and type-side encounters of the same logical
    -- variable resolve to the same allocation.
  }

makeLenses ''TranslationState

type TermTranslationMonad m =
  TranslationMonad TranslationReader TranslationState m

askTR :: TermTranslationMonad m => m TranslationReader
askTR = asks otherConfiguration

localTR :: TermTranslationMonad m =>
           (TranslationReader -> TranslationReader) -> m a -> m a
localTR f =
  local (\r -> r { otherConfiguration = f (otherConfiguration r) })

phaseBetaEnabled :: TermTranslationMonad m => m Bool
phaseBetaEnabled =
  (== WrappedValueMode) . view valueTranslationMode <$> askTR

withRawTranslationMode :: TermTranslationMonad m => m a -> m a
withRawTranslationMode =
  localTR ( set valueTranslationMode RawValueMode
          . set skipBinderWrap True
          . set sortBinderMode SortBinderAsSort
          )

-- | A subset of Lean 4's reserved identifiers. Not exhaustive — the
-- Lean parser has more — but covers the ones most likely to collide
-- with names generated from SAWCore.
reservedIdents :: Set Lean.Ident
reservedIdents =
  Set.fromList $ map Lean.Ident $ concatMap words
    -- @_@ is intentionally *not* reserved: Lean accepts @fun _ => …@
    -- and @(_ : A) -> B@ as valid anonymous-binder syntax. Treating
    -- @_@ as reserved was making the translator rename anonymous
    -- SAWCore binders to @_'@ / @_''@ / @_'''@ (audit finding 2C-3).
    [ "axiom def example fun if then else let rec match with"
    , "namespace end section open import variable instance theorem"
    , "Prop Type Sort by do return"
    ]

-- | The context in which a SAWCore 'Sort' appears determines how
-- we translate it into Lean. The two cases produce structurally
-- different Lean shapes:
--
--   * 'BinderPos' — the sort is the TYPE of a Pi/Lambda binder, as
--     in @(t : sort 1) → …@. At sort level @≥ 1@ we allocate a
--     fresh universe variable per occurrence (never share across
--     binders — the parked P4 "share by level" approach was
--     unsound; see @archive/2026-04-22_universe-internal-
--     investigation.md@). At sort 0 we emit Lean's concrete @Type@.
--
--   * 'ValuePos' — the sort is itself a value argument, as in
--     @Eq (sort 0) a b@. We emit a concrete Lean @Sort k@ literal:
--     @sort 0@ ↦ @Type@ (= @Type 0@), @sort 1@ ↦ @Type 1@, etc.
--     The "+1 shift" lives in the caller's universe-arithmetic,
--     not here.
data SortContext
  = BinderPos
  | TypeCarrierPos
  | ValuePos
  deriving (Show, Eq)

-- | Translate a SAWCore 'Sort' to a Lean 'Lean.Sort', threading
-- universe constraints into the surrounding declaration's universe
-- list when context is 'BinderPos'.
--
-- Soundness contract (the new L-10): at 'BinderPos' with sort
-- @k ≥ 1@, each call allocates a *fresh* universe variable — never
-- sharing with any prior allocation. Sharing was the bug the
-- parked WIP attempt parked on; the new architecture is correct
-- because each binder's universe constraint is independent of
-- every other binder's.
translateSort :: TermTranslationMonad m => SortContext -> Sort -> m Lean.Sort
translateSort _   PropSort     = pure Lean.Prop
translateSort _   (TypeSort 0) = pure Lean.Type
translateSort ctx (TypeSort k) = case ctx of
  ValuePos -> pure (Lean.TypeLvl (toInteger k))
  TypeCarrierPos -> do
    n <- gets (view universeVarCount)
    let uname = "u" ++ show n
    modify (over universeVars (++ [uname]))
    modify (over universeVarCount (+ 1))
    pure (Lean.TypeVar uname)
  BinderPos -> do
    n <- gets (view universeVarCount)
    let uname = "u" ++ show n
    modify (over universeVars (++ [uname]))
    modify (over universeVarCount (+ 1))
    pure (Lean.SortVar uname)

-- | Append @'@ until the identifier is not in use.
nextVariant :: Lean.Ident -> Lean.Ident
nextVariant (Lean.Ident s) = Lean.Ident (s ++ "'")

freshVariant :: TermTranslationMonad m => Lean.Ident -> m Lean.Ident
freshVariant x = do
  used <- view unavailableIdents <$> askTR
  let findVariant i = if Set.member i used then findVariant (nextVariant i) else i
  pure (findVariant x)

freshVariantAvoiding :: TermTranslationMonad m => Set Lean.Ident -> Lean.Ident -> m Lean.Ident
freshVariantAvoiding extra x = do
  used <- Set.union extra . view unavailableIdents <$> askTR
  let findVariant i = if Set.member i used then findVariant (nextVariant i) else i
  pure (findVariant x)

withUsedLeanIdent :: TermTranslationMonad m => Lean.Ident -> m a -> m a
withUsedLeanIdent ident =
  localTR (over unavailableIdents (Set.insert ident))

-- | SAWCore local name to a safe, fresh Lean identifier. We escape
-- before freshening so dot-containing SAW names (e.g. record-field
-- variables `p1.x` introduced by `llvm_fresh_var`) get Z-encoded
-- rather than emitted as `(p1.x : ...)` which Lean rejects (`.` is
-- the namespace separator).
translateLocalIdent :: TermTranslationMonad m => LocalName -> m Lean.Ident
translateLocalIdent x = freshVariant (escapeIdent (Lean.Ident (Text.unpack x)))

withSAWVar :: TermTranslationMonad m => VarName -> (Lean.Ident -> m a) -> m a
withSAWVar n f = do
  n_lean <- translateLocalIdent (vnName n)
  withUsedLeanIdent n_lean $
    localTR (over namedEnvironment (Map.insert n n_lean)) $
      f n_lean

-- | The result of translating a SAWCore binder to Lean: the Lean
-- identifier and the translated type. Pre-specialization we also
-- carried auxiliary @Inhabited@ instance binders here; those are
-- gone (see 'translateBinder'' for rationale).
data BindTrans = BindTrans Lean.Ident Lean.Type

-- | One binder in a recursor case handler's constructor-field prefix.
-- The distinction is semantic, not syntactic:
--
-- * 'CaseFieldRaw' is a structural constructor field. Lean's recursor
--   supplies it at the raw constructor type, so the case body gets a
--   Phase-beta shadow if it uses the field as a value.
--
-- * 'CaseFieldParam' is a field whose constructor type is exactly one
--   of the datatype parameters. Its Lean type is the already-translated
--   actual parameter supplied to this recursor application. This is the
--   expected-shape case for records such as
--   @RecordType s alpha beta@: if @alpha@ is instantiated with a
--   Phase-beta function type, the field binder must keep that function
--   type instead of being raw-eta-adapted.
data CaseBinderRole
  = CaseFieldRaw
  | CaseFieldParam Lean.Type

-- | Case-handler binder plan. 'CaseHandlerAllRaw' is the conservative
-- fallback for constructors unavailable in the module map.
data CaseHandlerPlan
  = CaseHandlerPlan [CaseBinderRole]
  | CaseHandlerAllRaw

-- | Flatten a 'BindTrans' into a Lean term-level 'Binder' list.
bindTransToBinder :: BindTrans -> [Lean.Binder]
bindTransToBinder (BindTrans name ty) =
  [Lean.Binder Lean.Explicit name (Just ty)]

-- | Flatten a 'BindTrans' into a Lean type-level 'PiBinder' list.
-- Anonymous binders (@_@) collapse to the arrow form.
bindTransToPiBinder :: BindTrans -> [Lean.PiBinder]
bindTransToPiBinder (BindTrans name ty)
  | name == Lean.Ident "_" = [Lean.PiBinder Lean.Explicit Nothing ty]
  | otherwise              = [Lean.PiBinder Lean.Explicit (Just name) ty]

-- | Translate a single SAW-core binder. An earlier revision also
-- injected an @[Inh_a : Inhabited a]@ instance binder for parameters
-- whose SAWCore type carries the @isort@ flag (the "inhabited sort"
-- annotation). We no longer do this: the injected instance binders
-- created positional-argument mismatches when the caller applied a
-- SAWCore term like @Num.rec motive tcnum tcinf n a xs@, where the
-- motive's returned type had an instance binder Lean couldn't insert
-- through the applied chain. SAWCore's @isort@ flag is an advisory
-- about reachability; preserving it as a Lean typeclass binder is
-- not required for soundness of value-level translation.
--
-- If we later need @Inhabited@ reasoning for specific primitives,
-- wire it per-primitive in 'SAWCorePrimitives.lean' rather than
-- sprinkling binders through every parameter list.
-- | Infer the universe level of a SAWCore argument *at the call
-- site*, for use with 'UseRenameUniv'. Returns @Just lvl@ when
-- the argument's type lives at a known universe. The level we
-- return is the level of the argument's *type* — i.e. for a
-- polymorphic-callee @f.{u}@ with binder @(α : Sort u)@, supplying
-- the argument @x@ requires @x : Sort u@, so @u@ is the level of
-- @x@'s type.
--
-- Cases handled:
--
-- * 'Variable' whose binder was @sort k@ at @k ≥ 1@: the binder
--   carries a 'boundUniverses' entry recording the universe
--   variable that 'translateBinder'' allocated.
--
-- * 'Sort' literal at @sort k@: the value is Lean @Type k@,
--   whose type is @Sort (k+2)@. (Type k = Sort (k+1); Sort (k+1)
--   inhabits Sort (k+2).) Used for SAW expressions like
--   @unsafeAssert (sort 0) a b@ where the first argument is a
--   value-position type literal.
--
-- * 'Sort' at @Prop@: Lean's @Prop = Sort 0@, type @Sort 1@.
--
-- * Any other term whose SAWCore kind is known from 'termSortOrType'.
--   A type-level term of SAW sort @k@ is emitted as a Lean value in
--   @Sort (k+1)@, so @Bool@ / @Vec n Bool@ resolve to level 1.
--
-- * Pi/function types: Lean places @(a : Sort u) -> Sort v@ in
--   @Sort (imax u v)@, so we compute the imax of all binder and result
--   levels. This is load-bearing for emitted Prelude lemmas such as
--   @Eq (a -> b) f g@, where the level is @max u_a u_b@ rather than
--   a concrete sort from the SAW kind alone.
--
-- Returns 'Nothing' only when the argument is not known to be a
-- type/sort argument. Callers that require explicit universes should
-- reject rather than falling back to Lean inference.
levelOfArg :: TermTranslationMonad m => Term -> m (Maybe Lean.UnivLevel)
levelOfArg t
  | (binders, ret) <- asPiList t
  , not (null binders) = do
      binderLvls <- traverse (levelOfArg . snd) binders
      retLvl <- levelOfArg ret
      pure (leanLevelIMax <$> sequence (binderLvls ++ [retLvl]))
  | otherwise = case unwrapTermF t of
      Variable nm _ -> do
        bu <- view boundUniverses <$> askTR
        case Map.lookup nm bu of
          Just lvl -> pure (Just lvl)
          Nothing  -> pure (levelOfTermSort t)
      FTermF (Sort srt _flags) -> case srt of
        TypeSort k -> pure (Just (Lean.LevelLit (fromIntegral k + 2)))
        PropSort   -> pure (Just (Lean.LevelLit 1))
      _ -> pure (levelOfTermSort t)
  where
    levelOfTermSort tm = case termSortOrType tm of
      Left PropSort     -> Just (Lean.LevelLit 0)
      Left (TypeSort k) -> Just (Lean.LevelLit (fromIntegral k + 1))
      Right _           -> Nothing
    leanLevelIMax [] = Lean.LevelLit 0
    leanLevelIMax [lvl] = lvl
    leanLevelIMax lvls = Lean.LevelIMax lvls

-- | Wrap a Lean type in @Except String α@. Cryptol's value-domain
-- expressions translate at this wrapped type (Lean stdlib's
-- 'Except', no custom wrapper).
wrapExcept :: Lean.Type -> Lean.Type
wrapExcept t =
  Lean.App (Lean.Var (Lean.Ident "Except"))
           [Lean.Var (Lean.Ident "String"), t]

-- | Syntactic test for the type shape emitted by 'wrapExcept'.
isExceptStringType :: Lean.Type -> Bool
isExceptStringType (Lean.App (Lean.Var (Lean.Ident "Except"))
                             [Lean.Var (Lean.Ident "String"), _]) = True
isExceptStringType _ = False

isLeanPiType :: Lean.Type -> Bool
isLeanPiType (Lean.Pi _ _) = True
isLeanPiType _ = False

peelLeanPiTypes :: Int -> Lean.Type -> ([Lean.Type], Lean.Type)
peelLeanPiTypes n ty
  | n <= 0 = ([], ty)
peelLeanPiTypes n (Lean.Pi (Lean.PiBinder _ _ bty : rest) body) =
  let nextTy = if null rest then body else Lean.Pi rest body
      (tys, ret) = peelLeanPiTypes (n - 1) nextTy
  in (bty : tys, ret)
peelLeanPiTypes _ ty = ([], ty)

-- | CONVENTION-INTERNAL helper (plan Slice 3.4 / 4c): classifies a
-- binder type that the CALLING FUNCTION ITSELF just emitted from a
-- known wrap decision — a deterministic self-mirror, not a position
-- authority. Legal inputs are types built in the same function
-- (`wrapExcept t` / raw `t`); never classify types that arrived from
-- elsewhere, and never use this to infer a position. (The forbidden
-- emitted-AST inspection class — shape from emitted TERMS — was
-- deleted in Slices 2/4b.)
bindingShapeOfType :: Lean.Type -> BindingShape
bindingShapeOfType ty
  | isExceptStringType ty = BindingWrapped
  | isLeanPiType ty       = BindingFunction
  | otherwise             = BindingRaw

-- NOTE: 'bindingShapeOfTerm' / 'bindingShapeOfLeanTermM' (shape
-- guessed from the emitted Lean term AST) are deleted per plan
-- Slice 2. Shape is an output of translation ('TranslatedTerm') or a
-- record in Γ ('BindingInfo') — never re-derived from generated
-- syntax. Do not reintroduce them.

isWrappedShape :: BindingShape -> Bool
isWrappedShape BindingWrapped = True
isWrappedShape _              = False

bindingShapeOfUseResultShape :: UseResultShape -> BindingShape
bindingShapeOfUseResultShape UseResultRaw      = BindingRaw
bindingShapeOfUseResultShape UseResultWrapped  = BindingWrapped
bindingShapeOfUseResultShape UseResultFunction = BindingFunction

withBindingInfo :: Lean.Ident -> BindingInfo -> TranslationReader -> TranslationReader
withBindingInfo ident info =
  over bindingEnv (Map.insert ident info)

-- | Should a SAW binder's type be wrapped in @Except String@ when
-- emitted in Lean?
--
-- Wrap = it's a value-domain type whose Cryptol semantics admits
-- the error case. Don't wrap when:
--
--   * Sorts (types-of-types) — they're not values themselves.
--   * Cryptol @Num@: this is the singleton width/index classifier
--     used by Cryptol's type-directed encodings, not a value-domain
--     computation result.
--   * @Nat@: SAW Nats double-duty as value-domain Nats and as
--     type-level indices (the @n@ in @Vec n α@). Wrapping the
--     latter use breaks dependent-type structure, so we keep
--     Nats raw everywhere. SAW workflows that explicitly @error@
--     at @Nat@ type get rejected; we revisit if that limit
--     proves real.
--   * Propositions like @Eq α x y@: a Prop has no error case;
--     wrapping would weaken the verification condition.
--   * Pi types (function types): the outer wrap stays off, but
--     the function's argument and result types still wrap via
--     recursive translation (translating the inner Pi structure).
--
-- CONVENTION-INTERNAL predicate (plan Slice 7): this is the
-- value-domain test the convention DERIVATIONS consult (binder
-- positions in the lambda/Pi/quantifier conventions,
-- 'phaseBetaResultIsValue', 'functionConventionValueSlot') — never a
-- standalone position authority at use sites. Positions come from
-- declared conventions and production records.
-- | THE domain map (2026-07-17 coherence audit; design doc
-- 2026-07-17_either-stream-recursor-convention.md). One authority
-- for "which representation do inhabitants of SAWCore type T take
-- in emitted Lean?" — every classification cascade must project
-- from this, never re-derive by hand (that scattering produced the
-- Either@core hole and is the historical seam-bug substrate).
--
-- Variable-headed types classify KIND-DIRECTED: by the declared
-- result sort of the head variable's kind (which the Variable node
-- carries), not by bare-vs-applied syntax.
--
-- PROP BACKSTOP (audit condition 2 — load-bearing, do not weaken):
-- SAWCore ADMITS Prop <= sort 0 cumulativity (Ord Sort:
-- PropSort <= _; scmSubtype/scmApply), so a Type-sort-kinded head
-- CAN be instantiated at a Prop. 'DVarValue' wrapping stays sound
-- because the Lean side is the backstop: @Except String P@ at
-- @P : Prop@ is ill-typed in Lean 4 (no term cumulativity), so the
-- bad instantiation fails LOUDLY at elaboration. Any change to the
-- wrapper type must re-establish a backstop with this property.
data Domain
  = DValue        -- ^ runtime data: wraps (@Except String T@)
  | DRawType      -- ^ sorts, Num (recorded raw representation)
  | DRawProp      -- ^ Eq/propositions/proofs: raw
  | DFunction     -- ^ Pi types: function position
  | DNat          -- ^ Nat: the ONE principled position-dependence
                  --   (index/binder raw; computed result value)
  | DVarValue     -- ^ var-headed, head kind results in a Type sort:
                  --   value domain (Lean backstop covers Prop
                  --   instantiation — see PROP BACKSTOP above)
  | DVarRaw       -- ^ var-headed, head kind results in Prop: a
                  --   proof-type family, raw (the ONLY production;
                  --   a term-level variable head is 'DValue')
  deriving (Eq, Show)

classifyDomain :: Term -> Domain
classifyDomain ty
  | Just _ <- asSort ty     = DRawType
  | isCryptolNumType ty     = DRawType
  | Just _ <- asNatType ty  = DNat
  | Just _ <- asEq ty       = DRawProp
  | Just _ <- asPi ty       = DFunction
  | otherwise =
      case unwrapTermF (fst (asApplyAll ty)) of
        Variable _ fty -> case asSort (snd (asPiList fty)) of
          Just s | s == propSort -> DVarRaw
                 | otherwise     -> DVarValue
          Nothing -> DValue  -- head is a term-level variable of a
                             -- concrete type: ordinary data
        _ -> DValue

shouldWrapBinder :: Term -> Bool
shouldWrapBinder ty = case classifyDomain ty of
  DValue    -> True
  DVarValue -> True
  -- DVarRaw was previously True here (the pre-classifier cascade
  -- fell through to @otherwise@); under the kind-directed rule a
  -- Prop-kinded var-headed family is a proof type and must not
  -- wrap — this is intended cell-(h) alignment, not drift
  -- (2026-07-17 audits, condition 3).
  DVarRaw   -> False
  DRawType  -> False
  DRawProp  -> False
  DFunction -> False
  DNat      -> False

isCryptolNumType :: Term -> Bool
isCryptolNumType ty = case asGlobalDef ty of
  Just i -> identName i == "Num"
         && identModule i == mkModuleName ["Cryptol"]
  Nothing -> False

-- | Convention-internal predicate (plan Slice 7): consulted by the
-- convention derivations ('phaseBetaResultIsValue',
-- 'functionConventionValueSlot'/'functionConventionResultIsValue') —
-- never a standalone position authority.
--

leanBinderName :: Lean.Binder -> Lean.Ident
leanBinderName (Lean.Binder _ name _) = name

termMentionsAny :: Set Lean.Ident -> Lean.Term -> Bool
termMentionsAny = go
  where
    go needles _
      | Set.null needles = False
    go needles (Lean.Var ident) = ident `Set.member` needles
    go needles (Lean.ExplVar ident) = ident `Set.member` needles
    go needles (Lean.ExplVarUniv ident _) = ident `Set.member` needles
    go needles (Lean.Lambda binders body) =
      any (binderMentions needles) binders
        || go (foldr (Set.delete . leanBinderName) needles binders) body
    go needles (Lean.Pi binders body) =
      any (piBinderMentions needles) binders
        || go (foldr Set.delete needles (mapMaybe piBinderName binders)) body
    go needles (Lean.Let name binders mty rhs body) =
      any (binderMentions needles) binders
        || maybe False (go needles) mty
        || go needles rhs
        || go (Set.delete name needles) body
    go needles (Lean.App f args) = go needles f || any (go needles) args
    go needles (Lean.Ascription a b) = go needles a || go needles b
    go needles (Lean.List xs) = any (go needles) xs
    go _ Lean.Sort{} = False
    go _ Lean.NatLit{} = False
    go _ Lean.IntLit{} = False
    go _ Lean.StringLit{} = False
    go _ Lean.Tactic{} = False

    piBinderName (Lean.PiBinder _ mName _) = mName
    binderMentions needles (Lean.Binder _ _ mty) = maybe False (go needles) mty
    piBinderMentions needles (Lean.PiBinder _ _ ty) = go needles ty

leanTermIdents :: Lean.Term -> Set Lean.Ident
leanTermIdents = go
  where
    go (Lean.Var ident) = Set.singleton ident
    go (Lean.ExplVar ident) = Set.singleton ident
    go (Lean.ExplVarUniv ident _) = Set.singleton ident
    go (Lean.Lambda binders body) =
      Set.unions (go body : map binderIdents binders)
    go (Lean.Pi binders body) =
      Set.unions (go body : map piBinderIdents binders)
    go (Lean.Let name binders mty rhs body) =
      let pieces =
            [go rhs, go body] ++ maybe [] ((: []) . go) mty ++
            map binderIdents binders
      in
      Set.insert name $
        Set.unions pieces
    go (Lean.App f args) = Set.unions (go f : map go args)
    go (Lean.Ascription a b) = Set.union (go a) (go b)
    go (Lean.List xs) = Set.unions (map go xs)
    go Lean.Sort{} = Set.empty
    go Lean.NatLit{} = Set.empty
    go Lean.IntLit{} = Set.empty
    go Lean.StringLit{} = Set.empty
    go Lean.Tactic{} = Set.empty

    binderIdents (Lean.Binder _ name mty) =
      Set.insert name (maybe Set.empty go mty)
    piBinderIdents (Lean.PiBinder _ mName ty) =
      maybe id Set.insert mName (go ty)
