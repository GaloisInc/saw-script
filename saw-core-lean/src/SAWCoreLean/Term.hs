{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : SAWCoreLean.Term
Copyright   : Galois, Inc. 2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : portable

SAWCore 'Term' to "Language.Lean.AST" translator. Mirrors
"SAWCoreRocq.Term" in scope and structure; Lean-specific divergences
are documented at each call site. Module-walk support lives in
'SAWCoreLean.CryptolModule'.
-}

module SAWCoreLean.Term
  ( -- * Monad
    TermTranslationMonad
  , TranslationState(..)
  , runTermTranslationMonad
  , globalDeclarations
  , topLevelDeclarations
  , universeVars
    -- * Translation
  , translateTerm
  , translateTermLet
  , translateDefDoc
    -- * Decl construction
  , mkDefinitionWith
    -- * Phase β wrap helpers (exposed for the Cryptol module path
    --   so it can apply the same closed-value top-level fixup)
  , shouldWrapBinder
  , wrapExcept
  ) where

import           Control.Applicative          ((<|>))
import           Control.Lens                 (makeLenses, over, set, view)
import qualified Control.Monad.Except         as Except
import           Control.Monad.Reader         (MonadReader(local), asks)
import           Control.Monad.State          (get, modify)
import           Data.Foldable                (toList)
import qualified Data.IntMap.Strict           as IntMap
import           Data.IntMap.Strict           (IntMap)
import qualified Data.IntSet                  as IntSet
import           Data.List                    (findIndex)
import qualified Data.Map                     as Map
import           Data.Map                     (Map)
import           Data.Maybe                   (fromMaybe, isJust, isNothing,
                                               mapMaybe)
import qualified Data.Set                     as Set
import           Data.Set                     (Set)
import qualified Data.Text                    as Text
import           Prelude                      hiding (fail)
import           Prettyprinter                (Doc, hardline, vcat)

import qualified Language.Lean.AST            as Lean
import qualified Language.Lean.Pretty         as Lean

import           SAWCore.Module               (Ctor(..), CtorArg(..),
                                               CtorArgStruct(..),
                                               DataType(..),
                                               Def(..),
                                               ModuleMap,
                                               ResolvedName(..),
                                               lookupVarIndexInMap,
                                               resolveNameInMap)
import           SAWCore.Name
import           SAWCore.Recognizer
import           SAWCore.SharedTerm
import           SAWCore.Term.Functor
import           SAWCore.Term.Pretty          (scTermCount, shouldMemoizeTerm)
import           SAWCore.Term.Raw             (Term(..))

import           SAWCoreLean.FixShapes        (FixShape(..), classifyFix,
                                               classifyPolyStreamIterate)
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

data TranslatedTerm = TranslatedTerm
  { ttLean  :: Lean.Term
  , ttShape :: BindingShape
  }
  deriving Show

data RawifiedExcept = RawifiedExcept
  { reHoists :: [(Lean.Ident, Lean.Term)]
  , reRaw    :: Lean.Term
  }
  deriving Show

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
  , _bindingShapes :: Map Lean.Ident BindingShape
    -- ^ Lean identifiers in scope paired with their Phase-beta shape.
    -- Used at application and recursor-app sites to decide whether a
    -- variable is an outer 'Except' value that must be 'Bind.bind'-ed,
    -- a function-shaped value that should be passed directly, or raw.
    -- This is the first slice of the expected-shape environment; result
    -- shapes are carried by translation rules and callee conventions.
  , _deferMkStreamLowering :: Bool
    -- ^ True only while translating the body of a recognized fix-shape
    -- lowering. Direct @MkStream@ lowering needs the recursive lookup
    -- substitution before it can prove the index function raw; this
    -- flag lets the body translation leave @mkStreamM@ as an
    -- intermediate AST marker. The enclosing fix lowerer must rawify
    -- it before emission, or reject.
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
  BinderPos -> do
    n <- view universeVarCount <$> get
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
  used <- Set.union extra <$> view unavailableIdents <$> askTR
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
-- Returns 'Nothing' for anything else (applied terms like
-- @Vec n Bool@, constants like @Bool@ — these would need a global
-- 'sortOf' lookup we don't currently thread through). The caller
-- falls back to bare @\@name@ and relies on Lean inference, which
-- is fine for the common cases we've covered so far.
levelOfArg :: TermTranslationMonad m => Term -> m (Maybe Lean.UnivLevel)
levelOfArg t = case unwrapTermF t of
  Variable nm _ -> do
    bu <- view boundUniverses <$> askTR
    pure (Map.lookup nm bu)
  FTermF (Sort srt _flags) -> case srt of
    TypeSort k -> pure (Just (Lean.LevelLit (fromIntegral k + 2)))
    PropSort   -> pure (Just (Lean.LevelLit 1))
  _ -> pure Nothing

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

bindingShapeOfType :: Lean.Type -> BindingShape
bindingShapeOfType ty
  | isExceptStringType ty = BindingWrapped
  | isLeanPiType ty       = BindingFunction
  | otherwise             = BindingRaw

bindingShapeOfTerm :: Lean.Term -> BindingShape
bindingShapeOfTerm tm
  | Lean.Lambda{} <- tm = BindingFunction
  | otherwise           = BindingRaw

bindingShapeOfLeanTermM :: TermTranslationMonad m => Lean.Term -> m BindingShape
bindingShapeOfLeanTermM tm = case tm of
  Lean.Var ident -> do
    shapes <- view bindingShapes <$> askTR
    pure (Map.findWithDefault (bindingShapeOfTerm tm) ident shapes)
  _ -> pure (bindingShapeOfTerm tm)

isWrappedShape :: BindingShape -> Bool
isWrappedShape BindingWrapped = True
isWrappedShape _              = False

bindingShapeOfUseResultShape :: UseResultShape -> BindingShape
bindingShapeOfUseResultShape UseResultRaw      = BindingRaw
bindingShapeOfUseResultShape UseResultWrapped  = BindingWrapped
bindingShapeOfUseResultShape UseResultFunction = BindingFunction

withBindingShape :: Lean.Ident -> BindingShape -> TranslationReader -> TranslationReader
withBindingShape ident shape =
  over bindingShapes (Map.insert ident shape)

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
shouldWrapBinder :: Term -> Bool
shouldWrapBinder ty
  | Just _ <- asSort ty       = False
  | isCryptolNumType ty       = False
  | Just _ <- asNatType ty    = False
  | Just _ <- asEq ty         = False
  | Just _ <- asPi ty         = False
  | otherwise                 = True

isCryptolNumType :: Term -> Bool
isCryptolNumType ty = case asGlobalDef ty of
  Just i -> identName i == "Num"
         && identModule i == mkModuleName ["Cryptol"]
  Nothing -> False

-- | True for terms whose head is a SAW 'Variable' — i.e. the term
-- is a (possibly applied) type-variable. Examples:
--   * @t@ where @t : sort 1@ — the binder is at the type
--     variable itself.
--   * @p y pf@ where @p : (y : t) → Eq t x y → sort u_motive@
--     — the term is a polymorphic application whose sort is
--     determined by the motive's universe (which could be
--     'Prop'). Wrapping would force a specific universe
--     constraint that doesn't hold polymorphically.
isVariableHead :: Term -> Bool
isVariableHead t = case unwrapTermF t of
  Variable _ _ -> True
  App f _ -> isVariableHead f
  _ -> False

-- | For a SAW function type @(x₁ : T₁) → … → (xₙ : Tₙ) → R@,
-- compute the 0-based positions of the *type-arg* binders. A
-- binder is a type-arg if its variable appears free in any
-- subsequent binder's type or in the return type — i.e. it's
-- used as a dependent index, like @n@ in @bvAdd : (n : Nat) →
-- Vec n Bool → Vec n Bool → Vec n Bool@.
--
-- At App-emission time, type-args splice directly into the
-- function-application head (no monadic lifting). Value-args
-- get lifted via @Bind.bind@ in the surrounding do-block.
typeArgPositions :: Term -> [Int]
typeArgPositions funType = go 0 binders retType
  where
    (binders, retType) = asPiList funType
    go _ [] _ = []
    go i ((vn, _bty) : rest) ret =
      let restFreeVars =
            mconcat (map (freeVars . snd) rest) <> freeVars ret
          isTypeArg = vnIndex vn `IntSet.member` restFreeVars
          here = [i | isTypeArg]
      in here ++ go (i+1) rest ret

-- | For a quantifier Pi @∀ (x : Vec n α) (y : Vec n α), …@, emit
-- a 'let'-shadow chain at the body entry that 'Pure.pure'-lifts
-- each value-typed binder. After @intro x y@, the user's goal has
-- @x, y@ at raw types (matching SAW's quantifier semantics);
-- inside the body, the shadows mean references to @x, y@ pick up
-- the wrapped form that the body's Phase-β bind chains expect.
--
-- Non-value-typed binders (Nat, Sort, Eq, …) are passed through
-- unshadowed — the body's operations on them don't go through
-- Phase-β lifts, so they stay raw.
quantifierShadow ::
  [(VarName, Term)] -> [Lean.PiBinder] -> Lean.Term -> Lean.Term
quantifierShadow params piBinders body =
  foldr shadowOne body (zip params piBinders)
  where
    pureVar = Lean.Var (Lean.Ident "Pure.pure")
    shadowOne :: ((VarName, Term), Lean.PiBinder) -> Lean.Term -> Lean.Term
    shadowOne ((_, ty), Lean.PiBinder _ mName _) inner
      | shouldWrapBinder ty
      , Just name <- mName =
          Lean.Let name [] Nothing
            (Lean.App pureVar [Lean.Var name])
            inner
      | otherwise = inner

-- | Like 'typeArgPositions' but for a sequence of binders without
-- access to the return type — e.g. a 'Lambda' chain whose body we
-- don't yet have a typed projection for. Returns positions whose
-- variable is referenced in some /later/ binder's type. Catches the
-- common case (numeric/type indices threaded through the binder
-- chain like @\\(a : Num) (key : Vec 8 Bool) (plaintext : seq a …) → …@
-- where @a@ must stay raw to feed plaintext's type), but misses the
-- weaker case where a binder is referenced only by the body's
-- value type. That undercount is acceptable here: a value-typed
-- binder we wrap but didn't need to fails loud at Lean elaboration
-- (the index position rejects @Except String Num@), and the fix is
-- a manual override or signature plumbing — neither silent
-- unsoundness.
typeArgPositionsBinders :: [(VarName, Term)] -> [Int]
typeArgPositionsBinders bs = go 0 bs
  where
    go _ [] = []
    go i ((vn, _) : rest) =
      let restFreeVars = mconcat (map (freeVars . snd) rest)
          isTypeArg = vnIndex vn `IntSet.member` restFreeVars
          here = [i | isTypeArg]
      in here ++ go (i + 1) rest

-- | True if the given SAWCore term is "type-producing" — its value
-- lives at @Sort@ level (a Lean type expression), not at value level.
-- Used to decide whether a 'Lambda' or 'Pi' binder belongs to a
-- type-level abstraction (motive, type-family) and so should NOT be
-- wrapped in @Except String@.
--
-- Heuristic, not a full type-checker:
--   * Sort / Pi shapes are unambiguously type-producing.
--   * A Lambda whose body is type-producing is itself
--     type-producing (motive of higher arity).
--   * An App headed by a Constant/Ctor whose declared return is a
--     'Sort' produces a type. Looks up the head's signature in
--     'sawModuleMap'; the (n - k)-ary residual return matters when
--     the head is under-applied, so we walk pi-binders past the
--     supplied args.
--   * Bare 'Constant' references behave the same.
--   * Anything else (variable-headed apps, literals, unmapped
--     constants) is treated as not-type-producing — the worst case
--     is that a value binder accidentally stays unwrapped, which
--     fails loud at Lean elaboration rather than silently.
isTypeProducing :: TermTranslationMonad m => Term -> m Bool
isTypeProducing t
  | Just _ <- asSort t = pure True
  | Just _ <- asPi t   = pure True
  | otherwise = case unwrapTermF t of
      Lambda _ _ body -> isTypeProducing body
      App {} -> case asGlobalDef head_ of
        Just ident -> headRetSort ident (length appArgs)
        Nothing    -> pure False
      Constant nm | ModuleIdentifier ident <- nameInfo nm ->
        headRetSort ident 0
      _ -> pure False
  where
    (head_, appArgs) = asApplyAll t
    headRetSort ident nArgs = do
      mm <- view sawModuleMap <$> askTR
      let fty = case resolveNameInMap mm ident of
            Just (ResolvedDef def)      -> Just (defType def)
            Just (ResolvedCtor c)       -> Just (ctorType c)
            Just (ResolvedDataType dt)  -> Just (dtType dt)
            _                           -> Nothing
      pure $ case fty of
        Nothing -> False
        Just ty ->
          let (binders, ret) = asPiList ty
              -- 'asPiList' strips all the outer pi binders. After
              -- applying @nArgs@ of them, the residual return is
              -- 'ret' if @nArgs >= length binders@ (fully applied);
              -- otherwise the residual is the @Pi@ of the leftover
              -- binders over 'ret', which is itself a type.
          in if nArgs >= length binders
                then isJust (asSort ret)
                else True

translateBinder' :: TermTranslationMonad m => VarName -> Term ->
                    (BindTrans -> m a) -> m a
translateBinder' vn ty f = do
  -- If the binder type is bare 'Sort k' at @k ≥ 1@, take the
  -- BinderPos path so 'translateSort' allocates a fresh universe
  -- variable for this occurrence. Otherwise fall through to
  -- 'translateTerm', which treats any nested 'Sort' as a value
  -- position. Per-binder fresh universes are the load-bearing
  -- fix from the parked P4 investigation; the dispatch happens
  -- here so we don't have to thread a context argument through
  -- the entire 'translateTerm' walk.
  --
  -- When the BinderPos path allocates a 'SortVar', remember the
  -- universe name in 'boundUniverses' under @vn@; call-site
  -- emission ('levelOfArg') consults this map to supply explicit
  -- @\.{u_n}@ levels at uses of polymorphic Lean targets.
  (ty', mUniv) <- case asSort ty of
    Just s -> do
      -- Body and type walks may both encounter this binder. Memoize
      -- on 'vn' so we allocate one universe per logical SAWCore
      -- variable, not one per syntactic occurrence.
      memo <- view universeBinderAssignments <$> get
      case Map.lookup vn memo of
        Just uname ->
          pure (Lean.Sort (Lean.SortVar uname), Just (Lean.LevelVar uname))
        Nothing -> do
          leanSort <- translateSort BinderPos s
          case leanSort of
            Lean.SortVar name -> do
              modify (over universeBinderAssignments (Map.insert vn name))
              pure (Lean.Sort leanSort, Just (Lean.LevelVar name))
            _ ->
              pure (Lean.Sort leanSort, Nothing)
    Nothing -> do
      skipWrap <- view skipBinderWrap <$> askTR
      inRecCase <- view inRecursorCaseBinder <$> askTR
      -- 'skipBinderWrap' is a decision about this binder boundary, not
      -- a blanket raw-mode for every nested type expression appearing in
      -- the binder's type. Translate the type itself with the flag
      -- cleared, then suppress only the outer 'Except' below. This keeps
      -- value-level function types that appear as datatype parameters in
      -- their Phase-β form, e.g. @Except α -> Except α -> Except Bool@,
      -- while still letting motive/recursor binders themselves arrive raw.
      t <- localTR (set skipBinderWrap False) (translateTerm ty)
      -- 'inRecursorCaseBinder' inhibits the value-typed wrap too:
      -- the recursor (RecordType.rec, Stream.rec, …) expects its
      -- case-handler binders at the constructor's raw argument
      -- types (e.g. RecordType.rec wants
      -- @(a' : α) (b' : β) → motive (RecordValue a' b')@ with raw
      -- α, β). The case body then operates on Phase-β-wrapped
      -- values via a 'let'-shadow chain emitted by
      -- 'translateCaseHandler'.
      let t' = if shouldWrapBinder ty && not skipWrap && not inRecCase
                  then wrapExcept t
                  else t
      pure (t', Nothing)
  let bindUniv = maybe id (\u -> over boundUniverses (Map.insert vn u)) mUniv
  -- Track whether the binder type wrapped in 'Except String', so
  -- recursor-scrutinee emission can tell whether the variable
  -- arrives wrapped or raw. Sort-typed binders never wrap.
  skipWrap <- view skipBinderWrap <$> askTR
  let binderWrapped =
        isNothing (asSort ty)
        && shouldWrapBinder ty
        && not skipWrap
  localTR bindUniv $
    withSAWVar vn $ \n' ->
      localTR (withBindingShape n'
                 (if binderWrapped
                     then BindingWrapped
                     else bindingShapeOfType ty')) $
        f (BindTrans n' ty')

-- | Introduce a SAW binder whose Lean type has already been determined
-- by the surrounding expected-shape calculation. This is intentionally
-- narrow: recursor case fields whose constructor type is a datatype
-- parameter must use the translated actual parameter type, not a fresh
-- translation of the binder's source type.
translateBinderWithLeanType ::
  TermTranslationMonad m =>
  VarName -> Lean.Type -> (Lean.Binder -> m a) -> m a
translateBinderWithLeanType vn ty f =
  withSAWVar vn $ \n' ->
    localTR (withBindingShape n' (bindingShapeOfType ty)) $
      f (Lean.Binder Lean.Explicit n' (Just ty))

translateBinders' :: TermTranslationMonad m => [(VarName, Term)] ->
                     ([BindTrans] -> m a) -> m a
translateBinders' [] f = f []
translateBinders' ((n, ty) : rest) f =
  translateBinder' n ty $ \bnd ->
    translateBinders' rest $ \bnds ->
      f (bnd : bnds)

-- | Like 'translateBinders'', but marks the binder at each
-- 0-based 'typeArgIxs' position as a *type argument*: its type
-- translates without the 'Except String' wrap, since the binder
-- itself appears as a type/index in subsequent binder types or the
-- return type and so must stay raw to feed those positions.
--
-- The 'skipBinderWrap' override is scoped to the wrap decision for
-- that single binder by re-asserting the surrounding context value
-- before the recursive call covering later binders.
translateBindersSelective :: TermTranslationMonad m =>
                             [Int] -> [(VarName, Term)] ->
                             ([BindTrans] -> m a) -> m a
translateBindersSelective typeIxs bs0 f = do
  surroundingCtx <- view skipBinderWrap <$> askTR
  let go _ [] acc = f (reverse acc)
      go i ((n, ty) : rest) acc =
        let enterCtx
              | i `elem` typeIxs = set skipBinderWrap True
              | otherwise        = set skipBinderWrap surroundingCtx
        in localTR enterCtx $ translateBinder' n ty $ \bnd ->
             -- Reset 'skipBinderWrap' to the surrounding value before
             -- continuing — the per-binder override must not leak.
             localTR (set skipBinderWrap surroundingCtx) $
               go (i + 1) rest (bnd : acc)
  go 0 bs0 []

-- | Produce a flat list of Lean term-level binders from a SAWCore
-- binding list. Zero-or-more auxiliary 'Inhabited' instance binders
-- may be interleaved (one per binder whose type is an @isort@).
translateBinders :: TermTranslationMonad m => [(VarName, Term)] ->
                    ([Lean.Binder] -> m a) -> m a
translateBinders bs f =
  translateBinders' bs (f . concatMap bindTransToBinder)

-- | Produce a flat list of Lean type-level pi binders from a SAWCore
-- binding list. Anonymous binders (@_@) with no auxiliary
-- hypotheses collapse to the @A -> rest@ arrow form.
translatePiBinders :: TermTranslationMonad m => [(VarName, Term)] ->
                      ([Lean.PiBinder] -> m a) -> m a
translatePiBinders bs f =
  translateBinders' bs (f . concatMap bindTransToPiBinder)

-- | Print a qualified Lean identifier from a SAWCore 'ModuleName' plus
-- a base identifier — @Some.Module.name@.
qualify :: ModuleName -> Lean.Ident -> Lean.Ident
qualify m (Lean.Ident base) =
  Lean.Ident (Text.unpack (Text.intercalate "." (moduleNamePieces m)) ++ "." ++ base)

-- | Compute the Lean 'Ident' that a SAWCore 'Ident' resolves to at a
-- use site (before any 'UseRename' / 'UseMacro' treatment). Handles:
--
--   * Data-type constructors: Lean scopes these inside the
--     inductive's namespace (@PairType.PairValue@, not @PairValue@).
--     We detect via 'resolveNameInMap' and prepend the datatype's
--     short name.
--   * Same-module references: Lean's 'namespace' scope supplies the
--     module prefix at use sites, so we emit the short name bare.
--   * Cross-module references: emit fully qualified.
defaultIdentTarget ::
  TermTranslationMonad m => Ident -> m Lean.Ident
defaultIdentTarget i = do
  curMod <- view currentModule <$> askTR
  mm     <- view sawModuleMap <$> askTR
  let short = escapeIdent (Lean.Ident (identName i))
      -- If this ident is a data-type constructor, scope the short
      -- name inside the datatype's short name.
      scopedShort = case resolveNameInMap mm i of
        Just (ResolvedCtor c) ->
          let dtShort = Text.unpack (toShortName (nameInfo (ctorDataType c)))
          in  Lean.Ident (dtShort ++ "." ++ identName i)
        _ -> short
      sameModule = Just (identModule i) == curMod
  pure $
    if sameModule
      then scopedShort
      else qualify (translateModuleName (identModule i)) scopedShort

-- | Resolve a SAWCore 'Ident' to the Lean 'Ident' used at its use
-- sites, when that mapping is fixed (i.e. the treatment is
-- 'UsePreserve' or 'UseRename'). Returns 'Nothing' for 'UseMacro'
-- entries, which don't have a single Lean ident to point at.
-- Mirrors @SAWCoreRocq.Term.translateIdentToIdent@.
translateIdentToIdent :: TermTranslationMonad m => Ident -> m (Maybe Lean.Ident)
translateIdentToIdent i = do
  qualifiedIdent <- defaultIdentTarget i
  treatment      <- atUseSite <$> findSpecialTreatment i
  case treatment of
    UsePreserve -> pure (Just qualifiedIdent)
    UseRename mTargetMod targetName _ ->
      pure $ Just $ case mTargetMod of
        Just mod_
          | isImplicitlyOpened mod_ -> targetName
          | otherwise               -> qualify mod_ targetName
        Nothing                     -> targetName
    UseRenameUniv mTargetMod targetName _ ->
      pure $ Just $ case mTargetMod of
        Just mod_
          | isImplicitlyOpened mod_ -> targetName
          | otherwise               -> qualify mod_ targetName
        Nothing                     -> targetName
    UseMacro{}        -> pure Nothing
    UseMacroOrVar{}   -> pure Nothing
    UseMapsToWrapped{} -> pure Nothing
    UseReject reason  ->
      Except.throwError
        (RejectedPrimitive (Text.pack (identName i)) reason)

-- | Apply a 'UseSiteTreatment' to a SAWCore 'Ident' with a list of
-- arguments — the Lean analogue of @applySpecialTreatment@ in
-- "SAWCoreRocq.Term".
--
-- 'Prelude.fix' applications are intercepted before the
-- 'SpecialTreatment' dispatch and routed through 'classifyFix'.
-- Shapes the recognizer matches lower to the corresponding
-- support-library helper (e.g. 'mkStreamFix' for 'StreamCorec');
-- unmatched shapes fall through to the L-5 reject path via the
-- 'reject' entry in 'SpecialTreatment.hs'.
-- | Build a do-block that lifts a Constant-headed App into the
-- @Except String@ monad. Each value-arg becomes a @← bind@ in the
-- block; type-args splice directly into the function-application
-- head; the bound-name application gets @pure@-wrapped at the
-- end. Literal value-args ('NatLit', 'IntLit', 'StringLit') get
-- a 'Pure.pure' wrap before binding so the bind chain typechecks
-- uniformly regardless of whether the source arg was wrapped.
--
-- Concretely, given @head : (t₁ : τ₁) → (v₁ : σ₁) → … → R@ with
-- @typeArgIxs@ marking type-arg positions, @[a₁, …, aₙ]@ the
-- translated args, this produces:
--
-- @
-- Bind.bind (lift a_{val_1}) (fun b_1 =>
--   Bind.bind (lift a_{val_2}) (fun b_2 =>
--     …
--       Pure.pure (head a_1 … aₙ' …)))
-- @
--
-- where @a_i'@ is @b_k@ for value-arg positions, @a_i@ for
-- type-arg positions.
buildLifted ::
  TermTranslationMonad m =>
  Lean.Term ->
  Bool ->       -- ^ wrap result in 'Pure.pure'?
  [Bool] ->     -- ^ per-position bind decision
  [Lean.Term] ->
  m Lean.Term
buildLifted head_ pureWrap shouldBind argTerms =
  go 0 argTerms shouldBind []
  where
    bindVar = Lean.Var (Lean.Ident "Bind.bind")
    pureVar = Lean.Var (Lean.Ident "Pure.pure")
    avoidIdents = Set.unions (leanTermIdents head_ : map leanTermIdents argTerms)

    -- Lift a plain Lean term into Except via 'Pure.pure' if it's
    -- syntactically a "raw" value. Shared with 'liftRawValue' in
    -- 'SAWCoreLean.SpecialTreatment' so any extension (new raw
    -- ctors) lives in one place.
    liftArg = liftRawValue

    go :: TermTranslationMonad m
       => Int -> [Lean.Term] -> [Bool] -> [(Int, Lean.Ident)] ->
       m Lean.Term
    go _ [] _ subs = do
      let finalArgs =
            [ case lookup pos subs of
                Just bname -> Lean.Var bname
                Nothing    -> origTerm
            | (pos, origTerm) <- zip [0..] argTerms
            ]
          body = Lean.App head_ finalArgs
      pure (if pureWrap then Lean.App pureVar [body] else body)
    go pos (_ : rest) (False : bs) subs = go (pos + 1) rest bs subs
    go pos (t : rest) (True  : bs) subs = do
      bname <- freshVariantAvoiding avoidIdents (Lean.Ident ("v_" ++ show pos))
      rest' <- go (pos + 1) rest bs ((pos, bname) : subs)
      let lam = Lean.Lambda
                  [Lean.Binder Lean.Explicit bname Nothing]
                  rest'
      pure (Lean.App bindVar [liftArg t, lam])
    -- 'shouldBind' is padded with 'False' to match 'argTerms'
    -- length at the call site (see 'applied' in
    -- 'originalDispatch'), so this final pattern is unreachable.
    -- Treat shorter shouldBind as "remaining args are non-binds"
    -- defensively rather than crashing.
    go pos (_ : rest) [] subs = go (pos + 1) rest [] subs

buildLiftedWithShape ::
  TermTranslationMonad m =>
  BindingShape ->
  Lean.Term ->
  Bool ->
  [Bool] ->
  [Lean.Term] ->
  m TranslatedTerm
buildLiftedWithShape resultShape head_ pureWrap shouldBind argTerms = do
  tm <- buildLifted head_ pureWrap shouldBind argTerms
  pure (TranslatedTerm tm resultShape)

-- | Compute per-argument bind decisions for a function with SAW type
-- @fty@ applied to the already-translated Lean arguments @argTerms@.
--
-- Nat is position-sensitive under Phase beta. A Nat used as a type index
-- stays raw, but a Nat produced by a value computation (for example
-- @bvToNat x@) is wrapped. For a Nat formal we bind only when the actual
-- translated argument is known to be wrapped.
argumentBindPlan :: Term -> [TranslatedTerm] -> [Bool]
argumentBindPlan fty argResults =
  argumentBindPlanFromWrapped fty argTerms wrappedActuals
  where
    argTerms = map ttLean argResults
    wrappedActuals = map (isWrappedShape . ttShape) argResults

argumentBindPlanFromWrapped :: Term -> [Lean.Term] -> [Bool] -> [Bool]
argumentBindPlanFromWrapped fty argTerms wrappedActuals =
  let (binders, _) = asPiList fty
      typeIxs = typeArgPositions fty
      paramActualFor ix bty = case unwrapTermF bty of
        Variable vn _ ->
          case findIndex (\(vn', _) -> vn' == vn) binders of
            Just paramIx
              | paramIx < ix
              , paramIx < length argTerms -> Just (argTerms !! paramIx)
            _ -> Nothing
        _ -> Nothing
      paramActualAlreadyExpected ix bty =
        case paramActualFor ix bty of
          Just actualTy ->
               isExceptStringType actualTy
            || isLeanPiType actualTy
          Nothing -> False
      bindable ix bty actualWrapped =
           ix `notElem` typeIxs
        && not (isJust (asSort bty))
        && not (isJust (asEq bty))
        && not (isJust (asPi bty))
        && not (paramActualAlreadyExpected ix bty)
        && (isNothing (asNatType bty) || actualWrapped)
  in
  [ bindable ix bty actualWrapped
  | (ix, ((_, bty), actualWrapped)) <-
      zip [0..] (zip binders wrappedActuals)
  ]

-- | A raw SAW function whose return type is Nat can still be a
-- value-domain computation under Phase beta when it consumes a non-index
-- value argument. Examples: @bvToNat : Vec n Bool -> Nat@ and
-- @intToNat : Int -> Nat@. Their Lean results must be @Pure.pure@-lifted.
natValueResult :: Term -> Bool
natValueResult fty =
  isJust (asNatType ret) && any valueInput (zip [0..] binders)
  where
    (binders, ret) = asPiList fty
    typeIxs = typeArgPositions fty
    valueInput (ix, (_, bty)) =
         ix `notElem` typeIxs
      && shouldWrapBinder bty

phaseBetaResultShape :: Term -> Int -> BindingShape
phaseBetaResultShape fty nApplied
  | nApplied < length binders = BindingFunction
  | shouldWrapBinder ret || isVariableHead ret || natValueResult fty =
      BindingWrapped
  | isJust (asPi ret) = BindingFunction
  | otherwise = BindingRaw
  where
    (binders, ret) = asPiList fty

translateFunctionWithWrappedResult ::
  TermTranslationMonad m => Term -> m Lean.Term
translateFunctionWithWrappedResult t =
  case unwrapTermF t of
    Lambda {} -> do
      let (params, body) = asLambdaList t
      surroundingCtx <- view skipBinderWrap <$> askTR
      typeBody <- isTypeProducing body
      if typeBody
         then translateTerm t
         else do
           let typeIxs = typeArgPositionsBinders params
           translateBindersSelective typeIxs params $ \bts ->
             localTR (set skipBinderWrap surroundingCtx
                    . set inRecursorCaseBinder False) $ do
               bodyResult <- translateTermLetWithShape body
               let bodyLean =
                     case ttShape bodyResult of
                       BindingWrapped -> ttLean bodyResult
                       _ -> Lean.App (Lean.Var (Lean.Ident "Pure.pure"))
                              [ttLean bodyResult]
               pure (Lean.Lambda (concatMap bindTransToBinder bts) bodyLean)
    _ -> translateTerm t

wrapHoistedExcepts :: [(Lean.Ident, Lean.Term)] -> Lean.Term -> Lean.Term
wrapHoistedExcepts hoists body = foldr mkOuterBind body hoists
  where
    mkOuterBind (name, rhs) body' =
      Lean.App (Lean.Var (Lean.Ident "Bind.bind"))
        [ rhs
        , Lean.Lambda [Lean.Binder Lean.Explicit name Nothing] body'
        ]

freshenHoists ::
  TermTranslationMonad m =>
  [(Lean.Ident, Lean.Term)] -> Lean.Term -> m ([(Lean.Ident, Lean.Term)], Lean.Term)
freshenHoists hoists body = go Map.empty hoists
  where
    applySubsts substs tm =
      Map.foldrWithKey substLeanIdent tm substs

    go substs [] = pure ([], applySubsts substs body)
    go substs ((oldName, rhs) : rest) = do
      newName <- freshVariant oldName
      let rhs' = applySubsts substs rhs
          substs' = Map.insert oldName (Lean.Var newName) substs
      (rest', body') <- go substs' rest
      pure ((newName, rhs') : rest', body')

lowerMkStreamSound ::
  TermTranslationMonad m => Lean.Term -> Lean.Term -> m Lean.Term
lowerMkStreamSound elTypeLean indexFnLean =
  case indexFnLean of
    Lean.Lambda [idxBinder@(Lean.Binder _ idxName _)] body -> do
      rawified <- case rawifyExceptToRaw (Set.singleton idxName) body of
        Just r -> pure r
        Nothing ->
          Except.throwError (RejectedPrimitive "MkStream"
            "MkStream index function has residual per-index error \
            \effects. A sound Lean backend cannot default those errors \
            \inside a Stream; specialize/prove the index function total \
            \or add a sound stream representation for per-index errors.")
      let hoists = reHoists rawified
          rawBody = reRaw rawified
      let rawIndexFn = Lean.Lambda [idxBinder] rawBody
          stream =
            Lean.App (Lean.ExplVar (Lean.Ident "Stream.MkStream"))
              [elTypeLean, rawIndexFn]
          base = Lean.App (Lean.Var (Lean.Ident "Pure.pure")) [stream]
      pure (wrapHoistedExcepts hoists base)
    _ ->
      Except.throwError (RejectedPrimitive "MkStream"
        "MkStream expects a unary index function after translation.")

-- | Interpret a translated @Except String α@ expression as an
-- index-independent sequence of hoisted @Except@ effects followed by a
-- raw term. This is the soundness gate for lowering
-- @MkStream : (Nat -> Except α) -> Except (Stream α)@: every residual
-- effect must either be hoisted before the stream is built, or be
-- proved syntactically pure.
--
-- The blocked set contains names known to vary per index. It starts
-- with the stream index and grows when we bind a raw term derived from
-- such names. A hoisted RHS may not mention any blocked name; this
-- prevents the unsound transform
-- @fun i => x_i >>= fun x => f x@  ~~>  @f x >>= ...@.
rawifyExceptToRaw :: Set Lean.Ident -> Lean.Term -> Maybe RawifiedExcept
rawifyExceptToRaw = go Map.empty
  where
  go rawEnv blocked tm = case tm of
    Lean.App (Lean.Lambda [Lean.Binder _ name _] body) [arg] ->
      go rawEnv blocked (substLeanIdent name arg body)

    Lean.App (Lean.Var (Lean.Ident "Pure.pure")) [raw] ->
      Just (RawifiedExcept [] raw)

    Lean.App (Lean.Var name) args
      | Just rawFn <- Map.lookup name rawEnv ->
          Just (RawifiedExcept [] (Lean.App rawFn args))

    Lean.Var name
      | Just raw <- Map.lookup name rawEnv ->
          Just (RawifiedExcept [] raw)

    Lean.Var name
      | name `Set.notMember` blocked ->
          Just (RawifiedExcept [(name, tm)] (Lean.Var name))

    Lean.App (Lean.Var (Lean.Ident "Bind.bind"))
      [ Lean.App (Lean.Var (Lean.Ident "Bind.bind"))
          [innerRhs, Lean.Lambda [innerBinder] innerBody]
      , outerLam@(Lean.Lambda [Lean.Binder _ _ _] _)
      ] ->
        let reassociated =
              Lean.App (Lean.Var (Lean.Ident "Bind.bind"))
                [ innerRhs
                , Lean.Lambda [innerBinder]
                    (Lean.App (Lean.Var (Lean.Ident "Bind.bind"))
                      [innerBody, outerLam])
                ]
        in go rawEnv blocked reassociated

    Lean.App (Lean.Var (Lean.Ident "Bind.bind"))
      [rhs, Lean.Lambda [Lean.Binder _ bindName _] body] ->
        case rhs of
          Lean.Var rhsName | Just rawRhs <- Map.lookup rhsName rawEnv -> do
            RawifiedExcept bodyHoists rawBody <-
              go (Map.insert bindName (Lean.Var bindName) rawEnv)
                 (Set.insert bindName blocked) body
            pure (RawifiedExcept bodyHoists
                    (Lean.Let bindName [] Nothing rawRhs rawBody))
          _ ->
            let rhsBlocked = termMentionsAny blocked rhs in
            case go rawEnv blocked rhs of
              Just (RawifiedExcept rhsHoists rawRhs)
                | rhsBlocked || isPureApp rhs -> do
                    RawifiedExcept bodyHoists rawBody <-
                      go (Map.insert bindName (Lean.Var bindName) rawEnv)
                         (Set.insert bindName blocked) body
                    pure (RawifiedExcept
                            (rhsHoists ++ bodyHoists)
                            (Lean.Let bindName [] Nothing rawRhs rawBody))
              _
                | not rhsBlocked -> do
                    RawifiedExcept bodyHoists rawBody <-
                      go rawEnv blocked body
                    pure (RawifiedExcept ((bindName, rhs) : bodyHoists) rawBody)
                | otherwise ->
                    case go rawEnv blocked rhs of
                      Just (RawifiedExcept rhsHoists rawRhs) -> do
                        RawifiedExcept bodyHoists rawBody <-
                          go (Map.insert bindName (Lean.Var bindName) rawEnv)
                             (Set.insert bindName blocked) body
                        pure (RawifiedExcept
                                (rhsHoists ++ bodyHoists)
                                (Lean.Let bindName [] Nothing rawRhs rawBody))
                      Nothing -> Nothing

    Lean.Let name binders mty rhs body ->
      case rawifyPureEtaShadow name rhs body of
        Just raw -> Just (RawifiedExcept [] raw)
        Nothing ->
          case peelPureValueShadow name rhs body of
            Just body' -> go rawEnv blocked body'
            Nothing
              | null binders
              , isTransparentRawifierLet rhs ->
                  go rawEnv blocked (substLeanIdent name rhs body)
              | otherwise -> do
                  case go rawEnv blocked rhs of
                    Just (RawifiedExcept rhsHoists rawRhs) -> do
                      RawifiedExcept bodyHoists rawBody <-
                        go (Map.insert name (Lean.Var name) rawEnv)
                           (Set.insert name blocked) body
                      pure (RawifiedExcept
                              (rhsHoists ++ bodyHoists)
                              (Lean.Let name binders mty rawRhs rawBody))
                    Nothing -> do
                      RawifiedExcept hoists rawBody <-
                        go rawEnv (Set.insert name blocked) body
                      pure (RawifiedExcept hoists
                              (Lean.Let name binders mty rhs rawBody))

    Lean.App (Lean.Var (Lean.Ident "atWithDefaultM")) [n, elTy, deflt, vec, ix] -> do
      RawifiedExcept vecHoists rawVec <- go rawEnv blocked vec
      if atIndexDefinitelyInBounds n ix
         then pure (RawifiedExcept vecHoists
                (atInBounds n elTy rawVec ix))
         else do
           RawifiedExcept defHoists rawDefault <- go rawEnv blocked deflt
           if null defHoists
              then pure (RawifiedExcept vecHoists
                     (Lean.App (Lean.Var (Lean.Ident "atWithDefault"))
                       [n, elTy, rawDefault, rawVec, ix]))
              else Nothing

    Lean.App (Lean.Var (Lean.Ident "vecSequenceM")) [_, _, Lean.List elems] -> do
      rawElems <- traverse (go rawEnv blocked) elems
      pure (RawifiedExcept
        (concatMap reHoists rawElems)
        (Lean.List (map reRaw rawElems)))

    Lean.App (Lean.Var (Lean.Ident "mkStreamM"))
      [elTy, Lean.Lambda [idxBinder@(Lean.Binder _ idxName _)] body] -> do
        RawifiedExcept hoists rawBody <-
          go rawEnv (Set.insert idxName blocked) body
        pure (RawifiedExcept hoists
          (Lean.App (Lean.ExplVar (Lean.Ident "Stream.MkStream"))
            [elTy, Lean.Lambda [idxBinder] rawBody]))

    Lean.App streamRecHead [elTy, motive, handler, scrut]
      | isLeanHead "Stream.rec" streamRecHead
      , Lean.Lambda handlerBinders handlerBody <- handler
      , Just rawMotive <- rawifyExceptMotive motive -> do
          (hoists, rawHandler) <-
            rawifyExceptHandler go rawEnv blocked handlerBinders handlerBody
          pure (RawifiedExcept hoists
                  (Lean.App streamRecHead
                    [ elTy
                    , rawMotive
                    , rawHandler
                    , scrut
                    ]))

    Lean.App recHead args
      | isOneCtorRecHead recHead
      , (params, [motive, handler, scrut]) <- splitAt (length args - 3) args
      , Lean.Lambda handlerBinders handlerBody <- handler
      , Just rawMotive <- rawifyExceptMotive motive -> do
          (hoists, rawHandler) <-
            rawifyExceptHandler go rawEnv blocked handlerBinders handlerBody
          pure (RawifiedExcept hoists
                  (Lean.App recHead
                    (params ++
                      [ rawMotive
                      , rawHandler
                      , scrut
                      ])))

    _ -> Nothing

  rawifyExceptHandler goFn rawEnv blocked handlerBinders handlerBody = do
    let handlerNames = map leanBinderName handlerBinders
        handlerBlocked =
          blocked `Set.union` Set.fromList handlerNames
        rawEnv' =
          foldr (\name -> Map.insert name (Lean.Var name)) rawEnv handlerNames
    rawBinders <- traverse rawifyExceptHandlerBinder handlerBinders
    RawifiedExcept hoists rawHandlerBody <-
      goFn rawEnv' handlerBlocked handlerBody
    pure (hoists, Lean.Lambda rawBinders rawHandlerBody)

rawifyExceptMotive :: Lean.Term -> Maybe Lean.Term
rawifyExceptMotive (Lean.Lambda binders body) =
  Lean.Lambda binders <$> unwrapExceptType body
rawifyExceptMotive _ = Nothing

unwrapExceptType :: Lean.Type -> Maybe Lean.Type
unwrapExceptType (Lean.App (Lean.Var (Lean.Ident "Except"))
                           [Lean.Var (Lean.Ident "String"), raw]) =
  Just raw
unwrapExceptType _ = Nothing

rawifyExceptHandlerBinder :: Lean.Binder -> Maybe Lean.Binder
rawifyExceptHandlerBinder (Lean.Binder imp name mty) =
  Just (Lean.Binder imp name (rawifyExceptHandlerType <$> mty))

rawifyExceptHandlerType :: Lean.Type -> Lean.Type
rawifyExceptHandlerType ty =
  fromMaybe ty (unwrapExceptCodomain ty)

unwrapExceptCodomain :: Lean.Type -> Maybe Lean.Type
unwrapExceptCodomain ty =
  unwrapExceptType ty <|> case ty of
    Lean.Pi binders body ->
      Lean.Pi binders <$> unwrapExceptCodomain body
    _ -> Nothing

unreachableDefault :: Lean.Term -> String -> Lean.Term
unreachableDefault ty msg =
  Lean.App (Lean.Var (Lean.Ident "saw_unreachable_default"))
    [ty, Lean.StringLit msg]

atInBounds :: Lean.Term -> Lean.Term -> Lean.Term -> Lean.Term -> Lean.Term
atInBounds n ty vec ix =
  Lean.App (Lean.Var (Lean.Ident "atInBounds"))
    [n, ty, vec, ix, Lean.Tactic "decide"]

atIndexDefinitelyInBounds :: Lean.Term -> Lean.Term -> Bool
atIndexDefinitelyInBounds (Lean.NatLit n) (Lean.NatLit ix) =
  0 <= ix && ix < n
atIndexDefinitelyInBounds _ _ = False

rawifyPureEtaShadow :: Lean.Ident -> Lean.Term -> Lean.Term -> Maybe Lean.Term
rawifyPureEtaShadow name
  (Lean.Lambda [Lean.Binder _ argName _]
    (Lean.App (Lean.Var (Lean.Ident "Pure.pure"))
      [Lean.App (Lean.Var rhsName) [Lean.Var argName']]))
  (Lean.App (Lean.Var bodyName) args)
  | name == rhsName
  , name == bodyName
  , argName == argName' =
      Just (Lean.App (Lean.Var name) args)
rawifyPureEtaShadow _ _ _ = Nothing

peelPureValueShadow :: Lean.Ident -> Lean.Term -> Lean.Term -> Maybe Lean.Term
peelPureValueShadow name
  (Lean.App (Lean.Var (Lean.Ident "Pure.pure")) [Lean.Var rhsName])
  body
  | name == rhsName = Just body
peelPureValueShadow _ _ _ = Nothing

isTransparentRawifierLet :: Lean.Term -> Bool
isTransparentRawifierLet (Lean.Lambda _ body) =
  not (mentionsEffectSyntax body)
isTransparentRawifierLet _ = False

mentionsEffectSyntax :: Lean.Term -> Bool
mentionsEffectSyntax = \case
  Lean.Var{} -> False
  Lean.ExplVar{} -> False
  Lean.ExplVarUniv{} -> False
  Lean.Sort{} -> False
  Lean.NatLit{} -> False
  Lean.IntLit{} -> False
  Lean.StringLit{} -> False
  Lean.Tactic{} -> False
  Lean.Lambda binders body ->
    any binderMentions binders || mentionsEffectSyntax body
  Lean.Pi binders body ->
    any piBinderMentions binders || mentionsEffectSyntax body
  Lean.Let _ binders mty rhs body ->
    any binderMentions binders ||
    maybe False mentionsEffectSyntax mty ||
    mentionsEffectSyntax rhs ||
    mentionsEffectSyntax body
  Lean.App head_ args ->
    isEffectHead head_ ||
    mentionsEffectSyntax head_ ||
    any mentionsEffectSyntax args
  Lean.Ascription tm ty ->
    mentionsEffectSyntax tm || mentionsEffectSyntax ty
  Lean.List elems ->
    any mentionsEffectSyntax elems
  where
    isEffectHead head_ =
      any (`isLeanHead` head_)
        [ "Pure.pure"
        , "Bind.bind"
        , "mkStreamM"
        , "atWithDefaultM"
        , "vecSequenceM"
        ]
    binderMentions (Lean.Binder _ _ mty) =
      maybe False mentionsEffectSyntax mty
    piBinderMentions (Lean.PiBinder _ _ ty) =
      mentionsEffectSyntax ty

isLeanHead :: String -> Lean.Term -> Bool
isLeanHead expected = \case
  Lean.Var (Lean.Ident actual) -> actual == expected
  Lean.ExplVar (Lean.Ident actual) -> actual == expected
  Lean.ExplVarUniv (Lean.Ident actual) _ -> actual == expected
  _ -> False

isOneCtorRecHead :: Lean.Term -> Bool
isOneCtorRecHead head_ =
  any (`isLeanHead` head_) ["PairType.rec", "RecordType.rec"]

isPureApp :: Lean.Term -> Bool
isPureApp (Lean.App (Lean.Var (Lean.Ident "Pure.pure")) [_]) = True
isPureApp _ = False

leanBinderName :: Lean.Binder -> Lean.Ident
leanBinderName (Lean.Binder _ name _) = name

termMentionsAny :: Set Lean.Ident -> Lean.Term -> Bool
termMentionsAny needles0 = go needles0
  where
    go needles _
      | Set.null needles = False
    go needles (Lean.Var ident) = ident `Set.member` needles
    go needles (Lean.ExplVar ident) = ident `Set.member` needles
    go needles (Lean.ExplVarUniv ident _) = ident `Set.member` needles
    go needles (Lean.Lambda binders body) =
      any (binderMentions needles) binders
        || go (foldr Set.delete needles (map leanBinderName binders)) body
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

substLeanIdent :: Lean.Ident -> Lean.Term -> Lean.Term -> Lean.Term
substLeanIdent target replacement = go
  where
    go (Lean.Var ident)
      | ident == target = replacement
      | otherwise = Lean.Var ident
    go (Lean.ExplVar ident) = Lean.ExplVar ident
    go (Lean.ExplVarUniv ident levels) = Lean.ExplVarUniv ident levels
    go (Lean.Lambda binders body) =
      let binders' = map substBinder binders
      in if any ((== target) . leanBinderName) binders
            then Lean.Lambda binders' body
            else Lean.Lambda binders' (go body)
    go (Lean.Pi binders body) =
      let binders' = map substPiBinder binders
          shadows (Lean.PiBinder _ mName _) = mName == Just target
      in if any shadows binders
            then Lean.Pi binders' body
            else Lean.Pi binders' (go body)
    go (Lean.Let name binders mty rhs body) =
      Lean.Let name (map substBinder binders) (go <$> mty) (go rhs)
        (if name == target then body else go body)
    go (Lean.App f args) = Lean.App (go f) (map go args)
    go (Lean.Ascription a b) = Lean.Ascription (go a) (go b)
    go (Lean.List xs) = Lean.List (map go xs)
    go t@Lean.Sort{} = t
    go t@Lean.NatLit{} = t
    go t@Lean.IntLit{} = t
    go t@Lean.StringLit{} = t
    go t@Lean.Tactic{} = t

    substBinder (Lean.Binder imp name mty) =
      Lean.Binder imp name (go <$> mty)
    substPiBinder (Lean.PiBinder imp mName ty) =
      Lean.PiBinder imp mName (go ty)

proofObligationPlaceholder :: Lean.Term
proofObligationPlaceholder =
  -- Emit-stage placeholder only. The check-stage must reject completed
  -- artifacts that still contain this `sorry`.
  Lean.Tactic "sorry"

withLocalProofObligation ::
  TermTranslationMonad m =>
  Lean.Ident ->
  Lean.Term ->
  (Lean.Term -> m Lean.Term) ->
  m Lean.Term
withLocalProofObligation baseName prop mkBody = do
  let propBaseName = case baseName of
        Lean.Ident s -> Lean.Ident (s ++ "obligation_")
  propName <- freshVariantAvoiding (leanTermIdents prop) propBaseName
  proofName <- freshVariantAvoiding (Set.insert propName (leanTermIdents prop)) baseName
  body <- mkBody (Lean.Var proofName)
  pure (Lean.Let propName [] (Just (Lean.Sort Lean.Prop)) prop
          (Lean.Let proofName [] (Just (Lean.Var propName))
             proofObligationPlaceholder body))

translateIdentWithArgs :: TermTranslationMonad m => Ident -> [Term] -> m Lean.Term
translateIdentWithArgs i args = ttLean <$> translateIdentWithArgsWithShape i args

translateIdentWithArgsWithShape ::
  TermTranslationMonad m => Ident -> [Term] -> m TranslatedTerm
translateIdentWithArgsWithShape i args
  | i == "Prelude.error"
  , (resultTy : _msg : _) <- args
  , not (shouldWrapBinder resultTy)
  = Except.throwError (RejectedPrimitive "error"
      "Prelude.error is only supported at wrapped value-domain result \
      \types. Raw Nat/Num indices, types, propositions/proofs, and \
      \function results must be rejected or represented by an explicit \
      \Lean proof obligation; the backend must not emit an Except value \
      \where Lean expects a raw/type/proof/function term.")
  | i == "Prelude.fix"
  , [typeArg, bodyArg] <- args
  = case classifyFix typeArg bodyArg of
      StreamCorec elT body                 ->
        TranslatedTerm <$> lowerStreamCorec elT body <*> pure BindingWrapped
      PairStreamCorec elTypeA elTypeB body ->
        TranslatedTerm <$> lowerPairStreamCorec elTypeA elTypeB body <*> pure BindingWrapped
      BoundedVecFold len elType body       ->
        TranslatedTerm <$> lowerBoundedVecFold len elType body <*> pure BindingWrapped
      NotMatched _                         -> originalDispatchWithShape i args
  -- Polymorphic stream iteration: Cryptol's `iterate` shape, where
  -- @fix@ is applied to its type/body plus three extras (α, f, x) that
  -- monomorphise the polymorphism. Pattern-matched on the body's
  -- @MkStream@ shape; lowered to a direct call to the hand-written
  -- structural-recursion def `cryptolIterate` in
  -- SAWCorePreludeExtra.lean — sidestepping the type-system challenge
  -- of encoding a polymorphic `Prelude.fix` body in Lean.
  | i == "Prelude.fix"
  , (typeArg : bodyArg : extras) <- args
  , Just (alphaArg, fArg, xArg) <- classifyPolyStreamIterate typeArg bodyArg extras
  = lowerPolyStreamIterate alphaArg fArg xArg
  | i == "Prelude.MkStream"
  , [elTypeArg, indexFnArg] <- args
  = do
      elTypeLean <- translateTerm elTypeArg
      indexFnLean <- translateFunctionWithWrappedResult indexFnArg
      defer <- view deferMkStreamLowering <$> askTR
      streamTerm <-
        if defer
           then pure (Lean.App (Lean.Var (Lean.Ident "mkStreamM"))
                  [elTypeLean, indexFnLean])
           else lowerMkStreamSound elTypeLean indexFnLean
      pure (TranslatedTerm streamTerm BindingWrapped)
  | i == "Prelude.coerce"
  , (fromTy : toTy : eqProof : valueArg : restArgs) <- args
  = do
      fromTyLean <- translateTerm fromTy
      toTyLean <- translateTerm toTy
      eqProofLean <- translateTerm eqProof
      valueLean <- translateTerm valueArg
      let coerceHead =
            Lean.App (Lean.Var (Lean.Ident "coerce"))
              [fromTyLean, toTyLean, eqProofLean]
      if isJust (asPi fromTy) || isJust (asPi toTy)
         then do
           restLean <- traverse translateTerm restArgs
           let tm = Lean.App (Lean.App coerceHead [valueLean]) restLean
           shape <- bindingShapeOfLeanTermM tm
           pure (TranslatedTerm tm shape)
         else do
           coerced <- buildLiftedWithShape BindingWrapped coerceHead True [True] [valueLean]
           restLean <- traverse translateTerm restArgs
           let tm = Lean.App (ttLean coerced) restLean
           shape <- bindingShapeOfLeanTermM tm
           pure (TranslatedTerm tm shape)
  -- SAWCore @Eq : (a : sort 1) → a → a → Prop@. When @a@ is a
  -- value-domain SAW type (Bool, Vec n α, …), the Phase β
  -- translation of @x@/@y@ at type @a@ is wrapped in
  -- @Except String a@. Lean's @Eq@ is polymorphic in its type
  -- arg, so we can pass @Except String a@ as the type-arg and
  -- @x@/@y@ at their wrapped types — natural shape for VC
  -- discharge ("@F_wrapped x = Pure.pure true@"). Type-level
  -- uses (@Eq Type X Y@) translate without wrap because
  -- 'shouldWrapBinder' returns False on @Sort@.
  | i == "Prelude.Eq"
  , [aArg, xArg, yArg] <- args
  , shouldWrapBinder aArg
  = do
      aTrans <- translateTerm aArg
      xTrans <- translateTerm xArg
      yTrans <- translateTerm yArg
      pure $ TranslatedTerm
        (Lean.App (Lean.ExplVar (Lean.Ident "Eq"))
          [ wrapExcept aTrans
          , liftRawValue xTrans
          , liftRawValue yTrans
          ])
        BindingRaw
translateIdentWithArgsWithShape i args = originalDispatchWithShape i args

originalDispatchWithShape ::
  TermTranslationMonad m => Ident -> [Term] -> m TranslatedTerm
originalDispatchWithShape i args = do
  specialTreatment <- findSpecialTreatment i
  qualifiedIdent   <- defaultIdentTarget i
  mm               <- view sawModuleMap <$> askTR
  -- SAWCore applies all arguments (including datatype parameters) to
  -- a constructor explicitly. Lean's auto-generated @MyData.ctor@
  -- takes datatype parameters /implicitly/, so we emit a leading
  -- @\@@ to force all arguments explicit.
  let isCtor = case resolveNameInMap mm i of
        Just (ResolvedCtor _) -> True
        _                     -> False
  apply isCtor qualifiedIdent (atUseSite specialTreatment)
  where
    -- Look up the function's SAW type so we can decide whether
    -- to lift the application into the @Except String@ monad.
    -- We lift iff the return is a value-domain type (e.g.
    -- @bvAdd@ returns @Vec n Bool@); for proof helpers whose
    -- return is a @Prop@ (e.g. @sym@, @trans@), no lift.
    funType mm = case resolveNameInMap mm i of
      Just (ResolvedDef def)  -> Just (defType def)
      Just (ResolvedCtor ctor) -> Just (ctorType ctor)
      _                         -> Nothing
    retTypeOfFun fty =
      let (_binders, ret) = asPiList fty in ret
    -- Wrap only when there are actual arguments; otherwise return the
    -- head bare. This keeps translated zero-arity constants as their
    -- natural form (e.g. @NatLit 1@ rather than @App (NatLit 1) []@),
    -- which lets 'UseMacro' entries pattern-match on literals through
    -- nested applications.
    --
    -- When 'shouldLift' (the function's return type is value-typed),
    -- emit a do-block that binds each value-arg from its wrapped
    -- expression and applies the function to bound names:
    --
    -- @
    -- do let v_i ← arg_i
    --    pure (f t_args v_args)
    -- @
    --
    -- Type-args (positions in 'typeArgIxs') splice directly into the
    -- function-application head; value-args go through the bind chain.
    -- Each value-arg's translation produces either an already-wrapped
    -- term (e.g. a variable bound by 'translateBinder'' under our
    -- wrap rule) or a non-wrapped term (e.g. a NatLit) — the
    -- 'liftArgIfNeeded' helper inserts a 'pure' for the latter so
    -- the bind chain typechecks uniformly.
    applied :: TermTranslationMonad m => Lean.Term -> [Term] -> m TranslatedTerm
    applied f [] = do
      shape <- bindingShapeOfLeanTermM f
      pure (TranslatedTerm f shape)
    applied f args' = do
      argResults <- mapM translateTermWithShape args'
      let argTerms = map ttLean argResults
      mm' <- view sawModuleMap <$> askTR
      case funType mm' of
        Just fty
          | any (shouldWrapBinder . snd) (fst (asPiList fty))
              || shouldWrapBinder (retTypeOfFun fty) -> do
              -- Lift when either:
              --   * the function returns a value-domain type
              --     (bvAdd-style: result needs wrapping), OR
              --   * any value-typed binder is present (ite-style:
              --     scrutinee 'b : Bool' arrives wrapped and must
              --     be bound before passing to the Lean target).
              --
              -- Per-position bind decision:
              --   * type-arg position (used as index in subsequent
              --     binder types or retType): no bind, splice raw.
              --   * formal binder type is value-domain (Bool, Vec,
              --     Nat-but-not-as-Nat, …): bind via Bind.bind.
              --   * formal binder type is a Pi (higher-order arg
              --     like @gen@'s @Nat → α@) / Sort / Prop / Eq /
              --     Nat: no bind, splice raw.
              --   * formal binder type is variable-headed (a, p y
              --     pf): bind. The SAW instantiation typically
              --     puts a concrete value-domain type there
              --     (PairValue's @α := Vec 8 Bool@), so the arg
              --     arrives Except-wrapped and the Lean target
              --     (e.g. 'PairValue' ctor) expects raw.
              --
              -- 'Pure.pure'-wrap the result when the function's
              -- SAW return type is value-domain OR variable-headed.
              -- Variable-headed (Pair_fst's @α@, coerce's @b@) is
              -- assumed instantiated to a value-domain type at use
              -- sites — most polymorphic SAWCore helpers produce
              -- value-domain results when applied. Proof helpers
              -- (sym, trans) return 'Eq' (not variable-headed), so
              -- this rule doesn't pure-wrap them. Macro-routed
              -- targets like 'iteM' bypass this lift entirely via
              -- 'UseMacroOrVar', so no double-wrap concern there.
              let shouldBind = argumentBindPlan fty argResults
              let (binders, _) = asPiList fty
                  ret = retTypeOfFun fty
                  fullyApplied = length args' >= length binders
              if fullyApplied
                 then
                   let shouldBindForArgs =
                         take (length args') (shouldBind ++ repeat False)
                       pureWrap =
                         shouldWrapBinder ret || isVariableHead ret || natValueResult fty
                       resultShape = phaseBetaResultShape fty (length args')
                   in buildLiftedWithShape resultShape f pureWrap shouldBindForArgs argTerms
                 else do
                   -- Partial application: eta-expand so the
                   -- function has the Phase-β wrapped shape at the
                   -- missing positions. Without this, passing
                   -- e.g. @bvAdd n@ as a higher-order arg to
                   -- 'foldlM' (whose @f@ formal is wrapped) would
                   -- fit @α → β → β@ but not
                   -- @Except α → Except β → Except β@. Eta-
                   -- expansion runs the same 'buildLifted'
                   -- pipeline on the full arg list (supplied
                   -- args + eta vars).
                   --
                   -- Binder types are emitted /without/ type
                   -- annotations: the missing binders' SAW types
                   -- may reference earlier-bound vars (e.g.
                   -- @Vec n Bool@'s @n@ is the 0th binder); we
                   -- can't translate them in isolation. Lean's
                   -- elaborator infers them from the surrounding
                   -- call's expected function type.
                   let missingBinders = drop (length args') binders
                       -- Use indexed names so each eta var is
                       -- distinct. 'freshVariant' alone is
                       -- idempotent across calls (it doesn't
                       -- update 'unavailableIdents'), so just
                       -- mintng "η_" twice yields the same name.
                       baseNames =
                         [ Lean.Ident ("η_" ++ show k)
                         | k <- [0 .. length missingBinders - 1]
                         ]
                   etaNames <- mapM freshVariant baseNames
                   let etaBindersLean =
                         [ Lean.Binder Lean.Explicit name Nothing
                         | name <- etaNames
                         ]
                       etaArgTerms = argTerms ++ map Lean.Var etaNames
                       pureWrap =
                         shouldWrapBinder ret || isVariableHead ret || natValueResult fty
                       typeIxs = typeArgPositions fty
                       missingWrapped =
                         [ ix `notElem` typeIxs
                           && isNothing (asSort bty)
                           && isNothing (asEq bty)
                           && isNothing (asPi bty)
                         | (ix, (_, bty)) <-
                             zip [length args'..] missingBinders
                         ]
                   let suppliedWrapped =
                         map (isWrappedShape . ttShape) argResults
                   let shouldBindEta =
                         argumentBindPlanFromWrapped fty etaArgTerms
                           (suppliedWrapped ++ missingWrapped)
                   body <- buildLifted f pureWrap
                             (take (length etaArgTerms)
                                   (shouldBindEta ++ repeat False))
                             etaArgTerms
                   pure (TranslatedTerm
                           (Lean.Lambda etaBindersLean body)
                           BindingFunction)
        Just fty -> do
          let tm = Lean.App f argTerms
          pure (TranslatedTerm tm (phaseBetaResultShape fty (length args')))
        Nothing -> do
          let tm = Lean.App f argTerms
          shape <- bindingShapeOfLeanTermM tm
          pure (TranslatedTerm tm shape)

    apply :: TermTranslationMonad m =>
             Bool -> Lean.Ident -> UseSiteTreatment -> m TranslatedTerm
    apply isCtor qualifiedIdent UsePreserve =
      let head_ = (if isCtor then Lean.ExplVar else Lean.Var) qualifiedIdent
      in applied head_ args
    apply isCtor _ (UseRename mTargetMod targetName expl) = do
      -- Resolving a use-site reference via a 'rename' / 'mapsTo'
      -- entry.
      --
      --   * If the caller explicitly supplied a target module
      --     (@Just mod_@) AND that module is in the implicit-open
      --     list (see 'isImplicitlyOpened'), emit the bare target
      --     name — the preamble's @open@ makes it resolve, and the
      --     output is dramatically shorter.
      --   * Else if the caller supplied a target module, emit
      --     fully-qualified.
      --   * Otherwise, if the target name already contains a '.'
      --     (e.g. @Eq.refl@), it's a pre-qualified Lean name that
      --     the caller wants emitted as-is.
      --   * Otherwise, if the SAWCore ident is a constructor, scope
      --     the new short name inside the datatype's short name
      --     (Lean inductives @C.ctor@).
      mm <- view sawModuleMap <$> askTR
      curMod <- view currentModule <$> askTR
      let Lean.Ident tName = targetName
          alreadyQualified = '.' `elem` tName
          scopedTarget = case mTargetMod of
            Just mod_
              | isImplicitlyOpened mod_ -> targetName
              | otherwise               -> qualify mod_ targetName
            Nothing
              | alreadyQualified -> targetName
              | isCtor, Just (ResolvedCtor c) <- resolveNameInMap mm i ->
                  let dtShort = Text.unpack (toShortName (nameInfo (ctorDataType c)))
                      scopedShort = Lean.Ident (dtShort ++ "." ++ tName)
                      sameModule = Just (identModule i) == curMod
                  in if sameModule
                       then scopedShort
                       else qualify (translateModuleName (identModule i)) scopedShort
              | otherwise -> targetName
          head_ = (if expl then Lean.ExplVar else Lean.Var) scopedTarget
      applied head_ args
    apply _ _ (UseRenameUniv mTargetMod targetName argIxs) = do
      -- Same scoping logic as 'UseRename'-with-expl, but also try to
      -- supply explicit universe levels at the indexed argument
      -- positions. Falls back to bare @\@name@ if any indexed
      -- universe doesn't resolve.
      let Lean.Ident tName = targetName
          alreadyQualified = '.' `elem` tName
          scopedTarget = case mTargetMod of
            Just mod_
              | isImplicitlyOpened mod_ -> targetName
              | otherwise               -> qualify mod_ targetName
            Nothing
              | alreadyQualified -> targetName
              | otherwise        -> targetName
      mLvls <- traverse (\ix ->
                  if ix < length args
                     then levelOfArg (args !! ix)
                     else pure Nothing) argIxs
      let head_ = case sequence mLvls of
            Just lvls -> Lean.ExplVarUniv scopedTarget lvls
            Nothing   -> Lean.ExplVar scopedTarget
      applied head_ args
    apply _ _ (UseMacro n resultShape macroFun)
      | length args >= n
      , (mArgs, rest) <- splitAt n args = do
          f <- macroFun <$> mapM translateTerm mArgs
          if null rest
             then pure (TranslatedTerm f (bindingShapeOfUseResultShape resultShape))
             else applied f rest
      | otherwise =
          -- Under-applied macro — the table entry promises to consume n
          -- arguments but fewer were supplied. Surface it explicitly;
          -- emitting a partial application would produce garbage.
          Except.throwError (UnderAppliedMacro (Text.pack (identName i)) n)
    apply _ _ (UseMacroOrVar n resultShape fallback macroFun)
      | length args >= n
      , (mArgs, rest) <- splitAt n args = do
          f <- macroFun <$> mapM translateTerm mArgs
          if null rest
             then pure (TranslatedTerm f (bindingShapeOfUseResultShape resultShape))
             else applied f rest
      | otherwise =
          -- Under-applied. With no args, emit the fallback head and let
          -- Lean eta-expand at use sites. With some args already
          -- supplied, run the macro's argument adaptation on that
          -- prefix before returning the function-shaped partial
          -- application; e.g. @ite Bool True@ must become
          -- @iteM Bool (Pure.pure Bool.true)@, not @iteM Bool
          -- Bool.true@.
          do argResults <- traverse translateTermWithShape args
             let argTerms = map ttLean argResults
                 tm = if null argTerms
                         then fallback
                         else macroFun argTerms
             pure (TranslatedTerm tm BindingFunction)
    apply _ _ (UseMapsToWrapped n target)
      | length args >= n
      , (mArgs, rest) <- splitAt n args = do
          mm <- view sawModuleMap <$> askTR
          let sawBinderTys = case resolveNameInMap mm i of
                Just (ResolvedDef def)  ->
                  map snd (fst (asPiList (defType def)))
                Just (ResolvedCtor ctor) ->
                  map snd (fst (asPiList (ctorType ctor)))
                _ -> []
              -- The SAW signature has @n@ or more pi binders; map
              -- the first @n@ to the supplied args. Per arg @i@: if
              -- the binder type is "value-domain at a wrapped-target
              -- position" — meaning either Phase-β's
              -- 'shouldWrapBinder' fires, OR the binder type is a
              -- polymorphic type variable (a 'sort 0' bound earlier
              -- in the signature; under Phase β polymorphic
              -- value-domain positions wrap in the Lean target).
              -- The wrapped target then expects 'Except String ty'
              -- there, so 'liftRawValue' the translated arg (a
              -- no-op on already-wrapped terms; lifts raw
              -- constructor / literal / nullary refs).
              isVarHeadOnly t = isVariableHead t && case unwrapTermF t of
                Variable {} -> True
                _ -> False
              wrapAtMapsToWrapped t =
                shouldWrapBinder t || isVarHeadOnly t
              shouldLift = take n (map wrapAtMapsToWrapped sawBinderTys
                                    ++ repeat False)
          argResults <- traverse translateTermWithShape mArgs
          let translated = map ttLean argResults
              actualWrapped = map (isWrappedShape . ttShape) argResults
              shouldBindRaw =
                zipWith (\expectsWrapped isWrappedActual ->
                           not expectsWrapped && isWrappedActual)
                        shouldLift actualWrapped
              adapted =
                zipWith (\expectsWrapped t ->
                           if expectsWrapped then liftRawValue t else t)
                        shouldLift translated
          helperApp <- buildLifted (Lean.Var target) False shouldBindRaw adapted
          if null rest
             then pure (TranslatedTerm helperApp BindingWrapped)
             else applied helperApp rest
      | otherwise =
          -- Under-applied: emit bare 'Var target' and apply whatever
          -- args we did receive (no per-arg lift here — partial
          -- applications are handled at App-level).
          do argResults <- traverse translateTermWithShape args
             let argTerms = map ttLean argResults
                 tm = if null argTerms
                         then Lean.Var target
                         else Lean.App (Lean.Var target) argTerms
             pure (TranslatedTerm tm BindingFunction)
    apply _ _ (UseReject reason) =
      Except.throwError
        (RejectedPrimitive (Text.pack (identName i)) reason)

-- | Lower a 'StreamCorec'-shaped @Prelude.fix@ to a Lean
-- 'mkStreamFix' call. The body — a SAWCore lambda
-- @\\rec -> MkStream α (\\i -> e)@ — is translated normally; the
-- lookup-form rewrite happens at Lean-AST level by applying the
-- translated body to @Stream.MkStream lookup_@ and projecting
-- through 'streamIdx'. Lean's iota-reduction substitutes through
-- the recursor calls inside @e@, so no SAWCore-term-level rewriting
-- is required.
--
-- See @doc/2026-05-02_recursion-design.md@ §"Soundness argument" for
-- the meaning-preservation argument; the Cryptol-productivity link
-- is residual trust documented in @residual-trust.md@.
lowerStreamCorec :: TermTranslationMonad m => Term -> Term -> m Lean.Term
lowerStreamCorec elTypeTerm bodyTerm = do
  elTypeLean <- translateTerm elTypeTerm
  bodyLean   <- localTR (set deferMkStreamLowering True) $
                  translateTerm bodyTerm
  lookupName <- freshVariant (Lean.Ident "lookup_")
  indexName  <- freshVariant (Lean.Ident "i_")
  -- Under Phase β the body translates with @rec : Except (Stream α)@:
  --   bodyLean : Except (Stream α) → Except (Stream α)
  -- Build the wrapped lookup-form body, then pass it through the same
  -- rawification gate used by direct MkStream lowering. This permits
  -- only index/lookup-pure bodies (plus hoistable captured effects)
  -- to reach the raw mkStreamFix helper; residual per-index effects
  -- reject instead of defaulting.
  let pureVar = Lean.Var (Lean.Ident "Pure.pure")
      errorTermRaw =
        unreachableDefault elTypeLean "fix lookup out of bounds"
      mkStreamCall =
        Lean.App (Lean.Var (Lean.Ident "Stream.MkStream"))
          [Lean.Var lookupName]
      bodyApplied = Lean.App bodyLean [Lean.App pureVar [mkStreamCall]]
      indexCall =
        Lean.App (Lean.Var (Lean.Ident "Bind.bind"))
          [ bodyApplied
          , Lean.Lambda [Lean.Binder Lean.Explicit (Lean.Ident "s_") Nothing]
              (Lean.App pureVar
                [Lean.App (Lean.Var (Lean.Ident "streamIdx"))
                  [elTypeLean, Lean.Var (Lean.Ident "s_"), Lean.Var indexName]])
          ]
  rawified <- case rawifyExceptToRaw (Set.fromList [lookupName, indexName]) indexCall of
    Just r -> pure r
    Nothing ->
      Except.throwError (RejectedPrimitive "fix"
        "Stream corecursion body has residual per-index error effects. \
        \The Lean backend cannot default those errors inside a Stream.")
  let innerLambda =
        Lean.Lambda
          [ Lean.Binder Lean.Explicit lookupName Nothing
          , Lean.Binder Lean.Explicit indexName  Nothing
          ]
          (reRaw rawified)
      productivityProp =
        Lean.App (Lean.Var (Lean.Ident "StreamBodyProductive"))
          [elTypeLean, innerLambda]
  checked <- withLocalProofObligation
    (Lean.Ident "h_productivity_")
    productivityProp
    $ \proof ->
        pure (Lean.App (Lean.Var (Lean.Ident "mkStreamFixChecked"))
          [ elTypeLean
          , errorTermRaw
          , innerLambda
          , proof
          ])
  let base = Lean.App pureVar [checked]
  pure (wrapHoistedExcepts (reHoists rawified) base)

-- | Lower a 'PairStreamCorec'-shaped @Prelude.fix@ to a Lean
-- 'mkStreamFixPairChecked' call. The body — a SAWCore lambda
-- @\\x -> PairValue1 _ _ (MkStream α f1) (MkStream β f2)@ — is
-- translated normally; the lookup-form rewrite happens at Lean-AST
-- level by applying the translated body to a synthesized
-- @PairType.PairValue (Stream.MkStream lkA) (Stream.MkStream lkB)@
-- and projecting through 'pairFst'/'pairSnd' + 'streamIdx'. Lean's
-- iota-reduction takes care of the @PairType1#rec1@ + @Stream#rec@
-- chains inside the body.
--
-- Because we project both the first and second component out of the
-- same applied body, the body lambda gets re-applied in each branch.
-- That's idempotent — the body is a pure function of @x@ — and the
-- redundant work disappears at iota-reduction time. See
-- @doc/2026-05-02_recursion-design.md@ §"Soundness argument".
lowerPairStreamCorec :: TermTranslationMonad m => Term -> Term -> Term -> m Lean.Term
lowerPairStreamCorec elTypeATerm elTypeBTerm bodyTerm = do
  elTypeALean <- translateTerm elTypeATerm
  elTypeBLean <- translateTerm elTypeBTerm
  bodyLean    <- localTR (set deferMkStreamLowering True) $
                   translateTerm bodyTerm
  lkA1 <- freshVariant (Lean.Ident "lkA_")
  lkB1 <- freshVariant (Lean.Ident "lkB_")
  i1   <- freshVariant (Lean.Ident "i_")
  lkA2 <- freshVariant (Lean.Ident "lkA_")
  lkB2 <- freshVariant (Lean.Ident "lkB_")
  i2   <- freshVariant (Lean.Ident "i_")
  let pureVar = Lean.Var (Lean.Ident "Pure.pure")
      bindVar = Lean.Var (Lean.Ident "Bind.bind")
      errA = unreachableDefault elTypeALean "fix lookup out of bounds"
      errB = unreachableDefault elTypeBLean "fix lookup out of bounds"
      streamA = Lean.App (Lean.Var (Lean.Ident "Stream")) [elTypeALean]
      streamB = Lean.App (Lean.Var (Lean.Ident "Stream")) [elTypeBLean]
      mkPairArg lkA lkB =
        Lean.App (Lean.Var (Lean.Ident "PairType.PairValue"))
          [ Lean.App (Lean.Var (Lean.Ident "Stream.MkStream")) [Lean.Var lkA]
          , Lean.App (Lean.Var (Lean.Ident "Stream.MkStream")) [Lean.Var lkB]
          ]
      mkBranchBody lkA lkB iName projectorName resultElType =
        let bodyApplied =
              Lean.App bodyLean [Lean.App pureVar [mkPairArg lkA lkB]]
            pairName = Lean.Ident "pair_"
            streamName = Lean.Ident "stream_"
            projection =
              Lean.App bindVar
                [ bodyApplied
                , Lean.Lambda [Lean.Binder Lean.Explicit pairName Nothing]
                    (Lean.App pureVar
                      [ Lean.App (Lean.Var (Lean.Ident projectorName))
                          [streamA, streamB, Lean.Var pairName]
                      ])
                ]
            indexed =
              Lean.App bindVar
                [ projection
                , Lean.Lambda [Lean.Binder Lean.Explicit streamName Nothing]
                    (Lean.App pureVar
                      [ Lean.App (Lean.Var (Lean.Ident "streamIdx"))
                          [resultElType, Lean.Var streamName, Lean.Var iName]
                      ])
                ]
        in indexed
  rawA <- case rawifyExceptToRaw (Set.fromList [lkA1, lkB1, i1])
                 (mkBranchBody lkA1 lkB1 i1 "pairFst" elTypeALean) of
    Just r -> pure r
    Nothing ->
      Except.throwError (RejectedPrimitive "fix"
        "Pair stream corecursion first component has residual per-index \
        \error effects. The Lean backend cannot default those errors \
        \inside a Stream.")
  rawB <- case rawifyExceptToRaw (Set.fromList [lkA2, lkB2, i2])
                 (mkBranchBody lkA2 lkB2 i2 "pairSnd" elTypeBLean) of
    Just r -> pure r
    Nothing ->
      Except.throwError (RejectedPrimitive "fix"
        "Pair stream corecursion second component has residual per-index \
        \error effects. The Lean backend cannot default those errors \
        \inside a Stream.")
  (hoistsA, rawBodyA) <- freshenHoists (reHoists rawA) (reRaw rawA)
  (hoistsB, rawBodyB) <- freshenHoists (reHoists rawB) (reRaw rawB)
  let branchA = Lean.Lambda
        [ Lean.Binder Lean.Explicit lkA1 Nothing
        , Lean.Binder Lean.Explicit lkB1 Nothing
        , Lean.Binder Lean.Explicit i1 Nothing
        ]
        rawBodyA
      branchB = Lean.Lambda
        [ Lean.Binder Lean.Explicit lkA2 Nothing
        , Lean.Binder Lean.Explicit lkB2 Nothing
        , Lean.Binder Lean.Explicit i2 Nothing
        ]
        rawBodyB
      productivityPropA =
        Lean.App (Lean.Var (Lean.Ident "PairStreamComponentProductive"))
          [elTypeALean, elTypeBLean, elTypeALean, branchA]
      productivityPropB =
        Lean.App (Lean.Var (Lean.Ident "PairStreamComponentProductive"))
          [elTypeALean, elTypeBLean, elTypeBLean, branchB]
  checked <- withLocalProofObligation
    (Lean.Ident "h_productivityA_")
    productivityPropA
    $ \proofA ->
      withLocalProofObligation
        (Lean.Ident "h_productivityB_")
        productivityPropB
        $ \proofB ->
          pure (Lean.App (Lean.Var (Lean.Ident "mkStreamFixPairChecked"))
            [ elTypeALean, elTypeBLean, errA, errB, branchA, branchB
            , proofA
            , proofB
            ])
  let base = Lean.App pureVar [checked]
  pure (wrapHoistedExcepts (hoistsA ++ hoistsB) base)

-- | Lower a polymorphic stream-iteration @Prelude.fix@ application
-- (Cryptol's `iterate` shape, recognized by 'classifyPolyStreamIterate')
-- to a direct call to the hand-written `cryptolIterate` def in
-- @CryptolToLean.SAWCorePreludeExtra@. Sidesteps the polymorphism
-- entirely — the structural-recursion def in Lean handles the
-- single-stream productive corecursion at any concrete element type.
lowerPolyStreamIterate :: TermTranslationMonad m =>
                          Term -> Term -> Term -> m TranslatedTerm
lowerPolyStreamIterate alphaArg fArg xArg = do
  alphaLean <- translateTerm alphaArg
  fLean     <- translateTerm fArg
  xLean     <- translateTerm xArg
  -- Emit fully-qualified reference: SAWCorePreludeExtra is not in the
  -- implicitly-opened module list (those are SAWCorePrimitives +
  -- Vectors), so a bare `cryptolIterate` would not resolve.
  --
  -- Under Phase β the body and seed translate as wrapped. A raw
  -- `Stream α` cannot preserve per-index `Except.error`, so this
  -- lowering proves the seed and one symbolic step raw before
  -- emitting `cryptolIterate`. Captured index-independent effects
  -- are hoisted outside stream construction, so the lowered term has
  -- the ordinary wrapped stream shape (`Except String (Stream α)`).
  -- Residual input-dependent effects reject.
  seedRaw <- case rawifyExceptToRaw Set.empty xLean of
    Just r -> pure r
    Nothing ->
      Except.throwError (RejectedPrimitive "fix"
        "Cryptol iterate seed has residual error effects. The Lean \
        \backend cannot default those errors inside a Stream.")
  stepName <- freshVariant (Lean.Ident "x_")
  let stepArg = Lean.Var stepName
      stepCall =
        Lean.App fLean
          [Lean.App (Lean.Var (Lean.Ident "Pure.pure")) [stepArg]]
  stepRaw <- case rawifyExceptToRaw (Set.singleton stepName) stepCall of
    Just r -> pure r
    Nothing ->
      Except.throwError (RejectedPrimitive "fix"
        "Cryptol iterate step has residual per-index error effects. \
        \The Lean backend cannot default those errors inside a Stream.")
  let rawStep =
        Lean.Lambda [Lean.Binder Lean.Explicit stepName Nothing]
                    (reRaw stepRaw)
      iter =
        Lean.App
          (Lean.Var (Lean.Ident "CryptolToLean.SAWCorePreludeExtra.cryptolIterate"))
          [alphaLean, rawStep, reRaw seedRaw]
  (hoists, iter') <- freshenHoists (reHoists seedRaw ++ reHoists stepRaw) iter
  pure (TranslatedTerm
          (wrapHoistedExcepts hoists
            (Lean.App (Lean.Var (Lean.Ident "Pure.pure")) [iter']))
          BindingWrapped)

-- | Lower a 'BoundedVecFold'-shaped @Prelude.fix@ to a Lean
-- 'genFixMChecked' call. Body shape:
-- @\\rec : Vec n α -> gen n α (\\i -> e[rec, i])@.
--
-- The lookup-form rewrite happens at Lean level by applying the
-- translated body to @gen n α lookup_@, then projecting the i-th
-- element via @atWithDefault n α err _ i@. The body's
-- @atWithDefault n α _ rec j@ accesses inside @e@ become
-- @atWithDefault n α _ (gen n α lookup_) j@; semantic equivalence
-- to @lookup_ j@ holds via the @atWithDefault_gen@ axiom in
-- @SAWCorePrelude_proofs.lean@. (The axiom doesn't auto-reduce in
-- the kernel — proofs over the lowered output need to invoke it
-- explicitly.)
lowerBoundedVecFold :: TermTranslationMonad m => Term -> Term -> Term -> m Lean.Term
lowerBoundedVecFold lenTerm elTypeTerm bodyTerm = do
  lenLean    <- translateTerm lenTerm
  elTypeLean <- translateTerm elTypeTerm
  bodyLean   <- translateTerm bodyTerm
  lookupName <- freshVariant (Lean.Ident "lookup_")
  indexName  <- freshVariant (Lean.Ident "i_")
  -- Under Phase β the translated 'bodyLean' is the wrapped version
  -- of the SAW body:
  --
  --   bodyLean : Except String (Vec n α) → Except String (Vec n α)
  --
  -- The recognizer's lookup-rewrite shape is
  -- @\\lookup_ i_ → atWithDefault n α err (body (gen n α lookup_)) i_@:
  -- we build a raw Vec from the lookup function, feed it to the body
  -- (after a 'Pure.pure' lift to match the wrapped formal), then
  -- extract the i_-th element from the wrapped result via
  -- 'atWithDefaultM' (which propagates errors from any of: the
  -- default, the body result, or out-of-bounds index).
  let pureVar = Lean.Var (Lean.Ident "Pure.pure")
      errorTermRaw =
        unreachableDefault elTypeLean "fix lookup out of bounds"
      errorTermWrapped = Lean.App pureVar [errorTermRaw]
      genCall =
        Lean.App (Lean.Var (Lean.Ident "gen"))
          [lenLean, elTypeLean, Lean.Var lookupName]
      bodyApplied = Lean.App bodyLean [Lean.App pureVar [genCall]]
      atCall =
        Lean.App (Lean.Var (Lean.Ident "atWithDefaultM"))
          [lenLean, elTypeLean, errorTermWrapped, bodyApplied, Lean.Var indexName]
      innerLambda =
        Lean.Lambda
          [ Lean.Binder Lean.Explicit lookupName Nothing
          , Lean.Binder Lean.Explicit indexName  Nothing
          ]
          atCall
      productivityProp =
        Lean.App (Lean.Var (Lean.Ident "GenFixBodyProductive"))
          [elTypeLean, innerLambda]
  withLocalProofObligation
    (Lean.Ident "h_productivity_")
    productivityProp
    $ \proof ->
        pure $ Lean.App (Lean.Var (Lean.Ident "genFixMChecked"))
                    [ lenLean, elTypeLean, errorTermWrapped, innerLambda
                    , proof
                    ]

-- | Translate a SAWCore constant reference.
--
-- Under the specialization architecture (see
-- @doc/2026-04-23_stage3-translator-sketch.md@) 'scNormalize' has
-- already unfolded every defined constant before the translator is
-- called, so any 'Constant' reaching this function is one of:
--
--   * a 'ModuleIdentifier' that dispatches through
--     'SpecialTreatment' (axioms, primitives, inductive types and
--     constructors, recursors that survive normalization).
--   * an 'ImportedName' for a Cryptol-user-introduced constant we
--     have no special treatment for. We emit a bare qualified
--     reference; the caller is expected to supply a realisation (or
--     the name resolves to something in the existing Cryptol
--     preamble). Pre-specialization this branch recursively
--     translated the constant's body; that is now dead code because
--     normalization would have unfolded the body in-place.
translateConstant :: TermTranslationMonad m => Name -> m Lean.Term
translateConstant nm
  | ModuleIdentifier ident <- nameInfo nm = translateIdentWithArgs ident []
  | otherwise = do
      config <- asks translationConfiguration
      let nm_str  = Text.unpack (toShortName (nameInfo nm))
      let renamed = escapeIdent $ Lean.Ident $
                      fromMaybe nm_str (lookup nm_str (constantRenaming config))
      pure (Lean.Var renamed)

-- | Combine a term-level 'Binder' with a type-level 'PiBinder', keeping
-- the binder's identifier and type but the pi's implicit/explicit
-- status. Mirrors @SAWCoreRocq.Term.combineBinders@.
combineBinders :: Lean.Binder -> Lean.PiBinder -> Lean.Binder
combineBinders (Lean.Binder _ n mty) (Lean.PiBinder impl _ _) =
  Lean.Binder impl n mty

-- | Produce a Lean @def@ from a 'Noncomputable' flag, a list of
-- universe-variable names, a name, a translated body, and a
-- translated type. The universe list is filtered to what the
-- emitted decl actually mentions — the type and body are translated
-- separately and may independently allocate universe variables that
-- get shadowed when Lambda binders hoist into the @def@ signature.
-- Declaring only the referenced ones matches what Lean expects.
--
-- If the body is a lambda and the type is a matching pi, the
-- binders are hoisted into the @def@ signature for readability.
--
-- If the body is a 'Lambda' with more binders than the type has
-- 'Pi' binders, or vice versa, the surplus stays in the body /
-- type as-is. Crucially, we strip the /type annotations/ from the
-- body's outer lambdas when the signature already supplies them —
-- otherwise Lean re-elaborates the annotated binder against the
-- signature's binder, and the body-side's universe variables go
-- unused (they're only referenced by the redundant annotation
-- Lean ignores).
mkDefinitionWith ::
  Lean.Noncomputable -> [String] ->
  Lean.Ident -> Lean.Term -> Lean.Term -> Lean.Decl
mkDefinitionWith nc univs name body tp =
  let raw = case (body, tp) of
        (Lean.Lambda bs t, Lean.Pi bs' tp')
          | length bs == length bs' ->
              -- Lengths match: hoist lambda binders into signature.
              Lean.Definition nc [] name (zipWith combineBinders bs bs')
                              (Just tp') t
          | length bs < length bs' ->
              -- Body has fewer lambdas than type has pi binders.
              -- Emit the body alone (the remaining pi binders stay
              -- in the signature's type).
              Lean.Definition nc [] name [] (Just tp)
                              (Lean.Lambda (map stripType bs) t)
        _ -> Lean.Definition nc [] name [] (Just tp) body
      used = usedUniversesInDecl raw
      keep = filter (`Set.member` used) univs
  in rebrandUnivs keep raw
  where
    rebrandUnivs us (Lean.Definition nc' _ nm bs mty bd) =
      Lean.Definition nc' us nm bs mty bd
    rebrandUnivs _ d = d

    -- | Drop the type annotation from a lambda binder. Lean will
    -- infer the type from the surrounding @def@'s pi signature.
    stripType :: Lean.Binder -> Lean.Binder
    stripType (Lean.Binder impl n _) = Lean.Binder impl n Nothing

-- | Collect every universe-variable name mentioned in a 'Lean.Decl'
-- by walking its AST. Used to filter the per-def universe list down
-- to the variables that are actually referenced after 'mkDefinition'
-- hoists binders (the type and the body may have introduced separate
-- shadowed variables).
usedUniversesInDecl :: Lean.Decl -> Set String
usedUniversesInDecl d = case d of
  Lean.Axiom _ _ ty -> usedUniversesInTerm ty
  Lean.Definition _ _ _ bs mty bd ->
    Set.unions
      [ Set.unions (map usedUniversesInBinder bs)
      , maybe Set.empty usedUniversesInTerm mty
      , usedUniversesInTerm bd
      ]
  Lean.InductiveDecl (Lean.Inductive _ _ ps ixs s ctors) ->
    Set.unions
      [ Set.unions (map usedUniversesInBinder ps)
      , Set.unions (map usedUniversesInPiBinder ixs)
      , usedUniversesInSort s
      , Set.unions [ usedUniversesInTerm t | Lean.Constructor _ t <- ctors ]
      ]
  Lean.Namespace _ ds -> Set.unions (map usedUniversesInDecl ds)

usedUniversesInBinder :: Lean.Binder -> Set String
usedUniversesInBinder (Lean.Binder _ _ mty) =
  maybe Set.empty usedUniversesInTerm mty

usedUniversesInPiBinder :: Lean.PiBinder -> Set String
usedUniversesInPiBinder (Lean.PiBinder _ _ ty) = usedUniversesInTerm ty

usedUniversesInSort :: Lean.Sort -> Set String
usedUniversesInSort = \case
  Lean.Prop            -> Set.empty
  Lean.TypeLvl _       -> Set.empty
  Lean.SortVar u       -> Set.singleton u

-- | Collect universe-variable names referenced inside a
-- 'Lean.UnivLevel' (the explicit per-arg level in @\@Foo.{u, v}@).
usedUniversesInLevel :: Lean.UnivLevel -> Set String
usedUniversesInLevel = \case
  Lean.LevelVar u  -> Set.singleton u
  Lean.LevelLit _  -> Set.empty
  Lean.LevelSucc l -> usedUniversesInLevel l
  Lean.LevelMax ls -> Set.unions (map usedUniversesInLevel ls)

usedUniversesInTerm :: Lean.Term -> Set String
usedUniversesInTerm = \case
  Lean.Lambda bs t ->
    Set.unions (usedUniversesInTerm t : map usedUniversesInBinder bs)
  Lean.Pi bs t ->
    Set.unions (usedUniversesInTerm t : map usedUniversesInPiBinder bs)
  Lean.Let _ bs mty t b ->
    Set.unions
      [ Set.unions (map usedUniversesInBinder bs)
      , maybe Set.empty usedUniversesInTerm mty
      , usedUniversesInTerm t
      , usedUniversesInTerm b
      ]
  Lean.App f args ->
    Set.unions (usedUniversesInTerm f : map usedUniversesInTerm args)
  Lean.Sort s -> usedUniversesInSort s
  Lean.Var _ -> Set.empty
  Lean.ExplVar _ -> Set.empty
  Lean.ExplVarUniv _ levels ->
    Set.unions (map usedUniversesInLevel levels)
  Lean.Ascription a b ->
    Set.union (usedUniversesInTerm a) (usedUniversesInTerm b)
  Lean.NatLit _ -> Set.empty
  Lean.IntLit _ -> Set.empty
  Lean.List ts -> Set.unions (map usedUniversesInTerm ts)
  Lean.StringLit _ -> Set.empty
  Lean.Tactic _ -> Set.empty

-- | Fail translation with a 'RejectedPrimitive' error. Previously
-- emitted an inline 'error_unrestricted' reference (Rocq mirror);
-- under Phase α the axiom was deleted, so emitting that name
-- produces a stale identifier Lean can't resolve. Failing loud at
-- translation time is the right behaviour — the caller (e.g. an
-- unmapped recursor) is a genuine gap that needs a real mapping
-- before the user term can be discharged in Lean.
errorTermM :: TermTranslationMonad m => String -> m Lean.Term
errorTermM msg =
  Except.throwError
    (RejectedPrimitive (Text.pack "<inline>") (Text.pack msg))

-- | Translate a recursor application by special-casing the
-- case-handler argument positions. SAWCore's recursor App has the
-- shape:
--
-- @
-- Foo#rec [param_1, …, param_p] motive
--         [case_1, …, case_k]
--         [index_1, …, index_i] scrutinee
-- @
--
-- where p = 'recursorNumParams', k = constructor count
-- (@length recursorCtorOrder@), i = 'recursorNumIxs'. Args after
-- params and motive are k case handlers; then i indices; then the
-- scrutinee.
--
-- Phase-β wraps Pi bodies when the body is a value-domain type
-- (so @Nat → Vec n Bool@ becomes @Nat → Except String (Vec n Bool)@).
-- That rule is correct for top-level def signatures and Cryptol
-- function types — but for a case handler's binder type, Lean's
-- recursor expects the raw shape (case for @Stream.MkStream@ takes
-- @(s : Nat → α)@ raw, not the wrapped variant). 'inRecursorCaseBinder'
-- is set during case-handler binder translation only; the case
-- body translates normally (with the flag cleared in the 'Lambda'
-- case), so internal Phase-β lifts still fire for value-domain
-- operations inside the body.
--
-- The case body's wrapped result matches the motive's wrapped
-- result (motive Lambda body wraps via gamma.8), so the
-- recursor's case-arg type still typechecks.
--
-- The motive is translated /without/ the flag — its body wrap
-- (gamma.8 rule) governs its own behaviour.
translateRecursorApp :: TermTranslationMonad m =>
                        CompiledRecursor -> [Term] -> m Lean.Term
translateRecursorApp crec args = ttLean <$> translateRecursorAppWithShape crec args

translateRecursorAppWithShape :: TermTranslationMonad m =>
                        CompiledRecursor -> [Term] -> m TranslatedTerm
translateRecursorAppWithShape crec args = do
  recHead <- translateFTermF (Recursor crec)
  let nParams  = recursorNumParams crec
      nCtors   = length (recursorCtorOrder crec)
      nIndices = recursorNumIxs crec
      caseFirst = nParams + 1
      caseLast  = nParams + nCtors
      scrutPos  = nParams + 1 + nCtors + nIndices
      isCasePos i = i >= caseFirst && i <= caseLast
      fullySupplied = length args >= scrutPos + 1
  if not fullySupplied
     then do
       argTrans <- traverse translateTerm args
       pure (TranslatedTerm (Lean.App recHead argTrans) BindingFunction)
     else do
       let (preScrut, rest)   = splitAt scrutPos args
           (scrut, postScrut) = case rest of
             (s : ss) -> (s, ss)
             []       -> error "translateRecursorApp: scrutinee \
                               \missing despite fullySupplied"
           (paramArgs, _) = splitAt nParams preScrut
       paramTrans <- traverse translateTerm paramArgs
       casePlans <- recursorCasePlans paramTrans crec
       preTrans <- sequence (zipWith
         (\i a -> if i < nParams
                     then pure (paramTrans !! i)
                     else if isCasePos i
                       then translateCaseHandler
                              (casePlans !! (i - caseFirst)) a
                       else translateTerm a)
         [0..] preScrut)
       scrutResult <- translateTermWithShape scrut
       let scrutTrans = ttLean scrutResult
       postTrans  <- traverse translateTerm postScrut
       -- Decide whether to 'Bind.bind' the scrutinee. The
       -- recursor's scrutinee SAW type is usually value-domain
       -- (Num, Stream α, RecordType, …), but the recursor result
       -- may be a type expression or a proof. Those results must
       -- stay raw: wrapping an equality proof through 'Bind.bind'
       -- gives an @Except String Prop@-shaped term where Lean
       -- expects a proof, which is both ill-typed and unsound for
       -- coercions.
       --
       -- A motive returning a 'Sort' (like @fun num => Type@)
       -- produces a type expression. A motive whose body itself
       -- has sort 'Prop' (like @fun y h => Eq Type ...@) produces
       -- a proof. Only value-producing motives use the Phase-β
       -- scrutinee bind.
       let motiveArg = preScrut !! nParams
           (_, motiveBody) = asLambdaList motiveArg
           motiveReturnsType = isJust (asSort motiveBody)
           motiveReturnsProof = case termSortOrType motiveBody of
             Left s  -> s == propSort
             Right _ -> False
           motiveReturnsRaw = motiveReturnsType || motiveReturnsProof
       -- Decide whether the scrutinee arrives Except-wrapped:
       --   * 'Lean.Var' tracked as 'BindingWrapped' — wrapped.
       --   * 'Lean.App' headed by a known wrap-producing
       --     identifier ('Bind.bind', 'Pure.pure', a '*.rec'
       --     call whose translated motive returns 'Except', or one
       --     of the wrapped support-library helpers like 'genM') —
       --     wrapped. This catches the rec-result-as-scrutinee
       --     case (chained 'RecordType.rec' projections) and
       --     bind-chain scrutinees, which the previous Var-only
       --     check missed.
       --   * Otherwise — pass directly (raw type-arg binder,
       --     constructor literal, etc.).
       let scrutWrapped = isWrappedShape (ttShape scrutResult)
           resultShape
             | motiveReturnsRaw = BindingRaw
             | otherwise        = BindingWrapped
       if motiveReturnsRaw || not scrutWrapped
          then pure (TranslatedTerm
                       (Lean.App recHead
                         (preTrans ++ [scrutTrans] ++ postTrans))
                       resultShape)
          else do
            scrutName <- freshVariant (Lean.Ident "scrut_")
            let recCall =
                  Lean.App recHead
                    (preTrans ++ [Lean.Var scrutName] ++ postTrans)
                lam = Lean.Lambda
                        [Lean.Binder Lean.Explicit scrutName Nothing]
                        recCall
            pure (TranslatedTerm
                    (Lean.App (Lean.Var (Lean.Ident "Bind.bind"))
                      [scrutTrans, lam])
                    BindingWrapped)
  where
    -- Constructor case handlers are lambdas whose first binders are
    -- determined by the constructor fields. These fields do not all have
    -- the same Phase-beta shape: structural fields are raw recursor
    -- inputs, while fields typed by a datatype parameter use the actual
    -- translated parameter type supplied to this recursor call.
    recursorCasePlans ::
      TermTranslationMonad m =>
      [Lean.Term] -> CompiledRecursor -> m [CaseHandlerPlan]
    recursorCasePlans paramTrans rec =
      traverse (casePlan paramTrans) (recursorCtorOrder rec)

    casePlan ::
      TermTranslationMonad m =>
      [Lean.Term] -> Name -> m CaseHandlerPlan
    casePlan paramTrans ctorNm = do
      mm <- view sawModuleMap <$> askTR
      pure $ case lookupVarIndexInMap (nameIndex ctorNm) mm of
        Just (ResolvedCtor ctor) ->
          CaseHandlerPlan (ctorCaseRoles paramTrans ctor)
        _ ->
          -- If the constructor is not in the module map, preserve the old
          -- conservative behavior: treat every handler binder as raw.
          CaseHandlerAllRaw

    ctorCaseRoles :: [Lean.Term] -> Ctor -> [CaseBinderRole]
    ctorCaseRoles paramTrans ctor =
      map roleForArg (ctorArgs argStruct)
      where
        argStruct = ctorArgStruct ctor
        ctorParamNames = map fst (ctorParams argStruct)

        roleForArg (_, ConstArg tp) =
          case datatypeParamIndex tp of
            Just ix | ix < length paramTrans ->
              CaseFieldParam (paramTrans !! ix)
            _ -> CaseFieldRaw
        -- Recursive constructor fields also generate induction-hypothesis
        -- binders in the recursor case type, but those are not constructor
        -- fields. Leave them to the ordinary post-field binder path.
        roleForArg (_, RecursiveArg _ _) = CaseFieldRaw

        datatypeParamIndex tp = case unwrapTermF tp of
          Variable vn _ ->
            findIndex (== vn) ctorParamNames
          _ -> Nothing

-- | Translate a recursor case-handler argument. The handler is
-- typically a 'Lambda' chain whose initial binders bind the
-- constructor's arguments — these must arrive at the recursor's raw
-- expected type (NOT Phase-β wrapped), so we set
-- 'inRecursorCaseBinder' for that prefix of the binder traversal.
-- Later binders can come from a function-valued motive; those are
-- ordinary value arguments to the function returned by the recursor
-- and must keep normal Phase-β wrapping.
--
-- The case /body/, however, runs at full Phase β: its operations
-- expect *wrapped* values. We bridge the raw constructor-field
-- prefix by emitting a 'let' chain at body entry that re-wraps each
-- value-domain field via 'Pure.pure'. The shadow binding lets the
-- body reference the binder name and get the wrapped form
-- transparently.
--
-- Higher-order binders (e.g. @s : Nat → α@ in Stream.rec's case)
-- get an eta-expanded shadow: @let s := fun i => Pure.pure (s i)@,
-- so each application of @s@ produces a wrapped result.
--
-- Non-Lambda case handlers (e.g. @Stream (Vec 8 Bool)@ as a
-- TCInf case for a type-computing motive) translate as
-- ordinary terms — there are no binders to shadow.
translateCaseHandler ::
  TermTranslationMonad m => CaseHandlerPlan -> Term -> m Lean.Term
translateCaseHandler casePlan caseTerm = case asLambdaList caseTerm of
  ([], _) ->
    -- No binders to wrap. Translate directly.
    translateTerm caseTerm
  (params, body) -> do
    -- Translate constructor-field binders according to their roles.
    -- Constructor fields are raw recursor inputs and get body-entry
    -- shadows. Parameter fields use the already-translated actual
    -- datatype parameter type for their binder, but still need the
    -- same shadowing bridge so the Phase-beta case body sees the
    -- wrapped value. Any remaining binders are arguments from a
    -- function-valued motive, so they use ordinary Phase-beta binder
    -- rules.
    surroundingFlag <- view inRecursorCaseBinder <$> askTR
    let roles = case casePlan of
          CaseHandlerPlan rs -> take (length params) rs
          CaseHandlerAllRaw  -> replicate (length params) CaseFieldRaw
    translateCaseFields surroundingFlag roles params $
      \fieldBinders rawFieldBinders normalParams ->
        -- Clear the flag before body translation: Phase beta's body
        -- lift rules should fire normally inside the case body.
        localTR (set inRecursorCaseBinder surroundingFlag) $
          translateBinders normalParams $ \normalParamTerms -> do
            body' <- translateTermLet body
            -- Shadow only raw constructor fields that the body uses.
            -- Function-shaped parameter fields and motive-result
            -- binders already have their expected Phase-beta type.
            shadowed <- shadowBinders rawFieldBinders body'
            pure (Lean.Lambda (fieldBinders ++ normalParamTerms)
                              shadowed)
  where
    translateCaseFields ::
      TermTranslationMonad m =>
      Bool ->
      [CaseBinderRole] ->
      [(VarName, Term)] ->
      ([Lean.Binder] -> [(Lean.Binder, (VarName, Term))] ->
        [(VarName, Term)] -> m a) ->
      m a
    translateCaseFields _ [] rest k = k [] [] rest
    translateCaseFields _ _ [] k = k [] [] []
    translateCaseFields surroundingFlag (role : roles) (param@(vn, ty) : rest) k =
      case role of
        CaseFieldRaw ->
          localTR (set inRecursorCaseBinder True) $
            translateBinder' vn ty $ \bnd ->
              localTR (set inRecursorCaseBinder surroundingFlag) $
                translateCaseFields surroundingFlag roles rest $
                  \binders rawFields normalParams ->
                    let thisBinders = bindTransToBinder bnd
                        thisRawFields =
                          [ (binder, param) | binder <- thisBinders ]
                    in k (thisBinders ++ binders)
                         (thisRawFields ++ rawFields)
                         normalParams
        CaseFieldParam paramTy ->
          translateBinderWithLeanType vn paramTy $ \binder ->
            translateCaseFields surroundingFlag roles rest $
              \binders rawFields normalParams ->
                let rawFields' = case paramTy of
                      Lean.Pi{} -> rawFields
                      _         -> (binder, param) : rawFields
                in
                k (binder : binders)
                  rawFields'
                  normalParams

    shadowBinders ::
      TermTranslationMonad m =>
      [(Lean.Binder, (VarName, Term))] -> Lean.Term -> m Lean.Term
    shadowBinders [] body' = pure body'
    shadowBinders (p : ps) body' = do
      inner <- shadowBinders ps body'
      shadowBinder p inner

    -- Build one 'let' shadowing one binder. Strategy depends on
    -- the binder's SAW type:
    --   * value-domain (Vec/Bool/...): @let v : Except String τ
    --     := Pure.pure v in …@ — the type annotation pins
    --     'Pure.pure''s typeclass resolution (Lean otherwise gets
    --     stuck when the recursor motive is a let-bound opaque
    --     reference, since the case body's expected type isn't
    --     visible to typeclass inference at the 'Pure.pure'
    --     position).
    --   * Pi to value-domain: eta-expand and lift result.
    --   * Nat/Sort/Eq/Prop: skip — body uses the binder raw.
    shadowBinder ::
      TermTranslationMonad m =>
      (Lean.Binder, (VarName, Term)) -> Lean.Term -> m Lean.Term
    shadowBinder (binder@(Lean.Binder _ _ binderTy), (_, saw_ty)) body'
      | not (termMentionsAny (Set.singleton (binderName binder)) body') =
          pure body'
      | otherwise
      = do
          mShadowRhs <- shadowExpr binder saw_ty
          case mShadowRhs of
            Just shadowRhs ->
              let mLetTy = case binderTy of
                    Just bt | shouldWrapBinder saw_ty -> Just (wrapExcept bt)
                    _ -> Nothing
              in pure (Lean.Let (binderName binder) [] mLetTy shadowRhs body')
            Nothing -> pure body'

    binderName :: Lean.Binder -> Lean.Ident
    binderName (Lean.Binder _ name _) = name

    -- Compute the shadow RHS given the binder's Lean ident and
    -- SAW type. Returns Nothing if no shadow is needed.
    shadowExpr ::
      TermTranslationMonad m =>
      Lean.Binder -> Term -> m (Maybe Lean.Term)
    shadowExpr (Lean.Binder _ name _) saw_ty
      -- Value-typed binders (Vec, Bool, …): under 'inRecursorCaseBinder'
      -- the binder type stays raw (the recursor expects raw
      -- constructor-arg types), so emit a 'Pure.pure'-lifted shadow
      -- @let v := Pure.pure v@. The case body, translated under
      -- Phase β, then sees @v : Except String τ@ transparently.
      | shouldWrapBinder saw_ty =
          pure (Just (Lean.App pureVar [Lean.Var name]))
      -- Pi-shaped binders: gamma.11 keeps the Pi body raw, so the
      -- binder is raw. Body operations under Phase β expect the
      -- corresponding wrapped function type. Eta-expand through the
      -- ordinary application binder plan, so e.g. @a -> a -> Bool@
      -- becomes @Except a -> Except a -> Except Bool@ while
      -- @Nat -> α@ keeps the Nat argument raw and wraps only the
      -- result.
      | Just _ <- asPi saw_ty =
          let (binders, retTy) = asPiList saw_ty
              pureWrap = shouldWrapBinder retTy
                      || isVariableHead retTy
                      || natValueResult saw_ty
          in if null binders || not pureWrap
                then pure Nothing
                else do
                  etaNames <- mapM
                    (freshVariant . Lean.Ident . ("η_arg_" ++) . show)
                    [0 .. length binders - 1]
                  let etaTerms = map Lean.Var etaNames
                      etaBinders =
                        [ Lean.Binder Lean.Explicit etaName Nothing
                        | etaName <- etaNames
                        ]
                      shouldBind =
                        argumentBindPlanFromWrapped saw_ty etaTerms
                          (replicate (length etaTerms) False)
                  body <- buildLifted (Lean.Var name) pureWrap
                            (take (length etaTerms)
                                  (shouldBind ++ repeat False))
                            etaTerms
                  pure (Just (Lean.Lambda etaBinders body))
      | otherwise = pure Nothing

    pureVar = Lean.Var (Lean.Ident "Pure.pure")

-- | Translate a 'FlatTermF' (atomic constructs of the SAWCore AST).
translateFTermF :: TermTranslationMonad m => FlatTermF Term -> m Lean.Term
translateFTermF ftf = case ftf of
  -- A 'Sort' in an FTermF — most commonly the codomain of a
  -- Pi-in-type-position, e.g. the @sort 1@ at the end of the
  -- motive @(y : t) → Eq t x y → sort 1@ in Eq__rec. Treat the
  -- same as a binder-position sort: at sort 0 emit concrete
  -- @Type@, at sort k≥1 allocate a fresh universe variable so
  -- the surrounding def becomes universe-polymorphic in this
  -- position. The Phase 0 Eq__rec probe is the load-bearing
  -- case: its motive return is @sort 1@, and the probe-validated
  -- shape needs a fresh @Sort u_2@ here, not concrete @Type 1@.
  --
  -- A 'sort k≥1' literal passed as an explicit value argument
  -- (e.g. @Eq (sort 0) a b@ where Eq's first arg is the carrier)
  -- also takes this path. The fresh universe lets Lean unify it
  -- with the caller's universe demands.
  Sort s _h -> Lean.Sort <$> translateSort BinderPos s

  -- @Foo#rec@ — SAWCore's eliminator. In Rocq this becomes @Foo_rect@;
  -- Lean's convention for an inductive @Foo@'s auto-generated
  -- eliminator is @Foo.rec@.
  --
  -- Always emit as @\@Foo.rec@ (explicit form). SAWCore's recursor
  -- arg list is @motive branch_1 … branch_n indices@, all positional
  -- and explicit; Lean's @Foo.rec@ marks the motive (and indices)
  -- implicit, so without @\@@ the positional SAW arg list would
  -- miss the motive slot. The instance-insertion concern that
  -- previously argued against @\@@ is gone now that we no longer
  -- auto-inject @[Inh_a : Inhabited a]@ binders on @isort@
  -- parameters.
  Recursor crec -> do
    let d     = recursorDataType crec
        dInfo = nameInfo d
    -- Guard the SAW-Nat / SAW-Pos mapping. We collapse those types
    -- to Lean's native 'Nat' at the 'SpecialTreatment' level and
    -- rely on 'leanOpaqueBuiltins' to keep every Prelude def whose
    -- RHS uses 'Nat#rec' / 'Pos#rec' opaque during normalization.
    -- If one still surfaces, the generated Lean would alias SAW's
    -- case order onto Lean's @Nat.rec@ (@zero, succ@) — a silent
    -- soundness divergence. Refuse with a clear error. See
    -- 'doc/2026-04-24_audit-nat-mapping.md'.
    --
    -- L-discipline-3 (post-2026-05-02 audit): @Bool#rec@ has the
    -- same character — SAW declares @data Bool { True; False; }@
    -- (True-first), Lean's @Bool.rec@ is False-first. L-16 closed
    -- the path where @scNormalize@ unfolded @iteDep@/@ite@ and
    -- exposed bare @Bool#rec@; this guard closes the residual path
    -- where a hand-written term (typically via @parse_core@) emits
    -- @Bool#rec@ directly. Both paths refuse with @RejectedPrimitive@
    -- since the right user action is always "use ite/iteDep
    -- instead", not "specialize harder".
    let preludeNat  = mkIdent preludeName "Nat"
        preludePos  = mkIdent preludeName "Pos"
        preludeBool = mkIdent preludeName "Bool"
        preludeZ    = mkIdent preludeName "Z"
        preludeAccessibleNat = mkIdent preludeName "AccessibleNat"
        preludeAccessiblePos = mkIdent preludeName "AccessiblePos"
    case dInfo of
      ModuleIdentifier i
        | i == preludeNat -> Except.throwError (UnsoundRecursor "Nat")
        | i == preludePos -> Except.throwError (UnsoundRecursor "Pos")
        | i == preludeZ   -> Except.throwError (UnsoundRecursor "Z")
        | i == preludeAccessibleNat ->
            Except.throwError (UnsoundRecursor "AccessibleNat")
        | i == preludeAccessiblePos ->
            Except.throwError (UnsoundRecursor "AccessiblePos")
        | i == preludeBool ->
            Except.throwError $ RejectedPrimitive "Bool#rec"
              "SAW's `data Bool { True; False; }` puts True before \
              \False, so Bool#rec's case order is \
              \(motive, trueCase, falseCase, scrutinee). Lean's \
              \auto-generated Bool.rec is False-first — emitting \
              \@Bool.rec with SAW's argument order would silently \
              \swap every if/then/else branch. Use the ite / iteDep \
              \wrappers in CryptolToLean.SAWCorePreludeExtra (which \
              \permute correctly) rather than Bool#rec directly. \
              \L-discipline-3 closes the parse_core / hand-written \
              \emission path; L-16 closes the scNormalize-unfolding \
              \path."
      _ -> pure ()
    maybeDIdent <- case dInfo of
      ModuleIdentifier ident -> translateIdentToIdent ident
      ImportedName{}         -> pure Nothing
    case maybeDIdent of
      Just (Lean.Ident i) ->
        pure $ Lean.ExplVar (Lean.Ident (i ++ ".rec"))
      Nothing -> do
        let dName = Text.unpack (toAbsoluteName dInfo)
        errorTermM ("Recursor for " ++ dName ++
                    " cannot be translated: its datatype has no " ++
                    "fixed target on the Lean side.")

  -- Array literals. Under Phase β, SAW value-domain elements
  -- translate at type @Except String α@, so the elements emitted
  -- here are individually wrapped (e.g. each @bvNat 8 N@ produces
  -- a @Bind.bind … (Pure.pure …)@ chain). The literal itself is
  -- @Vec n (Except String α)@; wrap with 'vecSequenceM' to lift
  -- to @Except String (Vec n α)@. Raw elements (NatLit /
  -- StringLit / nullary ctors) get the same 'Pure.pure' lift via
  -- 'liftRawValue' so the elements are uniformly wrapped before
  -- sequencing.
  --
  -- Empty arrays don't need sequencing — there's nothing to lift —
  -- so emit the bare literal; 'liftRawValue' on a 'Lean.List []'
  -- handles the surrounding wrap at the caller.
  --
  -- No bitvector specialization yet — the Rocq backend's
  -- 'intToBv' collapse needs the full Data.BitVector.Sized /
  -- Data.Parameterized machinery, which we leave to a later pass.
  ArrayValue elTyTerm vec -> do
    elems <- traverse translateTerm (toList vec)
    if null elems
       then pure (Lean.List [])
       else do
         elTyLean <- translateTerm elTyTerm
         let liftedElems = map liftRawValue elems
             n          = length elems
             vecLit     = Lean.List liftedElems
         pure $ Lean.App (Lean.Var (Lean.Ident "vecSequenceM"))
                  [Lean.NatLit (toInteger n), elTyLean, vecLit]

  StringLit s -> pure (Lean.StringLit (Text.unpack s))

-- | Translate a SAWCore 'Term' to Lean, consulting the let-sharing map
-- ('sharedNames') first. If the term's hash-consed index is in the
-- map, emit a 'Lean.Var' reference to the previously-allocated name;
-- otherwise translate the term in full via 'translateTermUnshared'.
--
-- This is the recursion point: every recursive descent eventually goes
-- through here so that shared subterms encountered deep inside larger
-- terms get folded into 'Lean.Var' references rather than re-translated.
-- 'translateTermLet' wraps the top-level body with the corresponding
-- @let@ bindings so the variables resolve.
--
-- Audit P-1 (2026-05-06): the prior unshared walk re-translated each
-- shared subterm 2^N times for N nested aliases, exhausting memory on
-- Salsa20. Ported from @SAWCoreRocq.Term.translateTerm@.
translateTerm :: TermTranslationMonad m => Term -> m Lean.Term
translateTerm t = ttLean <$> translateTermWithShape t

translateTermWithShape :: TermTranslationMonad m => Term -> m TranslatedTerm
translateTermWithShape t =
  case t of
    STApp { stAppIndex = i } -> do
      shared <- view sharedNames <$> askTR
      case IntMap.lookup i shared of
        Just sh -> do
          let tm = Lean.Var (sharedNameIdent sh)
          shape <- bindingShapeOfLeanTermM tm
          pure (TranslatedTerm tm shape)
        Nothing -> translateTermUnsharedWithShape t

-- | Translate a 'Term' WITHOUT consulting the 'sharedNames' map at the
-- top level. Used by 'translateTermLet' to emit the right-hand side of
-- a @let@ binding for a shared term: the term itself is what we're
-- about to bind, so we don't want to substitute it for its own
-- variable. Recursive descent inside still goes through 'translateTerm',
-- so smaller shared subterms ARE folded.
translateTermUnshared :: TermTranslationMonad m => Term -> m Lean.Term
translateTermUnshared t =
  case unwrapTermF t of

    FTermF ftf -> translateFTermF ftf

    -- For Pi/Lambda bodies, use 'translateTermLet' rather than
    -- 'translateTerm' so shared subterms inside the binder body get
    -- detected and let-bound. 'scTermCount' (the occurrence-counting
    -- pass underlying 'translateTermLet') is called with
    -- @doBinders=False@ and so does NOT descend through Pi/Lambda
    -- when invoked at the def-level top — without this site applying
    -- 'translateTermLet' anew once the binder is in scope, every
    -- shared subterm inside a Cryptol forall-quantified prop / lambda
    -- body would be re-translated per occurrence, producing
    -- exponential blowup on chained tuple projections (cdround-shape
    -- emissions, ChaCha20). Mirrors `translatePi` / `translateLambda`
    -- in saw-core-rocq's `Term.hs`. Regression pinned by
    -- drivers/cryptol_chained_projection_share/.
    Pi {} -> do
      let (params, body) = asPiList t
      -- Pi vs Lambda predicate asymmetry — intentional:
      --
      -- A 'Pi' is a function /type/. Its 'body' is the function's
      -- *return type*, which is always a type expression. The
      -- question is whether that return type lives at value level
      -- (Vec n α, Bool — wrap) or sort level (Type, Sort u, Pi-to-
      -- Sort — leave raw, this Pi is a type-of-types). The
      -- syntactic 'shouldWrapBinder' predicate answers that
      -- directly.
      --
      -- A 'Lambda' is a function /value/. Its body is the result
      -- value, which can be either a value (value-level lambda)
      -- or a type expression (motive). The 'isTypeProducing'
      -- predicate (the Lambda case below) consults the body's
      -- *sort* via 'sawModuleMap' lookup; 'shouldWrapBinder' is
      -- the wrong predicate there because @Vec n α@ as a Lambda
      -- body means "this lambda returns a type" (motive), not
      -- "this lambda returns a value of type Vec n α".
      --
      -- The two predicates can therefore disagree on the same
      -- syntactic body — that's the point. Pi's body and Lambda's
      -- body mean different things.
      --
      -- Within a value-level Pi, individual binders that act as
      -- *type indices* (their variable appears free in subsequent
      -- binder types or the return type, like @n@ in @bvAdd : (n :
      -- Nat) → Vec n Bool → Vec n Bool → Vec n Bool@) must stay
      -- raw; wrapping them would feed @Except String Nat@ into a
      -- position expecting @Nat@. 'typeArgPositions' computes
      -- those positions; 'translateBindersSelective' applies
      -- 'skipBinderWrap' transiently at each.
      let valueBody = shouldWrapBinder body
          -- A Pi with a Prop or Eq body is a /quantifier/
          -- ('∀ x, P x') — its binders are universally-quantified
          -- value inputs that should wrap (so the body's
          -- Phase-β-lifted operations can bind them). Distinct
          -- from a Pi with a Sort-or-Pi body, which describes a
          -- type-of-types (motive shape) and whose binders are
          -- type indices that must stay raw.
          propBody = isJust (asEq body)
                  || case asSort body of
                       Just s -> s == propSort
                       Nothing -> False
      surroundingSkipWrap <- view skipBinderWrap <$> askTR
      let withBinders k
            | valueBody =
                translateBindersSelective (typeArgPositions t) params
                  (k . concatMap bindTransToPiBinder)
            | propBody =
                -- Quantifier Pi (∀ x, P x): binders translate
                -- RAW. The body's Phase-β bind chains over the
                -- binders are bridged by a 'let'-shadow chain at
                -- the body entry that 'Pure.pure'-lifts each
                -- value-typed binder. This makes the quantifier
                -- match SAW's semantics — over raw value-domain
                -- inputs — rather than over Except-wrapped
                -- inputs (which would include error inputs the
                -- SAW VC never intended).
                localTR (set skipBinderWrap True)
                  (translatePiBinders params (\pbs ->
                     -- Reset 'skipBinderWrap' before translating
                     -- the body: the True flag was scoped to the
                     -- raw-binder emission for the quantifier,
                     -- but the body (and any inner lambdas
                     -- nested inside it) should re-evaluate wrap
                     -- decisions against their own contexts.
                     -- Without this reset, nested lambdas like
                     -- the @foldr@ folding function inherit
                     -- skipWrap=True and emit raw binders that
                     -- don't match the wrapped-formal positions
                     -- the surrounding context expects.
                     --
                     -- Also: the 'quantifierShadow' let-chain
                     -- emitted at body entry rebinds each value-
                     -- typed quantifier variable to 'Pure.pure v',
                     -- so references to those variables inside
                     -- the body resolve to wrapped values at
                     -- elaboration time. Reflect this in
                     -- 'bindingShapes' during body translation so
                     -- recursor-scrutinee detection treats the
                     -- references as wrapped (otherwise an outer
                     -- 'RecordType.rec p2'-style call wouldn't
                     -- bind, but the let-shadowed p2 IS wrapped).
                     let shadowedNames =
                           [ name
                           | ((_, ty), Lean.PiBinder _ (Just name) _)
                               <- zip params pbs
                           , shouldWrapBinder ty
                           ]
                     in localTR
                          ( set skipBinderWrap surroundingSkipWrap
                          . over bindingShapes
                              (\m -> foldr
                                (`Map.insert` BindingWrapped) m
                                shadowedNames))
                          (k pbs)))
            | otherwise =
                -- Type-family / motive Pi: skip binder wrap, and
                -- keep the flag set across body translation —
                -- type-family bodies are themselves type
                -- expressions whose nested binders are also
                -- type-level.
                localTR (set skipBinderWrap True)
                  (translatePiBinders params k)
      withBinders $ \paramTerms -> do
        body' <- translateTermLet body
        inRecCase <- view inRecursorCaseBinder <$> askTR
        -- Suppress body-wrap when this Pi is the type of a
        -- recursor case handler's binder — Lean's recursor
        -- expects the raw 'Nat → α' shape, not the Phase-β
        -- wrapped 'Nat → Except String α'.
        let bodyWrapped =
              if valueBody && not inRecCase
                 then wrapExcept body' else body'
        -- For a quantifier Pi, shadow each value-typed binder
        -- with its 'Pure.pure'-lifted counterpart so the body's
        -- Phase-β bind chains over the binder typecheck.
        let bodyFinal =
              if propBody
                 then quantifierShadow params paramTerms bodyWrapped
                 else bodyWrapped
        pure (Lean.Pi paramTerms bodyFinal)

    Lambda {} -> do
      let (params, body) = asLambdaList t
      -- Motive lambdas like @fun (n : Num) => Type@ produce a Lean
      -- type expression, not a value. Their binders are type
      -- indices and must NOT be wrapped — wrapping breaks recursor
      -- elimination (the motive ends up expecting a wrapped
      -- scrutinee but the recursor supplies the raw datatype).
      --
      -- 'skipBinderWrap' is scoped to the binder traversal only,
      -- NOT to the body translation. If the body is itself a Pi
      -- describing a value-level function type (e.g. the motive
      -- @fun n => seq n α → seq n α@ inside Cryptol's polymorphic
      -- return types), that inner Pi should still wrap its
      -- binders according to its own rules — the inner Pi's
      -- binders represent value-level function args, not motive
      -- scrutinees. Resetting 'skipBinderWrap' before descending
      -- prevents the override from leaking into nested
      -- abstractions.
      surroundingCtx <- view skipBinderWrap <$> askTR
      typeBody <- isTypeProducing body
      if typeBody
         then localTR (set skipBinderWrap True) $
                translateBinders params $ \paramTerms ->
                  localTR (set skipBinderWrap surroundingCtx) $ do
                    body' <- translateTermLet body
                    -- If the motive body is a value-domain type
                    -- expression (Vec n α, Bool, …), wrap it so
                    -- recursor case handlers' wrapped bodies
                    -- match. For higher-sort bodies (Type, Pi-to-
                    -- Type), don't wrap — they're not value-
                    -- domain. 'shouldWrapBinder' is the same
                    -- predicate the Pi case uses for its body.
                    let body'' = if shouldWrapBinder body
                                    then wrapExcept body'
                                    else body'
                    pure (Lean.Lambda paramTerms body'')
         else do
           -- Value-level lambda. Skip wrapping at binder positions
           -- whose variable feeds a later binder's type — those are
           -- type indices threaded through the binder chain (e.g.
           -- @a@ in @\\(a : Num) (plaintext : seq a Bool) → …@) and
           -- wrapping them would feed @Except String Num@ into the
           -- @seq a@ position.
           let typeIxs = typeArgPositionsBinders params
           translateBindersSelective typeIxs params
             (\bts ->
                -- Clear 'inRecursorCaseBinder' before translating
                -- the body: the flag is scoped to binder-type
                -- translation only. Internal Pis in the body
                -- (e.g. a let-bound function type) should wrap
                -- normally.
                localTR (set skipBinderWrap surroundingCtx
                       . set inRecursorCaseBinder False) $ do
                  body' <- translateTermLet body
                  pure (Lean.Lambda (concatMap bindTransToBinder bts) body'))

    App {} -> do
      let (f, args) = asApplyAll t
      case asGlobalDef f of
        Just ident -> translateIdentWithArgs ident args
        Nothing    -> case asRecursor f of
          Just crec -> translateRecursorApp crec args
          Nothing   -> do
            f' <- translateTerm f
            argResults <- traverse translateTermWithShape args
            let args' = map ttLean argResults
            case unwrapTermF f of
              Variable _ fty -> do
                let shouldBind = argumentBindPlan fty argResults
                buildLifted f' False (take (length args') (shouldBind ++ repeat False)) args'
              _ -> pure (Lean.App f' args')

    Constant nm -> translateConstant nm

    Variable nm _tp -> do
      nenv <- view namedEnvironment <$> askTR
      case Map.lookup nm nenv of
        Just ident -> pure (Lean.Var ident)
        Nothing    -> Except.throwError (LocalVarOutOfBounds t)

translateTermUnsharedWithShape ::
  TermTranslationMonad m => Term -> m TranslatedTerm
translateTermUnsharedWithShape t =
  case unwrapTermF t of
    App {} -> do
      let (f, args) = asApplyAll t
      case asGlobalDef f of
        Just ident -> translateIdentWithArgsWithShape ident args
        Nothing    -> case asRecursor f of
          Just crec -> translateRecursorAppWithShape crec args
          Nothing   -> do
            f' <- translateTerm f
            argResults <- traverse translateTermWithShape args
            let args' = map ttLean argResults
            case unwrapTermF f of
              Variable _ fty -> do
                let shouldBind = argumentBindPlan fty argResults
                    resultShape = phaseBetaResultShape fty (length args)
                buildLiftedWithShape resultShape f' False
                  (take (length args') (shouldBind ++ repeat False))
                  args'
              _ -> do
                let tm = Lean.App f' args'
                shape <- bindingShapeOfLeanTermM tm
                pure (TranslatedTerm tm shape)
    _ -> do
      tm <- translateTermUnshared t
      shape <- bindingShapeOfLeanTermM tm
      pure (TranslatedTerm tm shape)

-- | Allocate a fresh Lean identifier for a shared subterm at
-- 'TermIndex' @idx@ and bind it in 'sharedNames' for the duration of
-- the inner computation. Mirrors @SAWCoreRocq.Term.withSharedTerm@.
withSharedTerm :: TermTranslationMonad m =>
                  TermIndex -> (Lean.Ident -> m a) -> m a
withSharedTerm idx f = do
  ident <- (view nextSharedName <$> askTR) >>= freshVariant
  let sh = SharedName ident
  localTR (set nextSharedName (nextVariant ident)
           . over sharedNames (IntMap.insert idx sh)) $
    withUsedLeanIdent ident $ f ident

-- | Bind every @(idx, _)@ in 'sharedNames' simultaneously. The order
-- in which entries are introduced matters: 'IntMap.assocs' returns
-- subterms before superterms (smaller @stAppIndex@ first), so a
-- superterm's right-hand side translation can reference subterms by
-- their already-allocated names.
withSharedTerms :: TermTranslationMonad m =>
                   [(TermIndex, Term)] -> ([Lean.Ident] -> m a) -> m a
withSharedTerms []           f = f []
withSharedTerms ((i, _) : ts) f =
  withSharedTerm i $ \n ->
    withSharedTerms ts $ \ns -> f (n : ns)

-- | Build a Lean @let@ wrapping. @mkLet (name, rhs) body@ produces
-- @let name := rhs; body@ at the value level.
mkLet :: (Lean.Ident, Lean.Term) -> Lean.Term -> Lean.Term
mkLet (name, rhs) body = Lean.Let name [] Nothing rhs body

-- | Top-level entry: walk the SAWCore term, identify subterms that
-- appear more than once and warrant memoisation, allocate fresh Lean
-- names for them, translate each shared subterm without going through
-- its own variable substitution, and wrap the body in nested @let@s.
--
-- Mirrors @SAWCoreRocq.Term.translateTermLet@. The 'IntMap.assocs'
-- ordering of the occurrence map guarantees subterms appear before
-- superterms in the resulting let-chain, so each RHS only references
-- variables bound earlier.
translateTermLet :: TermTranslationMonad m => Term -> m Lean.Term
translateTermLet t = ttLean <$> translateTermLetWithShape t

translateTermLetWithShape :: TermTranslationMonad m => Term -> m TranslatedTerm
translateTermLetWithShape t = do
  let occMap = scTermCount False t
      -- Skip subterms that are themselves types (their @stAppType@ is
      -- @Left Sort{}@). Lean's elaborator does not always unfold
      -- @let@-bound names during type-class search and recursor
      -- motive checking, so a shared type binding can break
      -- elaboration even though it is term-level @let@ definitionally
      -- transparent. Rocq's type checker handles this fine, hence the
      -- divergence from the Rocq backend's filter (audit P-1,
      -- 2026-05-06).
      isType sub = case termSortOrType sub of
        Left _  -> True
        Right _ -> False
      keep (sub, n) = n > 1 && shouldMemoizeTerm sub && not (isType sub)
      shares = IntMap.assocs $ fmap fst $ IntMap.filter keep occMap
      shareTms = map snd shares
  withSharedTerms shares $ \names -> do
    -- Translate shared RHSs in dependency order, extending the shape
    -- environment after each one. Later shared RHSs may reference
    -- earlier shared names, and raw/wrapped adaptation at those use
    -- sites needs the earlier binding's shape just as much as the final
    -- body does.
    defResults <- translateSharedDefs [] names shareTms
    let defs = map ttLean defResults
        letShapes =
          [ (name, shape)
          | (name, TranslatedTerm _ shape) <- zip names defResults
          ]
    localTR (over bindingShapes
               (\m -> foldr (uncurry Map.insert) m letShapes)) $ do
      body <- translateTermWithShape t
      pure (TranslatedTerm
              (foldr mkLet (ttLean body) (zip names defs))
              (ttShape body))
  where
    translateSharedDefs _ [] [] = pure []
    translateSharedDefs knownShapes (name : ns) (tm : tms) = do
      result <- localTR (over bindingShapes
                 (\m -> foldr (uncurry Map.insert) m knownShapes)) $
                  translateTermUnsharedWithShape tm
      let knownShapes' = (name, ttShape result) : knownShapes
      rest <- translateSharedDefs knownShapes' ns tms
      pure (result : rest)
    translateSharedDefs _ _ _ =
      Except.throwError (RejectedPrimitive "shared let"
        "internal shared name/term length mismatch")

-- | Run a translation computation in an empty top-level environment.
runTermTranslationMonad ::
  TranslationConfiguration ->
  Maybe ModuleName ->
    -- ^ the SAWCore module whose declarations are being translated,
    --   if any. References to other identifiers defined in this
    --   module are emitted unqualified.
  ModuleMap ->
  [Lean.Ident] ->
    -- ^ globals already translated (so we don't re-emit them as
    --   auxiliary @def@s when their bodies are referenced).
  [Lean.Ident] ->
    -- ^ local variables already in scope (e.g. the name of the
    --   definition being translated, to avoid shadowing).
  (forall m. TermTranslationMonad m => m a) ->
  Either TranslationError (a, TranslationState)
runTermTranslationMonad configuration mname mm globals localEnv =
  runTranslationMonad configuration
    (TranslationReader
       { _namedEnvironment  = Map.empty
       , _skipBinderWrap        = False
       , _inRecursorCaseBinder  = False
       , _bindingShapes         = Map.empty
       , _deferMkStreamLowering = False
       , _boundUniverses    = Map.empty
       , _unavailableIdents = Set.unions [ reservedIdents
                                         , Set.fromList globals
                                         , Set.fromList localEnv
                                         ]
       , _sawModuleMap      = mm
       , _currentModule     = mname
       , _sharedNames       = IntMap.empty
       , _nextSharedName    = Lean.Ident "x__"
       })
    (TranslationState
       { _globalDeclarations         = globals
       , _topLevelDeclarations       = []
       , _universeVars               = []
       , _universeVarCount           = 0
       , _universeBinderAssignments  = Map.empty
       })

-- | Translate a SAWCore 'Term' and its type to a Lean @def@, together
-- with any auxiliary declarations needed to support it (the bodies of
-- constants referenced along the way).
--
-- Emits @noncomputable def@: SAWCore primitives like @coerce@,
-- @unsafeAssert@, @error@ are axioms that Lean's code generator
-- refuses to compile, and typical normalized terms reference at
-- least one of them. Marking every user def @noncomputable@ is a
-- safe over-approximation — the goal is a file that typechecks, not
-- one that runs.
translateDefDoc ::
  TranslationConfiguration ->
  ModuleMap ->
  Lean.Ident -> Term -> Term ->
  Either TranslationError (Doc ann)
translateDefDoc configuration mm name body tp = do
  ((body', tp'), state) <-
    runTermTranslationMonad configuration Nothing mm [] [name] $
      -- P-1 (2026-05-06): use 'translateTermLet' on the body so
      -- shared subterms are emitted as let-bound variables rather
      -- than re-translated. Without this, hash-consed inputs with
      -- N levels of aliasing blow up exponentially (~100 GB on
      -- Salsa20). Type-side rarely shares; plain 'translateTerm'
      -- is enough there.
      (,) <$> translateTermLet body <*> translateTerm tp
  let auxDecls = reverse (view topLevelDeclarations state)
      univs    = view universeVars state
      -- Wrap a top-level closed type in 'Except String' if it's a
      -- value-domain type. The translated body lives at
      -- 'Except String τ' (Phase β); without this wrap the def's
      -- declared type stays at 'τ' raw, which fails to elaborate.
      -- For Pi-shaped types (function defs like
      -- @addOne : Vec 8 Bool → Vec 8 Bool@) the wrap already
      -- happens inside the Pi case of 'translateTermUnshared';
      -- this fixup only fires on closed-value top-level defs
      -- whose type expression is a bare 'Vec' / 'Bool' / etc.
      wrapType = shouldWrapBinder tp
      tp'' = if wrapType then wrapExcept tp' else tp'
      -- If the type wrapped, the body must too. The generic call-
      -- site lift handles most cases (function applications get
      -- 'Pure.pure' / 'Bind.bind' threaded through), but a bare
      -- constructor literal at a closed-value top-level def (e.g.
      -- @TestBool := Bool.false@) doesn't go through that path —
      -- it's emitted raw. Apply the same raw-value lift the
      -- @ite@ macro uses so the body matches the wrapped type.
      body'' = if wrapType then liftRawValue body' else body'
      mainDecl = mkDefinitionWith Lean.Noncomputable univs name body'' tp''
      -- Each 'prettyDecl' already ends with 'hardline'; 'vcat' adds
      -- another between elements, yielding one blank line between
      -- decls.
  pure $ if null auxDecls
    then Lean.prettyDecl mainDecl
    else vcat (map Lean.prettyDecl auxDecls) <> hardline <> Lean.prettyDecl mainDecl
