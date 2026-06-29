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
  , translateTermLetWithShape
  , TranslatedTerm
  , translatedTermLean
  , translatedTermAsWrapped
  , translateDefDoc
  , withRawTranslationMode
    -- * Decl construction
  , mkDefinitionWith
    -- * Phase β wrap helpers (exposed for the Cryptol module path
    --   so it can apply the same closed-value top-level fixup)
  , shouldWrapBinder
  , wrapExcept
  ) where

import           Control.Lens                 (makeLenses, over, set, view)
import           Control.Monad                (zipWithM)
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
import           Text.Encoding.Z              (zEncodeString)

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

translatedTermLean :: TranslatedTerm -> Lean.Term
translatedTermLean = ttLean

-- | Adapt a translated value to an @Except String@ formal using the
-- translator's shape metadata, not Lean-AST recognition. Raw terms are
-- successful values; wrapped terms are already in the monad.
translatedTermAsWrapped :: TranslatedTerm -> Lean.Term
translatedTermAsWrapped (TranslatedTerm tm BindingWrapped) = tm
translatedTermAsWrapped (TranslatedTerm tm _) =
  Lean.App (Lean.Var (Lean.Ident "Pure.pure")) [tm]

adaptWrappedFormal :: Bool -> TranslatedTerm -> TranslatedTerm
adaptWrappedFormal True result =
  TranslatedTerm (translatedTermAsWrapped result) BindingWrapped
adaptWrappedFormal False result = result

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
  , _bindingShapes :: Map Lean.Ident BindingShape
    -- ^ Lean identifiers in scope paired with their Phase-beta shape.
    -- Used at application and recursor-app sites to decide whether a
    -- variable is an outer 'Except' value that must be 'Bind.bind'-ed,
    -- a function-shaped value that should be passed directly, or raw.
    -- This is the first slice of the expected-shape environment; result
    -- shapes are carried by translation rules and callee conventions.
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
  (== WrappedValueMode) <$> (view valueTranslationMode <$> askTR)

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
    n <- view universeVarCount <$> get
    let uname = "u" ++ show n
    modify (over universeVars (++ [uname]))
    modify (over universeVarCount (+ 1))
    pure (Lean.TypeVar uname)
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
          do mode <- view sortBinderMode <$> askTR
             let sort' = case mode of
                   SortBinderAsSort -> Lean.SortVar uname
                   SortBinderAsType -> Lean.TypeVar uname
                 lvl = case mode of
                   SortBinderAsSort -> Lean.LevelVar uname
                   SortBinderAsType -> Lean.LevelSucc (Lean.LevelVar uname)
             pure (Lean.Sort sort', Just lvl)
        Nothing -> do
          mode <- view sortBinderMode <$> askTR
          let ctx = case mode of
                SortBinderAsSort -> BinderPos
                SortBinderAsType -> TypeCarrierPos
          leanSort <- translateSort ctx s
          case leanSort of
            Lean.SortVar name -> do
              modify (over universeBinderAssignments (Map.insert vn name))
              pure (Lean.Sort leanSort, Just (Lean.LevelVar name))
            Lean.TypeVar name -> do
              modify (over universeBinderAssignments (Map.insert vn name))
              pure (Lean.Sort leanSort, Just (Lean.LevelSucc (Lean.LevelVar name)))
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
      phase <- phaseBetaEnabled
      let t' = if phase && shouldWrapBinder ty && not skipWrap && not inRecCase
                  then wrapExcept t
                  else t
      pure (t', Nothing)
  let bindUniv = maybe id (\u -> over boundUniverses (Map.insert vn u)) mUniv
  -- Track whether the binder type wrapped in 'Except String', so
  -- recursor-scrutinee emission can tell whether the variable
  -- arrives wrapped or raw. Sort-typed binders never wrap.
  skipWrap <- view skipBinderWrap <$> askTR
  inRecCase <- view inRecursorCaseBinder <$> askTR
  phase <- phaseBetaEnabled
  let binderWrapped =
        isNothing (asSort ty)
        && phase
        && shouldWrapBinder ty
        && not skipWrap
        && not inRecCase
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
  phase <- phaseBetaEnabled
  let go _ [] acc = f (reverse acc)
      go i ((n, ty) : rest) acc =
        let isTypeIx = i `elem` typeIxs
            enterCtx =
              (if isTypeIx
                  then set skipBinderWrap True
                  else set skipBinderWrap surroundingCtx)
              . (if phase && isTypeIx && isJust (asSort ty)
                    then set sortBinderMode SortBinderAsType
                    else set sortBinderMode SortBinderAsSort)
        in localTR enterCtx $ translateBinder' n ty $ \bnd ->
             -- Reset 'skipBinderWrap' to the surrounding value before
             -- continuing — the per-binder override must not leak.
             localTR ( set skipBinderWrap surroundingCtx
                     . set sortBinderMode SortBinderAsSort) $
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
    UseMapsToWrapped{} -> pure Nothing
    UseReject reason  ->
      Except.throwError
        (RejectedPrimitive (Text.pack (identName i)) reason)

-- | Apply a 'UseSiteTreatment' to a SAWCore 'Ident' with a list of
-- arguments — the Lean analogue of @applySpecialTreatment@ in
-- "SAWCoreRocq.Term".
--
-- 'Prelude.fix' applications are intercepted before the
-- 'SpecialTreatment' dispatch and routed through proof-carrying
-- emission. Haskell does not classify recursive bodies as particular
-- stream/vector recurrences; it emits a Lean fixed-point obligation and
-- uses only kernel-checked evidence supplied in Lean.
-- | Build a do-block that lifts a Constant-headed App into the
-- @Except String@ monad. Each value-arg becomes a @← bind@ in the
-- block; type-args splice directly into the function-application
-- head; the bound-name application gets @pure@-wrapped at the end.
-- Bind inputs are adapted from 'TranslatedTerm' shape metadata, not
-- by inspecting the generated Lean syntax.
--
-- Concretely, given @head : (t₁ : τ₁) → (v₁ : σ₁) → … → R@ with
-- @typeArgIxs@ marking type-arg positions, @[a₁, …, aₙ]@ the
-- translated args with known shapes, this produces:
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
  [TranslatedTerm] ->
  m Lean.Term
buildLifted head_ pureWrap shouldBind argResults =
  go 0 argResults shouldBind []
  where
    bindVar = Lean.Var (Lean.Ident "Bind.bind")
    pureVar = Lean.Var (Lean.Ident "Pure.pure")
    argTerms = map ttLean argResults
    avoidIdents = Set.unions (leanTermIdents head_ : map leanTermIdents argTerms)

    go :: TermTranslationMonad m
       => Int -> [TranslatedTerm] -> [Bool] -> [(Int, Lean.Ident)] ->
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
      pure (Lean.App bindVar [translatedTermAsWrapped t, lam])
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
  [TranslatedTerm] ->
  m TranslatedTerm
buildLiftedWithShape resultShape head_ pureWrap shouldBind argResults = do
  tm <- buildLifted head_ pureWrap shouldBind argResults
  pure (TranslatedTerm tm resultShape)

useArgExpectsWrapped :: UseArgShape -> Bool
useArgExpectsWrapped UseArgWrapped = True
useArgExpectsWrapped _             = False

useFunctionArgExpectsWrapped :: UseFunctionArgShape -> Bool
useFunctionArgExpectsWrapped UseFunctionArgWrapped = True
useFunctionArgExpectsWrapped UseFunctionArgRaw     = False

adaptFunctionForWrappedHelper ::
  TermTranslationMonad m =>
  Text.Text ->
  Int ->
  Term ->
  Lean.Term ->
  UseFunctionConvention ->
  m Lean.Term
adaptFunctionForWrappedHelper primName pos argTerm fn
    conv@(UseFunctionConvention fnArgShapes resultWrapped) =
  case unwrapTermF argTerm of
    Lambda {} -> do
      let (params, body) = asLambdaList argTerm
          argWrapped = map useFunctionArgExpectsWrapped fnArgShapes
      typeBody <- isTypeProducing body
      if typeBody
         then etaExpandFromType conv
         else if length params /= length argWrapped
           then etaExpandFromType conv
           else translateBindersForWrappedHelper argWrapped params $ \bts -> do
             bodyResult <- translateTermLetWithShape body
             bodyLean <-
               if resultWrapped
                  then pure (translatedTermAsWrapped bodyResult)
                  else case ttShape bodyResult of
                    BindingWrapped ->
                      reject "lambda body returns Except where the helper expects a raw result"
                    _ -> pure (ttLean bodyResult)
             pure (Lean.Lambda (concatMap bindTransToBinder bts) bodyLean)
    _ -> etaExpandFromType conv
  where
    reject reason =
      Except.throwError (RejectedPrimitive primName
        ("wrapped helper expected an adaptable function argument at position "
          <> Text.pack (show pos) <> ", but " <> reason))

    translateBinderForWrappedHelper expectsWrapped vn ty k
      | expectsWrapped = do
          tyLean <- localTR (set skipBinderWrap True) (translateTerm ty)
          withSAWVar vn $ \n' ->
            localTR (withBindingShape n' BindingWrapped) $
              k (BindTrans n' (wrapExcept tyLean))
      | otherwise = do
          surroundingCtx <- view skipBinderWrap <$> askTR
          localTR (set skipBinderWrap True) $
            translateBinder' vn ty $ \bnd ->
              localTR (set skipBinderWrap surroundingCtx) (k bnd)

    translateBindersForWrappedHelper [] [] k = k []
    translateBindersForWrappedHelper (wrapArg : wrapRest)
                                     ((vn, ty) : paramRest) k =
      translateBinderForWrappedHelper wrapArg vn ty $ \bnd ->
        translateBindersForWrappedHelper wrapRest paramRest $ \bnds ->
          k (bnd : bnds)
    translateBindersForWrappedHelper _ _ _ =
      reject "lambda arity does not match the declared helper convention"

    etaExpandFromType (UseFunctionConvention fnArgShapes' resultWrapped') =
      case termSortOrType argTerm of
        Right fty -> do
          ftyLean <- translateTerm fty
          let argWrapped = map useFunctionArgExpectsWrapped fnArgShapes'
              (sourceArgTypes, sourceRetType) =
                peelLeanPiTypes (length argWrapped) ftyLean
          if length sourceArgTypes < length argWrapped
             then reject "could not determine enough source function arguments"
             else do
               let sourceArgWrapped = map isExceptStringType sourceArgTypes
                   sourceRetWrapped = isExceptStringType sourceRetType
                   alreadyMatches =
                        sourceArgWrapped == argWrapped
                     && sourceRetWrapped == resultWrapped'
               if alreadyMatches
                  then pure fn
                  else do
                    etaNames <- mapM
                      (freshVariantAvoiding (leanTermIdents fn) . Lean.Ident .
                         ("η_wrapped_" ++) . show)
                      [0 .. length argWrapped - 1]
                    let etaTerms = map Lean.Var etaNames
                        etaBinders =
                          [ Lean.Binder Lean.Explicit etaName Nothing
                          | etaName <- etaNames
                          ]
                    body <- buildBody resultWrapped' sourceRetWrapped etaTerms
                              sourceArgWrapped argWrapped []
                    pure (Lean.Lambda etaBinders body)
        Left _ ->
          Except.throwError (RejectedPrimitive primName
            ("wrapped helper expected a function argument at position "
              <> Text.pack (show pos)
              <> ", but the source term has no recoverable function type"))

    buildBody resultWrapped' sourceRetWrapped [] [] [] finalArgs =
          let app = Lean.App fn finalArgs
          in case (resultWrapped', sourceRetWrapped) of
               (True, False) ->
                 pure (Lean.App (Lean.Var (Lean.Ident "Pure.pure")) [app])
               (True, True) -> pure app
               (False, False) -> pure app
               (False, True) ->
                 reject "the source function returns Except where the helper expects a raw result"
    buildBody resultWrapped' sourceRetWrapped
                  (eta : etas) (sourceWrapped : sourceRest)
                  (helperWrapped : helperRest) finalArgs
          | helperWrapped && not sourceWrapped = do
              bname <- freshVariantAvoiding
                (Set.unions [leanTermIdents fn, leanTermIdents eta])
                (Lean.Ident ("v_fn_" ++ show (length finalArgs)))
              rest <- buildBody resultWrapped' sourceRetWrapped
                        etas sourceRest helperRest
                        (finalArgs ++ [Lean.Var bname])
              let lam = Lean.Lambda
                    [Lean.Binder Lean.Explicit bname Nothing]
                    rest
              pure (Lean.App (Lean.Var (Lean.Ident "Bind.bind")) [eta, lam])
          | sourceWrapped && not helperWrapped =
              buildBody resultWrapped' sourceRetWrapped etas sourceRest helperRest
                (finalArgs ++
                  [ Lean.App (Lean.Var (Lean.Ident "Pure.pure")) [eta] ])
          | otherwise =
              buildBody resultWrapped' sourceRetWrapped etas sourceRest helperRest
                (finalArgs ++ [eta])
    buildBody _ _ _ _ _ _ =
          reject "the source function type did not match the declared helper convention"

adaptWrappedHelperArg ::
  TermTranslationMonad m =>
  Text.Text ->
  Int ->
  UseArgShape ->
  Term ->
  TranslatedTerm ->
  m TranslatedTerm
adaptWrappedHelperArg primName pos argShape argTerm argResult =
  case argShape of
    UseArgRaw -> pure argResult
    UseArgWrapped -> pure (adaptWrappedFormal True argResult)
    UseArgFunction conv ->
      case ttShape argResult of
        BindingWrapped ->
          Except.throwError (RejectedPrimitive primName
            ("wrapped helper expected a function argument at position "
              <> Text.pack (show pos)
              <> ", but the translated actual was an Except value"))
        _ -> do
          tm <- adaptFunctionForWrappedHelper
                  primName pos argTerm (ttLean argResult) conv
          pure (TranslatedTerm tm BindingFunction)

etaExpandWrappedFunctionResult ::
  TermTranslationMonad m => Term -> Lean.Term -> m Lean.Term
etaExpandWrappedFunctionResult fty fn = do
  let (binders, retTy) = asPiList fty
      pureWrap = shouldWrapBinder retTy
              || isVariableHead retTy
              || natValueResult fty
  if null binders || not pureWrap
     then pure fn
     else do
       etaNames <- mapM
         (freshVariant . Lean.Ident . ("η_arg_" ++) . show)
         [0 .. length binders - 1]
       let etaTerms = map Lean.Var etaNames
           etaBinders =
             [ Lean.Binder Lean.Explicit etaName Nothing
             | etaName <- etaNames
             ]
           typeIxs = typeArgPositions fty
           expectedWrapped =
             [ ix `notElem` typeIxs
               && isNothing (asSort bty)
               && isNothing (asEq bty)
               && isNothing (asPi bty)
               && (isNothing (asNatType bty) || shouldWrapBinder bty)
             | (ix, (_, bty)) <- zip [0..] binders
             ]
           shouldBind =
             argumentBindPlanFromWrapped fty etaTerms expectedWrapped
           etaResults =
             [ TranslatedTerm tm
                 (if wrapped then BindingWrapped else BindingRaw)
             | (tm, wrapped) <- zip etaTerms expectedWrapped
             ]
       body <- buildLifted fn pureWrap
                 (take (length etaTerms) (shouldBind ++ repeat False))
                 etaResults
       pure (Lean.Lambda etaBinders body)

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
translateFunctionWithWrappedResult t = do
  phase <- phaseBetaEnabled
  if not phase
     then translateTerm t
     else case unwrapTermF t of
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
                  let bodyLean = translatedTermAsWrapped bodyResult
                  pure (Lean.Lambda (concatMap bindTransToBinder bts) bodyLean)
       _ -> translateTerm t

lowerMkStreamSound ::
  TermTranslationMonad m => Lean.Term -> Lean.Term -> m Lean.Term
lowerMkStreamSound elTypeLean indexFnLean =
  case indexFnLean of
    Lean.Lambda [idxBinder@(Lean.Binder _ _idxName _)] body -> do
      let indexFn = Lean.Lambda [idxBinder] body
      withSharedLocalTerm
        (Lean.Ident "mkStream_fn_")
        (leanTermIdents elTypeLean)
        indexFn
        $ \indexFnVar -> do
            let prop =
                  Lean.App (Lean.Var (Lean.Ident "saw_mkStream_total_exists"))
                    [elTypeLean, indexFnVar]
            withLocalProofObligation
              (Lean.Ident "h_mkStream_total_")
              prop
              $ \proof ->
                  pure (Lean.App (Lean.Var (Lean.Ident "saw_mkStream_choose"))
                    [elTypeLean, indexFnVar, proof])
    _ ->
      Except.throwError (RejectedPrimitive "MkStream"
        "MkStream expects a unary index function after translation.")

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

proofObligationPlaceholder :: Lean.Term
proofObligationPlaceholder =
  -- Emit-stage placeholder only. The check-stage must reject completed
  -- artifacts that still contain this `sorry`.
  Lean.Tactic "sorry"

withLocalProofObligationUsing ::
  TermTranslationMonad m =>
  Lean.Ident ->
  Lean.Term ->
  (Lean.Ident -> Lean.Term) ->
  (Lean.Term -> m Lean.Term) ->
  m Lean.Term
withLocalProofObligationUsing baseName prop mkProof mkBody = do
  let propBaseName = case baseName of
        Lean.Ident s -> Lean.Ident (s ++ "obligation_")
  propName <- freshVariantAvoiding (leanTermIdents prop) propBaseName
  proofName <- freshVariantAvoiding (Set.insert propName (leanTermIdents prop)) baseName
  body <- mkBody (Lean.Var proofName)
  pure (Lean.Let propName [] (Just (Lean.Sort Lean.Prop)) prop
          (Lean.Let proofName [] (Just (Lean.Var propName))
             (mkProof propName) body))

withLocalProofObligation ::
  TermTranslationMonad m =>
  Lean.Ident ->
  Lean.Term ->
  (Lean.Term -> m Lean.Term) ->
  m Lean.Term
withLocalProofObligation baseName prop =
  withLocalProofObligationUsing baseName prop (const proofObligationPlaceholder)

withSharedLocalTerm ::
  TermTranslationMonad m =>
  Lean.Ident ->
  Set Lean.Ident ->
  Lean.Term ->
  (Lean.Term -> m Lean.Term) ->
  m Lean.Term
withSharedLocalTerm baseName extraAvoid rhs mkBody = do
  name <- freshVariantAvoiding (Set.union extraAvoid (leanTermIdents rhs)) baseName
  body <- mkBody (Lean.Var name)
  pure (Lean.Let name [] Nothing rhs body)

rawErrorResultShape :: Term -> BindingShape
rawErrorResultShape resultTy
  | isJust (asPi resultTy) = BindingFunction
  | otherwise              = BindingRaw

-- | Translate @Prelude.error@ when the expected result type is raw
-- (Nat/index, type, proof, or function). A raw Lean term cannot
-- preserve SAW's value-or-error semantics directly, and fabricating a
-- default would be unsound. Instead, emit the exact contract required
-- for this branch to be sound: the branch must be unreachable.
--
-- Emit-stage files may contain the placeholder proof. Completed
-- discharge must reject unresolved placeholders, so the only way to
-- use the produced raw value in a checked artifact is through a real
-- proof of 'False' in context.
translateRawErrorObligation ::
  TermTranslationMonad m => Term -> m TranslatedTerm
translateRawErrorObligation resultTy = do
  resultTyLean <- translateTerm resultTy
  tm <- withLocalProofObligation
    (Lean.Ident "h_raw_error_")
    (Lean.Var (Lean.Ident "False"))
    $ \proof ->
        pure (Lean.App (Lean.ExplVar (Lean.Ident "False.elim"))
          [resultTyLean, proof])
  pure (TranslatedTerm tm (rawErrorResultShape resultTy))

-- | Lower SAWCore's proof-producing @unsafeAssert α x y@ to an
-- explicit local Lean proof obligation. Haskell only reconstructs the
-- literal equality proposition from the SAW arguments; it does not
-- fabricate a proof or erase the assertion. Emitted proof outlines use
-- the standard placeholder, so a completed artifact must replace it
-- with a Lean-checked proof (possibly using @saw_unsafeAssert@ or a
-- stronger domain-specific tactic).
translateUnsafeAssertObligation ::
  TermTranslationMonad m => Term -> Term -> Term -> m TranslatedTerm
translateUnsafeAssertObligation aArg xArg yArg = do
  aLean <- translateTerm aArg
  xTrans <- translateTermWithShape xArg
  yTrans <- translateTermWithShape yArg
  let (eqType, xLean, yLean)
        | shouldWrapBinder aArg =
            ( wrapExcept aLean
            , translatedTermAsWrapped xTrans
            , translatedTermAsWrapped yTrans
            )
        | otherwise =
            (aLean, ttLean xTrans, ttLean yTrans)
      prop =
        Lean.App (Lean.ExplVar (Lean.Ident "Eq"))
          [eqType, xLean, yLean]
  tm <- withLocalProofObligation
          (Lean.Ident "h_unsafeAssert_")
          prop
          pure
  pure (TranslatedTerm tm BindingRaw)

translateIdentWithArgs :: TermTranslationMonad m => Ident -> [Term] -> m Lean.Term
translateIdentWithArgs i args = ttLean <$> translateIdentWithArgsWithShape i args

translateIdentWithArgsWithShape ::
  TermTranslationMonad m => Ident -> [Term] -> m TranslatedTerm
translateIdentWithArgsWithShape i args
  | i == "Prelude.unsafeAssert"
  , [aArg, xArg, yArg] <- args
  = translateUnsafeAssertObligation aArg xArg yArg
  | i == "Prelude.error"
  , (resultTy : _msg : _) <- args
  , not (shouldWrapBinder resultTy)
  = translateRawErrorObligation resultTy
  | i == "Prelude.fix"
  , (typeArg : bodyArg : rest) <- args
  = do
      fixedPoint <- lowerFixProofObligation typeArg bodyArg
        "all Prelude.fix applications use proof-carrying emission"
      if null rest
         then pure fixedPoint
         else applyKnownFunctionWithShape typeArg (ttLean fixedPoint) rest
  | i == "Prelude.MkStream"
  , [elTypeArg, indexFnArg] <- args
  = do
      elTypeLean <- translateTerm elTypeArg
      indexFnLean <- translateFunctionWithWrappedResult indexFnArg
      streamTerm <- lowerMkStreamSound elTypeLean indexFnLean
      pure (TranslatedTerm streamTerm BindingWrapped)
  | i == "Prelude.if0Nat"
  , [aArg, nArg, xArg, yArg] <- args
  = do
      aLean <- translateTerm aArg
      nLean <- translateTerm nArg
      xTrans <- translateTermWithShape xArg
      yTrans <- translateTermWithShape yArg
      let xLean = ttLean xTrans
          yLean = ttLean yTrans
      if shouldWrapBinder aArg
         then pure (TranslatedTerm
                (Lean.App (Lean.Var (Lean.Ident "if0NatM"))
                  [ aLean, nLean
                  , translatedTermAsWrapped xTrans
                  , translatedTermAsWrapped yTrans
                  ])
                BindingWrapped)
         else pure (TranslatedTerm
                (Lean.App (Lean.Var (Lean.Ident "if0NatRaw"))
                  [aLean, nLean, xLean, yLean])
                (rawErrorResultShape aArg))
  | i == "Prelude.natCase"
  , [pArg, zArg, sArg, nArg] <- args
  = do
      let (_motiveBinders, motiveBody) = asLambdaList pArg
      if shouldWrapBinder motiveBody
         then Except.throwError (RejectedPrimitive "natCase"
                "Value-domain Prelude.natCase is not yet lowered. \
                \The Lean backend currently supports residual natCase \
                \only for raw type/index/proof motives; value motives \
                \need the same proof-carrying totality treatment as \
                \other effectful eliminators.")
         else do
           pLean <- withRawTranslationMode (translateTerm pArg)
           zLean <- withRawTranslationMode (translateTerm zArg)
           sLean <- withRawTranslationMode (translateTerm sArg)
           nLean <- withRawTranslationMode (translateTerm nArg)
           pure (TranslatedTerm
                  (Lean.App (Lean.Var (Lean.Ident "natCaseRaw"))
                    [pLean, zLean, sLean, nLean])
                  BindingRaw)
  | i == "Prelude.coerce"
  , (fromTy : toTy : eqProof : valueArg : restArgs) <- args
  = do
      phase <- phaseBetaEnabled
      if not phase
         then originalDispatchWithShape i args
         else do
           fromTyLean <- translateTerm fromTy
           toTyLean <- translateTerm toTy
           eqProofLean <- translateTerm eqProof
           valueResult <- translateTermWithShape valueArg
           let valueLean = ttLean valueResult
           let coerceHead =
                 Lean.App (Lean.Var (Lean.Ident "coerce"))
                   [fromTyLean, toTyLean, eqProofLean]
           if isJust (asPi fromTy) || isJust (asPi toTy)
              then do
                let coercedFn = Lean.App coerceHead [valueLean]
                if null restArgs
                   then pure (TranslatedTerm coercedFn BindingFunction)
                   else applyKnownFunctionWithShape toTy coercedFn restArgs
              else do
                coerced <- buildLiftedWithShape BindingWrapped coerceHead True [True] [valueResult]
                if null restArgs
                   then pure coerced
                   else Except.throwError (RejectedPrimitive "coerce"
                          "non-function coerce was applied to extra arguments")
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
      phase <- phaseBetaEnabled
      if not phase
         then originalDispatchWithShape i args
         else do
           aTrans <- translateTerm aArg
           xTrans <- translateTermWithShape xArg
           yTrans <- translateTermWithShape yArg
           pure $ TranslatedTerm
             (Lean.App (Lean.ExplVar (Lean.Ident "Eq"))
               [ wrapExcept aTrans
               , translatedTermAsWrapped xTrans
               , translatedTermAsWrapped yTrans
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
      phase <- phaseBetaEnabled
      case funType mm' of
        Just fty
          | phase
          , any (shouldWrapBinder . snd) (fst (asPiList fty))
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
              -- this rule doesn't pure-wrap them. Explicit wrapped
              -- helpers such as 'iteM' use 'UseMapsToWrapped', so no
              -- double-wrap concern there.
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
                   in buildLiftedWithShape resultShape f pureWrap shouldBindForArgs argResults
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
                   let etaResults =
                         argResults ++
                         [ TranslatedTerm (Lean.Var etaName)
                             (if wrapped then BindingWrapped else BindingRaw)
                         | (etaName, wrapped) <- zip etaNames missingWrapped
                         ]
                   let shouldBindEta =
                         argumentBindPlanFromWrapped fty etaArgTerms
                           (suppliedWrapped ++ missingWrapped)
                   body <- buildLifted f pureWrap
                             (take (length etaArgTerms)
                                   (shouldBindEta ++ repeat False))
                             etaResults
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
      -- Same scoping logic as 'UseRename'-with-expl, but also
      -- supplies explicit universe levels at the indexed argument
      -- positions. This convention is deterministic: if a required
      -- level cannot be recovered from the SAW term, reject rather
      -- than silently falling back to Lean inference.
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
      case sequence mLvls of
        Just lvls ->
          applied (Lean.ExplVarUniv scopedTarget lvls) args
        Nothing ->
          Except.throwError (RejectedPrimitive (Text.pack (identName i))
            "could not determine required explicit Lean universe levels")
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
    apply _ _ (UseMapsToWrapped argShapes target)
      | length args >= n
      , (mArgs, rest) <- splitAt n args = do
          argResults0 <- traverse translateTermWithShape mArgs
          -- For an explicitly wrapped helper formal, lift raw values
          -- into 'Except'. For raw helper formals, bind an already-
          -- wrapped actual before applying the helper. Function
          -- formals eta-expand through their declared raw/wrapped
          -- boundary; this is wrapper plumbing, not a semantic
          -- replacement of the source function.
          adapted <- zipWithM
            (\pos (argShape, argTerm, argResult) ->
               adaptWrappedHelperArg
                 (Text.pack (identName i)) pos argShape argTerm argResult)
            [0..]
            (zip3 argShapes mArgs argResults0)
          let actualWrapped = map (isWrappedShape . ttShape) adapted
              expectedWrapped = map useArgExpectsWrapped argShapes
          let shouldBindRaw =
                zipWith (\expectsWrapped isWrappedActual ->
                           not expectsWrapped && isWrappedActual)
                        expectedWrapped actualWrapped
          helperApp <- buildLifted (Lean.Var target) False shouldBindRaw adapted
          if null rest
             then pure (TranslatedTerm helperApp BindingWrapped)
             else applied helperApp rest
      | otherwise =
          -- Under-applied: adapt the supplied prefix with the same
          -- explicit convention table as the fully-applied path, then
          -- return a function-shaped partial application. This keeps
          -- partial helpers from escaping the raw/wrapped convention
          -- system.
          do argResults <- traverse translateTermWithShape args
             let suppliedShapes = take (length args) argShapes
             adapted <- zipWithM
               (\pos (argShape, argTerm, argResult) ->
                  adaptWrappedHelperArg
                    (Text.pack (identName i)) pos argShape argTerm argResult)
               [0..]
               (zip3 suppliedShapes args argResults)
             let actualWrapped = map (isWrappedShape . ttShape) adapted
                 expectedWrapped = map useArgExpectsWrapped suppliedShapes
             let shouldBindRaw =
                   zipWith (\expectsWrapped isWrappedActual ->
                              not expectsWrapped && isWrappedActual)
                           expectedWrapped actualWrapped
             tm <- if null args
                     then pure (Lean.Var target)
                     else buildLifted (Lean.Var target) False shouldBindRaw adapted
             pure (TranslatedTerm tm BindingFunction)
      where
        n = length argShapes
    apply _ _ (UseReject reason) =
      Except.throwError
        (RejectedPrimitive (Text.pack (identName i)) reason)

-- | Lower an otherwise-unsupported @Prelude.fix@ to an explicit Lean
-- proof obligation rather than rejecting outright.
--
-- The obligation is intentionally semantic and strong: Lean must prove
-- that the translated body has a unique fixed point. For wrapped
-- value-domain results, uniqueness ranges over the whole
-- @Except String α@ fixed-point space, not only over successful
-- @Pure.pure@ values; otherwise an error fixed point could coexist
-- with the chosen successful value. Under SAW's @fix_unfold@
-- principle, uniqueness forces that Lean witness to be the SAW fixed
-- point. This is conservative for shapes whose productivity/boundedness
-- we do not recognize in Haskell: the generated file may be hard to
-- prove, but it cannot silently assign a different meaning to recursion.
lowerFixProofObligation ::
  TermTranslationMonad m =>
  Term -> Term -> Text.Text -> m TranslatedTerm
lowerFixProofObligation typeArg bodyArg _reason = do
  typeLean <- translateTerm typeArg
  bodyLean <- translateTerm bodyArg
  if shouldWrapBinder typeArg
     then do
       term <- lowerWrappedFixProofObligationLean typeLean bodyLean
       pure (TranslatedTerm term BindingWrapped)
     else do
       term <- withSharedLocalTerm
         (Lean.Ident "fix_body_")
         (leanTermIdents typeLean)
         bodyLean
         $ \bodyVar -> do
             let prop =
                   Lean.App (Lean.Var (Lean.Ident "saw_fix_unique_exists_raw"))
                     [typeLean, bodyVar]
             withLocalProofObligation
               (Lean.Ident "h_fix_unique_")
               prop
               $ \proof ->
                   pure (Lean.App (Lean.Var (Lean.Ident "saw_fix_choose_raw"))
                     [typeLean, bodyVar, proof])
       pure (TranslatedTerm term (rawErrorResultShape typeArg))

lowerWrappedFixProofObligationLean ::
  TermTranslationMonad m =>
  Lean.Term -> Lean.Term -> m Lean.Term
lowerWrappedFixProofObligationLean typeLean bodyLean = do
  withSharedLocalTerm
    (Lean.Ident "fix_body_")
    (leanTermIdents typeLean)
    bodyLean
    $ \bodyVar -> do
        let prop =
              Lean.App (Lean.Var (Lean.Ident "saw_fix_unique_exists"))
                [typeLean, bodyVar]
        withLocalProofObligation
          (Lean.Ident "h_fix_unique_")
          prop
          $ \proof ->
              pure (Lean.App (Lean.Var (Lean.Ident "saw_fix_choose"))
                [typeLean, bodyVar, proof])

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
--   * an 'ImportedName' for a caller-supplied realization. This must be
--     explicit through 'constantRenaming' or 'constantSkips'; otherwise
--     emitting a bare Lean reference would silently assume a semantic
--     connection that Haskell did not check. Even when explicit, we do
--     not splice the target name directly into user terms. Instead we
--     emit a small Lean alias whose type is the translated SAWCore type
--     and use that alias. This makes the imported-name contract visible
--     and Lean-checked: the caller-supplied realization must elaborate
--     at the type SAW assigned to the imported constant.
translateConstantWithType ::
  TermTranslationMonad m => Name -> Either Sort Term -> m Lean.Term
translateConstantWithType nm sawType
  | ModuleIdentifier ident <- nameInfo nm = translateIdentWithArgs ident []
  | otherwise = do
      config <- asks translationConfiguration
      let nm_str  = Text.unpack (toShortName (nameInfo nm))
          mRenamed = lookup nm_str (constantRenaming config)
          explicitlySkipped = nm_str `elem` constantSkips config
      case (mRenamed, explicitlySkipped) of
        (Nothing, False) ->
          Except.throwError $ RejectedPrimitive (Text.pack nm_str) $
            "imported constants require an explicit Lean realization. \
            \Add the name to the skip list when the Lean environment supplies \
            \a declaration with the same name, or provide an explicit renaming."
        _ ->
          emitImportedRealizationAlias nm sawType $
            escapeIdent $ Lean.Ident $ fromMaybe nm_str mRenamed

translateConstantWithShape ::
  TermTranslationMonad m => Name -> Either Sort Term -> m TranslatedTerm
translateConstantWithShape nm sawType = do
  tm <- translateConstantWithType nm sawType
  shape <- case nameInfo nm of
    ModuleIdentifier{} -> bindingShapeOfLeanTermM tm
    ImportedName{} -> case sawType of
      Right ty
        | isJust (asPi ty) -> pure BindingFunction
        | shouldWrapBinder ty -> pure BindingWrapped
      _ -> bindingShapeOfLeanTermM tm
  pure (TranslatedTerm tm shape)

emitImportedRealizationAlias ::
  TermTranslationMonad m =>
  Name -> Either Sort Term -> Lean.Ident -> m Lean.Term
emitImportedRealizationAlias nm sawType targetIdent = do
  let aliasIdent = importedRealizationAliasIdent nm
  globals <- view globalDeclarations <$> get
  if aliasIdent `elem` globals
     then pure (Lean.Var aliasIdent)
     else do
       typeLean <- translateConstantContractType sawType
       univs <- view universeVars <$> get
       let body = Lean.Var targetIdent
           decl = mkDefinitionWith Lean.Noncomputable univs aliasIdent body typeLean
       modify (over topLevelDeclarations (decl :))
       modify (over globalDeclarations (aliasIdent :))
       pure (Lean.Var aliasIdent)

translateConstantContractType ::
  TermTranslationMonad m => Either Sort Term -> m Lean.Term
translateConstantContractType (Left srt) =
  Lean.Sort <$> translateSort ValuePos srt
translateConstantContractType (Right ty) = do
  tyLean <- translateTerm ty
  pure $ if shouldWrapBinder ty then wrapExcept tyLean else tyLean

importedRealizationAliasIdent :: Name -> Lean.Ident
importedRealizationAliasIdent nm =
  Lean.Ident $
    "__saw_realizes_" ++
    zEncodeString (Text.unpack (toAbsoluteName (nameInfo nm)))

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
  Lean.TypeVar u       -> Set.singleton u
  Lean.SortVar u       -> Set.singleton u

-- | Collect universe-variable names referenced inside a
-- 'Lean.UnivLevel' (the explicit per-arg level in @\@Foo.{u, v}@).
usedUniversesInLevel :: Lean.UnivLevel -> Set String
usedUniversesInLevel = \case
  Lean.LevelVar u  -> Set.singleton u
  Lean.LevelLit _  -> Set.empty
  Lean.LevelSucc l -> usedUniversesInLevel l
  Lean.LevelMax ls -> Set.unions (map usedUniversesInLevel ls)
  Lean.LevelIMax ls -> Set.unions (map usedUniversesInLevel ls)

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
-- The motive is translated with raw binders, because Lean's recursor
-- applies motives to raw inductive values. Its result type still uses
-- the Phase-β wrap when the motive is value-producing.
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
       -- A motive returning a 'Sort' (like @fun num => Type@)
       -- produces a type expression. A motive whose body itself
       -- has sort 'Prop' (like @fun y h => Eq Type ...@) produces
       -- a proof. Only value-producing motives use the Phase-β
       -- scrutinee bind and wrapped result type.
       let motiveArg = preScrut !! nParams
           (_, motiveBody) = asLambdaList motiveArg
           motiveReturnsType = isJust (asSort motiveBody)
           motiveReturnsProof = case termSortOrType motiveBody of
             Left s  -> s == propSort
             Right _ -> False
           motiveReturnsRaw = motiveReturnsType || motiveReturnsProof
       paramTrans <- traverse translateTerm paramArgs
       casePlans <- recursorCasePlans paramTrans crec
       preTrans <- sequence (zipWith
         (\i a -> if i < nParams
                     then pure (paramTrans !! i)
                     else if i == nParams
                       then translateRecursorMotive motiveReturnsRaw a
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

    translateRecursorMotive ::
      TermTranslationMonad m => Bool -> Term -> m Lean.Term
    translateRecursorMotive motiveReturnsRaw motiveTerm =
      case asLambdaList motiveTerm of
        ([], _) -> translateTerm motiveTerm
        (params, body) -> do
          surroundingSkipWrap <- view skipBinderWrap <$> askTR
          phase <- phaseBetaEnabled
          localTR (set skipBinderWrap True) $
            translateBinders params $ \paramTerms ->
              localTR (set skipBinderWrap surroundingSkipWrap) $ do
                bodyLean <- translateTermLet body
                let bodyWrapped =
                      if phase && not motiveReturnsRaw && shouldWrapBinder body
                         then wrapExcept bodyLean
                         else bodyLean
                pure (Lean.Lambda paramTerms bodyWrapped)

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
    -- No explicit source binders to wrap. A bare function-valued
    -- handler such as `bvNat` may still be used at a recursor branch
    -- whose motive expects a wrapped result function, so eta-expand
    -- and lift the result when the handler's SAW type demands it.
    adaptBareCaseHandler caseTerm
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
          do expanded <- etaExpandWrappedFunctionResult saw_ty (Lean.Var name)
             case expanded of
               Lean.Var name' | name' == name -> pure Nothing
               _ -> pure (Just expanded)
      | otherwise = pure Nothing

    pureVar = Lean.Var (Lean.Ident "Pure.pure")

    adaptBareCaseHandler ::
      TermTranslationMonad m => Term -> m Lean.Term
    adaptBareCaseHandler caseTerm' = do
      caseLean <- translateTerm caseTerm'
      mFty <- functionTypeOfTerm caseTerm'
      case mFty of
        Just fty -> etaExpandWrappedFunctionResult fty caseLean
        Nothing  -> pure caseLean

    functionTypeOfTerm ::
      TermTranslationMonad m => Term -> m (Maybe Term)
    functionTypeOfTerm t = case unwrapTermF t of
      Variable _ fty -> pure (Just fty)
      Constant nm
        | ModuleIdentifier ident <- nameInfo nm -> do
            mm <- view sawModuleMap <$> askTR
            pure $ case resolveNameInMap mm ident of
              Just (ResolvedDef def)  -> Just (defType def)
              Just (ResolvedCtor ctor) -> Just (ctorType ctor)
              _                       -> Nothing
      _ -> pure Nothing

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
  -- @Vec n (Except String α)@; wrap with 'vecSequenceM' to lift to
  -- @Except String (Vec n α)@. Raw elements are lifted from their
  -- translation shape before sequencing.
  --
  -- Empty arrays don't need sequencing — there's nothing to lift —
  -- so emit the bare literal; callers that need an @Except@ value
  -- lift it from the returned raw shape.
  --
  -- No bitvector specialization yet — the Rocq backend's
  -- 'intToBv' collapse needs the full Data.BitVector.Sized /
  -- Data.Parameterized machinery, which we leave to a later pass.
  ArrayValue elTyTerm vec -> do
    elemResults <- traverse translateTermWithShape (toList vec)
    if null elemResults
       then pure (Lean.List [])
       else do
         elTyLean <- translateTerm elTyTerm
         let liftedElems = map translatedTermAsWrapped elemResults
             n          = length elemResults
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
      phase <- phaseBetaEnabled
      let valueBody = phase && shouldWrapBinder body
          -- A Pi with a Prop or Eq body is a /quantifier/
          -- ('∀ x, P x') — its binders are universally-quantified
          -- value inputs that should wrap (so the body's
          -- Phase-β-lifted operations can bind them). Distinct
          -- from a Pi with a Sort-or-Pi body, which describes a
          -- type-of-types (motive shape) and whose binders are
          -- type indices that must stay raw.
          propBody = phase &&
            ( isJust (asEq body)
              || case asSort body of
                   Just s -> s == propSort
                   Nothing -> False
            )
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
      phase <- phaseBetaEnabled
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
                    let body'' = if phase && shouldWrapBinder body
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
                ttLean <$> applyKnownFunctionWithShape fty f' args
              Constant _ ->
                case termSortOrType f of
                  Right fty -> ttLean <$> applyKnownFunctionWithShape fty f' args
                  Left _    -> pure (Lean.App f' args')
              _ -> pure (Lean.App f' args')

    Constant nm -> translateConstantWithType nm (termSortOrType t)

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
                applyKnownFunctionWithShape fty f' args
              Constant _ ->
                case termSortOrType f of
                  Right fty -> applyKnownFunctionWithShape fty f' args
                  Left _    -> do
                    let tm = Lean.App f' args'
                    shape <- bindingShapeOfLeanTermM tm
                    pure (TranslatedTerm tm shape)
              _ -> do
                let tm = Lean.App f' args'
                shape <- bindingShapeOfLeanTermM tm
                pure (TranslatedTerm tm shape)
    _ -> do
      case unwrapTermF t of
        Constant nm -> translateConstantWithShape nm (termSortOrType t)
        _ -> do
          tm <- translateTermUnshared t
          shape <- case unwrapTermF t of
            FTermF (ArrayValue _ vec)
              | not (null (toList vec)) -> pure BindingWrapped
            _ -> bindingShapeOfLeanTermM tm
          pure (TranslatedTerm tm shape)

applyKnownFunctionWithShape ::
  TermTranslationMonad m =>
  Term -> Lean.Term -> [Term] -> m TranslatedTerm
applyKnownFunctionWithShape fty f args = do
  ftyLean <- translateTerm fty
  argResults <- traverse translateTermWithShape args
  let argTerms = map ttLean argResults
  phase <- phaseBetaEnabled
  if phase
     then do
       let (expectedTypes, retType) = peelLeanPiTypes (length args) ftyLean
           expectedWrapped =
             take (length argTerms) (map isExceptStringType expectedTypes ++ repeat False)
           expectedFunction =
             take (length argTerms) (map isLeanPiType expectedTypes ++ repeat False)
           actualWrapped =
             map (isWrappedShape . ttShape) argResults
           shouldBindRaw =
             zipWith3
               (\expectsWrapped expectsFunction isWrappedActual ->
                  not expectsWrapped && not expectsFunction && isWrappedActual)
               expectedWrapped
               expectedFunction
               actualWrapped
           adapted =
             zipWith adaptWrappedFormal expectedWrapped argResults
           resultShape = bindingShapeOfType retType
       buildLiftedWithShape resultShape f False
         (take (length adapted) (shouldBindRaw ++ repeat False))
         adapted
     else do
       let tm = Lean.App f argTerms
       pure (TranslatedTerm tm BindingRaw)

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
       , _boundUniverses    = Map.empty
       , _unavailableIdents = Set.unions [ reservedIdents
                                         , Set.fromList globals
                                         , Set.fromList localEnv
                                         ]
       , _sawModuleMap      = mm
       , _currentModule     = mname
       , _sharedNames       = IntMap.empty
       , _nextSharedName    = Lean.Ident "x__"
       , _valueTranslationMode = WrappedValueMode
       , _sortBinderMode       = SortBinderAsSort
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
  ((bodyResult, tp'), state) <-
    runTermTranslationMonad configuration Nothing mm [] [name] $
      -- P-1 (2026-05-06): use 'translateTermLet' on the body so
      -- shared subterms are emitted as let-bound variables rather
      -- than re-translated. Without this, hash-consed inputs with
      -- N levels of aliasing blow up exponentially (~100 GB on
      -- Salsa20). Type-side rarely shares; plain 'translateTerm'
      -- is enough there.
      (,) <$> translateTermLetWithShape body <*> translateTerm tp
  let auxDecls = reverse (view topLevelDeclarations state)
      univs    = view universeVars state
      body'    = ttLean bodyResult
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
      -- If the type wrapped, the body must too. Use the translated
      -- body's shape metadata, not Lean-AST recognition, to decide
      -- whether a 'Pure.pure' lift is needed.
      body'' = if wrapType then translatedTermAsWrapped bodyResult else body'
      mainDecl = mkDefinitionWith Lean.Noncomputable univs name body'' tp''
      -- Each 'prettyDecl' already ends with 'hardline'; 'vcat' adds
      -- another between elements, yielding one blank line between
      -- decls.
  pure $ if null auxDecls
    then Lean.prettyDecl mainDecl
    else vcat (map Lean.prettyDecl auxDecls) <> hardline <> Lean.prettyDecl mainDecl
