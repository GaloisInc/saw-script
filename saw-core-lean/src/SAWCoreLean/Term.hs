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
  ) where

import           Control.Lens                 (makeLenses, over, set, view)
import qualified Control.Monad.Except         as Except
import           Control.Monad.Reader         (MonadReader(local), asks)
import           Control.Monad.State          (get, modify)
import           Data.Foldable                (toList)
import qualified Data.IntMap.Strict           as IntMap
import           Data.IntMap.Strict           (IntMap)
import qualified Data.IntSet                  as IntSet
import qualified Data.Map                     as Map
import           Data.Map                     (Map)
import           Data.Maybe                   (fromMaybe, isJust)
import qualified Data.Set                     as Set
import           Data.Set                     (Set)
import qualified Data.Text                    as Text
import           Prelude                      hiding (fail)
import           Prettyprinter                (Doc, hardline, vcat)

import qualified Language.Lean.AST            as Lean
import qualified Language.Lean.Pretty         as Lean

import           SAWCore.Module               (Ctor(..), Def(..),
                                               ModuleMap,
                                               ResolvedName(..),
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

-- | Should a SAW binder's type be wrapped in @Except String@ when
-- emitted in Lean?
--
-- Wrap = it's a value-domain type whose Cryptol semantics admits
-- the error case. Don't wrap when:
--
--   * Sorts (types-of-types) — they're not values themselves.
--   * Type-variables (a 'Variable' in the SAW term). Polymorphic
--     helpers like @sym (a : sort 1) (x : a)@ have @x : a@ where
--     @a@ is a bound type-variable. Keeping @x@ at @a@ (unwrapped)
--     means the helper stays Lean-polymorphic and callers
--     instantiate at @Except String β@ if they want the wrapped
--     version — no parallel monadic mirror needed.
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
  | isVariableHead ty         = False
  | Just _ <- asNatType ty    = False
  | Just _ <- asEq ty         = False
  | Just _ <- asPi ty         = False
  | otherwise                 = True
  where
    -- True for terms whose head is a SAW 'Variable' — i.e. the
    -- term is a (possibly applied) type-variable. Examples:
    --   * @t@ where @t : sort 1@ — the binder is at the type
    --     variable itself.
    --   * @p y pf@ where @p : (y : t) → Eq t x y → sort u_motive@
    --     — the term is a polymorphic application whose sort is
    --     determined by the motive's universe (which could be
    --     'Prop'). Wrapping would force a specific universe
    --     constraint that doesn't hold polymorphically.
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
            Just (ResolvedDef def)  -> Just (defType def)
            Just (ResolvedCtor c)   -> Just (ctorType c)
            _                       -> Nothing
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
      t <- translateTerm ty
      skipWrap <- view skipBinderWrap <$> askTR
      let t' = if shouldWrapBinder ty && not skipWrap
                  then wrapExcept t
                  else t
      pure (t', Nothing)
  let bindUniv = maybe id (\u -> over boundUniverses (Map.insert vn u)) mUniv
  localTR bindUniv $
    withSAWVar vn $ \n' ->
      f (BindTrans n' ty')

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
    UseMacro _ _      -> pure Nothing
    UseMacroOrVar{}   -> pure Nothing
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
      bname <- freshVariant (Lean.Ident ("v_" ++ show pos))
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

translateIdentWithArgs :: TermTranslationMonad m => Ident -> [Term] -> m Lean.Term
translateIdentWithArgs i args
  | i == "Prelude.fix"
  , [typeArg, bodyArg] <- args
  = case classifyFix typeArg bodyArg of
      StreamCorec elT body                 -> lowerStreamCorec elT body
      PairStreamCorec elTypeA elTypeB body -> lowerPairStreamCorec elTypeA elTypeB body
      BoundedVecFold len elType body       -> lowerBoundedVecFold len elType body
      NotMatched _                         -> originalDispatch i args
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
translateIdentWithArgs i args = originalDispatch i args

originalDispatch :: TermTranslationMonad m => Ident -> [Term] -> m Lean.Term
originalDispatch i args = do
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
    applied :: TermTranslationMonad m => Lean.Term -> [Term] -> m Lean.Term
    applied f [] = pure f
    applied f args' = do
      argTerms <- mapM translateTerm args'
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
              --     like @gen@'s @Nat → α@) / Sort / Prop / Nat /
              --     Eq / variable: no bind, splice raw.
              --
              -- 'Pure.pure'-wrap the result only when the function's
              -- SAW return type is value-domain. For variable-headed
              -- returns (ite, coerce …) the Lean target's return is
              -- already wrapped (its signature uses
              -- @Except String a@), so 'Pure.pure' would double-wrap.
              let (binders, _) = asPiList fty
                  typeIxs = typeArgPositions fty
                  shouldBind =
                    [ (ix `notElem` typeIxs) && shouldWrapBinder bty
                    | (ix, (_, bty)) <- zip [0..] binders
                    ]
                  shouldBindForArgs =
                    take (length args') (shouldBind ++ repeat False)
                  pureWrap = shouldWrapBinder (retTypeOfFun fty)
              buildLifted f pureWrap shouldBindForArgs argTerms
        _ -> pure (Lean.App f argTerms)

    apply :: TermTranslationMonad m =>
             Bool -> Lean.Ident -> UseSiteTreatment -> m Lean.Term
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
    apply _ _ (UseMacro n macroFun)
      | length args >= n
      , (mArgs, rest) <- splitAt n args = do
          f <- macroFun <$> mapM translateTerm mArgs
          applied f rest
      | otherwise =
          -- Under-applied macro — the table entry promises to consume n
          -- arguments but fewer were supplied. Surface it explicitly;
          -- emitting a partial application would produce garbage.
          Except.throwError (UnderAppliedMacro (Text.pack (identName i)) n)
    apply _ _ (UseMacroOrVar n fallback macroFun)
      | length args >= n
      , (mArgs, rest) <- splitAt n args = do
          f <- macroFun <$> mapM translateTerm mArgs
          applied f rest
      | otherwise =
          -- Under-applied: emit the fallback term as the head and
          -- apply whatever args we did receive. Lean will eta-expand
          -- as needed at use sites.
          applied fallback args
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
  bodyLean   <- translateTerm bodyTerm
  lookupName <- freshVariant (Lean.Ident "lookup_")
  indexName  <- freshVariant (Lean.Ident "i_")
  let errorTerm =
        Lean.App (Lean.Var (Lean.Ident "error_unrestricted"))
          [elTypeLean, Lean.StringLit "fix lookup out of bounds"]
      mkStreamCall =
        Lean.App (Lean.Var (Lean.Ident "Stream.MkStream"))
          [Lean.Var lookupName]
      bodyApplied = Lean.App bodyLean [mkStreamCall]
      indexCall =
        Lean.App (Lean.Var (Lean.Ident "streamIdx"))
          [elTypeLean, bodyApplied, Lean.Var indexName]
      innerLambda =
        Lean.Lambda
          [ Lean.Binder Lean.Explicit lookupName Nothing
          , Lean.Binder Lean.Explicit indexName  Nothing
          ]
          indexCall
  pure $ Lean.App (Lean.Var (Lean.Ident "mkStreamFix"))
                  [elTypeLean, errorTerm, innerLambda]

-- | Lower a 'PairStreamCorec'-shaped @Prelude.fix@ to a Lean
-- 'mkStreamFixPair' call. The body — a SAWCore lambda
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
  bodyLean    <- translateTerm bodyTerm
  lkA1 <- freshVariant (Lean.Ident "lkA_")
  lkB1 <- freshVariant (Lean.Ident "lkB_")
  i1   <- freshVariant (Lean.Ident "i_")
  lkA2 <- freshVariant (Lean.Ident "lkA_")
  lkB2 <- freshVariant (Lean.Ident "lkB_")
  i2   <- freshVariant (Lean.Ident "i_")
  let errA = Lean.App (Lean.Var (Lean.Ident "error_unrestricted"))
               [elTypeALean, Lean.StringLit "fix lookup out of bounds"]
      errB = Lean.App (Lean.Var (Lean.Ident "error_unrestricted"))
               [elTypeBLean, Lean.StringLit "fix lookup out of bounds"]
      streamA = Lean.App (Lean.Var (Lean.Ident "Stream")) [elTypeALean]
      streamB = Lean.App (Lean.Var (Lean.Ident "Stream")) [elTypeBLean]
      mkPairArg lkA lkB =
        Lean.App (Lean.Var (Lean.Ident "PairType.PairValue"))
          [ Lean.App (Lean.Var (Lean.Ident "Stream.MkStream")) [Lean.Var lkA]
          , Lean.App (Lean.Var (Lean.Ident "Stream.MkStream")) [Lean.Var lkB]
          ]
      mkBranch lkA lkB iName projectorName resultElType =
        let bodyApplied = Lean.App bodyLean [mkPairArg lkA lkB]
            projection  = Lean.App (Lean.Var (Lean.Ident projectorName))
                            [streamA, streamB, bodyApplied]
            indexed     = Lean.App (Lean.Var (Lean.Ident "streamIdx"))
                            [resultElType, projection, Lean.Var iName]
        in Lean.Lambda
             [ Lean.Binder Lean.Explicit lkA Nothing
             , Lean.Binder Lean.Explicit lkB Nothing
             , Lean.Binder Lean.Explicit iName Nothing
             ]
             indexed
      branchA = mkBranch lkA1 lkB1 i1 "pairFst" elTypeALean
      branchB = mkBranch lkA2 lkB2 i2 "pairSnd" elTypeBLean
  pure $ Lean.App (Lean.Var (Lean.Ident "mkStreamFixPair"))
                  [elTypeALean, elTypeBLean, errA, errB, branchA, branchB]

-- | Lower a polymorphic stream-iteration @Prelude.fix@ application
-- (Cryptol's `iterate` shape, recognized by 'classifyPolyStreamIterate')
-- to a direct call to the hand-written `cryptolIterate` def in
-- @CryptolToLean.SAWCorePreludeExtra@. Sidesteps the polymorphism
-- entirely — the structural-recursion def in Lean handles the
-- single-stream productive corecursion at any concrete element type.
lowerPolyStreamIterate :: TermTranslationMonad m =>
                          Term -> Term -> Term -> m Lean.Term
lowerPolyStreamIterate alphaArg fArg xArg = do
  alphaLean <- translateTerm alphaArg
  fLean     <- translateTerm fArg
  xLean     <- translateTerm xArg
  -- Emit fully-qualified reference: SAWCorePreludeExtra is not in the
  -- implicitly-opened module list (those are SAWCorePrimitives + Vectors),
  -- so a bare `cryptolIterate` would not resolve.
  pure $ Lean.App
           (Lean.Var (Lean.Ident "CryptolToLean.SAWCorePreludeExtra.cryptolIterate"))
           [alphaLean, fLean, xLean]

-- | Lower a 'BoundedVecFold'-shaped @Prelude.fix@ to a Lean
-- 'genFix' call. Body shape:
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
  let errorTerm =
        Lean.App (Lean.Var (Lean.Ident "error_unrestricted"))
          [elTypeLean, Lean.StringLit "fix lookup out of bounds"]
      genCall =
        Lean.App (Lean.Var (Lean.Ident "gen"))
          [lenLean, elTypeLean, Lean.Var lookupName]
      bodyApplied = Lean.App bodyLean [genCall]
      atCall =
        Lean.App (Lean.Var (Lean.Ident "atWithDefault"))
          [lenLean, elTypeLean, errorTerm, bodyApplied, Lean.Var indexName]
      innerLambda =
        Lean.Lambda
          [ Lean.Binder Lean.Explicit lookupName Nothing
          , Lean.Binder Lean.Explicit indexName  Nothing
          ]
          atCall
  pure $ Lean.App (Lean.Var (Lean.Ident "genFix"))
                  [lenLean, elTypeLean, errorTerm, innerLambda]

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

-- | Produce a Lean term that represents a translation error inline
-- rather than failing the whole walk. Mirrors Rocq's @errorTermM@.
-- Useful for recursors over unmapped datatypes — the result is a
-- well-formed Lean value that points at where the problem is.
errorTermM :: TermTranslationMonad m => String -> m Lean.Term
errorTermM msg =
  pure $ Lean.App (Lean.Var (Lean.Ident "error_unrestricted")) [Lean.StringLit msg]

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

  -- Array literals. No bitvector specialization yet — the Rocq
  -- backend's `intToBv` collapse needs the full
  -- Data.BitVector.Sized / Data.Parameterized machinery, which we
  -- leave to a later pass.
  ArrayValue _ vec ->
    Lean.List <$> traverse translateTerm (toList vec)

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
translateTerm t =
  case t of
    STApp { stAppIndex = i } -> do
      shared <- view sharedNames <$> askTR
      case IntMap.lookup i shared of
        Just sh -> pure (Lean.Var (sharedNameIdent sh))
        Nothing -> translateTermUnshared t

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
      let withBinders k =
            if valueBody
               then translateBindersSelective (typeArgPositions t) params
                      (k . concatMap bindTransToPiBinder)
               else localTR (set skipBinderWrap True)
                      (translatePiBinders params k)
      withBinders $ \paramTerms -> do
        body' <- translateTermLet body
        let body'' = if valueBody then wrapExcept body' else body'
        pure (Lean.Pi paramTerms body'')

    Lambda {} -> do
      let (params, body) = asLambdaList t
      -- Motive lambdas like @fun (n : Num) => Type@ produce a Lean
      -- type expression, not a value. Their binders are type
      -- indices and must NOT be wrapped — wrapping breaks recursor
      -- elimination (the motive ends up expecting a wrapped
      -- scrutinee but the recursor supplies the raw datatype).
      typeBody <- isTypeProducing body
      if typeBody
         then localTR (set skipBinderWrap True) $
                translateBinders params $ \paramTerms -> do
                  body' <- translateTermLet body
                  pure (Lean.Lambda paramTerms body')
         else do
           -- Value-level lambda. Skip wrapping at binder positions
           -- whose variable feeds a later binder's type — those are
           -- type indices threaded through the binder chain (e.g.
           -- @a@ in @\\(a : Num) (plaintext : seq a Bool) → …@) and
           -- wrapping them would feed @Except String Num@ into the
           -- @seq a@ position.
           let typeIxs = typeArgPositionsBinders params
           translateBindersSelective typeIxs params
             (\bts -> do
                body' <- translateTermLet body
                pure (Lean.Lambda (concatMap bindTransToBinder bts) body'))

    App {} ->
      let (f, args) = asApplyAll t in
      case asGlobalDef f of
        Just ident -> translateIdentWithArgs ident args
        Nothing    -> Lean.App <$> translateTerm f <*> traverse translateTerm args

    Constant nm -> translateConstant nm

    Variable nm _tp -> do
      nenv <- view namedEnvironment <$> askTR
      case Map.lookup nm nenv of
        Just ident -> pure (Lean.Var ident)
        Nothing    -> Except.throwError (LocalVarOutOfBounds t)

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
translateTermLet t = do
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
    defs <- traverse translateTermUnshared shareTms
    body <- translateTerm t
    pure (foldr mkLet body (zip names defs))

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
       , _skipBinderWrap     = False
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
      tp'' = if shouldWrapBinder tp then wrapExcept tp' else tp'
      mainDecl = mkDefinitionWith Lean.Noncomputable univs name body' tp''
      -- Each 'prettyDecl' already ends with 'hardline'; 'vcat' adds
      -- another between elements, yielding one blank line between
      -- decls.
  pure $ if null auxDecls
    then Lean.prettyDecl mainDecl
    else vcat (map Lean.prettyDecl auxDecls) <> hardline <> Lean.prettyDecl mainDecl
