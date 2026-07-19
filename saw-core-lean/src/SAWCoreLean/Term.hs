{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

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
    -- (Export list trimmed by the 2026-07-14 release audit to the
    -- names external modules actually consume.)
  , translateTerm
  , translateTermLetWithShape
  , adaptToRuntime
  , translatedTermLean
  , topLevelDefConvention
  , translateDefDoc
  , translateDefDocWithArity
  , translateDefDocWithTelescope
  , leanPiSpineArity
  , leanPiSpineBinderTypes
  , TelescopeFp(..)
  , telescopeFpMismatch
  , withRawTranslationMode
    -- * Decl construction
  , mkDefinitionWith
    -- * Phase β wrap helpers (exposed for the Cryptol module path
    --   so it can apply the same closed-value top-level fixup)
  , shouldWrapBinder
  , wrapExcept
    -- * OP-3 successor recognizer (Slice R0: inert, trace/test only;
    --   nothing in emission may depend on it until Slice R2)
  , FixClass(..)
  , classifyFixShape
  ) where

import           Control.Lens                 (over, set, view)
import           Control.Monad                (unless, zipWithM)
import qualified Control.Monad.Except         as Except
import           Control.Monad.Reader         (asks)
import           Control.Monad.State          (gets, modify)
import           Data.Foldable                (toList)
import qualified Data.IntMap.Strict           as IntMap
import qualified Data.IntSet                  as IntSet
import           Data.List                    (elemIndex, findIndex)
import qualified Data.Map                     as Map
import           Data.Map                     (Map)
import           Data.Maybe                   (fromMaybe, isJust, isNothing)
import qualified Data.Set                     as Set
import           Data.Set                     (Set)
import qualified Data.Text                    as Text
import qualified Debug.Trace
import           Prelude                      hiding (fail)
import           Prettyprinter                (Doc, hardline, vcat)
import           System.Environment           (lookupEnv)
import           System.IO.Unsafe             (unsafePerformIO)
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

import           SAWCoreLean.Contracts
import           SAWCoreLean.Convention
import           SAWCoreLean.FixRecognizer
import           SAWCoreLean.Monad
import           SAWCoreLean.SpecialTreatment
-- The historical 'isVariableHead' (kind-blind var-headed test) was
-- retired by the 2026-07-17 domain-map consolidation: every former
-- consumer now projects from 'classifyDomain', whose var-headed
-- arms are KIND-DIRECTED (Type-sort head kind -> value, Prop ->
-- raw). Its universe rationale lives on in the 'Domain' doc
-- (Convention.hs) as the Prop backstop contract.

-- | True when the head is an opaque local type family, e.g.
-- @p : (y : t) -> Eq t x y -> Sort u@ used as @p y pf@.
-- Such a term is type-producing, but Haskell cannot know whether
-- the family returns a value-domain type, a proposition, or a
-- higher universe. Keep it raw and let Lean check the motive.
isVariableHeadTypeFamily :: Term -> Bool
isVariableHeadTypeFamily t =
  case unwrapTermF (fst (asApplyAll t)) of
    Variable _ fty -> case snd (asPiList fty) of
      ret | Just _ <- asSort ret -> True
      _                          -> False
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
typeArgPositionsBinders = go 0
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
  | isVariableHeadTypeFamily t = pure True
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
          in nArgs < length binders || isJust (asSort ret)

translateBinder' :: TermTranslationMonad m => VarName -> Term ->
                    (BindTrans -> m a) -> m a
translateBinder' = translateBinderAt Nothing

-- | Introduce a SAW binder, optionally at a position declared by the
-- surrounding function convention (plan Slice 3). @'Nothing'@
-- reproduces the historical flag-driven behaviour EXACTLY
-- ('translateBinder''). @'Just' ρ@ overrides only the outer wrap
-- decision and the recorded Γ position:
--
--   * 'ExpectRuntimeValue'          → wrap the binder type in
--     @Except String@;
--   * 'ExpectRaw' / 'ExpectFunctionPosition' → keep the binder type
--     raw (a function type never wraps its outer arrow).
--
-- A sort-typed binder always takes the universe-allocating sort path
-- regardless of ρ; a convention that demands a runtime value for a
-- sort binder is a contradiction and throws 'ForbiddenAdaptation'
-- (never wrap a sort).
translateBinderAt :: TermTranslationMonad m =>
                     Maybe ExpectedPosition -> VarName -> Term ->
                     (BindTrans -> m a) -> m a
translateBinderAt mrho vn ty f = do
  -- The convention override, if any, collapses to a single wrap
  -- decision applied in place of the flag-driven legacy predicate.
  let mOverrideWrap = case mrho of
        Nothing                         -> Nothing
        Just ExpectRuntimeValue         -> Just True
        Just (ExpectRaw _)              -> Just False
        Just (ExpectFunctionPosition _) -> Just False
  case (asSort ty, mrho) of
    (Just _, Just ExpectRuntimeValue) ->
      Except.throwError (ForbiddenAdaptation
        (Text.pack (show ExpectRuntimeValue))
        (Text.pack "sort-typed binder (a sort never wraps in Except String)"))
    _ -> pure ()
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
      -- When the surrounding function convention declares this
      -- sort-typed binder a TYPE position ('RawTypePosition' — the
      -- @a@ in @\(a : sort 0) (x : a) -> …@), the universe it
      -- allocates must use the same 'sortBinderMode' the legacy
      -- 'translateBindersSelective' index-binder path sets: Phase-β
      -- enters a type binder as 'SortBinderAsType', otherwise
      -- 'SortBinderAsSort'. Scoped to THIS binder's type translation
      -- only — the continuation 'f' runs under the surrounding
      -- reader, matching the legacy per-binder reset. For every other
      -- @ρ@ (and 'Nothing', the legacy 'translateBinder'' callers) the
      -- surrounding 'sortBinderMode' is read unchanged.
      phase <- phaseBetaEnabled
      let applyMode = case mrho of
            Just (ExpectRaw RawTypePosition) ->
              localTR (set sortBinderMode
                         (if phase then SortBinderAsType else SortBinderAsSort))
            _ -> id
      applyMode $ do
        -- Body and type walks may both encounter this binder. Memoize
        -- on 'vn' so we allocate one universe per logical SAWCore
        -- variable, not one per syntactic occurrence.
        memo <- gets (view universeBinderAssignments)
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
      let ambientWrap = phase && shouldWrapBinder ty && not skipWrap && not inRecCase
          t' = if fromMaybe ambientWrap mOverrideWrap
                  then wrapExcept t
                  else t
      pure (t', Nothing)
  let bindUniv = maybe id (over boundUniverses . Map.insert vn) mUniv
  -- Track whether the binder type wrapped in 'Except String', so
  -- recursor-scrutinee emission can tell whether the variable
  -- arrives wrapped or raw. Sort-typed binders never wrap.
  skipWrap <- view skipBinderWrap <$> askTR
  inRecCase <- view inRecursorCaseBinder <$> askTR
  phase <- phaseBetaEnabled
  let ambientBinderWrap = phase && shouldWrapBinder ty && not skipWrap && not inRecCase
      binderWrapped =
        isNothing (asSort ty)
        && fromMaybe ambientBinderWrap mOverrideWrap
  -- Γ record: the binder's Phase-β representation. (A declared ρ from
  -- 'mrho' governs the wrap decision above; positions are demanded
  -- through conventions, not stored per binder.)
  let repr = if binderWrapped then BindingWrapped else bindingShapeOfType ty'
  localTR bindUniv $
    withSAWVar vn $ \n' ->
      localTR (withBindingInfo n' (BindingInfo repr)) $
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
    localTR (withBindingInfo n'
               (BindingInfo (bindingShapeOfType ty))) $
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

-- | Like 'translateIdentToIdent' but always FULLY QUALIFIED — the
-- implicitly-opened-module shortening is deliberately skipped.
-- Term-position short names are safe because Lean's term elaborator
-- disambiguates colliding interpretations by type (and errors loudly
-- on ties), but COMMAND-position references (the constructor-order
-- assertions, plan Slice 6.2) have no expected type to disambiguate
-- with: a short @Stream@ is ambiguous against Lean core's @Stream@
-- at command level. Qualification names the support-library constant
-- the assertion pins, unambiguously.
translateIdentToQualifiedIdent ::
  TermTranslationMonad m => Ident -> m (Maybe Lean.Ident)
translateIdentToQualifiedIdent i = do
  treatment <- atUseSite <$> findSpecialTreatment i
  case treatment of
    UsePreserve -> do
      mm <- view sawModuleMap <$> askTR
      let short = escapeIdent (Lean.Ident (identName i))
          scopedShort = case resolveNameInMap mm i of
            Just (ResolvedCtor c) ->
              let dtShort =
                    Text.unpack (toShortName (nameInfo (ctorDataType c)))
              in Lean.Ident (dtShort ++ "." ++ identName i)
            _ -> short
      pure (Just (qualify (translateModuleName (identModule i)) scopedShort))
    UseRename mTargetMod targetName _ ->
      pure $ Just $ maybe targetName (`qualify` targetName) mTargetMod
    UseRenameUniv mTargetMod targetName _ ->
      pure $ Just $ maybe targetName (`qualify` targetName) mTargetMod
    UseMacro{}         -> pure Nothing
    UseMapsToWrapped{} -> pure Nothing
    UseReject reason   ->
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
            [ maybe origTerm Lean.Var (lookup pos subs)
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
      bound <- adaptToRuntime t
      pure (Lean.App bindVar [bound, lam])
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

etaExpandWrappedFunctionResult ::
  TermTranslationMonad m => Term -> Lean.Term -> m Lean.Term
etaExpandWrappedFunctionResult fty fn = do
  let (binders, _) = asPiList fty
      pureWrap = phaseBetaResultIsValue fty
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
           -- Plan Slice 4b: eta formals at the convention's declared
           -- representations. No source actuals are supplied here, so
           -- the polymorphic-instantiation lookup never fires — every
           -- variable-headed formal is a raw value formal. A Nat
           -- 'IndexArg' formal stays raw ('shouldWrapBinder Nat' was
           -- always False on this path).
           etaModes = phaseBetaArgModesFor fty []
           expectedWrapped =
             [ mode == RawValueArg
             | mode <- etaModes
             ]
           shouldBind =
             [ phaseBetaBindFromMode ix typeIxs mode wrapped
             | (ix, (mode, wrapped)) <-
                 zip [0 :: Int ..] (zip etaModes expectedWrapped)
             ]
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
-- NOTE: the legacy 'argumentBindPlan' / 'argumentBindPlanFromWrapped'
-- and the emitted-Lean-type instantiation predicate
-- ('polymorphicFormalInstantiatedExpected') are deleted (plan Slice
-- 4b). The bind plan derives from the declared convention
-- ('phaseBetaArgModesFor' + 'phaseBetaBindFromMode'); equivalence was
-- proven corpus-wide by the two-oracle inert step before the swap.
-- No shape or bind decision is inferred from emitted Lean TERMS any
-- more. Two type-classification self-mirrors remain
-- ('bindingShapeOfType' at binder sites; the Except/Pi peel in
-- 'applyKnownFunctionWithShape') — they classify types the translator
-- itself just emitted from known source types, and are 4c demotion
-- targets. Do not add new consumers of either.

-- | For a formal whose declared type is a bare parameter variable
-- (@x : α@ with @α@ bound earlier in the same telescope), look up the
-- SUPPLIED type actual instantiating that parameter. 'Nothing' when
-- the actual is not supplied (partial application cut before the type
-- argument) or the formal's type is not a bare telescope variable
-- (var-headed applications like @α x@ stay residual-assumed).
varHeadedInstantiation ::
  [(VarName, Term)] -> [Term] -> Int -> Term -> Maybe Term
varHeadedInstantiation binders srcArgs ix bty =
  case unwrapTermF bty of
    Variable vn _ -> do
      paramIx <- findIndex (\(vn', _) -> vn' == vn) binders
      if paramIx < ix && paramIx < length srcArgs
         then Just (srcArgs !! paramIx)
         else Nothing
    _ -> Nothing

-- | Direct a var-headed formal's mode by the domain of its
-- INSTANTIATING type actual — the same domain analysis 'modeFor'
-- applies to a concrete formal type, applied to the actual instead
-- (debts slice; generalizes the Pi-only
-- @polymorphicFormalInstantiatedExpectedSrc@ predicate of plan Slice
-- 4b). The actual's variables belong to the CALLER's context, so it
-- is classified by head form only — never re-looked-up in this
-- callee's telescope. A variable actual (nested polymorphism, the
-- caller's own type parameter) lands in the value-domain residual,
-- the same assumption the un-supplied case carries.
instantiationMode :: Term -> ArgMode
instantiationMode inst = case classifyDomain inst of
  DRawType  -> TypeArg
  DRawProp  -> PropositionArg
  -- A Pi instantiation carries its DECLARED convention derived from
  -- the instantiating Pi itself (2026-07-18 eta-adaptation design:
  -- the value side must read the same authority the type side's Pi
  -- translation uses — FunctionArg Nothing structural delivery let
  -- raw-target function values reach wrapped-arrow dictionary
  -- slots, the rev.cry intNeg elaboration failure).
  DFunction -> FunctionArg (Just (piFunctionConvention inst))
  DNat      -> IndexArg
  DValue    -> RawValueArg
  -- Var-headed instantiations (nested polymorphism — the caller's
  -- own type parameter) keep the value-domain residual for BOTH
  -- kinds: RawValueArg's bind-iff-wrapped discipline is inert for
  -- raw actuals, so a Prop-kinded family's (always-raw) values
  -- splice unchanged. Not a kind-directed cell change.
  DVarValue -> RawValueArg
  DVarRaw   -> RawValueArg

-- | Derive the ordinary Phase-β definition convention's argument
-- modes from the callee's SAWCore Pi type plus the supplied actuals
-- (calculus §Callee Conventions: a convention maps "a callee plus
-- already known type information" to argument positions). The callees
-- on this path are RAW-formal Lean targets (bvAdd-family primitives),
-- so the modes' bind disciplines are ('phaseBetaBindFromMode'):
--
--   * 'RawValueArg' (concrete value formals) and 'IndexArg'
--     (Nat formals, index binders): bind only a wrapped
--     (runtime-computed) actual — a raw actual splices directly;
--   * types, propositions, function formals: splice raw, never bind.
--
-- A var-headed formal (@x : α@) is INSTANTIATION-DIRECTED (debts
-- slice): when the type actual instantiating @α@ is supplied, the
-- mode is the actual's own domain ('instantiationMode' — a Pi
-- instantiation is a function position, a Nat instantiation an index
-- position, and so on). Only when the instantiation is genuinely
-- unavailable (type actual not supplied, or the formal's type is a
-- var-headed APPLICATION rather than a bare parameter) does the
-- value-domain residual assumption apply — sound for every
-- instantiation at supplied positions (bind-iff-wrapped keys off the
-- actual's recorded shape, and function values deliver structurally,
-- never wrapped), an assumption only for the eta-declared
-- representation of MISSING formals in partial applications.
phaseBetaArgModesFor :: Term -> [Term] -> [ArgMode]
phaseBetaArgModesFor fty srcArgs =
  [ modeFor ix bty | (ix, (_, bty)) <- zip [0 :: Int ..] binders ]
  where
    (binders, _) = asPiList fty
    typeIxs = typeArgPositions fty
    modeFor ix bty
      | ix `elem` typeIxs =
          if isJust (asSort bty) then TypeArg else IndexArg
      | otherwise = case classifyDomain bty of
          -- Num is Cryptol's singleton width/index CLASSIFIER, not
          -- a value-domain computation — the type-argument family,
          -- never bound; 'DRawType' covers both sorts and Num.
          DRawType  -> TypeArg
          DRawProp  -> PropositionArg
          DFunction -> FunctionArg Nothing
          DNat      -> IndexArg
          DValue    -> RawValueArg
          -- Var-headed formals: instantiation-directed where the
          -- type actual is supplied (see the function doc); the
          -- value-domain residual otherwise (discipline-inert for
          -- raw actuals — see 'instantiationMode').
          _ | Just inst <- varHeadedInstantiation binders srcArgs ix bty ->
                instantiationMode inst
            | otherwise -> RawValueArg

-- | The bind discipline each mode implies on the raw-formal
-- ordinary-definition path. See 'phaseBetaArgModesFor'.
phaseBetaBindFromMode :: Int -> [Int] -> ArgMode -> Bool -> Bool
phaseBetaBindFromMode ix typeIxs mode actualWrapped
  | ix `elem` typeIxs = False
  | otherwise = case mode of
      -- Bind-iff-wrapped (debts slice): a raw actual at a raw Lean
      -- formal splices directly; only a wrapped (runtime-computed)
      -- actual binds. The eta paths are unaffected — they DECLARE
      -- their missing formals wrapped, so @actualWrapped@ is True
      -- there by construction. (The legacy plan bound raw actuals
      -- too, pure-lift-then-bind — identity, but monadic noise.)
      RawValueArg -> actualWrapped
      IndexArg    -> actualWrapped
      _           -> False

-- | Argument modes for a phase-β FUNCTION VALUE callee (plan Slice 4c
-- step 1) — a bound variable or constant whose own emitted type
-- carries phase-β formals. A DIFFERENT family from
-- 'phaseBetaArgModesFor''s raw-formal Lean targets: here a
-- 'RawValueArg' mode means the emitted formal is WRAPPED (the value
-- formal of a phase-β function), and dependent/var-headed formals
-- mirror the un-substituted emitted type — raw, adapting by binding
-- only wrapped actuals ('IndexArg' discipline). This is deliberately
-- the exact source-level mirror of the historical
-- 'peelLeanPiTypes'/'isExceptStringType' inspection it will replace;
-- the inert assert in 'applyKnownFunctionWithShape' adjudicates
-- equivalence across the corpus before any swap.
phaseBetaFunctionValueModesFor :: Term -> [ArgMode]
phaseBetaFunctionValueModesFor fty =
  [ modeFor ix bty | (ix, (_, bty)) <- zip [0 :: Int ..] binders ]
  where
    (binders, _) = asPiList fty
    typeIxs = typeArgPositions fty
    modeFor ix bty
      | ix `elem` typeIxs =
          if isJust (asSort bty) then TypeArg else IndexArg
      | otherwise = case classifyDomain bty of
          DRawType  -> TypeArg
          DRawProp  -> PropositionArg
          DFunction -> FunctionArg Nothing
          DNat      -> IndexArg
          DValue    -> RawValueArg
          -- Var-headed formals of Type-sort kind: this family's
          -- emitted Pi WRAPS them (the function value's formal is a
          -- phase-β value slot), unlike the raw-target family where
          -- they bind. An earlier candidate special-cased them raw
          -- and the oracle rejected it on the smoketest (fix/iterate
          -- shapes peel Except at var-headed slots).
          DVarValue -> RawValueArg
          -- Prop-kinded family formals are proof slots: raw, never
          -- wrapped by the emitted Pi (kind-directed cell (h);
          -- 'IndexArg' discipline = splice raw, bind only wrapped).
          DVarRaw   -> IndexArg

-- | Convention-internal predicate (plan Slice 7), consulted ONLY by
-- 'phaseBetaResultIsValue' — never a standalone position authority.
-- A raw SAW function whose return type is Nat can still be a
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

-- | Calculus §Callee Conventions: THE value-domain result rule of the
-- ordinary Phase-β convention family — a callee's (fully applied)
-- result is a runtime value, and therefore Except-wrapped, iff its
-- source return type is value-domain ('shouldWrapBinder'), var-headed
-- (a polymorphic result instantiated by the caller), or a Nat computed
-- from a value input ('natValueResult'). This is the single authority;
-- every consumer (the application paths, partial-op contracts, eta
-- expansion, the Pi type translator's body wrap, the recursor motive
-- convention) reads it rather than restating the disjunction (plan
-- Slice 7 centralization — the disjuncts are convention-internal
-- predicates, not position authorities).
phaseBetaResultIsValue :: Term -> Bool
phaseBetaResultIsValue fty =
  case classifyDomain ret of
    DValue    -> True
    -- Kind-directed (2026-07-17 audits, condition 3): the historical
    -- 'isVariableHead ret' disjunct wrapped EVERY var-headed result
    -- with no kind check; under 'classifyDomain' only Type-sort-
    -- kinded heads are value results, and a Prop-kinded family
    -- result is a proof (raw) — the deliberate cell-(h) fix.
    DVarValue -> True
    DNat      -> natValueResult fty
    _         -> natValueResult fty
  where
    (_, ret) = asPiList fty

-- | The result-shape stamp of the ordinary Phase-β definition
-- convention ('phaseBetaArgModesFor' family) — convention-internal
-- (plan Slice 7): consulted only where that convention is the
-- declared one (the ordinary application paths and the partial-op
-- contracts), never as a free-floating shape oracle. Function iff
-- partially applied or Pi result; wrapped iff
-- 'phaseBetaResultIsValue'; raw otherwise.
phaseBetaResultShape :: Term -> Int -> BindingShape
phaseBetaResultShape fty nApplied
  | nApplied < length binders = BindingFunction
  | phaseBetaResultIsValue fty = BindingWrapped
  | isJust (asPi ret) = BindingFunction
  | otherwise = BindingRaw
  where
    (binders, ret) = asPiList fty

-- | The TRUTHFUL result stamp for a raw-mode application (debts
-- slice). Raw translation mode never Except-wraps anything, so the
-- only honest shapes are function (partial application or Pi result)
-- and raw. Stamping 'phaseBetaResultShape' here — as the raw-mode
-- application path historically did — produced records claiming
-- 'BindingWrapped' for bare raw applications, the stamp/emission
-- divergence that forced the raw-mode pipeline guards
-- ('lowerRawLogicalCalleeRawMode', unsafeAssert's raw-mode arm).
rawModeResultShape :: Term -> Int -> BindingShape
rawModeResultShape fty nApplied
  | nApplied < length binders = BindingFunction
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
              inRecCase <- view inRecursorCaseBinder <$> askTR
              -- Slice 3b: declare the convention ONCE and push it down
              -- through 'translateAt' — the dependent index/type
              -- binders join the non-dependent value binders migrated in
              -- 3a, so no guard remains (this reproduces the legacy
              -- 'translateBindersSelective' path by construction, moving
              -- authority to the declared convention).
              --
              -- Convention-internal use of 'shouldWrapBinder' (plan
              -- Slice 3.4): the position of each binder is exactly the
              -- decision the legacy path would make here — an index
              -- binder (in 'typeIxs') is 'ExpectRaw RawIndexPosition', a
              -- sort-typed index binder is 'ExpectRaw RawTypePosition',
              -- a wrap-worthy value binder is 'ExpectRuntimeValue', and
              -- any other value binder stays 'ExpectRaw RawValuePosition'.
              let mkPos ix ty
                    | ix `elem` typeIxs, isJust (asSort ty)
                    = ExpectRaw RawTypePosition
                    | ix `elem` typeIxs
                    = ExpectRaw RawIndexPosition
                    | shouldWrapBinder ty
                        && not surroundingCtx && not inRecCase
                    = ExpectRuntimeValue
                    | otherwise = ExpectRaw RawValuePosition
                  conv = FunctionConvention
                           [ mkPos ix ty | (ix, (_, ty)) <- zip [0 ..] params ]
                           ExpectRuntimeValue
                  rho = ExpectFunctionPosition (Just conv)
              -- Translate in place (never via the sharing lookup): the
              -- legacy path destructured this lambda inline, so
              -- stamping/tracing the unshared translation preserves
              -- byte-identical output even for shared terms.
              result <- translateTermUnsharedWithShapeAt (Just rho) t
              tracePositionAt rho t result
              pure (ttLean result)
       _ -> translateTerm t

-- | Convention-internal (plan Slice 7): the value-slot test of the
-- function-convention derivations ('recursorMotiveFunctionConvention',
-- 'translateFunctionConventionBinders', 'recursorPostArgs' via the
-- declared convention) — a binder is a runtime-value slot iff it is
-- not a type index and its type is value-domain (var-headed counts as
-- value: the instantiation is the caller's). Not a standalone
-- position authority.
functionConventionValueSlot :: [Int] -> Int -> Term -> Bool
functionConventionValueSlot typeIxs ix ty =
     ix `notElem` typeIxs
  && case classifyDomain ty of
       DValue    -> True
       -- Kind-directed (2026-07-17 audits): the historical
       -- 'isVariableHead' disjunct counted every var-headed type as
       -- value; only Type-sort-kinded heads are — a Prop-kinded
       -- family slot is a proof slot (raw), cell (h).
       DVarValue -> True
       _         -> False

-- | Convention-internal (plan Slice 7): the type-domain test "is this
-- SAW type a value-domain type" with var-headed types counting as
-- value. Consulted by the structural-recursor-field convention (case
-- handler field shadows: which constructor fields get the
-- @Pure.pure@ let-shadow and the wrapped let annotation). Despite
-- the name, the argument is a TYPE, not a function; the function
-- RESULT rule is 'phaseBetaResultIsValue'. Not a standalone position
-- authority.
functionConventionResultIsValue :: Term -> Bool
functionConventionResultIsValue ty =
  case classifyDomain ty of
    DValue    -> True
    DVarValue -> True  -- kind-directed; see 'functionConventionValueSlot'
    _         -> False

-- | Calculus §Recursors (plan Slice 6.1): the declared position of a
-- fully-applied recursor's result — the single field
-- 'recursorConvention' derives its result mode and final shape from,
-- and the position the motive convention consumes. Classified from
-- the recursor motive's body TYPE by the same domain analysis the
-- argument-mode tables apply to formal/instantiating types
-- ('phaseBetaArgModesFor' / 'instantiationMode'), with the two
-- refinements the recursor convention declares:
--
--   * a Nat-typed motive body is a runtime VALUE when the recursor
--     eliminates into a non-Prop sort: the recursor COMPUTES that Nat
--     from a runtime scrutinee (the recursor instance of the
--     'natValueResult' rule), it does not stand in an index slot.
--     Prop-sort elimination keeps Nat raw with the rest of the
--     logical family.
--   * a var-headed type-family application (@p y pf@ where @p@'s type
--     returns a Sort) stays raw: Haskell cannot know whether the
--     family instantiates to a value-domain type, a proposition, or a
--     higher universe — commit to nothing and let Lean check the
--     motive.
--
-- A Pi motive body is a function position that always carries its
-- declared convention ('recursorMotiveFunctionConvention') — never
-- @ExpectFunctionPosition Nothing@.
recursorMotiveResultPosition :: Sort -> Term -> ExpectedPosition
recursorMotiveResultPosition elimSort motiveBody =
  case classifyDomain motiveBody of
    DRawType  -> ExpectRaw RawTypePosition
    DRawProp  -> ExpectRaw RawPropositionPosition
    DFunction ->
      ExpectFunctionPosition
        (Just (recursorMotiveFunctionConvention motiveBody))
    DNat
      | elimSort /= propSort -> ExpectRuntimeValue
      | otherwise            -> ExpectRaw RawIndexPosition
    DValue    -> ExpectRuntimeValue
    -- Kind-directed rule (2026-07-17 design + audits; the Either@core
    -- / Stream@core fix): a var-headed motive body whose head kind
    -- results in a Type sort is a VALUE the recursor computes — it
    -- wraps and the wrapped-scrutinee Bind.bind path applies. Gated
    -- on non-Prop elimination like the Nat arm (audit condition 1);
    -- Prop-kinded heads stay raw. The pre-classifier rule sent every
    -- var-headed body raw, which over-rejected (bare 'a' motives —
    -- Prelude.either, streamGet) against every other site's answer.
    DVarValue
      | elimSort /= propSort -> ExpectRuntimeValue
      | otherwise            -> ExpectRaw RawValuePosition
    DVarRaw   -> ExpectRaw RawValuePosition

-- | The declared function convention of a function-motive recursor
-- (plan Slice 6.1): binder positions from the same value-slot
-- analysis every function convention uses
-- ('functionConventionValueSlot'), result position mirroring the Pi
-- type translator's body-wrap rule (gamma.8's @valueBody@: a
-- value-domain or var-headed body wraps, and a Nat body wraps when
-- the function consumes a value input — 'natValueResult', both
-- convention-internal predicates here, not standalone authorities).
-- The emitted recursor call inhabits the translated motive Pi type,
-- so this convention is the truthful record of what a fully-applied
-- function-motive recursor produces.
recursorMotiveFunctionConvention :: Term -> FunctionConvention
recursorMotiveFunctionConvention = piFunctionConvention

-- | The generic Pi→convention derivation (2026-07-18 rename of the
-- motive-specific name: the analysis was always generic over a Pi
-- type). Also the declared convention a Pi INSTANTIATION carries at
-- 'FunctionArg' slots ('instantiationMode', eta-adaptation design).
piFunctionConvention :: Term -> FunctionConvention
piFunctionConvention fty =
  FunctionConvention
    [ binderPos ix bty | (ix, (_, bty)) <- zip [0 :: Int ..] binders ]
    resultPos
  where
    (binders, ret) = asPiList fty
    typeIxs = typeArgPositions fty
    binderPos ix bty
      | ix `elem` typeIxs =
          if isJust (asSort bty)
             then ExpectRaw RawTypePosition
             else ExpectRaw RawIndexPosition
      | functionConventionValueSlot typeIxs ix bty = ExpectRuntimeValue
      -- 2026-07-18 eta part 3b: a Pi-typed binder is a FUNCTION
      -- position carrying its own derived convention (recursively),
      -- so function actuals (natToInt at Num#rec post slots)
      -- eta-adapt instead of splicing raw.
      | isJust (asPi bty) =
          ExpectFunctionPosition (Just (piFunctionConvention bty))
      | otherwise = ExpectRaw RawValuePosition
    resultPos
      | Just _ <- asSort ret = ExpectRaw RawTypePosition
      | Just _ <- asEq ret = ExpectRaw RawPropositionPosition
      | isCryptolNumType ret = ExpectRaw RawTypePosition
      | phaseBetaResultIsValue fty = ExpectRuntimeValue
      | Just _ <- asNatType ret = ExpectRaw RawIndexPosition
      | otherwise = ExpectRaw RawValuePosition

wrappedHelperFunctionValueSlot :: [Int] -> Int -> Term -> Bool
wrappedHelperFunctionValueSlot typeIxs ix ty =
     ix `notElem` typeIxs
  && isNothing (asSort ty)
  && isNothing (asEq ty)
  && isNothing (asPi ty)
  && not (isCryptolNumType ty)

wrappedHelperFunctionResultIsValue :: Term -> Bool
wrappedHelperFunctionResultIsValue ty =
     isNothing (asSort ty)
  && isNothing (asEq ty)
  && isNothing (asPi ty)
  && not (isCryptolNumType ty)

translateFunctionConventionBindersWith ::
  TermTranslationMonad m =>
  ([Int] -> Int -> Term -> Bool) ->
  [Int] ->
  [(VarName, Term)] ->
  ([Lean.Binder] -> [TranslatedTerm] -> m a) ->
  m a
translateFunctionConventionBindersWith valueSlot typeIxs params0 k =
  go 0 [] [] params0
  where
    go _ binders args [] = k (reverse binders) (reverse args)
    go ix binders args ((vn, ty) : rest) = do
      tyLean <- localTR (set skipBinderWrap False) (translateTerm ty)
      let wrapped = valueSlot typeIxs ix ty
          binderTy = if wrapped then wrapExcept tyLean else tyLean
      ident <-
        if vnName vn == "_"
           then freshVariant (Lean.Ident ("η_arg_" ++ show ix))
           else translateLocalIdent (vnName vn)
      withUsedLeanIdent ident $
        localTR ( over namedEnvironment (Map.insert vn ident)
                . withBindingInfo ident
                    (BindingInfo (bindingShapeOfType binderTy))) $ do
          let binder = Lean.Binder Lean.Explicit ident (Just binderTy)
          let argShape = if wrapped then BindingWrapped
                                    else bindingShapeOfType binderTy
              arg = TranslatedTerm (Lean.Var ident) argShape
          go (ix + 1) (binder : binders) (arg : args) rest

translateFunctionConventionBinders ::
  TermTranslationMonad m =>
  [Int] ->
  [(VarName, Term)] ->
  ([Lean.Binder] -> [TranslatedTerm] -> m a) ->
  m a
translateFunctionConventionBinders =
  translateFunctionConventionBindersWith functionConventionValueSlot

translateFunctionToWrappedFormal ::
  TermTranslationMonad m =>
  Text.Text ->
  Term ->
  m Lean.Term
translateFunctionToWrappedFormal primitiveName fnTerm =
  case unwrapTermF fnTerm of
    Lambda{} -> do
      let (params, body) = asLambdaList fnTerm
          mFunType = case termSortOrType fnTerm of
            Right fty -> Just fty
            Left{}    -> Nothing
          typeIxs = maybe (typeArgPositionsBinders params)
                          typeArgPositions
                          mFunType
          resultIsValue = case mFunType of
            Just fty ->
              let (_, retTy) = asPiList fty
              in wrappedHelperFunctionResultIsValue retTy
            Nothing -> True
      typeBody <- isTypeProducing body
      if typeBody
         then Except.throwError (RejectedPrimitive primitiveName
                "wrapped helper expected a value-level function argument, but the lambda body is type-producing")
         else if not resultIsValue
         then Except.throwError (RejectedPrimitive primitiveName
                "wrapped helper expected a value-level function argument with a value result")
         else do
           -- Slice 3b: declare the convention ONCE and push it down —
           -- the dependent index/type binders join the non-dependent
           -- value slots migrated in 3a, so no guard remains.
           --
           -- Convention-internal use of 'wrappedHelperFunctionValueSlot'
           -- (plan Slice 3.4): the position of each slot is exactly the
           -- decision the legacy path would make — an index binder (in
           -- 'typeIxs') is 'ExpectRaw RawIndexPosition', a sort-typed
           -- index binder is 'ExpectRaw RawTypePosition', a value slot
           -- (including @Nat@) is 'ExpectRuntimeValue', and any other
           -- binder stays 'ExpectRaw RawValuePosition'.
           let mkPos ix ty
                 | ix `elem` typeIxs, isJust (asSort ty)
                 = ExpectRaw RawTypePosition
                 | ix `elem` typeIxs
                 = ExpectRaw RawIndexPosition
                 | wrappedHelperFunctionValueSlot typeIxs ix ty
                 = ExpectRuntimeValue
                 | otherwise = ExpectRaw RawValuePosition
               conv = FunctionConvention
                        [ mkPos ix ty | (ix, (_, ty)) <- zip [0 ..] params ]
                        ExpectRuntimeValue
               rho = ExpectFunctionPosition (Just conv)
           -- Translate in place (never via the sharing lookup): the
           -- legacy path destructured this lambda inline.
           result <- translateTermUnsharedWithShapeAt (Just rho) fnTerm
           tracePositionAt rho fnTerm result
           pure (ttLean result)
    _ ->
      case termSortOrType fnTerm of
        Right fty
          | (params, retTy) <- asPiList fty
          , not (null params)
          , wrappedHelperFunctionResultIsValue retTy -> do
              fnTranslated <- translateTermWithShape fnTerm
              let typeIxs = typeArgPositions fty
              case (unwrapTermF fnTerm, ttShape fnTranslated) of
                (App{}, BindingFunction) ->
                  pure (ttLean fnTranslated)
                _ ->
                  translateFunctionConventionBindersWith
                    wrappedHelperFunctionValueSlot typeIxs params $
                    \binders args -> do
                      let shouldBind = map (isWrappedShape . ttShape) args
                      body <- buildLifted (ttLean fnTranslated) True shouldBind args
                      pure (Lean.Lambda binders body)
        _ ->
          Except.throwError (RejectedPrimitive primitiveName
            "wrapped helper expected a value-level function argument with a value result")

translateFunctionWithNatLtWrappedResult ::
  TermTranslationMonad m =>
  Text.Text ->
  Lean.Term ->
  Bool ->
  Term ->
  m Lean.Term
translateFunctionWithNatLtWrappedResult primitiveName nLean expectsSourceProof fnTerm =
  case unwrapTermF fnTerm of
    Lambda {} ->
      case asLambdaList fnTerm of
        ([(idxName, _)], body)
          | not expectsSourceProof ->
              translateBinderWithLeanType idxName (Lean.Var (Lean.Ident "Nat")) $
                \idxBinder@(Lean.Binder _ idxLean _) -> do
                  let idxTerm = Lean.Var idxLean
                      proofTy = natLt idxTerm nLean
                  proofName <- freshVariantAvoiding
                    (Set.insert idxLean (leanTermIdents nLean))
                    (Lean.Ident "h_gen_bounds_")
                  let proofBinder =
                        Lean.Binder Lean.Explicit proofName (Just proofTy)
                  -- Record the binder's bound (i < n) in Γ's Nat-bounds
                  -- environment so downstream at-contract obligations
                  -- can interval-entail against it (OP-2).
                  bodyResult <-
                    localTR (over natBoundsEnv (Map.insert idxLean nLean))
                      (translateTermLetWithShape body)
                  bodyLean <- adaptToRuntime bodyResult
                  pure (Lean.Lambda [idxBinder, proofBinder] bodyLean)
        ([(idxName, _), (proofName, _)], body)
          | expectsSourceProof ->
              translateBinderWithLeanType idxName (Lean.Var (Lean.Ident "Nat")) $
                \idxBinder@(Lean.Binder _ idxLean _) ->
                  let idxTerm = Lean.Var idxLean
                      proofTy = natLt idxTerm nLean
                  in translateBinderWithLeanType proofName proofTy $
                    \proofBinder -> do
                      bodyResult <-
                        localTR (over natBoundsEnv (Map.insert idxLean nLean))
                          (translateTermLetWithShape body)
                      bodyLean <- adaptToRuntime bodyResult
                      pure (Lean.Lambda [idxBinder, proofBinder] bodyLean)
        _ ->
          Except.throwError (RejectedPrimitive primitiveName
            (if expectsSourceProof
                then "expected a generator function with exactly Nat and bounds-proof binders"
                else "expected a generator function with exactly one Nat binder"))
    _ ->
      Except.throwError (RejectedPrimitive primitiveName
        "expected a lambda generator function so Lean can receive checked index evidence")

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


-- | Lower an UNDER-APPLIED contract-bearing partial op to its
-- runtime-checked support wrapper (2026-07-18 design, audited): a
-- plain application of the wrapper to the supplied actuals at the
-- wrapper's declared modes (raw splice for Index/Type slots,
-- runtime adaptation for value slots). No obligations; the wrapper
-- itself reifies the excluded point as an Except throw. The result
-- is a function value (strictly under arity by the caller's guard).
lowerPartialOpRuntimeWrapper ::
  TermTranslationMonad m =>
  PartialOpContract -> [Term] -> m TranslatedTerm
lowerPartialOpRuntimeWrapper contract args = do
  actuals <- zipWithM translateOne (pocRuntimeWrapperModes contract) args
  let head_ = Lean.Var (pocRuntimeWrapper contract)
      app   = if null actuals then head_ else Lean.App head_ actuals
  pure (TranslatedTerm app BindingFunction)
  where
    translateOne mode a = case mode of
      RuntimeArg -> adaptToRuntime =<< translateTermWithShape a
      _          -> withRawTranslationMode (translateTerm a)

-- | Lower direct partial primitives through proof-carrying helpers.
-- Haskell constructs the visible nonzero contract and wires the checked
-- evidence into the helper call; it does not inspect or prove the divisor.
lowerPartialOpContract ::
  TermTranslationMonad m =>
  PartialOpContract ->
  Ident ->
  [Term] ->
  m TranslatedTerm
lowerPartialOpContract contract ident args = do
  argResults <- traverse translateTermWithShape args
  mm <- view sawModuleMap <$> askTR
  phase <- phaseBetaEnabled
  fty <- case resolveNameInMap mm ident of
    Just (ResolvedDef def)   -> pure (defType def)
    Just (ResolvedCtor ctor) -> pure (ctorType ctor)
    Just (ResolvedDataType _) ->
      Except.throwError (RejectedPrimitive (Text.pack (identName ident))
        "partial-operation contract unexpectedly resolved to a datatype")
    Nothing ->
      Except.throwError (RejectedPrimitive (Text.pack (identName ident))
        "partial-operation contract could not find the SAWCore source type")
  let (binders, _) = asPiList fty
      pureWrap = phase && phaseBetaResultIsValue fty
      -- Plan Slice 4b: bind plan from the derived convention (the
      -- raw checked helpers are ordinary raw-formal targets).
      derivedModes = phaseBetaArgModesFor fty args
      typeIxsFor = typeArgPositions fty
      shouldBind =
        if phase
           then take (length args)
                  ([ phaseBetaBindFromMode ix typeIxsFor mode wrapped
                   | (ix, (mode, wrapped)) <-
                       zip [0 :: Int ..]
                         (zip derivedModes
                              (map (isWrappedShape . ttShape) argResults))
                   ] ++ repeat False)
           else replicate (length args) False
      resultShape =
        if phase
           then phaseBetaResultShape fty (length args)
           else rawModeResultShape fty (length args)
  if length args /= length binders
     then Except.throwError (RejectedPrimitive (Text.pack (identName ident))
            "partial-operation contracts currently require a fully applied direct primitive")
     else case pocConvention contract of
       PartialOpRaw checkedName ->
         buildRawProofCarryingApplication
           resultShape
           (Lean.Var checkedName)
           pureWrap
           shouldBind
           argResults
           contract
       PartialOpWrapped checkedName argModes ->
         buildWrappedProofCarryingApplication
           (Lean.Var checkedName)
           argModes
           argResults
           contract

buildWrappedProofCarryingApplication ::
  TermTranslationMonad m =>
  Lean.Term ->
  [ArgMode] ->
  [TranslatedTerm] ->
  PartialOpContract ->
  m TranslatedTerm
buildWrappedProofCarryingApplication head_ argModes argResults contract = do
  actuals <- zipWithM partialOpActual argModes argResults
  tm <- lowerProofCarryingActuals
          (Lean.Ident "h_nonzero_")
          partialOpProofScript
          (Just (pocBuildProp contract))
          head_
          actuals
  pure (TranslatedTerm tm BindingWrapped)
  where
    -- The wrapped partial-op convention shares the checked-application
    -- interpretation: runtime slots adapt, and a WRAPPED actual at an
    -- index slot (a runtime-computed bitvector width) is sequenced
    -- through the error-preserving bind chain rather than escaping raw.
    partialOpActual RuntimeArg result =
      CheckedDirect <$> adaptToRuntime result
    partialOpActual IndexArg result = case ttShape result of
      BindingRaw      -> pure (CheckedDirect (ttLean result))
      BindingWrapped  -> pure (CheckedBindIndex (ttLean result))
      BindingFunction ->
        Except.throwError (ForbiddenAdaptation
          "IndexArg (raw index position)"
          "BindingFunction")
    partialOpActual mode _ =
      Except.throwError (RejectedPrimitive "partial operation"
        ("wrapped partial-op contract used argument mode "
         <> Text.pack (show mode)
         <> " outside its interpreter"))

buildRawProofCarryingApplication ::
  TermTranslationMonad m =>
  BindingShape ->
  Lean.Term ->
  Bool ->
  [Bool] ->
  [TranslatedTerm] ->
  PartialOpContract ->
  m TranslatedTerm
buildRawProofCarryingApplication resultShape head_ pureWrap shouldBind argResults contract = do
  tm <- go 0 argResults shouldBind []
  pure (TranslatedTerm tm resultShape)
  where
    bindVar = Lean.Var (Lean.Ident "Bind.bind")
    pureVar = Lean.Var (Lean.Ident "Pure.pure")
    argTerms = map ttLean argResults
    avoidIdents = Set.unions (leanTermIdents head_ : map leanTermIdents argTerms)

    go :: TermTranslationMonad m =>
          Int ->
          [TranslatedTerm] ->
          [Bool] ->
          [(Int, Lean.Ident)] ->
          m Lean.Term
    go _ [] _ subs = do
      let finalArgs =
            [ maybe origTerm Lean.Var (lookup pos subs)
            | (pos, origTerm) <- zip [0..] argTerms
            ]
          prop = pocBuildProp contract finalArgs
      unavailable <- view unavailableIdents <$> askTR
      let proofIdents = Set.union (leanTermIdents prop) unavailable
      withLocalProofObligationUsing
        (Lean.Ident "h_nonzero_")
        prop
        (`partialOpProofScript` proofIdents)
        $ \proof -> do
            let body = Lean.App head_ (finalArgs ++ [proof])
            pure (if pureWrap then Lean.App pureVar [body] else body)
    go pos (_ : rest) (False : bs) subs =
      go (pos + 1) rest bs subs
    go pos (t : rest) (True : bs) subs = do
      bname <- freshVariantAvoiding avoidIdents (Lean.Ident ("v_" ++ show pos))
      rest' <- go (pos + 1) rest bs ((pos, bname) : subs)
      let lam = Lean.Lambda
                  [Lean.Binder Lean.Explicit bname Nothing]
                  rest'
      bound <- adaptToRuntime t
      pure (Lean.App bindVar [bound, lam])
    go pos (_ : rest) [] subs =
      go (pos + 1) rest [] subs

-- | Lower direct proof-carrying applications through checked Lean helpers.
-- The source proof arguments are intentionally ignored: Haskell only emits
-- the corresponding Lean proposition and passes a proof variable checked by
-- Lean. It does not inspect the index arithmetic or trust SAW proof terms.
-- | Nat interval @[lo, hi]@ over an emitted index expression; @hi@ of
-- 'Nothing' means unbounded. OP-2's entailment domain
-- (doc/2026-07-12_obligation-placement-design.md, amended + audited).
data NatInterval = NatInterval Integer (Maybe Integer)

unboundedNat :: NatInterval
unboundedNat = NatInterval 0 Nothing

-- | The final dot-component of an emitted identifier. Arithmetic
-- helpers emit unqualified (artifacts @open@ the primitives
-- namespace) while the numeral macros emit fully qualified; matching
-- the base name covers both spellings of the same helper.
leanBaseName :: Lean.Ident -> String
leanBaseName (Lean.Ident s) =
  case break (== '.') s of
    (_, '.' : rest) -> leanBaseName (Lean.Ident rest)
    (chunk, _)      -> chunk

-- | Evaluate an emitted constant Nat expression (numeral macros and
-- literals) to its value.
evalNatConst :: Lean.Term -> Maybe Integer
evalNatConst tm = case tm of
  Lean.NatLit k | k >= 0 -> Just k
  Lean.IntLit k | k >= 0 -> Just k
  Lean.Var v -> case leanBaseName v of
    "zero_macro" -> Just 0
    "one_macro"  -> Just 1
    _            -> Nothing
  Lean.App (Lean.Var v) [a] -> case leanBaseName v of
    "natPos_macro" -> evalNatConst a
    "succ_macro"   -> (+ 1) <$> evalNatConst a
    "bit0_macro"   -> (* 2) <$> evalNatConst a
    "bit1_macro"   -> (\k -> 2 * k + 1) <$> evalNatConst a
    _              -> Nothing
  _ -> Nothing

-- | Interval of an emitted Nat index expression under the recorded
-- binder bounds. Propagates ONLY through the omega-closable operation
-- set fixed by the 2026-07-12 amendment audit: addNat, subNat (Nat
-- monus), mulNat with a constant operand, divNat/modNat (checked or
-- not) by a positive constant, and the numeral macros. minNat,
-- maxNat, and variable-times-variable mulNat are deliberately
-- unbounded — omega atomizes @Nat.min@/@Nat.max@ and nonlinear
-- products (kernel-checked audit witnesses), so treating them as
-- bounded would greenlight obligations the emitted evidence chain
-- cannot close. This must remain an UNDER-approximation of the chain.
natIntervalOf :: Map Lean.Ident Lean.Term -> Lean.Term -> NatInterval
natIntervalOf bounds = go
  where
    go tm
      | Just k <- evalNatConst tm = NatInterval k (Just k)
    go (Lean.Var v)
      | Just boundTm <- Map.lookup v bounds
      , Just n <- evalNatConst boundTm
      , n > 0 = NatInterval 0 (Just (n - 1))
    go (Lean.Let _ _ _ _ body) = go body
    go (Lean.App (Lean.Var v) as) = case (leanBaseName v, as) of
      ("addNat", [a, b]) ->
        let NatInterval la ha = go a
            NatInterval lb hb = go b
        in NatInterval (la + lb) ((+) <$> ha <*> hb)
      ("subNat", [a, b]) ->
        let NatInterval la ha = go a
            NatInterval lb hb = go b
        in NatInterval (maybe 0 (\ub -> max 0 (la - ub)) hb)
             ((\ua -> max 0 (ua - lb)) <$> ha)
      ("mulNat", [a, b])
        | Just k <- evalNatConst b ->
            let NatInterval la ha = go a
            in NatInterval (la * k) ((* k) <$> ha)
        | Just k <- evalNatConst a ->
            let NatInterval lb hb = go b
            in NatInterval (lb * k) ((* k) <$> hb)
      ("divNat", [a, b])
        | Just k <- evalNatConst b, k > 0 ->
            let NatInterval la ha = go a
            in NatInterval (la `div` k) ((`div` k) <$> ha)
      ("divNat_checked", [a, b, _pf])
        | Just k <- evalNatConst b, k > 0 ->
            let NatInterval la ha = go a
            in NatInterval (la `div` k) ((`div` k) <$> ha)
      ("modNat", [_a, b])
        | Just k <- evalNatConst b, k > 0 -> NatInterval 0 (Just (k - 1))
      ("modNat_checked", [_a, b, _pf])
        | Just k <- evalNatConst b, k > 0 -> NatInterval 0 (Just (k - 1))
      _ -> unboundedNat
    go _ = unboundedNat

-- | Does the recorded binder-bounds environment interval-entail the
-- @at@ contract's bound @i < n@? Both the length and index must be
-- 'CheckedDirect' (a wrapped actual is a runtime value with no static
-- interval), the length must be a constant, and the index's upper
-- bound must fall below it.
atBoundsEntailed ::
  Map Lean.Ident Lean.Term -> [CheckedActual] -> Bool
atBoundsEntailed bounds helperArgs = case helperArgs of
  (CheckedDirect nTm : _ty : _xs : CheckedDirect iTm : _)
    | Just nVal <- evalNatConst nTm
    , NatInterval _ (Just hi) <- natIntervalOf bounds iTm
    -> hi < nVal
  _ -> False

isAtIndexContract :: CheckedApplicationContract -> Bool
isAtIndexContract contract =
  cacModule contract == mkModuleName ["Prelude"]
    && cacName contract == "at"

-- | OP-2's two-lowering decision for the @at@ contract's index slot
-- (doc/2026-07-12_obligation-placement-design.md, amended + audited).
-- Interval-entailed positions keep the proof-carrying refinement
-- (atWithProof_checkedM + the OP-1 evidence chain, which provably
-- closes everything the interval rule admits); every other position —
-- eta formals, guard-dependent branch indices, runtime values —
-- lowers through 'atRuntimeCheckedM', whose out-of-range result is
-- SAWCore's own @at@ error semantics (@Prelude.sawcore:1563@:
-- @at n a v i = atWithDefault n a (error a "at: index out of bounds") v i@).
-- Binding audit conditions: this decision is gated on the @at@
-- contract identity and must NEVER move into the shared IndexArg
-- machinery (upd/slice/genWithProof have different out-of-range
-- meanings; atWithDefaultM keeps a genuine caller default), and the
-- accessor's error message is the bare Prelude string with nothing
-- interpolated.
lowerCheckedHelperArgsDecided ::
  TermTranslationMonad m =>
  CheckedApplicationContract ->
  [CheckedActual] ->
  m Lean.Term
lowerCheckedHelperArgsDecided contract helperArgs
  | isAtIndexContract contract = do
      bounds <- view natBoundsEnv <$> askTR
      if atBoundsEntailed bounds helperArgs
        then lowerCheckedApplicationHelperArgs contract helperArgs
        else lowerProofCarryingActuals
               (Lean.Ident "h_bounds_")
               boundsProofScript
               Nothing
               (Lean.Var (Lean.Ident "atRuntimeCheckedM"))
               helperArgs
  | otherwise = lowerCheckedApplicationHelperArgs contract helperArgs

lowerCheckedApplicationContract ::
  TermTranslationMonad m =>
  CheckedApplicationContract ->
  Ident ->
  [Term] ->
  m TranslatedTerm
lowerCheckedApplicationContract contract ident args = do
  helperArgs <- checkedApplicationHelperArgs (cacArgModes contract) args
  tm <- lowerCheckedHelperArgsDecided contract helperArgs
  -- The result shape is the contract's DECLARED result mode, not a
  -- hardcoded assumption.
  let shape = case cacResultMode contract of
        RuntimeResult    -> BindingWrapped
        RawResult _      -> BindingRaw
        FunctionResult _ -> BindingFunction
  pure (TranslatedTerm tm shape)
  where
    checkedApplicationHelperArgs =
      checkedApplicationHelperArgsFor ident

-- | Lower a prefix partial proof-carrying application to a function that emits
-- the same checked obligation once the missing arguments are supplied. This is
-- deliberately limited to missing raw/wrapped value arguments; missing source
-- proof and higher-order function arguments still reject until they have an
-- explicit proof-carrying convention.
lowerPartialCheckedApplicationContract ::
  TermTranslationMonad m =>
  CheckedApplicationContract ->
  Ident ->
  [Term] ->
  m TranslatedTerm
lowerPartialCheckedApplicationContract contract ident args = do
  mm <- view sawModuleMap <$> askTR
  fty <- case resolveNameInMap mm ident of
    Just (ResolvedDef def)   -> pure (defType def)
    Just (ResolvedCtor ctor) -> pure (ctorType ctor)
    Just (ResolvedDataType _) ->
      Except.throwError (RejectedPrimitive (Text.pack (identName ident))
        "checked-application contract unexpectedly resolved to a datatype")
    Nothing ->
      Except.throwError (RejectedPrimitive (Text.pack (identName ident))
        "checked-application contract could not find the SAWCore source type")
  let (sourceBinders, _) = asPiList fty
      suppliedCount = length args
      argModes = cacArgModes contract
      suppliedSourceVars =
        IntSet.fromList (map (vnIndex . fst) (take suppliedCount sourceBinders))
      missingSourceBinders = drop suppliedCount (take (cacArity contract) sourceBinders)
      missingBinderMentionsSupplied (_, ty) =
        not (IntSet.null (IntSet.intersection suppliedSourceVars (freeVars ty)))
  if length sourceBinders < cacArity contract
     then Except.throwError (RejectedPrimitive (Text.pack (identName ident))
            "checked-application source type has fewer binders than its contract arity")
     else if any missingBinderMentionsSupplied missingSourceBinders
     then Except.throwError (RejectedPrimitive (Text.pack (identName ident))
            "prefix checked-application binders depend on supplied arguments; this needs an explicit substitution-aware proof-carrying convention")
     else do
       suppliedHelperArgs <-
         checkedApplicationHelperArgsFor ident
           (take suppliedCount argModes)
           args
       withMissingCheckedApplicationBinders
         ident
         (drop suppliedCount argModes)
         missingSourceBinders
         $ \lambdaBinders missingHelperArgs -> do
             -- Missing args become lambda binders already emitted at
             -- their declared representation; they never need a bind.
             -- For the at contract, an eta-bound index formal carries
             -- no bound fact, so the OP-2 decision routes it through
             -- the runtime-checked accessor instead of fabricating
             -- in-lambda evidence.
             body <- lowerCheckedHelperArgsDecided contract
                       (suppliedHelperArgs ++ map CheckedDirect missingHelperArgs)
             pure (TranslatedTerm (Lean.Lambda lambdaBinders body) BindingFunction)

-- | The per-actual verdict of interpreting a checked-application
-- argument at its declared 'ArgMode' (plan Slice 4a).
-- 'CheckedBindIndex' is the calculus's error-preserving adapter for a
-- runtime-computed index demanded raw: the wrapped actual is
-- sequenced through 'Bind.bind' ahead of the bounds obligation, and
-- the bound raw variable is what BOTH the proposition and the checked
-- helper consume. The wrapped value is never opened and never
-- defaulted; its error case propagates through the surrounding
-- 'Except' result.
data CheckedActual
  = CheckedDirect Lean.Term
  | CheckedBindIndex Lean.Term

checkedActualTerm :: CheckedActual -> Lean.Term
checkedActualTerm (CheckedDirect tm)    = tm
checkedActualTerm (CheckedBindIndex tm) = tm

-- | Build a proof-carrying application over interpreted actuals: an
-- error-preserving bind chain for every 'CheckedBindIndex' (in
-- application order — calculus §Callee Conventions sequencing), then
-- the declared obligation and the helper call over the final (raw)
-- argument terms. Shared by the checked-application and wrapped
-- partial-op conventions; with no bound indices it reduces exactly to
-- the historical emissions.
lowerProofCarryingActuals ::
  TermTranslationMonad m =>
  Lean.Ident ->
    -- ^ obligation name stem (@h_bounds_@, @h_nonzero_@, …)
  (Lean.Ident -> Set Lean.Ident -> Lean.Term) ->
    -- ^ proof-script builder for the obligation
  Maybe ([Lean.Term] -> Lean.Term) ->
    -- ^ proposition over the final argument terms, if any
  Lean.Term ->
    -- ^ helper head
  [CheckedActual] ->
  m Lean.Term
lowerProofCarryingActuals obligName script mBuildProp head_ actuals =
  go 0 actuals []
  where
    bindVar = Lean.Var (Lean.Ident "Bind.bind")
    argTerms = map checkedActualTerm actuals
    avoidIdents = Set.unions (leanTermIdents head_ : map leanTermIdents argTerms)

    go _ [] subs = do
      let finalArgs =
            [ maybe tm Lean.Var (lookup pos subs)
            | (pos, tm) <- zip [0 :: Int ..] argTerms
            ]
      case mBuildProp of
        Nothing ->
          pure (Lean.App head_ finalArgs)
        Just buildProp -> do
          let prop = buildProp finalArgs
          unavailable <- view unavailableIdents <$> askTR
          let proofIdents = Set.union (leanTermIdents prop) unavailable
          withLocalProofObligationUsing
            obligName
            prop
            (`script` proofIdents)
            $ \proof ->
                pure (Lean.App head_ (finalArgs ++ [proof]))
    go pos (CheckedDirect _ : rest) subs = go (pos + 1) rest subs
    go pos (CheckedBindIndex tm : rest) subs = do
      bname <- freshVariantAvoiding avoidIdents
                 (Lean.Ident ("v_idx_" ++ show pos))
      rest' <- go (pos + 1) rest ((pos, bname) : subs)
      let lam = Lean.Lambda [Lean.Binder Lean.Explicit bname Nothing] rest'
      pure (Lean.App bindVar [tm, lam])

lowerCheckedApplicationHelperArgs ::
  TermTranslationMonad m =>
  CheckedApplicationContract ->
  [CheckedActual] ->
  m Lean.Term
lowerCheckedApplicationHelperArgs contract =
  lowerProofCarryingActuals
    (Lean.Ident "h_bounds_")
    boundsProofScript
    (cacBuildProp contract)
    (Lean.Var (cacHelperName contract))

checkedApplicationHelperArgsFor ::
  TermTranslationMonad m =>
  Ident ->
  [ArgMode] ->
  [Term] ->
  m [CheckedActual]
checkedApplicationHelperArgsFor ident = go []
  where
    go acc [] [] = pure (reverse acc)
    go acc (ProofArg : modes) (_ : rest) =
      -- Source proof argument: dropped at emission, re-proved as a
      -- Lean obligation by the contract's proposition.
      go acc modes rest
    go acc (FunctionWithNatLtArg nIdx : modes) (arg : rest)
      | nIdx < length acc =
          case reverse acc !! nIdx of
            CheckedDirect bound -> do
              helperArg <- translateFunctionWithNatLtWrappedResult
                (Text.pack (identName ident))
                bound
                True
                arg
              go (CheckedDirect helperArg : acc) modes rest
            CheckedBindIndex{} ->
              Except.throwError (RejectedPrimitive (Text.pack (identName ident))
                "proof-carrying generator bound is a runtime-computed index; \
                \a bound-in-bind generator convention is not implemented")
      | otherwise =
          Except.throwError (RejectedPrimitive (Text.pack (identName ident))
            "checked-application proof-function argument referenced a missing Nat bound")
    go acc (mode : modes) (arg : rest) = do
      actual <- checkedApplicationActual ident mode arg
      go (actual : acc) modes rest
    go _ _ _ =
      Except.throwError (RejectedPrimitive (Text.pack (identName ident))
        "checked-application contract argument table did not match source arity")

-- | Interpret one checked-application actual at its declared mode.
checkedApplicationActual ::
  TermTranslationMonad m => Ident -> ArgMode -> Term -> m CheckedActual
checkedApplicationActual ident mode arg = case mode of
  RuntimeArg ->
    CheckedDirect <$> (translateAt ExpectRuntimeValue arg >>= adaptToRuntime)
  TypeArg -> do
    translated <- translateTermWithShape arg
    CheckedDirect . ttLean <$> adaptTo (ExpectRaw RawTypePosition) translated
  IndexArg -> do
    translated <- translateTermWithShape arg
    case ttShape translated of
      BindingRaw      -> pure (CheckedDirect (ttLean translated))
      -- A runtime-computed index: legal via the error-preserving
      -- bind chain built by 'lowerCheckedApplicationHelperArgs'.
      BindingWrapped  -> pure (CheckedBindIndex (ttLean translated))
      BindingFunction ->
        Except.throwError (ForbiddenAdaptation
          "IndexArg (raw index position)"
          "BindingFunction")
  FunctionArg mconv -> do
    translated <- translateTermWithShape arg
    CheckedDirect . ttLean <$> adaptTo (ExpectFunctionPosition mconv) translated
  RawValueArg -> do
    translated <- translateTermWithShape arg
    CheckedDirect . ttLean <$> adaptTo (ExpectRaw RawValuePosition) translated
  ProofArg -> internalModeError
  FunctionWithNatLtArg{} -> internalModeError
  PropositionArg -> internalModeError
  MotiveArg -> internalModeError
  StructuralFieldArg -> internalModeError
  where
    internalModeError =
      Except.throwError (RejectedPrimitive (Text.pack (identName ident))
        ("checked-application contract used argument mode "
         <> Text.pack (show mode)
         <> " outside its interpreter"))

withMissingCheckedApplicationBinders ::
  TermTranslationMonad m =>
  Ident ->
  [ArgMode] ->
  [(VarName, Term)] ->
  ([Lean.Binder] -> [Lean.Term] -> m a) ->
  m a
withMissingCheckedApplicationBinders ident modes0 binders0 k =
  go [] [] modes0 binders0
  where
    go binders helperArgs [] [] =
      k (reverse binders) (reverse helperArgs)
    go binders helperArgs (mode : modes) ((vn, ty) : rest) =
      case mode of
        RuntimeArg ->
          bindMissing True
            binders helperArgs modes (vn, ty) rest
        IndexArg ->
          bindMissing False
            binders helperArgs modes (vn, ty) rest
        TypeArg ->
          bindMissing False
            binders helperArgs modes (vn, ty) rest
        RawValueArg ->
          bindMissing False
            binders helperArgs modes (vn, ty) rest
        ProofArg ->
          Except.throwError (RejectedPrimitive (Text.pack (identName ident))
            "missing source proof arguments need an explicit higher-order proof-carrying convention")
        FunctionArg{} ->
          Except.throwError (RejectedPrimitive (Text.pack (identName ident))
            "missing function arguments need an explicit higher-order proof-carrying convention")
        FunctionWithNatLtArg{} ->
          Except.throwError (RejectedPrimitive (Text.pack (identName ident))
            "missing proof-function arguments need an explicit higher-order proof-carrying convention")
        PropositionArg ->
          Except.throwError (RejectedPrimitive (Text.pack (identName ident))
            "checked-application contract used PropositionArg for a missing argument")
        MotiveArg ->
          Except.throwError (RejectedPrimitive (Text.pack (identName ident))
            "checked-application contract used MotiveArg for a missing argument")
        StructuralFieldArg ->
          Except.throwError (RejectedPrimitive (Text.pack (identName ident))
            "checked-application contract used StructuralFieldArg for a missing argument")
    go _ _ _ _ =
      Except.throwError (RejectedPrimitive (Text.pack (identName ident))
        "checked-application partial argument table did not match source arity")

    bindMissing wrapped binders helperArgs modes (vn, ty) rest = do
      tyLean <- localTR (set skipBinderWrap False) (translateTerm ty)
      let binderTy = if wrapped then wrapExcept tyLean else tyLean
      ident' <-
        if vnName vn == "_"
           then freshVariant (Lean.Ident ("η_checked_arg_" ++ show (length binders)))
           else translateLocalIdent (vnName vn)
      withUsedLeanIdent ident' $
        localTR ( over namedEnvironment (Map.insert vn ident')
                . withBindingInfo ident'
                    (BindingInfo (bindingShapeOfType binderTy))) $ do
          let binder = Lean.Binder Lean.Explicit ident' (Just binderTy)
              helperArg = Lean.Var ident'
          go (binder : binders) (helperArg : helperArgs) modes rest

-- | Lower proof primitives to explicit local proof obligations. The
-- contract table decides which arguments are raw proof/type terms and which
-- are wrapped value terms, then states the checked local proposition and how
-- the local evidence is consumed. Haskell only reconstructs the proposition;
-- it does not prove or simplify it.
lowerProofPrimitiveContract ::
  TermTranslationMonad m =>
  ProofPrimitiveContract ->
  [Term] ->
  m TranslatedTerm
lowerProofPrimitiveContract contract args = do
  argTerms <- proofPrimitiveArgs (ppcArgModes contract) args
  prop <- ppcBuildProp contract argTerms
  tm <- withLocalProofObligation
          (Lean.Ident "h_proof_")
          prop
          (ppcUseProof contract argTerms)
  pure (TranslatedTerm tm BindingRaw)
  where
    proofPrimitiveArgs [] [] = pure []
    proofPrimitiveArgs (mode : modes) (arg : rest) = do
      translated <- case mode of
        -- Raw-family modes: proof primitives state their
        -- propositions over raw LOGICAL terms — all of these
        -- translate in raw mode ('ppcArgModes' doc).
        TypeArg        -> withRawTranslationMode (translateTerm arg)
        IndexArg       -> withRawTranslationMode (translateTerm arg)
        RawValueArg    -> withRawTranslationMode (translateTerm arg)
        ProofArg       -> withRawTranslationMode (translateTerm arg)
        PropositionArg -> withRawTranslationMode (translateTerm arg)
        MotiveArg      -> withRawTranslationMode (translateTerm arg)
        RuntimeArg ->
          translateAt ExpectRuntimeValue arg >>= adaptToRuntime
        StructuralFieldArg ->
          Except.throwError (RejectedPrimitive "proof primitive"
            "proof-primitive contracts do not take structural-field arguments")
        FunctionArg{} ->
          Except.throwError (RejectedPrimitive "proof primitive"
            "proof-primitive contracts do not take function arguments yet")
        FunctionWithNatLtArg{} ->
          Except.throwError (RejectedPrimitive "proof primitive"
            "proof-primitive contracts do not take proof-function arguments")
      (translated :) <$> proofPrimitiveArgs modes rest
    proofPrimitiveArgs _ _ =
      Except.throwError (RejectedPrimitive "proof primitive"
        "proof-primitive contract argument table did not match source arity")

proofObligationPlaceholder :: Lean.Term
proofObligationPlaceholder =
  -- Emit-stage placeholder only. The check-stage must reject completed
  -- artifacts that still contain this `sorry`.
  Lean.Tactic "sorry"

-- | Evidence script for @h_unsafeAssert_@ obligations (OP-1). The
-- shapes SAW actually emits are reflexive @Eq Num x x@ instances, so
-- `rfl` (through the let-bound Prop, which whnf unfolds) closes them;
-- a genuinely non-reflexive assertion stays a loud `sorry` — correct,
-- it is a real obligation the user must discharge.
unsafeAssertProofScript :: Lean.Term
unsafeAssertProofScript =
  Lean.Tactic "(first | rfl | skip); all_goals sorry"

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

-- | Translate @Prelude.error@ demanded at a raw position, per the
-- audited disposition (doc/2026-07-14_reachable-raw-error-disposition.md):
--
--   * RULE 1 — a non-dependent Pi type whose final result is
--     value-domain lowers to the CONSTANT-ERROR FUNCTION: SAW only
--     observes a function-typed @error@ by applying it (the evaluator
--     raises on WHNF-forcing the applied error value; no @VFun@ is
--     ever produced), and every application lands on the same
--     wrapped 'saw_throw_error' route as a value-domain error, with
--     SAW's own message preserved (the deleted False-obligation
--     contract silently dropped the message). Binder carriers are
--     position-directed: value-domain binders wrap, index/type/proof
--     binders stay raw — the same rule the Pi type translator applies,
--     so the lambda inhabits exactly the translated Pi type.
--   * RULE 2 — everything else (Nat/index, sort, proof, dependent Pi,
--     or a Pi whose final result is itself raw) has no error carrier;
--     fabricating a default would be unsound and the retired
--     @h_raw_error_ : False@ contract was undischargeable at every
--     reachable position, so REJECT with a named diagnostic.
translateRawPositionError ::
  TermTranslationMonad m => Term -> Term -> m TranslatedTerm
translateRawPositionError resultTy msgArg = do
  mode <- view valueTranslationMode <$> askTR
  case asPiList resultTy of
    (binders@(_ : _), finalTy)
      | shouldWrapBinder finalTy
      , null (typeArgPositions resultTy)  -- fully non-dependent spine
      , WrappedValueMode <- mode
      -> do
          finalRaw <- translateTerm finalTy
          -- The message slot is UseArgWrapped in the value-domain
          -- error lowering; adapt to the same wrapped carrier here.
          msgLean  <- adaptToRuntime =<< translateTermWithShape msgArg
          domTys   <- mapM (binderDomainCarrier . snd) binders
          let body = Lean.App (Lean.Var (Lean.Ident "saw_throw_error"))
                       [finalRaw, msgLean]
              avoid = Set.union (leanTermIdents body)
                                (Set.unions (map leanTermIdents domTys))
          names <- mapM
            (\ix -> freshVariantAvoiding avoid
                      (Lean.Ident ("η_err_arg_" ++ show ix)))
            [0 .. length binders - 1]
          let lam = foldr
                      (\(nm, dom) acc ->
                        Lean.Lambda [Lean.Binder Lean.Explicit nm (Just dom)] acc)
                      body
                      (zip names domTys)
          pure (TranslatedTerm lam BindingFunction)
    _ ->
      Except.throwError $ RejectedPrimitive "error"
        "Prelude.error demanded at a raw position (Nat/index, sort, \
         \proof, dependent function, or a function whose final result \
         \is raw). No Except carrier exists at this position, so a \
         \faithful translation is impossible and a default would be \
         \unsound; the retired False-obligation contract was \
         \undischargeable at every reachable position (see \
         \doc/2026-07-14_reachable-raw-error-disposition.md). \
         \Function-typed error with a value-domain result lowers \
         \soundly; other shapes reject until a checked design exists."
  where
    -- The same carrier rule the Pi type translator applies to binder
    -- domains: value-domain wraps, index/type/proof stays raw.
    binderDomainCarrier dom = do
      domLean <- translateTerm dom
      pure (if shouldWrapBinder dom then wrapExcept domLean else domLean)

-- | Lower SAWCore's proof-producing @unsafeAssert α x y@ to an
-- explicit local Lean proof obligation. Haskell only reconstructs the
-- literal equality proposition from the SAW arguments; it does not
-- fabricate a proof or erase the assertion. Emitted proof outlines use
-- 'unsafeAssertProofScript' (rfl-first), so reflexive assertions close
-- at emission and anything else stays a loud `sorry` a completed
-- artifact must replace with a Lean-checked proof.
translateUnsafeAssertObligation ::
  TermTranslationMonad m => Term -> Term -> Term -> m TranslatedTerm
translateUnsafeAssertObligation aArg xArg yArg = do
  -- The subject representation follows the operands' domain — the
  -- same faithful-rep rule as the standalone equality convention.
  -- unsafeAssert's operands are arbitrary values, so an unconditional
  -- "declared raw" here was miscalibrated: over an effectful operand
  -- it rebuilt the proposition at a raw reading that dropped the
  -- effect structure, and the resulting obligation could not stand at
  -- the goal's wrapped carrier (a loud Lean carrier mismatch, but the
  -- right emission is the faithful wrapped obligation). The rule is
  -- MODE-UNIFORM (debts slice): raw-mode operands carry truthful raw
  -- production records ('rawModeResultShape'), so the classification
  -- reduces to the raw reading inside raw content without a separate
  -- raw-mode arm.
  prop <- do
    aLean <- withRawTranslationMode (translateTerm aArg)
    xTrans <- translateTermWithShape xArg
    yTrans <- translateTermWithShape yArg
    rep <- standaloneEqualitySubjectRep "unsafeAssert" [xTrans, yTrans]
    eqHead <- explicitCoreNameAtArgUniverse (Lean.Ident "Eq") aArg
    carrier <- subjectCarrierAt rep aArg aLean
    xLean <- subjectTerm rep xTrans
    yLean <- subjectTerm rep yTrans
    pure (Lean.App eqHead [carrier, xLean, yLean])
  tm <- withLocalProofObligationUsing
          (Lean.Ident "h_unsafeAssert_")
          prop
          (const unsafeAssertProofScript)
          pure
  pure (TranslatedTerm tm BindingRaw)

translateIdentWithArgs :: TermTranslationMonad m => Ident -> [Term] -> m Lean.Term
translateIdentWithArgs i args = ttLean <$> translateIdentWithArgsWithShape i args

-- | The raw-logical callee classifier (Eq / Refl / Eq__rec). All
-- other callees classify through the contract tables and named
-- branches of 'translateIdentWithArgsWithShape'.
rawLogicalCalleeForIdent :: Ident -> Maybe RawLogicalCallee
rawLogicalCalleeForIdent i
  | isPreludeIdent "Eq" i      = Just RawLogicalEq
  | isPreludeIdent "Refl" i    = Just RawLogicalRefl
  | isPreludeIdent "Eq__rec" i = Just RawLogicalEqRec
  | otherwise                  = Nothing

rawLogicalCalleeForRecursor :: CompiledRecursor -> Maybe RawLogicalCallee
rawLogicalCalleeForRecursor rec
  | ModuleIdentifier ident <- nameInfo (recursorDataType rec)
  , isPreludeIdent "Eq" ident = Just RawLogicalEqRec
  | otherwise                 = Nothing

isPreludeIdent :: String -> Ident -> Bool
isPreludeIdent baseName i =
     identModule i == preludeModule
  && identName i == baseName
  where
    preludeModule = mkModuleName ["Prelude"]

-- | The standalone-proposition convention (calculus §Raw Logical
-- Callees, plan Slice 5a): when @Eq@ / @Refl@ / @Eq__rec@ is reached
-- through ident or recursor dispatch with no equality-aware
-- surrounding convention, the declared subject representation is the
-- joint produced domain of the source operands under the current
-- translation mode — 'EqualitySubjectRuntimeValue' iff any operand's
-- declared production record ('ttShape', stamped by producers, never
-- read off emitted Lean AST) is wrapped, raw otherwise.
-- Function-shaped subjects reject until the function-carrier
-- convention (plan Slice 5c) decides them. The carrier type name
-- never participates: @Bool@ and @Nat@ equalities are raw in proof
-- lemmas and runtime over value-domain computations, and only the
-- operand domain distinguishes them.
--
-- This is one convention among several, not a universal authority.
-- A surround that knows its ρ_eq (e.g. 'unsafeAssert', declared raw)
-- calls 'equalityPropositionAtSubjectRep' with it directly and never
-- falls through to this function.
standaloneEqualitySubjectRep ::
  TermTranslationMonad m =>
  Text.Text -> [TranslatedTerm] -> m EqualitySubjectRep
standaloneEqualitySubjectRep who operands
  | any ((== BindingFunction) . ttShape) operands
  , any (isWrappedShape . ttShape) operands =
      Except.throwError (RejectedPrimitive who
        "raw logical equality with a function-shaped subject on one \
        \side and a wrapped runtime computation on the other does not \
        \determine a carrier uniquely; this signals an upstream \
        \classification bug, so the backend rejects instead of \
        \coercing either side")
  | otherwise = do
      let rep | any ((== BindingFunction) . ttShape) operands =
                  EqualitySubjectRawFunction
              | any (isWrappedShape . ttShape) operands =
                  EqualitySubjectRuntimeValue
              | otherwise = EqualitySubjectRaw RawLogicalPosition
      traceSubjectRep who operands rep
      pure rep

-- | Subject classification with the type-subject sub-case (calculus
-- §Raw Logical Callees, 2026-07-19): a SORT carrier means the
-- subjects are TYPES, and D decides from the carrier ALONE — operand
-- production shapes never participate (types happen to carry raw
-- shapes today, but the declared rule must not depend on that
-- accident). Everything else classifies from operand production
-- shapes via 'standaloneEqualitySubjectRep'.
subjectRepForCarrier ::
  TermTranslationMonad m =>
  Text.Text -> Term -> [TranslatedTerm] -> m EqualitySubjectRep
subjectRepForCarrier who aArg operands
  | isJust (asSort aArg) = do
      traceSubjectRep who operands EqualitySubjectTypeImage
      pure EqualitySubjectTypeImage
  | otherwise = standaloneEqualitySubjectRep who operands

-- | Subject-representation decisions join the position trace so every
-- ρ_eq choice is auditable alongside the per-term position log.
traceSubjectRep ::
  TermTranslationMonad m =>
  Text.Text -> [TranslatedTerm] -> EqualitySubjectRep -> m ()
traceSubjectRep who operands rep
  | not positionTraceEnabled = pure ()
  | otherwise =
      Debug.Trace.traceM $
        "[subjectRep] who=" ++ Text.unpack who
        ++ " operands=" ++ show (map ttShape operands)
        ++ " rep=" ++ show rep

-- | Construct the declared @Eq.rec@ convention for the standalone
-- dispatch path (no equality-aware surround): ρ_eq comes from the
-- standalone subject convention, and every other field derives from
-- it —
--
--   * raw subject: raw motive binders, raw motive result, raw branch,
--     raw result (the classic proof-transport shape, e.g. transporting
--     a raw @Nat@ along @addNat@ equations);
--   * runtime subject: the @y@ binder binds the wrapped carrier, the
--     motive result is a runtime value type (@Except String T@), the
--     branch adapts to a runtime value, and the transport produces a
--     wrapped result.
--
-- The standalone rule deliberately ties the motive result mode to
-- ρ_eq (raw-in-raw, value-in-value). The record keeps the fields
-- separate so a surround that knows better can someday declare them
-- independently — but the standalone convention never guesses a
-- mixed transport.
eqRecConventionForStandalone ::
  TermTranslationMonad m => Term -> [TranslatedTerm] -> m EqRecConvention
eqRecConventionForStandalone aArg operands = do
  rep <- subjectRepForCarrier "Eq__rec" aArg operands
  mLvl <- levelOfArg aArg
  let conv = case rep of
        EqualitySubjectRaw _ -> EqRecConvention
          { ercSubjectRep     = rep
          , ercCarrierLevel   = mLvl
          , ercMotive         = MotiveConvention
              [ ExpectRaw RawLogicalPosition
              , ExpectRaw RawProofPosition
              ]
              MotiveComputesRawType
          , ercBranchPosition = ExpectRaw RawLogicalPosition
          , ercProofPosition  = RawProofPosition
          , ercResultShape    = BindingRaw
          }
        EqualitySubjectRuntimeValue -> EqRecConvention
          { ercSubjectRep     = rep
          , ercCarrierLevel   = mLvl
          , ercMotive         = MotiveConvention
              [ ExpectRuntimeValue
              , ExpectRaw RawProofPosition
              ]
              MotiveComputesRuntimeValueType
          , ercBranchPosition = ExpectRuntimeValue
          , ercProofPosition  = RawProofPosition
          , ercResultShape    = BindingWrapped
          }
        -- Function-carrier transport (plan Slice 5c), e.g. the
        -- auto-emitted Prelude's @inverse_eta_rule@: the subject
        -- binder and the branch stand at function positions (a
        -- function-shaped branch is the norm — the motive result is
        -- typically a Pi over the function's domain), the motive is
        -- raw logical content, and the transported result is raw.
        EqualitySubjectRawFunction -> EqRecConvention
          { ercSubjectRep     = rep
          , ercCarrierLevel   = mLvl
          , ercMotive         = MotiveConvention
              [ ExpectFunctionPosition Nothing
              , ExpectRaw RawProofPosition
              ]
              MotiveComputesRawType
          , ercBranchPosition = ExpectFunctionPosition Nothing
          , ercProofPosition  = RawProofPosition
          , ercResultShape    = BindingRaw
          }
        -- Type-subject transport (2026-07-19): the subjects are TYPES
        -- and the ENTIRE spine reads them at one interpretation — the
        -- current mode's type translation (T-images in ambient Phase-β
        -- content, raw inside raw logical mode). No field flips mode:
        -- the motive and the nested proof translate with plain
        -- 'translateTerm', so the branch (a Refl whose subject is a
        -- type, translated ambient before the convention is chosen)
        -- and the motive agree by construction instead of by
        -- coincidence. The result is a proof: 'BindingRaw'.
        EqualitySubjectTypeImage -> EqRecConvention
          { ercSubjectRep     = rep
          , ercCarrierLevel   = mLvl
          , ercMotive         = MotiveConvention
              [ ExpectRaw RawTypePosition
              , ExpectRaw RawProofPosition
              ]
              MotiveComputesTypeImage
          , ercBranchPosition = ExpectRaw RawTypePosition
          , ercProofPosition  = RawProofPosition
          , ercResultShape    = BindingRaw
          }
  traceEqRecConvention conv
  pure conv

traceEqRecConvention ::
  TermTranslationMonad m => EqRecConvention -> m ()
traceEqRecConvention conv
  | not positionTraceEnabled = pure ()
  | otherwise =
      Debug.Trace.traceM ("[eqRecConvention] " ++ show conv)

-- | Translate an @Eq.rec@ motive at its declared convention.
--
-- The all-raw convention keeps the legacy-exact interpretation: the
-- whole motive translates under raw logical mode, which realizes
-- \"every binder raw, result raw, every nested equality raw\" in one
-- stroke and preserves the emitted corpus byte-for-byte.
--
-- The runtime-subject convention introduces the binders positionally:
-- @y@ binds the wrapped carrier ('ExpectRuntimeValue'), the equality
-- proof binder stays a raw proof whose TYPE translates in the ambient
-- mode — so its inner @Eq@ node classifies its subjects from the same
-- Γ the declared carrier came from ('standaloneEqualitySubjectRep'
-- sees the wrapped-bound @y@), keeping the motive's proposition and
-- the convention's carrier consistent by construction. The body is a
-- TYPE-level expression and wraps in @Except String@ per the declared
-- result mode.
translateEqRecMotiveAtConvention ::
  TermTranslationMonad m => EqRecConvention -> Term -> m Lean.Term
translateEqRecMotiveAtConvention conv motiveTerm =
  case mcResultMode (ercMotive conv) of
    MotiveComputesRawType ->
      withRawTranslationMode (translateTerm motiveTerm)
    -- Type-subject transport motive: CURRENT mode, no flip — the
    -- lambda is type/prop-level structural content (D of the body is
    -- a raw type/prop domain, so no value lift and no Except wrap of
    -- the lambda itself), and its embedded value-domain Pis wrap to
    -- their T-images in ambient content exactly as the branch's do.
    MotiveComputesTypeImage ->
      translateTerm motiveTerm
    MotiveComputesRuntimeValueType ->
      case (asLambda motiveTerm, mcBinderPositions (ercMotive conv)) of
        (Just (yv, yty, rest), [yPos, hPos])
          | Just (hv, hty, body) <- asLambda rest ->
              translateBinderAt (Just yPos) yv yty $ \ybnd ->
                translateBinderAt (Just hPos) hv hty $ \hbnd -> do
                  bodyLean <- translateTermLet body
                  let bodyWrapped = wrapExcept bodyLean
                      lam = Lean.Lambda
                              (concatMap bindTransToBinder [ybnd, hbnd])
                              bodyWrapped
                  tracePositionAt (ExpectRaw RawMotivePosition) motiveTerm
                    (TranslatedTerm lam BindingFunction)
                  pure lam
        _ ->
          Except.throwError (RejectedPrimitive "Eq__rec"
            "a runtime-subject Eq__rec motive must be a two-binder \
            \lambda (subject, then equality proof) so its binder \
            \positions can be declared; other motive forms do not \
            \determine the convention's fields uniquely")

subjectCarrier :: EqualitySubjectRep -> Lean.Term -> Lean.Term
subjectCarrier EqualitySubjectRuntimeValue ty = wrapExcept ty
subjectCarrier (EqualitySubjectRaw _) ty = ty
subjectCarrier EqualitySubjectRawFunction ty = ty
-- The type-subject carrier is the translation of a SORT — raw and
-- ambient coincide on sorts, so the caller-provided translation is
-- already the carrier.
subjectCarrier EqualitySubjectTypeImage ty = ty

-- | The carrier type at the declared subject representation. Raw and
-- runtime subjects reuse the raw translation of the source type the
-- caller already produced — callers translate it FIRST, before the
-- operands, because let-share and universe names allocate in
-- translation order and the legacy emission order must not shift.
-- The function carrier instead translates the source type in the
-- CURRENT mode (this arm only runs where the legacy path rejected, so
-- the extra translation cannot perturb existing emissions): raw
-- logical content gets the raw @a -> b@ it quantifies over, Phase-β
-- value content the translated effectful function type its operands
-- actually inhabit.
subjectCarrierAt ::
  TermTranslationMonad m =>
  EqualitySubjectRep -> Term -> Lean.Term -> m Lean.Term
subjectCarrierAt EqualitySubjectRawFunction aArg _aLeanRaw = translateTerm aArg
-- Explicit type-subject arm (audit condition 2, 2026-07-19): never
-- reach the wildcard below by accident. The carrier is a SORT, whose
-- translation is mode-independent, so the raw translation the caller
-- already produced IS the carrier.
subjectCarrierAt EqualitySubjectTypeImage _aArg aLeanRaw = pure aLeanRaw
subjectCarrierAt rep _aArg aLeanRaw = pure (subjectCarrier rep aLeanRaw)

subjectTerm ::
  TermTranslationMonad m => EqualitySubjectRep -> TranslatedTerm -> m Lean.Term
subjectTerm EqualitySubjectRuntimeValue = adaptToRuntime
subjectTerm (EqualitySubjectRaw r)      = fmap ttLean . adaptTo (ExpectRaw r)
subjectTerm EqualitySubjectRawFunction  =
  fmap ttLean . adaptTo (ExpectFunctionPosition Nothing)
-- Type subjects arrive at their current-mode translation (T-images in
-- ambient content) with raw production shapes; the raw-type position
-- keeps them on the adaptTo chokepoint without representation change.
subjectTerm EqualitySubjectTypeImage    =
  fmap ttLean . adaptTo (ExpectRaw RawTypePosition)

explicitCoreNameAtArgUniverse ::
  TermTranslationMonad m => Lean.Ident -> Term -> m Lean.Term
explicitCoreNameAtArgUniverse target arg = do
  mLvl <- levelOfArg arg
  pure $ case mLvl of
    Just lvl -> Lean.ExplVarUniv target [lvl]
    Nothing  -> Lean.ExplVar target

-- | Lower the standalone raw-logical callees (@Eq@ / @Refl@ /
-- @Eq__rec@ reached through ident or recursor dispatch with no
-- equality-aware surround). MODE-UNIFORM (debts slice): the standalone
-- convention classifies the subjects from their production records and
-- everything moves through the 'adaptTo' chokepoint at declared
-- positions. Inside raw translation mode every operand carries a
-- truthful raw record ('rawModeResultShape' — the false wrapped stamps
-- that once steered @coerce__def_trans@'s carrier into @Except String@
-- are gone), so the classification reduces to ρ_eq = raw for raw
-- content without a separate raw-mode pipeline.
lowerRawLogicalCallee ::
  TermTranslationMonad m =>
  RawLogicalCallee -> Ident -> [Term] -> m TranslatedTerm
lowerRawLogicalCallee RawLogicalEq _ [aArg, xArg, yArg] = do
  aLean <- withRawTranslationMode (translateTerm aArg)
  xTrans <- translateTermWithShape xArg
  yTrans <- translateTermWithShape yArg
  rep <- subjectRepForCarrier "Eq" aArg [xTrans, yTrans]
  eqHead <- explicitCoreNameAtArgUniverse (Lean.Ident "Eq") aArg
  carrier <- subjectCarrierAt rep aArg aLean
  xLean <- subjectTerm rep xTrans
  yLean <- subjectTerm rep yTrans
  pure (TranslatedTerm
    (Lean.App eqHead [carrier, xLean, yLean])
    BindingRaw)
lowerRawLogicalCallee RawLogicalRefl _ [aArg, xArg] = do
  aLean <- withRawTranslationMode (translateTerm aArg)
  xTrans <- translateTermWithShape xArg
  rep <- subjectRepForCarrier "Refl" aArg [xTrans]
  reflHead <- explicitCoreNameAtArgUniverse (Lean.Ident "Eq.refl") aArg
  carrier <- subjectCarrierAt rep aArg aLean
  xLean <- subjectTerm rep xTrans
  pure (TranslatedTerm
    (Lean.App reflHead [carrier, xLean])
    BindingRaw)
lowerRawLogicalCallee RawLogicalEqRec _ [aArg, xArg, motiveArg, branchArg, yArg, eqProofArg] = do
  aLean <- withRawTranslationMode (translateTerm aArg)
  xTrans <- translateTermWithShape xArg
  yTrans <- translateTermWithShape yArg
  -- Translation order (a, x, y, branch, motive, proof) is the legacy
  -- order: translation allocates fresh names and universe variables,
  -- so reordering would perturb unrelated emissions.
  branchTrans <- translateTermWithShape branchArg
  conv <- eqRecConventionForStandalone aArg [xTrans, yTrans]
  let rep = ercSubjectRep conv
  xLean <- subjectTerm rep xTrans
  yLean <- subjectTerm rep yTrans
  branchLean <- ttLean <$> adaptTo (ercBranchPosition conv) branchTrans
  motiveLean <- translateEqRecMotiveAtConvention conv motiveArg
  -- The proof stands at a raw proof position either way; its
  -- interpreter follows ρ_eq so that equality/reflexivity nodes
  -- INSIDE the proof term classify their subjects from the same Γ
  -- and mode the declared carrier came from (a raw-mode proof over a
  -- wrapped carrier would rebuild the proposition at the wrong
  -- representation).
  eqProofLean <- case rep of
    EqualitySubjectRaw _        -> withRawTranslationMode (translateTerm eqProofArg)
    EqualitySubjectRuntimeValue -> translateTerm eqProofArg
    -- Function-carrier proofs translate in the current mode for the
    -- same reason the carrier does: raw logical content is already in
    -- raw mode, and ambient content rebuilds any inner equality at
    -- the same mode its declared carrier came from.
    EqualitySubjectRawFunction  -> translateTerm eqProofArg
    -- Type-subject proofs: CURRENT mode, uniformly with the motive —
    -- nested spines (value-subject index equalities, further
    -- type-subject transports) recurse at the same one type
    -- interpretation the whole spine reads.
    EqualitySubjectTypeImage    -> translateTerm eqProofArg
  carrier <- subjectCarrierAt rep aArg aLean
  pure (TranslatedTerm
    (Lean.App (Lean.ExplVar (Lean.Ident "Eq.rec"))
      [ carrier
      , xLean
      , motiveLean
      , branchLean
      , yLean
      , eqProofLean
      ])
    (ercResultShape conv))
lowerRawLogicalCallee callee ident _ =
  Except.throwError (RejectedPrimitive (Text.pack (identName ident))
    ("raw logical callee "
     <> Text.pack (show callee)
     <> " was used at an unsupported arity"))

-- First-slice dispatch classification:
--
-- * 'findProofPrimitiveContract', 'findCheckedApplicationContract',
--   'findPartialOpContract', 'Prelude.unsafeAssert', raw 'Prelude.error',
--   'Prelude.fix', and 'Prelude.MkStream' are proof-obligation or
--   checked-helper conventions: Haskell emits the declared contract or
--   rejects unsupported arities, but does not prove it.
-- * 'Prelude.Eq', 'Prelude.Refl', and 'Prelude.Eq__rec' are the only
--   behavior-changing raw logical callees in this slice. They route through
--   'lowerRawLogicalCallee' so equality subject representation is explicit
--   and proof-transport motives stay raw.
-- * 'Prelude.if0Nat', raw 'Prelude.natCase', and function 'Prelude.coerce'
--   are existing transitional macro/raw-target branches. They are kept here
--   with their current conservative rejections instead of being broadened
--   during the equality slice.
-- * 'UseMapsToWrapped' in 'originalDispatchWithShape' is the wrapped-helper
--   convention. Its argument table controls wrapped function/value formals
--   and rejects unsupported higher-order residuals rather than rawifying.
-- * Other 'autoEmitRaw' proof combinators such as 'sym', 'trans',
--   'eq_cong', and 'coerce__def' remain transitional raw-logical
--   'UsePreserve' calls in this checkpoint. Do not add name-by-name behavior
--   here until the next convention slice gives them explicit subject and
--   arity contracts.
-- * The final 'originalDispatchWithShape' call is the declared transitional
--   fallback for pre-existing use-site treatments and ordinary Phase-beta
--   definitions; unmapped identifiers still reject through
--   'SpecialTreatment.defaultTreatmentFor'.
translateIdentWithArgsWithShape ::
  TermTranslationMonad m => Ident -> [Term] -> m TranslatedTerm
translateIdentWithArgsWithShape i args
  | Just contract <- findProofPrimitiveContract i (length args)
  = lowerProofPrimitiveContract contract args
  | Just callee <- rawLogicalCalleeForIdent i
  = lowerRawLogicalCallee callee i args
  | Just contract <- findCheckedApplicationContract i (length args)
  = lowerCheckedApplicationContract contract i args
  | Just contract <- findCheckedApplicationContractPrefix i (length args)
  = lowerPartialCheckedApplicationContract contract i args
  | Just expectedArity <- findCheckedApplicationContractArity i
  = Except.throwError (RejectedPrimitive (Text.pack (identName i))
      ("checked bounds/index contracts require exactly "
       <> Text.pack (show expectedArity)
       <> " argument(s); under-applied or over-applied proof-carrying \
          \operations must use a higher-order proof-wrapper design before \
          \they can be emitted soundly"))
  | Just contract <- findPartialOpContract i (length args)
  = lowerPartialOpContract contract i args
    -- STRICT under-application (2026-07-18 wrapper design, audited
    -- SAFE-WITH-CONDITIONS): a contract-bearing partial op at less
    -- than contract arity (dictionary field, partial application)
    -- lowers to its runtime-checked support wrapper — a plain
    -- application, ZERO proof obligations (condition 5); the
    -- wrapper throws at the contract-excluded point. Placed after
    -- the exact-arity match so full-arity lowerings are untouched
    -- (condition 4); over-application still rejects below.
  | Just contract <- findPartialOpContractUnderApplied i (length args)
  = lowerPartialOpRuntimeWrapper contract args
  | Just expectedArity <- findPartialOpContractArity i
  = Except.throwError (RejectedPrimitive (Text.pack (identName i))
      ("partial-operation contracts require exactly "
       <> Text.pack (show expectedArity)
       <> " argument(s); over-applied partial operations are not \
          \emittable (non-function result types make this unreachable \
          \from well-typed SAWCore; kept as defense-in-depth)"))
  | i == "Prelude.unsafeAssert"
  , [aArg, xArg, yArg] <- args
  = translateUnsafeAssertObligation aArg xArg yArg
  | i == "Prelude.error"
  , (resultTy : msgArg : _) <- args
  , not (shouldWrapBinder resultTy)
  = translateRawPositionError resultTy msgArg
  | i == "Prelude.fix"
  , (typeArg : bodyArg : rest) <- args
  = do
      traceFixClass typeArg bodyArg
      fixedPoint <-
        case classifyFixShape typeArg bodyArg of
          FixClassF
            | shouldWrapBinder typeArg ->
                lowerClassFBounded typeArg bodyArg
          FixClassSSingle
            | shouldWrapBinder typeArg ->
                lowerClassSSingle typeArg bodyArg
          FixClassSPaired ->
            -- R3b, fifth-audit amendment D: mutual paired-stream
            -- corecursion has its OWN disposition — an explicit
            -- named rejection, never a silently introduced lowering and never
            -- the retired-contract fallback.
            Except.throwError (RejectedPrimitive "Prelude.fix"
              ("paired-stream mutual corecursion is not realized "
               <> "(fifth-audit amendment D); a paired lowering is "
               <> "a separate post-R4 design"))
          verdict
            | shouldWrapBinder typeArg ->
                -- R4: the wrapped unique-fixed-point contract is
                -- RETIRED (no emitter may produce it — no fixed-point
                -- predicate can express productivity, Instance 3).
                -- Every wrapped fix is now two-state: a recognized
                -- class with a proven realization, or this named
                -- rejection carrying the recognizer's reason.
                Except.throwError (RejectedPrimitive "Prelude.fix"
                  ("unrecognized wrapped fix shape (the "
                   <> "unique-fixed-point contract is retired): "
                   <> Text.pack (fixVerdictReason verdict)))
            | otherwise ->
                -- Raw-position fixes (function/proof/index results)
                -- keep the raw proof-carrying contract, explicitly
                -- retained per Instance 3; believed corpus-unreachable
                -- for divergent shapes and census-checked.
                lowerFixProofObligation typeArg bodyArg
                  "raw-position fix uses the raw proof-carrying contract"
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
         then do
           xWrapped <- adaptToRuntime xTrans
           yWrapped <- adaptToRuntime yTrans
           pure (TranslatedTerm
                (Lean.App (Lean.Var (Lean.Ident "if0NatM"))
                  [aLean, nLean, xWrapped, yWrapped])
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
translateIdentWithArgsWithShape i args = originalDispatchWithShape i args

originalDispatchWithShape ::
  TermTranslationMonad m => Ident -> [Term] -> m TranslatedTerm
originalDispatchWithShape i args = do
  -- Pair/tuple carriers instantiated at a PROPOSITION reject at
  -- translation time. The Lean realization is
  -- @PairType : Type -> Type -> Type@; a Prop component (SAWCore
  -- pairs of proofs, e.g. @PairValue (Eq Bool True True) …@) cannot
  -- inhabit it, and without a reviewed universe-generalization of the
  -- support inductive (release 0.02 candidate work) the only faithful
  -- move is a loud, named refusal here instead of a downstream Lean
  -- elaboration failure. Proposition recognition uses the same
  -- 'asEq' authority as the argument-mode domain analysis.
  let pairCarrierTypeSlots
        | identName i `elem` [ "PairType", "PairValue"
                             , "PairType1", "PairValue1"
                             , "Pair_fst", "Pair_snd" ] = take 2 args
        | otherwise = []
  case filter (isJust . asEq) pairCarrierTypeSlots of
    (_propComponent : _) ->
      Except.throwError $ RejectedPrimitive (Text.pack (identName i))
        ("pair carrier instantiated at a proposition (an Eq component): "
         <> "the Lean PairType realization takes Type components; "
         <> "Prop-instantiated SAWCore pairs have no faithful "
         <> "realization until the support inductive is "
         <> "universe-generalized")
    [] -> pure ()
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
      mm0 <- view sawModuleMap <$> askTR
      let isValueFn = case funType mm0 of
            Just fty | (_ : _, ret) <- asPiList fty
                     , isNothing (asSort ret) -> True
            _ -> False
      if isValueFn
         then
           -- 2026-07-18 eta part 3b: the honest shape of a bare
           -- Pi-typed (non-type-family) global is FUNCTION — the
           -- BindingRaw stamp let value slots pure-lift raw function
           -- values (pure natToInt). Consumers adapt by convention.
           pure (TranslatedTerm f BindingFunction)
         else
           -- Bare zero-arg reference to a non-function global
           -- (literals, type constants): raw, as before.
           pure (TranslatedTerm f BindingRaw)
    applied f args' = do
      mm0 <- view sawModuleMap <$> askTR
      phase0 <- phaseBetaEnabled
      -- Mode-aware actual translation (2026-07-18 eta-adaptation
      -- design, part 2): a supplied actual at a 'FunctionArg (Just
      -- conv)' slot (the convention derived from the instantiating
      -- Pi — 'instantiationMode') translates AT that convention, so
      -- a raw-formal function value eta-adapts to the wrapped-arrow
      -- slot instead of splicing structurally. All other modes keep
      -- the as-produced translation.
      argResults <- case funType mm0 of
        Just fty | phase0 -> do
          let modes = phaseBetaArgModesFor fty args'
          sequence
            [ case mode of
                FunctionArg (Just conv) ->
                  translateFunctionActualAtConvention conv a
                _ -> translateTermWithShape a
            | (mode, a) <- zip (modes ++ repeat (FunctionArg Nothing)) args'
            ]
        _ -> mapM translateTermWithShape args'
      let argTerms = map ttLean argResults
      mm' <- view sawModuleMap <$> askTR
      phase <- phaseBetaEnabled
      case funType mm' of
        Just fty
          | phase -> do
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
              -- Plan Slice 4b: the declared CalleePhaseBetaDefinition
              -- convention IS the bind plan on the full-application
              -- path. The modes derive once from the callee's SAWCore
              -- Pi type + the supplied source actuals; equivalence
              -- with the legacy 'argumentBindPlan' was proven by the
              -- inert two-oracle sweep across the whole corpus before
              -- this swap. The eta/partial path below still uses the
              -- legacy plan until its own step.
              let derivedModes = phaseBetaArgModesFor fty args'
                  typeIxsFor   = typeArgPositions fty
                  shouldBind   =
                    [ phaseBetaBindFromMode ix typeIxsFor mode wrapped
                    | (ix, (mode, wrapped)) <-
                        zip [0 :: Int ..]
                          (zip derivedModes
                               (map (isWrappedShape . ttShape) argResults))
                    ]
              let (binders, _) = asPiList fty
                  ret = retTypeOfFun fty
                  fullyApplied = length args' >= length binders
                  shouldUseLift =
                       any (shouldWrapBinder . snd) binders
                    || shouldWrapBinder ret
                    || or shouldBind
              if not shouldUseLift
                 then do
                   let tm = Lean.App f argTerms
                   pure (TranslatedTerm tm (phaseBetaResultShape fty (length args')))
                 else if fullyApplied
                 then
                   let shouldBindForArgs =
                         take (length args') (shouldBind ++ repeat False)
                       pureWrap =
                            phaseBetaResultIsValue fty
                         || or shouldBindForArgs
                       resultShape =
                         if pureWrap
                            then BindingWrapped
                            else phaseBetaResultShape fty (length args')
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
                       pureWrap = phaseBetaResultIsValue fty
                       -- Plan Slice 4b: the eta formals present the
                       -- convention's declared representations — a
                       -- missing 'RawValueArg' formal is wrapped
                       -- (phase-β shape at missing positions), a
                       -- missing Nat 'IndexArg' formal is wrapped and
                       -- re-bound, types/props/functions stay raw.
                       missingModes = drop (length args') derivedModes
                       etaFormalWrapped ix mode =
                            mode == RawValueArg
                            || (mode == IndexArg && ix `notElem` typeIxsFor)
                       missingWrapped =
                         [ etaFormalWrapped ix mode
                         | (ix, mode) <- zip [length args'..] missingModes
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
                         [ phaseBetaBindFromMode ix typeIxsFor mode wrapped
                         | (ix, (mode, wrapped)) <-
                             zip [0 :: Int ..]
                               (zip derivedModes
                                    (suppliedWrapped ++ missingWrapped))
                         ]
                   let pureWrapEta = pureWrap || or shouldBindEta
                   body <- buildLifted f pureWrapEta
                             (take (length etaArgTerms)
                                   (shouldBindEta ++ repeat False))
                             etaResults
                   pure (TranslatedTerm
                           (Lean.Lambda etaBindersLean body)
                           BindingFunction)
        Just fty -> do
          -- Raw mode (the phase-guarded alternative above matched
          -- every ambient case): the emission is a bare application;
          -- stamp what raw mode actually produced, not the phase-β
          -- shape ('rawModeResultShape' doc).
          let tm = Lean.App f argTerms
          pure (TranslatedTerm tm (rawModeResultShape fty (length args')))
        Nothing -> do
          -- No SAWCore type for the callee. A 'Lean.App' is neither
          -- a lambda nor a variable, so the old AST guess was
          -- constantly 'BindingRaw'; state that explicitly.
          let tm = Lean.App f argTerms
          pure (TranslatedTerm tm BindingRaw)

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
          argResults <- translateWrappedHelperArgs argShapes mArgs
          let actualWrapped = map (isWrappedShape . ttShape) argResults
              expectedWrapped =
                [ wrappedHelperArgExpectsWrapped argShape
                | argShape <- argShapes
                ]
              functionMismatches =
                [ pos
                | (pos, (argShape, BindingWrapped)) <-
                    zip [0 :: Int ..] (zip argShapes (map ttShape argResults))
                , wrappedHelperArgExpectsFunction argShape
                ]
          case functionMismatches of
            pos : _ ->
              Except.throwError (RejectedPrimitive (Text.pack (identName i))
                ("wrapped helper expected a function argument at position "
                  <> Text.pack (show pos)
                  <> ", but the translated actual was an Except value"))
            [] -> pure ()
          -- For an explicitly wrapped helper formal, lift raw values
          -- into 'Except'. For raw helper formals, bind an already-
          -- wrapped actual before applying the helper. Function
          -- formals pass through as function-shaped values; there is
          -- no sound general conversion from an arbitrary Except
          -- value to a function. Proof-carrying generator formals
          -- translate source lambdas into Lean callbacks that receive
          -- checked index evidence from the helper.
          let shouldBindRaw =
                zipWith (\expectsWrapped isWrappedActual ->
                           not expectsWrapped && isWrappedActual)
                        expectedWrapped actualWrapped
          adapted <- zipWithM adaptWrappedFormal expectedWrapped argResults
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
          do let suppliedShapes = take (length args) argShapes
             argResults <- translateWrappedHelperArgs suppliedShapes args
             let actualWrapped = map (isWrappedShape . ttShape) argResults
                 expectedWrapped =
                   [ wrappedHelperArgExpectsWrapped argShape
                   | argShape <- suppliedShapes
                   ]
                 functionMismatches =
                   [ pos
                   | (pos, (argShape, BindingWrapped)) <-
                       zip [0 :: Int ..] (zip suppliedShapes (map ttShape argResults))
                   , wrappedHelperArgExpectsFunction argShape
                   ]
             case functionMismatches of
               pos : _ ->
                 Except.throwError (RejectedPrimitive (Text.pack (identName i))
                   ("wrapped helper expected a function argument at position "
                     <> Text.pack (show pos)
                     <> ", but the translated actual was an Except value"))
               [] -> pure ()
             let shouldBindRaw =
                   zipWith (\expectsWrapped isWrappedActual ->
                              not expectsWrapped && isWrappedActual)
                           expectedWrapped actualWrapped
             adapted <- zipWithM adaptWrappedFormal expectedWrapped argResults
             tm <- if null args
                     then pure (Lean.Var target)
                     else buildLifted (Lean.Var target) False shouldBindRaw adapted
             pure (TranslatedTerm tm BindingFunction)
      where
        n = length argShapes
        wrappedHelperArgExpectsWrapped UseArgWrapped = True
        wrappedHelperArgExpectsWrapped _ = False
        wrappedHelperArgExpectsFunction UseArgFunction = True
        wrappedHelperArgExpectsFunction UseArgFunctionWithNatLt{} = True
        wrappedHelperArgExpectsFunction _ = False
        translateWrappedHelperArgs = go []
          where
            go acc [] [] = pure acc
            go acc (UseArgFunctionWithNatLt nIdx : modes) (arg : rest)
              | nIdx < length acc = do
                  helperArg <- translateFunctionWithNatLtWrappedResult
                    (Text.pack (identName i))
                    (ttLean (acc !! nIdx))
                    False
                    arg
                  go (acc ++ [TranslatedTerm helperArg BindingFunction]) modes rest
              | otherwise =
                  Except.throwError (RejectedPrimitive (Text.pack (identName i))
                    "wrapped helper proof-carrying function argument referenced a missing Nat bound")
            go acc (UseArgFunction : modes) (arg : rest) = do
              helperArg <- translateFunctionToWrappedFormal
                (Text.pack (identName i))
                arg
              go (acc ++ [TranslatedTerm helperArg BindingFunction]) modes rest
            go acc (_mode : modes) (arg : rest) = do
              translated <- translateTermWithShape arg
              go (acc ++ [translated]) modes rest
            go _ _ _ =
              Except.throwError (RejectedPrimitive (Text.pack (identName i))
                "wrapped helper argument table did not match source arity")
    apply _ _ (UseReject reason) =
      Except.throwError
        (RejectedPrimitive (Text.pack (identName i)) reason)

-- | Lower a RAW-POSITION @Prelude.fix@ (function/proof/index result)
-- to the raw unique-fixed-point proof obligation. Post-R4 this is the
-- ONLY caller of the unique-fixed-point contract family: the wrapped
-- variant is retired (the dispatch rejects every unrecognized wrapped
-- fix with a named diagnostic; recognized classes have proven
-- realizations). The raw obligation is intentionally semantic and
-- strong — uniqueness over the whole raw fixed-point space — and is
-- retained per Instance 3; believed corpus-unreachable for divergent
-- shapes and census-checked.
lowerFixProofObligation ::
  TermTranslationMonad m =>
  Term -> Term -> Text.Text -> m TranslatedTerm
lowerFixProofObligation typeArg bodyArg _reason = do
  typeLean <- translateTerm typeArg
  bodyLean <- translateTerm bodyArg
  -- R4: the wrapped branch is GONE — the dispatch rejects every
  -- unrecognized wrapped fix before reaching here, so this lowering
  -- serves raw result positions only (Instance 3 retention).
  do
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

-- | Lower a RECOGNIZED Class-F (bounded-lookback) wrapped
-- @Prelude.fix@ to the OP-3 successor realization (Slice R2):
--
-- > let fix_body_ := <translated body — UNTOUCHED>;
-- > let h_fix_prod_obligation_ : Prop :=
-- >   saw_fix_bounded_productive n α fix_body_;
-- > let h_fix_prod_ : h_fix_prod_obligation_ := (by sorry);
-- > saw_fix_bounded_choose n α fix_body_ h_fix_prod_
--
-- H_prod (seed nonemptiness + element totality + bounded lookback)
-- is a PER-INSTANCE proof obligation, discharged in the proof row by
-- unfolding the concrete body — never assumed (fourth-audit
-- amendment A). A wrong recognizer verdict makes the obligation
-- unprovable: loud failure, never a silently different value. The
-- faithfulness core (stabilization/fixed-point/uniqueness lemmas,
-- conditional only on H_prod) lives in SAWCorePreludeProofs.
lowerClassFBounded ::
  TermTranslationMonad m =>
  Term -> Term -> m TranslatedTerm
lowerClassFBounded typeArg bodyArg =
  case asGlobalApply "Prelude.Vec" typeArg of
    Just [nT, aT] -> do
      nLean <- translateTerm nT
      aLean <- translateTerm aT
      bodyLean <- translateTerm bodyArg
      term <- withSharedLocalTerm
        (Lean.Ident "fix_body_")
        (Set.union (leanTermIdents nLean) (leanTermIdents aLean))
        bodyLean
        $ \bodyVar -> do
            let prop =
                  Lean.App
                    (Lean.Var (Lean.Ident "saw_fix_bounded_productive"))
                    [nLean, aLean, bodyVar]
            withLocalProofObligation
              (Lean.Ident "h_fix_prod_")
              prop
              $ \proof ->
                  pure (Lean.App
                    (Lean.Var (Lean.Ident "saw_fix_bounded_choose"))
                    [nLean, aLean, bodyVar, proof])
      pure (TranslatedTerm term BindingWrapped)
    _ ->
      Except.throwError (RejectedPrimitive "Prelude.fix"
        ("internal invariant violation: Class-F fix at a non-Vec type "
         <> "(recognizer/lowering disagreement)"))

-- | Lower a RECOGNIZED Class S-single (identity-step stream
-- corecursion) wrapped @Prelude.fix@ to the R3b realization:
--
-- > let stream_fn_ := (fun rec => <translated index function>);
-- > let h_stream_prod_obligation_ : Prop :=
-- >   saw_stream_single_productive α x0 (fun prev_ => prev_) stream_fn_;
-- > let h_stream_prod_ : … := (by sorry);
-- > saw_stream_realize α x0 (fun prev_ => prev_) stream_fn_ h_stream_prod_
--
-- ONE per-instance PROVEN obligation (faithful + lookback, fifth-audit
-- amendments 2-3) replaces the old path's DOUBLE by-sorry stub
-- (mkStream totality + fix uniqueness). The seed @x0@ is the
-- recognized literal's single element and must translate raw (or be
-- a syntactic @Pure.pure e@, which is stripped); a computed-wrapped
-- seed rejects loudly — no unwrap is manufactured.
lowerClassSSingle ::
  TermTranslationMonad m =>
  Term -> Term -> m TranslatedTerm
lowerClassSSingle typeArg bodyArg
  | Just [elemTyT] <- asGlobalApply "Prelude.Stream" typeArg
  , Just (recVn, recTy, inner) <- asLambda bodyArg
  , Just [_elemTyT2, idxF] <- asGlobalApply "Prelude.MkStream" inner
  , Just (_iVn, _ity, fbody) <- asLambda idxF
  , Just [_sLen, _ety, _dflt, seedV, _idx] <-
      asGlobalApply "Prelude.atWithDefault" fbody
  , Just seedElt <- asSingletonArraySeed seedV
  = do
      elemTyLean <- translateTerm elemTyT
      seedTrans <- translateTermWithShape seedElt
      x0Lean <- case (ttShape seedTrans, ttLean seedTrans) of
        (BindingRaw, e) -> pure e
        (BindingWrapped,
         Lean.App (Lean.Var (Lean.Ident "Pure.pure")) [e]) -> pure e
        (_, _) ->
          Except.throwError (RejectedPrimitive "Prelude.fix"
            ("Class S-single stream seed element translates to a "
             <> "computed wrapped or function-shaped value; the "
             <> "realization requires a raw seed and manufactures "
             <> "no unwrap"))
      mkfnLean <- translateBinderAt (Just ExpectRuntimeValue)
        recVn recTy $ \(BindTrans recIdent recTyLean) -> do
          idxFLean <- translateFunctionWithWrappedResult idxF
          pure (Lean.Lambda
            [Lean.Binder Lean.Explicit recIdent (Just recTyLean)]
            idxFLean)
      let idStep = Lean.Lambda
            [Lean.Binder Lean.Explicit (Lean.Ident "prev_") Nothing]
            (Lean.Var (Lean.Ident "prev_"))
      term <- withSharedLocalTerm
        (Lean.Ident "stream_fn_")
        (Set.union (leanTermIdents elemTyLean) (leanTermIdents x0Lean))
        mkfnLean
        $ \fnVar -> do
            let prop =
                  Lean.App
                    (Lean.Var (Lean.Ident "saw_stream_single_productive"))
                    [elemTyLean, x0Lean, idStep, fnVar]
            withLocalProofObligation
              (Lean.Ident "h_stream_prod_")
              prop
              $ \proof ->
                  pure (Lean.App
                    (Lean.Var (Lean.Ident "saw_stream_realize"))
                    [elemTyLean, x0Lean, idStep, fnVar, proof])
      pure (TranslatedTerm term BindingWrapped)
  | otherwise =
      Except.throwError (RejectedPrimitive "Prelude.fix"
        ("internal invariant violation: Class S-single fix does not "
         <> "match the recognized shape (recognizer/lowering "
         <> "disagreement)"))

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
          Except.throwError $ RejectedPrimitive (Text.pack nm_str)
            "imported constants require an explicit Lean realization. \
            \Add the name to the skip list when the Lean environment supplies \
            \a declaration with the same name, or provide an explicit renaming."
        _ ->
          emitImportedRealizationAlias nm sawType $
            escapeIdent $ Lean.Ident $ fromMaybe nm_str mRenamed

translateConstantWithShape ::
  TermTranslationMonad m => Name -> Either Sort Term -> m TranslatedTerm
translateConstantWithShape nm sawType = case nameInfo nm of
  -- The ident dispatch already computes the shape; use its result
  -- directly instead of re-guessing from the emitted Lean (old
  -- 'bindingShapeOfLeanTermM' behavior, deleted in plan Slice 2).
  ModuleIdentifier ident -> translateIdentWithArgsWithShape ident []
  ImportedName{} -> do
    tm <- translateConstantWithType nm sawType
    -- Imported realizations emit a 'Lean.Var' alias; the shape comes
    -- from the constant's SAWCore type. A sort-typed constant is a
    -- type (raw); a non-Pi, non-value type (Nat, Num, …) is raw.
    let shape = case sawType of
          Right ty
            | isJust (asPi ty)    -> BindingFunction
            | shouldWrapBinder ty -> BindingWrapped
          _                       -> BindingRaw
    pure (TranslatedTerm tm shape)

emitImportedRealizationAlias ::
  TermTranslationMonad m =>
  Name -> Either Sort Term -> Lean.Ident -> m Lean.Term
emitImportedRealizationAlias nm sawType targetIdent = do
  let aliasIdent = importedRealizationAliasIdent nm
  globals <- gets (view globalDeclarations)
  if aliasIdent `elem` globals
     then pure (Lean.Var aliasIdent)
     else do
       typeLean <- translateConstantContractType sawType
       univs <- gets (view universeVars)
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
  -- A constructor-order assertion mentions only constant names.
  Lean.CtorOrderAssertion _ _ -> Set.empty

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
translateRecursorAppWithShape crec args
  | Just RawLogicalEqRec <- rawLogicalCalleeForRecursor crec =
      lowerRawLogicalCallee
        RawLogicalEqRec
        (mkIdent (mkModuleName ["Prelude"]) "Eq__rec")
        args
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
       scrutResult <- translateTermWithShape scrut
       let scrutTrans = ttLean scrutResult
           scrutWrapped = isWrappedShape (ttShape scrutResult)
       -- Lean recursors consume raw scrutinees. The convention decision below
       -- is the only place that classifies the motive result and decides
       -- whether a wrapped source scrutinee may be sequenced through
       -- 'Bind.bind'. Value-producing motives always return @Except String T@.
       -- Function-producing motives may bind the scrutinee only after
       -- eta-expanding to a function whose final result can carry @Except@.
       -- Raw/proof/type motives never extract a raw scrutinee from @Except@.
       let motiveArg = preScrut !! nParams
           (_, motiveBody) = asLambdaList motiveArg
       convention <- recursorConvention
         crec scrutWrapped motiveBody (length postScrut)
       let motiveReturnsRaw =
             recResultMode convention /= RecursorReturnsWrappedValue
           motiveReturnsWrappedValue =
             recResultMode convention == RecursorReturnsWrappedValue
       paramTrans <- traverse translateTerm paramArgs
       casePlans <- recursorCasePlans paramTrans crec
       preTrans <- zipWithM
         (\i a -> if i < nParams
                     then pure (paramTrans !! i)
                     else if i == nParams
                       then translateMotiveAtConvention
                              (motiveConventionFor nIndices
                                (recMotiveResultPosition convention) a) a
                       else if isCasePos i
                         then translateCaseHandler
                                motiveReturnsRaw
                                motiveReturnsWrappedValue
                                (casePlans !! (i - caseFirst)) a
                         else translateTerm a)
         [0..] preScrut
       -- 2026-07-18 eta part 3b: post-scrutinee args at declared
       -- FUNCTION positions translate at their conventions (raw-
       -- formal globals like natToInt eta-adapt to the wrapped-arrow
       -- formal the motive-derived Pi declares).
       let postPositions =
             fcArgPositions (piFunctionConvention motiveBody)
             ++ repeat (ExpectRaw RawValuePosition)
       postResults <-
         sequence
           [ case pos of
               ExpectFunctionPosition (Just conv) ->
                 translateFunctionActualAtConvention conv a
               _ -> translateTermWithShape a
           | (pos, a) <- zip postPositions postScrut
           ]
       postTrans <- recursorPostArgs motiveBody postResults
       let recCallWith scrutTerm =
             Lean.App recHead (preTrans ++ [scrutTerm] ++ postTrans)
       case (recScrutineeMode convention, recResultMode convention) of
         (RecursorScrutineeRaw, _) ->
           pure (TranslatedTerm (recCallWith scrutTrans)
                                (recFinalShape convention))
         (RecursorScrutineeWrapped, RecursorReturnsWrappedValue) -> do
           scrutName <- freshVariant (Lean.Ident "scrut_")
           let recCall = recCallWith (Lean.Var scrutName)
               lam = Lean.Lambda
                       [Lean.Binder Lean.Explicit scrutName Nothing]
                       recCall
           pure (TranslatedTerm
                   (Lean.App (Lean.Var (Lean.Ident "Bind.bind"))
                     [scrutTrans, lam])
                   BindingWrapped)
         (RecursorScrutineeWrapped, RecursorReturnsFunction)
           | recFinalShape convention == BindingWrapped -> do
               scrutName <- freshVariant (Lean.Ident "scrut_")
               let recCall = recCallWith (Lean.Var scrutName)
                   lam = Lean.Lambda
                           [Lean.Binder Lean.Explicit scrutName Nothing]
                           recCall
               pure (TranslatedTerm
                       (Lean.App (Lean.Var (Lean.Ident "Bind.bind"))
                         [scrutTrans, lam])
                       BindingWrapped)
           | null postScrut
           , recFinalShape convention == BindingFunction
           , recursorFunctionResultCanPropagate motiveBody -> do
               fn <- etaExpandWrappedScrutineeFunctionResult
                       motiveBody scrutTrans recCallWith
               pure (TranslatedTerm fn BindingFunction)
         (RecursorScrutineeWrapped, _) ->
           rejectWrappedRawRecursor crec convention
  where
    -- Plan Slice 6.1: the convention DERIVES from the declared
    -- motive result position ('recursorMotiveResultPosition' — the
    -- shared domain analysis) instead of local classification
    -- predicates. RecursorReturnsWrappedValue iff the position is
    -- 'ExpectRuntimeValue'; a function-motive final shape reads the
    -- declared function convention's arity and result position (the
    -- record 'phaseBetaResultShape' used to re-derive here).
    recursorConvention ::
      TermTranslationMonad m =>
      CompiledRecursor -> Bool -> Term -> Int -> m RecursorConvention
    recursorConvention rec scrutWrapped' motiveBody nPostArgs = do
      let scrutMode =
            if scrutWrapped'
               then RecursorScrutineeWrapped
               else RecursorScrutineeRaw
          motivePos =
            recursorMotiveResultPosition (recursorSort rec) motiveBody
          resultMode = case motivePos of
            ExpectRuntimeValue       -> RecursorReturnsWrappedValue
            ExpectFunctionPosition _ -> RecursorReturnsFunction
            ExpectRaw _              -> RecursorReturnsRawTypeOrProof
      finalShape <- case motivePos of
        ExpectRuntimeValue -> pure BindingWrapped
        ExpectRaw _        -> pure BindingRaw
        ExpectFunctionPosition (Just conv)
          | nPostArgs < length (fcArgPositions conv) -> pure BindingFunction
          | fcResultPosition conv == ExpectRuntimeValue -> pure BindingWrapped
          | otherwise -> pure BindingRaw
        ExpectFunctionPosition Nothing ->
          Except.throwError (RejectedPrimitive "recursor motive"
            "internal contract: a recursor motive's function position \
            \must carry its declared convention")
      let convention = RecursorConvention
            { recScrutineeMode = scrutMode
            , recResultMode    = resultMode
            , recMotiveResultPosition = motivePos
            , recFinalShape    = finalShape
            }
      case (scrutMode, resultMode) of
        (RecursorScrutineeWrapped, RecursorReturnsRawTypeOrProof) ->
          rejectWrappedRawRecursor rec convention
        (RecursorScrutineeWrapped, RecursorReturnsFunction) ->
          if finalShape == BindingWrapped ||
             (nPostArgs == 0 &&
              finalShape == BindingFunction &&
              recursorFunctionResultCanPropagate motiveBody)
             then pure convention
             else rejectWrappedRawRecursor rec convention
        _ -> pure convention

    rejectWrappedRawRecursor ::
      TermTranslationMonad m =>
      CompiledRecursor -> RecursorConvention -> m a
    rejectWrappedRawRecursor rec convention =
      Except.throwError (RejectedPrimitive
        (toAbsoluteName (nameInfo (recursorDataType rec)))
        ("raw/wrapped recursor convention cannot extract a raw "
         <> recursorResultDescription (recResultMode convention)
         <> " from an Except-wrapped scrutinee; only value-producing \
            \recursors and value-producing function recursors may bind \
            \wrapped scrutinees"))

    recursorResultDescription :: RecursorResultMode -> Text.Text
    recursorResultDescription RecursorReturnsWrappedValue =
      "value result"
    recursorResultDescription RecursorReturnsRawTypeOrProof =
      "type/proof/raw result"
    recursorResultDescription RecursorReturnsFunction =
      "function result"

    -- Convention read (plan Slice 6.1): a wrapped scrutinee may be
    -- sequenced through an eta-expanded function result only when the
    -- declared motive function convention's result position is a
    -- runtime value — i.e. the emitted Pi's body wraps, so the eta
    -- body's @Bind.bind@ typechecks and errors propagate.
    recursorFunctionResultCanPropagate :: Term -> Bool
    recursorFunctionResultCanPropagate fty =
      not (null (fcArgPositions conv)) &&
      fcResultPosition conv == ExpectRuntimeValue
      where
        conv = recursorMotiveFunctionConvention fty

    -- Post-scrutinee actuals adapt at the declared motive function
    -- convention's binder positions (plan Slice 6.1): runtime-value
    -- slots lift, every raw slot splices.
    recursorPostArgs ::
      TermTranslationMonad m => Term -> [TranslatedTerm] -> m [Lean.Term]
    recursorPostArgs fty argResults =
      sequence
        [ case drop ix positions of
            ExpectRuntimeValue : _ -> adaptToRuntime result
            _                      -> pure (ttLean result)
        | (ix, result) <- zip [0..] argResults
        ]
      where
        positions = fcArgPositions (recursorMotiveFunctionConvention fty)

    etaExpandWrappedScrutineeFunctionResult ::
      TermTranslationMonad m =>
      Term ->
      Lean.Term ->
      (Lean.Term -> Lean.Term) ->
      m Lean.Term
    etaExpandWrappedScrutineeFunctionResult fty scrutTrans recCallWith = do
      let (binders, _) = asPiList fty
          typeIxs = typeArgPositions fty
      translateFunctionConventionBinders typeIxs binders $
        \etaBinders etaArgs -> do
          scrutName <- freshVariant (Lean.Ident "scrut_")
          let recFun = recCallWith (Lean.Var scrutName)
              recResult = Lean.App recFun (map ttLean etaArgs)
              scrutLam = Lean.Lambda
                [Lean.Binder Lean.Explicit scrutName Nothing]
                recResult
          pure (Lean.Lambda etaBinders
            (Lean.App (Lean.Var (Lean.Ident "Bind.bind"))
              [scrutTrans, scrutLam]))

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
            elemIndex vn ctorParamNames
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
  TermTranslationMonad m => Bool -> Bool -> CaseHandlerPlan -> Term -> m Lean.Term
translateCaseHandler motiveReturnsRaw expectedWrappedResult casePlan caseTerm = case asLambdaList caseTerm of
  ([], _) ->
    -- No explicit source binders to wrap. A bare function-valued
    -- handler such as `bvNat` may still be used at a recursor branch
    -- whose motive expects a wrapped result function, so eta-expand
    -- and lift the result when the handler's SAW type demands it.
    adaptBareCaseHandler expectedWrappedResult caseTerm
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
        -- Value fields shadowed at recursor entry are already lifted for a
        -- wrapped-value motive, so later variable uses must be treated as
        -- wrapped rather than lifted a second time.
        let valueShadowNames =
              [ binderName binder
              | (binder, (_, sawTy)) <- rawFieldBinders
              , functionConventionResultIsValue sawTy
              ]
            -- The let-shadow chain rebinds these fields as wrapped
            -- runtime values.
            shadowInfo = BindingInfo BindingWrapped
            markValueShadows =
              if motiveReturnsRaw
                 then id
                 else over bindingEnv
                        (\m -> foldr (`Map.insert` shadowInfo) m
                                  valueShadowNames)
        in localTR (set inRecursorCaseBinder surroundingFlag
                    . markValueShadows) $
          translateBinders normalParams $ \normalParamTerms -> do
            body' <-
              if motiveReturnsRaw
                 then translateTermLet body
                 else do
                   bodyResult <- translateTermLetWithShape body
                   if expectedWrappedResult
                      then adaptToRuntime bodyResult
                      else pure (ttLean bodyResult)
            -- Shadow raw constructor fields only for value-producing motives.
            -- Type/proof motives must keep constructor fields raw; wrapping a
            -- Nat index there feeds `Except String Nat` into type constructors
            -- such as `Vec n Bool`.
            shadowed <- if motiveReturnsRaw
                           then pure body'
                           else shadowBinders rawFieldBinders body'
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
                    Just bt | functionConventionResultIsValue saw_ty ->
                      Just (wrapExcept bt)
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
      | functionConventionResultIsValue saw_ty =
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
      TermTranslationMonad m => Bool -> Term -> m Lean.Term
    adaptBareCaseHandler expectedWrapped caseTerm' = do
      caseResult <- translateTermWithShape caseTerm'
      caseLean <-
            case ttShape caseResult of
              BindingFunction -> pure (ttLean caseResult)
              _ | expectedWrapped -> adaptToRuntime caseResult
              _ -> pure (ttLean caseResult)
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

-- | Record a constructor-order assertion for a datatype whose
-- @Foo.rec@ head is being emitted with SAWCore's positional argument
-- order (plan Slice 6.2). The assertion — a @saw_ctor_order@ command
-- the support library's @CryptolToLean.SAWCoreCtorOrder@ elaborates —
-- carries SAWCore's declared constructor order (translated to
-- fully-qualified Lean names), so the emitted file refuses to
-- elaborate if EITHER side drifts: a reordered Lean support-library
-- inductive or a reordered SAWCore datatype declaration. Same-payload
-- constructors make such drift typecheck while swapping every case
-- handler — this is the only silent (typechecks-but-wrong) recursor
-- risk, and the assertion closes it.
--
-- One assertion per datatype per translation run, deduplicated
-- against 'topLevelDeclarations'. A constructor without a fixed
-- fully-qualified Lean identifier rejects loudly: emitting the
-- recursor without its order assertion would reopen the hole.
recordCtorOrderAssertion ::
  TermTranslationMonad m => CompiledRecursor -> m ()
recordCtorOrderAssertion crec = do
  dtQual <- qualifiedIdentFor (recursorDataType crec)
  ctorQuals <- traverse qualifiedIdentFor (recursorCtorOrder crec)
  decls <- gets (view topLevelDeclarations)
  let already = any (\case
        Lean.CtorOrderAssertion dt' _ -> dt' == dtQual
        _                             -> False) decls
  unless already $
    modify (over topLevelDeclarations
      (Lean.CtorOrderAssertion dtQual ctorQuals :))
  where
    qualifiedIdentFor nm = case nameInfo nm of
      ModuleIdentifier ident -> do
        mq <- translateIdentToQualifiedIdent ident
        maybe (refuse nm) pure mq
      ImportedName{} -> refuse nm
    refuse nm = Except.throwError (RejectedPrimitive
      (toAbsoluteName (nameInfo (recursorDataType crec)))
      ("cannot emit the constructor-order assertion for this \
       \recursor: " <> toAbsoluteName (nameInfo nm)
       <> " has no fixed fully-qualified Lean identifier. Emitting \
          \@Foo.rec with SAWCore's positional case order but without \
          \the Lean-checked order assertion would reopen the silent \
          \branch-swap hole; add a fixed SpecialTreatment mapping."))

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
      Just (Lean.Ident i) -> do
        -- Slice 6.2: no @Foo.rec@ leaves the translator with
        -- unchecked constructor-order trust — record the
        -- Lean-checked assertion alongside the head.
        recordCtorOrderAssertion crec
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
         liftedElems <- traverse adaptToRuntime elemResults
         let n      = length elemResults
             vecLit = Lean.List liftedElems
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

-- | Seam for the position-directed translation refactor
-- (doc/archive/2026-07-08_position-directed-translation-plan.md, Slice 0):
-- translate a term at a declared expected position ρ — the calculus
-- judgment
--
-- >  Γ ⊢ e : τ  ⟹_ρ  L : R(ρ, τ)
--
-- Transitional implementation: run the existing bottom-up translation
-- unchanged and observe whether the shape it produced is consistent
-- with ρ. Behavior-identical to 'translateTermWithShape'; later slices
-- move the dispatch itself under ρ. Call sites migrate here only as
-- their expected position becomes explicit — the ρ must be declared by
-- the surrounding convention (a contract-table arg mode, a callee
-- convention), never guessed to make a site migrate.
--
-- With @SAW_LEAN_TRACE_POSITIONS@ set, logs
-- @(ρ, term head, produced shape)@ per call and flags productions
-- inconsistent with ρ — the migration's differential oracle.
translateAt ::
  TermTranslationMonad m => ExpectedPosition -> Term -> m TranslatedTerm
translateAt rho t = do
  result <- translateSharedAt (Just rho) t
  tracePositionAt rho t result
  pure result

-- | The adaptation chokepoint (plan Slice 2): move a translated term
-- to the position a convention demands, using exactly the adapters the
-- calculus allows (§Adaptation):
--
--   * identity at the same position;
--   * raw → runtime value via 'Pure.pure';
--   * a non-lambda term standing at function position ('BindingShape'
--     cannot distinguish a function-typed variable from a raw value,
--     so 'BindingRaw' is accepted there — Lean's typechecker still
--     guards the arity).
--
-- Everything else — wrapping a function, demanding a runtime 'Except'
-- value at a raw type/proof/motive position without an error-
-- preserving bind context, wrapping a motive — throws
-- 'ForbiddenAdaptation'. It must never be caught and defaulted: it
-- means the demanding convention is wrong, not the term.
--
-- Runtime → raw is deliberately absent. The only sound way to consume
-- a wrapped value at a raw position is a 'Bind.bind' continuation that
-- preserves the error case, and those are built by the translator's
-- bind-chain emitters, not by point adaptation.
adaptTo ::
  TermTranslationMonad m => ExpectedPosition -> TranslatedTerm -> m TranslatedTerm
adaptTo rho result =
  let deliver tm shape = pure (TranslatedTerm tm shape)
      forbidden =
        Except.throwError (ForbiddenAdaptation
          (Text.pack (show rho))
          (Text.pack (show (ttShape result))))
  in case (rho, ttShape result) of
    (ExpectRuntimeValue, BindingWrapped)  -> deliver (ttLean result) BindingWrapped
    (ExpectRuntimeValue, BindingRaw)      ->
      deliver (Lean.App (Lean.Var (Lean.Ident "Pure.pure")) [ttLean result])
              BindingWrapped
    (ExpectRuntimeValue, BindingFunction) -> forbidden
    (ExpectRaw _, BindingRaw)             -> deliver (ttLean result) BindingRaw
    (ExpectRaw RawMotivePosition, BindingFunction) ->
      deliver (ttLean result) BindingFunction
    (ExpectRaw _, _)                      -> forbidden
    (ExpectFunctionPosition _, BindingFunction) ->
      deliver (ttLean result) BindingFunction
    (ExpectFunctionPosition _, BindingRaw)  -> deliver (ttLean result) BindingRaw
    (ExpectFunctionPosition _, BindingWrapped) -> forbidden

-- | 'adaptTo' at runtime-value position, projected to the Lean term —
-- the common shape at bind-chain and wrapped-formal sites.
adaptToRuntime :: TermTranslationMonad m => TranslatedTerm -> m Lean.Term
adaptToRuntime = fmap ttLean . adaptTo ExpectRuntimeValue

-- | Adapt an argument whose formal the convention declares wrapped;
-- leave other formals untouched.
adaptWrappedFormal ::
  TermTranslationMonad m => Bool -> TranslatedTerm -> m TranslatedTerm
adaptWrappedFormal True  = adaptTo ExpectRuntimeValue
adaptWrappedFormal False = pure

-- | Is the shape the bottom-up translator produced consistent with the
-- demanded position? Consistent = exactly the representation @R(ρ, τ)@
-- prescribes, or one an allowed adapter reaches from it (raw → runtime
-- via 'Pure.pure'; a non-lambda term standing at function position,
-- since 'BindingShape' cannot distinguish a function-typed variable
-- from a raw value). A runtime ('Except') value at a raw or function
-- position is inconsistent: reaching it needs an error-preserving
-- 'Bind.bind' context, which only the adaptation chokepoint 'adaptTo'
-- may build. Slice 0 only observes this relation via the position
-- trace; translation must never branch on it.
shapeConsistentWithPosition :: ExpectedPosition -> BindingShape -> Bool
shapeConsistentWithPosition rho shape = case rho of
  ExpectRuntimeValue          -> shape /= BindingFunction
  ExpectRaw RawMotivePosition -> shape /= BindingWrapped
  ExpectRaw _                 -> shape == BindingRaw
  ExpectFunctionPosition _    -> shape /= BindingWrapped

-- | One-shot read of @SAW_LEAN_TRACE_POSITIONS@. Debug instrumentation
-- only: translation is pure ('TranslationMonad' has no IO), so the
-- flag is read once at module load and the trace goes through
-- 'Debug.Trace.traceM'. Nothing downstream may depend on it.
positionTraceEnabled :: Bool
positionTraceEnabled =
  unsafePerformIO (isJust <$> lookupEnv "SAW_LEAN_TRACE_POSITIONS")
{-# NOINLINE positionTraceEnabled #-}

tracePositionAt ::
  TermTranslationMonad m => ExpectedPosition -> Term -> TranslatedTerm -> m ()
tracePositionAt rho t result
  | not positionTraceEnabled = pure ()
  | otherwise =
      Debug.Trace.traceM $
        "[translateAt] rho=" ++ show rho
        ++ " head=" ++ termHeadLabel t
        ++ " shape=" ++ show (ttShape result)
        ++ (if shapeConsistentWithPosition rho (ttShape result)
              then ""
              else " INCONSISTENT")

-- | Compact head label for the position trace.
termHeadLabel :: Term -> String
termHeadLabel t =
  case asApplyAll t of
    (hd, args@(_ : _)) -> atomLabel hd ++ "@" ++ show (length args)
    _                  -> atomLabel t
  where
    atomLabel u = case unwrapTermF u of
      FTermF (Recursor rec) ->
        "Recursor:"
        ++ Text.unpack (toShortName (nameInfo (recursorDataType rec)))
      FTermF Sort{}       -> "Sort"
      FTermF ArrayValue{} -> "ArrayValue"
      FTermF StringLit{}  -> "StringLit"
      App{}               -> "App"
      Lambda{}            -> "Lambda"
      Pi{}                -> "Pi"
      Constant nm         -> Text.unpack (toShortName (nameInfo nm))
      Variable vn _       -> "$" ++ Text.unpack (vnName vn)

translateTermWithShape :: TermTranslationMonad m => Term -> m TranslatedTerm
translateTermWithShape = translateSharedAt Nothing

-- | The shared-term walk with the expected position threaded through
-- as an explicit parameter — 'Nothing' for legacy call sites that do
-- not declare one, @'Just' ρ@ when entered via 'translateAt'. The
-- position applies to THIS term only; recursive descent into subterms
-- passes its own (usually 'Nothing' until the corresponding Slice 3/4
-- step migrates the case arm). Never a reader field: an inherited
-- position that silently leaks one level too deep is exactly the
-- stale-context bug the calculus exists to kill.
translateSharedAt ::
  TermTranslationMonad m =>
  Maybe ExpectedPosition -> Term -> m TranslatedTerm
translateSharedAt mrho t =
  case t of
    STApp { stAppIndex = i } -> do
      shared <- view sharedNames <$> askTR
      case IntMap.lookup i shared of
        Just sh -> do
          let ident = sharedNameIdent sh
              tm = Lean.Var ident
          env <- view bindingEnv <$> askTR
          case Map.lookup ident env of
            Just info ->
              pure (TranslatedTerm tm (biRepr info))
            Nothing ->
              -- A shared name is bound in Γ before anything can
              -- reference it ('translateSharedDefs' extends Γ in
              -- dependency order; subterms precede superterms).
              -- Reaching this branch means the sharing invariant
              -- broke — reject loudly rather than guess a shape.
              Except.throwError (RejectedPrimitive "shared let"
                "internal error: shared subterm referenced before its \
                \binding was recorded in the translation environment")
        Nothing -> translateTermUnsharedWithShapeAt mrho t

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
      -- gamma.8: the Pi body wraps iff the convention's value-domain
      -- result rule says the function computes a runtime value —
      -- @body@ is 'asPiList'-peeled above, exactly the ret the rule
      -- inspects.
      let valueBody = phase && phaseBetaResultIsValue t
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
                     -- 'bindingEnv' during body translation so
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
                          . over bindingEnv
                              (\m -> foldr
                                (`Map.insert` BindingInfo BindingWrapped) m
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
                    -- Generic type-producing lambda (an UNDIRECTED
                    -- type family — recursor motives never route
                    -- here; the dispatch translates them at their
                    -- declared convention via
                    -- 'translateMotiveAtConvention'). Wrap only a
                    -- CONCRETE value-domain body (Vec n α, Bool, …);
                    -- a var-headed body stays raw because with no
                    -- consumer convention this path cannot commit a
                    -- polymorphic family to the wrapped carrier
                    -- (2026-07-17 doc-coherence audit M-1: this was
                    -- the last hand-composed cascade; the projection
                    -- below is behavior-identical to the old
                    -- shouldWrapBinder && not isVariableHeadTypeFamily
                    -- composite).
                    let body'' = if phase
                                    && classifyDomain body == DValue
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
translateTermUnsharedWithShape = translateTermUnsharedWithShapeAt Nothing

-- | Translate a value-level lambda at a fully-declared function
-- convention (plan Slice 3a). The convention's per-binder positions
-- drive each binder's wrap decision ('translateBinderAt') and its
-- result position drives the body adaptation — the binder/body
-- machinery no longer re-derives them from 'shouldWrapBinder'.
-- Rejects (never pads) when the declared arity does not match the
-- lambda's binder count.
-- | Translate a FUNCTION-VALUE actual at its declared convention
-- (2026-07-18 eta-adaptation design, part 2). Lambdas consume the
-- convention directly. A mapped raw-formal global (asGlobalDef +
-- SpecialTreatment rename — intNeg-family primitives) eta-adapts:
-- its produced Lean value has raw formals, but the declared
-- convention (derived from the instantiating Pi, whose TYPE-side
-- translation wraps) demands the wrapped-arrow form — so wrap it in
-- convention binders + 'buildLifted'. Module constants and
-- function-valued variables already carry wrapped formals under
-- phase-β and pass through as-produced.
translateFunctionActualAtConvention ::
  TermTranslationMonad m => FunctionConvention -> Term -> m TranslatedTerm
translateFunctionActualAtConvention conv arg =
  case unwrapTermF arg of
    Lambda{} -> translateLambdaAtConvention conv arg
    -- Prelude DEFINITIONS with rename treatments (natToInt-family)
    -- arrive as Constant nodes, not GlobalDefs — same raw-formal
    -- gate applies (2026-07-18 part 3b survivor: the asGlobalDef
    -- guard silently missed them, raw-splicing natToInt at wrapped
    -- Num#rec slots).
    Constant nm
      | ModuleIdentifier ident <- nameInfo nm ->
          etaAdaptMappedGlobal ident
    _ | Just ident <- asGlobalDef arg
        -- Partial-op globals already lowered to their WRAPPED-formal
        -- runtime wrappers by the under-application branch — eta
        -- with the raw-formal discipline would double-adapt (the
        -- intDiv_runtimeM v_0 regression); pass them through.
      -> etaAdaptMappedGlobal ident
    _ -> translateTermWithShape arg
  where
    etaAdaptMappedGlobal ident
      | Nothing <- findPartialOpContractUnderApplied ident 0
      , Right fty <- termSortOrType arg = do
          -- Raw-formal gate: only Preserve/Rename targets carry raw
          -- formals; UseMacro/UseMapsToWrapped products are already
          -- in their declared (wrapped) conventions.
          mqi <- translateIdentToIdent ident
          case mqi of
            Nothing -> translateTermWithShape arg
            Just _
              | not (null (fst (asPiList fty))) -> etaAdaptAtPi fty
              | otherwise                       -> etaAdaptFromConv
      | otherwise = translateTermWithShape arg
    -- Convention-only eta for globals whose declared type is a
    -- Constant-headed ALIAS (natToInt : PLiteral Integer — no
    -- syntactic Pi to read binders from; the 2026-07-18 rev
    -- survivor's actual mechanism). Binders are unannotated — the
    -- consuming slot's expected type infers them.
    etaAdaptFromConv = do
      produced <- translateTermWithShape arg
      case ttShape produced of
        BindingWrapped -> pure produced
        _ -> do
          names <- mapM (\i2 -> freshVariant
                           (Lean.Ident ("\951_c" ++ show (i2 :: Int) ++ "_")))
                        [0 .. length (fcArgPositions conv) - 1]
          let binders = [ Lean.Binder Lean.Explicit nm2 Nothing
                        | nm2 <- names ]
              etaArgs =
                [ TranslatedTerm (Lean.Var nm2)
                    (case pos of
                       ExpectRuntimeValue -> BindingWrapped
                       _                  -> BindingRaw)
                | (nm2, pos) <- zip names (fcArgPositions conv) ]
              shouldBind = map (isWrappedShape . ttShape) etaArgs
              pureWrap = fcResultPosition conv == ExpectRuntimeValue
          body <- buildLifted (ttLean produced) pureWrap shouldBind etaArgs
          pure (TranslatedTerm (Lean.Lambda binders body) BindingFunction)
    etaAdaptAtPi fty
      | (params@(_ : _), _) <- asPiList fty = do
          produced <- translateTermWithShape arg
          case ttShape produced of
            BindingWrapped -> pure produced
            _ -> do
              let typeIxs = typeArgPositions fty
              translateFunctionConventionBindersWith
                functionConventionValueSlot typeIxs params $
                \binders etaArgs -> do
                  let shouldBind = map (isWrappedShape . ttShape) etaArgs
                      pureWrap =
                        fcResultPosition conv == ExpectRuntimeValue
                  body <- buildLifted (ttLean produced) pureWrap
                            shouldBind etaArgs
                  pure (TranslatedTerm (Lean.Lambda binders body)
                          BindingFunction)
      | otherwise = translateTermWithShape arg

translateLambdaAtConvention ::
  TermTranslationMonad m => FunctionConvention -> Term -> m TranslatedTerm
translateLambdaAtConvention conv t = do
  let (params, body) = asLambdaList t
  if length (fcArgPositions conv) /= length params
     then Except.throwError (RejectedPrimitive "value lambda convention"
            "internal contract: declared function convention arity does \
            \not match the lambda's binder count (no silent padding)")
     else do
       -- Clear 'skipBinderWrap'/'inRecursorCaseBinder' for the body
       -- exactly as the legacy value-lambda paths do: both flags are
       -- scoped to binder-type translation, and internal Pis in the
       -- body wrap according to their own context.
       surroundingCtx <- view skipBinderWrap <$> askTR
       let introduce [] [] k = k []
           introduce (rho : rhos) ((vn, ty) : rest) k =
             translateBinderAt (Just rho) vn ty $ \bnd ->
               introduce rhos rest $ \bnds -> k (bnd : bnds)
           introduce _ _ _ =
             Except.throwError (RejectedPrimitive "value lambda convention"
               "internal contract: convention/binder length mismatch")
       introduce (fcArgPositions conv) params $ \bts ->
         localTR (set skipBinderWrap surroundingCtx
                . set inRecursorCaseBinder False) $ do
           -- Slice 3d: the body inherits the convention's declared
           -- result position through the let-sharing entry.
           bodyResult <- translateTermLetAt (Just (fcResultPosition conv)) body
           bodyLean <- ttLean <$> adaptTo (fcResultPosition conv) bodyResult
           let lam = Lean.Lambda (concatMap bindTransToBinder bts) bodyLean
           pure (TranslatedTerm lam BindingFunction)

-- | The declared convention for a recursor's motive argument (plan
-- Slice 3c). Binders are the datatype's indices followed by the
-- eliminated scrutinee; both are raw. The scrutinee reuses
-- 'StructuralRecursorFieldPosition' (the calculus's "structural
-- field" raw reason); indices are 'RawIndexPosition'. Neither is
-- 'RawTypePosition' even for sort-typed index binders — motive
-- binders keep the surrounding 'sortBinderMode', unlike the
-- type-binder slots of value-lambda conventions.
motiveConventionFor :: Int -> ExpectedPosition -> Term -> MotiveConvention
motiveConventionFor nIndices motiveResultPos motiveTerm =
  let (params, _) = asLambdaList motiveTerm
      positions =
        [ if ix < nIndices
             then ExpectRaw RawIndexPosition
             else ExpectRaw StructuralRecursorFieldPosition
        | (ix, _) <- zip [0 :: Int ..] params
        ]
  in MotiveConvention positions
       (if motiveResultPos == ExpectRuntimeValue
           then MotiveComputesRuntimeValueType
           else MotiveComputesRawType)

-- | Translate a recursor motive at its declared convention (plan
-- Slice 3c; calculus §Recursors / §Eq.rec: motive binder positions
-- and motive result position are convention fields, not local
-- rediscovery). Binders introduce at their declared raw positions via
-- 'translateBinderAt' — replacing the blanket @skipBinderWrap True@
-- flag the legacy motive path set — and the TYPE-level body wraps in
-- @Except String@ exactly when the convention says the motive
-- computes a runtime value type. Non-lambda motives (no binders to
-- declare) keep the generic translation.
translateMotiveAtConvention ::
  TermTranslationMonad m => MotiveConvention -> Term -> m Lean.Term
translateMotiveAtConvention conv motiveTerm =
  case asLambdaList motiveTerm of
    ([], _) -> translateTerm motiveTerm
    (params, body) -> do
      phase <- phaseBetaEnabled
      let introduce [] [] k = k []
          introduce (rho : rhos) ((vn, ty) : rest) k =
            translateBinderAt (Just rho) vn ty $ \bnd ->
              introduce rhos rest $ \bnds -> k (bnd : bnds)
          introduce _ _ _ =
            Except.throwError (RejectedPrimitive "recursor motive"
              "internal contract: motive convention arity does not \
              \match the motive lambda's binder count")
      introduce (mcBinderPositions conv) params $ \bts -> do
        bodyLean <- translateTermLet body
        let bodyWrapped =
              if phase && mcResultMode conv == MotiveComputesRuntimeValueType
                 then wrapExcept bodyLean
                 else bodyLean
            lam = Lean.Lambda (concatMap bindTransToBinder bts) bodyWrapped
        tracePositionAt (ExpectRaw RawMotivePosition) motiveTerm
          (TranslatedTerm lam BindingFunction)
        pure lam

-- | Unshared translation with the expected position threaded (see
-- 'translateSharedAt'). Case arms consume @mrho@ as Slice 3 migrates
-- them family by family; unmigrated arms ignore it and translate
-- bottom-up as before.
translateTermUnsharedWithShapeAt ::
  TermTranslationMonad m =>
  Maybe ExpectedPosition -> Term -> m TranslatedTerm
translateTermUnsharedWithShapeAt mrho t =
  case unwrapTermF t of
    -- Position-directed value lambda (plan Slice 3a): a lambda entered
    -- at a fully-declared function convention consumes it rather than
    -- re-deriving binder/body wrap decisions locally. Lambdas without a
    -- declared convention (Nothing, or 'ExpectFunctionPosition Nothing')
    -- fall through to the legacy generic path below.
    Lambda {} | Just (ExpectFunctionPosition (Just conv)) <- mrho ->
      translateLambdaAtConvention conv t
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
                  Left _    ->
                    -- Sort-typed head applied to args: a type
                    -- application, raw by construction (and a
                    -- 'Lean.App' never matched the old AST guess's
                    -- lambda/variable cases anyway).
                    pure (TranslatedTerm (Lean.App f' args') BindingRaw)
              _ ->
                pure (TranslatedTerm (Lean.App f' args') BindingRaw)
    _ -> do
      case unwrapTermF t of
        Constant nm -> translateConstantWithShape nm (termSortOrType t)
        _ -> do
          tm <- translateTermUnshared t
          -- Shape from the SOURCE term form, not the emitted Lean
          -- (plan Slice 2: 'bindingShapeOfTerm' is deleted):
          --   * non-empty ArrayValue emits a vecSequenceM value —
          --     wrapped;
          --   * a Lambda emits a Lean lambda — function;
          --   * a Variable's shape lives in Γ (its introduction
          --     site recorded it; absent = never bound here, keep
          --     the historical raw default);
          --   * sorts, Pis (function *types*), string literals,
          --     empty vectors, and bare recursor heads are raw.
          shape <- case unwrapTermF t of
            FTermF (ArrayValue _ vec)
              | not (null (toList vec)) -> pure BindingWrapped
            Lambda{} -> pure BindingFunction
            Variable vn _ -> do
              nenv <- view namedEnvironment <$> askTR
              env  <- view bindingEnv <$> askTR
              pure $ maybe BindingRaw biRepr ((`Map.lookup` env) =<< Map.lookup vn nenv)
            _ -> pure BindingRaw
          pure (TranslatedTerm tm shape)

applyKnownFunctionWithShape ::
  TermTranslationMonad m =>
  Term -> Lean.Term -> [Term] -> m TranslatedTerm
applyKnownFunctionWithShape fty f args = do
  ftyLean <- translateTerm fty
  -- 2026-07-18 eta part 3b: function-typed FORMALS of a phase-beta
  -- function value carry the wrapped-arrow convention derived from
  -- the formal's own Pi ('piFunctionConvention') — raw-formal
  -- global actuals (natToInt at posNegCases' pos/neg slots)
  -- eta-adapt instead of splicing raw.
  argResults <-
    sequence
      [ case snd <$> lookup ix (zip [0 :: Int ..] (fst (asPiList fty))) of
          Just bty | isJust (asPi bty) ->
            translateFunctionActualAtConvention (piFunctionConvention bty) a
          -- Args BEYOND the callee's Pi binders (dependent result is
          -- itself a function — Num_rec1's p n): the demanded slot is
          -- the phase-beta translation of the instantiated result
          -- arrow, so a function-typed actual translates at the
          -- convention of its OWN source Pi (equal to the
          -- instantiated formal here). 2026-07-18 part 3b survivor.
          Nothing | Right aty <- termSortOrType a
                  , isJust (asPi aty) ->
            translateFunctionActualAtConvention (piFunctionConvention aty) a
          _ -> translateTermWithShape a
      | (ix, a) <- zip [0 ..] args
      ]
  let argTerms = map ttLean argResults
  phase <- phaseBetaEnabled
  if phase
     then do
       -- Plan Slice 4c: the declared function-value convention drives
       -- the formal expectations; equivalence with the historical
       -- 'peelLeanPiTypes'/'isExceptStringType' inspection was proven
       -- corpus-wide by the inert oracle before this swap. The
       -- RESULT-type peel ('targetReturnsWrapped' below) is the one
       -- remaining type self-mirror on this path, tracked with
       -- 'bindingShapeOfType' for demotion.
       let (_, retType) = peelLeanPiTypes (length args) ftyLean
           fnModes = phaseBetaFunctionValueModesFor fty
           expectedWrapped =
             take (length argTerms)
               ([ m == RawValueArg | m <- fnModes ] ++ repeat False)
           expectedFunction =
             take (length argTerms)
               ([ case m of FunctionArg _ -> True; _ -> False
                | m <- fnModes ] ++ repeat False)
       let actualWrapped =
             map (isWrappedShape . ttShape) argResults
           shouldBindRaw =
             zipWith3
               (\expectsWrapped expectsFunction isWrappedActual ->
                  not expectsWrapped && not expectsFunction && isWrappedActual)
               expectedWrapped
               expectedFunction
               actualWrapped
           targetReturnsWrapped = isExceptStringType retType
           sourceResultShape = phaseBetaResultShape fty (length args)
           pureWrap =
                not targetReturnsWrapped
             && (isWrappedShape sourceResultShape || or shouldBindRaw)
           resultShape =
             if targetReturnsWrapped || pureWrap
                then BindingWrapped
                else sourceResultShape
       adapted <- zipWithM adaptWrappedFormal expectedWrapped argResults
       buildLiftedWithShape resultShape f pureWrap
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
  ident <- askTR >>= freshVariant . view nextSharedName
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
mkLet (name, rhs) = Lean.Let name [] Nothing rhs

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
translateTermLetWithShape = translateTermLetAt Nothing

-- | The let-sharing entry with the expected position threaded (plan
-- Slice 3d; calculus §Definitions "local let"). Each shared RHS
-- translates at its own natural position and Γ records its exact
-- representation (Slices 1–2); the BODY — whose value the let-chain
-- delivers — translates at the demanded position. A shared RHS
-- demanded at an incompatible position at a use site fails loudly in
-- 'adaptTo' ('ForbiddenAdaptation'); emitting separate bindings for
-- genuinely position-polymorphic shares is future work, pinned only
-- if a real fixture demands it.
translateTermLetAt ::
  TermTranslationMonad m =>
  Maybe ExpectedPosition -> Term -> m TranslatedTerm
translateTermLetAt mrho t = do
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
      shares = IntMap.assocs $ fmap fst (IntMap.filter keep occMap)
      shareTms = map snd shares
  withSharedTerms shares $ \names -> do
    -- Translate shared RHSs in dependency order, extending the shape
    -- environment after each one. Later shared RHSs may reference
    -- earlier shared names, and raw/wrapped adaptation at those use
    -- sites needs the earlier binding's shape just as much as the final
    -- body does.
    defResults <- translateSharedDefs [] names shareTms
    let defs = map ttLean defResults
        letInfos =
          [ (name, sharedBindingInfo result)
          | (name, result) <- zip names defResults
          ]
    localTR (over bindingEnv
               (\m -> foldr (uncurry Map.insert) m letInfos)) $ do
      body <- translateSharedAt mrho t
      pure (TranslatedTerm
              (foldr mkLet (ttLean body) (zip names defs))
              (ttShape body))
  where
    -- Γ record for a let-bound shared subterm: the binding carries
    -- its RHS's produced representation.
    sharedBindingInfo result =
      BindingInfo (ttShape result)
    translateSharedDefs _ [] [] = pure []
    translateSharedDefs known (name : ns) (tm : tms) = do
      result <- localTR (over bindingEnv
                 (\m -> foldr (uncurry Map.insert) m known)) $
                  translateTermUnsharedWithShape tm
      let known' = (name, sharedBindingInfo result) : known
      rest <- translateSharedDefs known' ns tms
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
       , _bindingEnv            = Map.empty
       , _natBoundsEnv          = Map.empty
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
-- | Number of binders in the (greedy) Pi spine of a translated Lean
-- term — the emitted goal's quantifier telescope. Used by the
-- goal-telescope emission pin (replay design, seventh-audit
-- amendment 1, ratified 2026-07-17): the emitted telescope must
-- match the SAWCore-side Pi count, or emission REFUSES — a dropped
-- or invented quantifier at this seam is the unsoundness path.
leanPiSpineArity :: Lean.Term -> Int
leanPiSpineArity (Lean.Pi bs t) = length bs + leanPiSpineArity t
leanPiSpineArity _ = 0

-- | The emitted goal Pi spine's binder types, outermost first
-- (2026-07-18 replay hardening: the binder-TYPE half of the
-- goal-telescope pin — the arity pin alone let a same-arity
-- wrong-type binder through).
leanPiSpineBinderTypes :: Lean.Term -> [Lean.Type]
leanPiSpineBinderTypes (Lean.Pi bs t) =
  [ ty | Lean.PiBinder _ _ ty <- bs ] ++ leanPiSpineBinderTypes t
leanPiSpineBinderTypes _ = []

-- | Coarse TYPE-FAMILY fingerprints for the telescope pin. The
-- comparison can only REFUSE emission (never admit), so coarseness
-- is safe: 'FpOther' matches anything (var-headed and exotic types
-- stay unpinned); the concrete families must agree pointwise.
data TelescopeFp = FpVec | FpBool | FpNat | FpInt | FpFun | FpOther
  deriving (Eq, Show)

sawBinderFp :: Term -> TelescopeFp
sawBinderFp ty
  | Just _ <- asGlobalApply "Prelude.Vec" ty = FpVec
  | Just i <- asGlobalDef ty, identName i == "Bool" = FpBool
  | Just _ <- asNatType ty = FpNat
  | Just i <- asGlobalDef ty, identName i == "Integer" = FpInt
  | Just _ <- asPi ty = FpFun
  | otherwise = FpOther

leanBinderFp :: Lean.Type -> TelescopeFp
leanBinderFp ty0 = go (stripExcept ty0)
  where
    stripExcept (Lean.App (Lean.Var (Lean.Ident h)) [_, t])
      | baseName h == "Except" = t
    stripExcept t = t
    go t = case t of
      Lean.Pi{} -> FpFun
      _ -> case fst (leanAppHead t) of
        Just h | baseName h == "Vec" || baseName h == "BitVec" -> FpVec
               | baseName h == "Bool" -> FpBool
               | baseName h == "Nat"  -> FpNat
               | baseName h == "Int"  -> FpInt
        _ -> FpOther
    leanAppHead (Lean.App f _) = leanAppHead f
    leanAppHead (Lean.Var (Lean.Ident h)) = (Just h, ())
    leanAppHead (Lean.ExplVar (Lean.Ident h)) = (Just h, ())
    leanAppHead _ = (Nothing, ())
    baseName h = reverse (takeWhile (/= '.') (reverse h))

-- | Pointwise fingerprint agreement; 'FpOther' on EITHER side is a
-- wildcard. Returns the first mismatch (index, saw, lean).
telescopeFpMismatch :: [Term] -> [Lean.Type] -> Maybe (Int, TelescopeFp, TelescopeFp)
telescopeFpMismatch sawTys leanTys =
  case [ (ix, s, l)
       | (ix, (sty, lty)) <- zip [0 :: Int ..] (zip sawTys leanTys)
       , let s = sawBinderFp sty
       , let l = leanBinderFp lty
       , s /= FpOther, l /= FpOther, s /= l
       ] of
    m : _ -> Just m
    []    -> Nothing

translateDefDoc ::
  TranslationConfiguration ->
  ModuleMap ->
  Lean.Ident -> Term -> Term ->
  Either TranslationError (Doc ann)
translateDefDoc configuration mm name body tp =
  fst <$> translateDefDocWithArity configuration mm name body tp

-- | 'translateDefDoc' plus the emitted goal body's Pi-spine arity
-- (see 'leanPiSpineArity').
-- | THE top-level definition convention (calculus §Definitions;
-- 2026-07-18 exception-hunt Finding 1). Single authority for the two
-- questions every top-level emitter must answer identically: the
-- position the body stands at (runtime-value iff the declared SAW
-- type is value-domain — the body then adapts through the
-- chokepoint), and whether the type ANNOTATION wraps (value-domain
-- type, OR a wrapped-produced body at a non-wrapping type, e.g. a
-- runtime-computed Nat — annotating such a def raw cannot elaborate;
-- filed 2026-07-12, fixed 2026-07-14). The three top-level emitters
-- (translateDefDocWithArity, CryptolModule, SAWModule) had
-- hand-copied this and CryptolModule's copy had already drifted
-- (missing the wrapped-body clause) — all three now call here.
topLevelDefConvention ::
  TermTranslationMonad m =>
  Term -> TranslatedTerm -> m (Lean.Term, Bool)
topLevelDefConvention tp bodyResult = do
  let wrapType = shouldWrapBinder tp
  bodyLean <- if wrapType
                 then adaptToRuntime bodyResult
                 else pure (translatedTermLean bodyResult)
  pure (bodyLean, wrapType || ttShape bodyResult == BindingWrapped)

translateDefDocWithArity ::
  TranslationConfiguration ->
  ModuleMap ->
  Lean.Ident -> Term -> Term ->
  Either TranslationError (Doc ann, Int)
translateDefDocWithArity configuration mm name body tp =
  (\(d, a, _) -> (d, a)) <$>
    translateDefDocWithTelescope configuration mm name body tp

-- | 'translateDefDocWithArity' plus the emitted body Pi spine's
-- binder types (the telescope pin's type half).
translateDefDocWithTelescope ::
  TranslationConfiguration ->
  ModuleMap ->
  Lean.Ident -> Term -> Term ->
  Either TranslationError (Doc ann, Int, [Lean.Type])
translateDefDocWithTelescope configuration mm name body tp = do
  ((bodyLean, wrapAnn, tp'), state) <-
    runTermTranslationMonad configuration Nothing mm [] [name] $ do
      -- P-1 (2026-05-06): use 'translateTermLet' on the body so
      -- shared subterms are emitted as let-bound variables rather
      -- than re-translated. Without this, hash-consed inputs with
      -- N levels of aliasing blow up exponentially (~100 GB on
      -- Salsa20). Type-side rarely shares; plain 'translateTerm'
      -- is enough there.
      bodyResult <- translateTermLetWithShape body
      (bodyLean, wrapAnn) <- topLevelDefConvention tp bodyResult
      tpLean <- translateTerm tp
      pure (bodyLean, wrapAnn, tpLean)
  let auxDecls = reverse (view topLevelDeclarations state)
      univs    = view universeVars state
      -- Annotation carrier decided by 'topLevelDefConvention' (the
      -- single definition-convention authority).
      tp'' = if wrapAnn then wrapExcept tp' else tp'
      mainDecl = mkDefinitionWith Lean.Noncomputable univs name bodyLean tp''
      -- Each 'prettyDecl' already ends with 'hardline'; 'vcat' adds
      -- another between elements, yielding one blank line between
      -- decls.
      rendered = if null auxDecls
        then Lean.prettyDecl mainDecl
        else vcat (map Lean.prettyDecl auxDecls) <> hardline <> Lean.prettyDecl mainDecl
  pure (rendered, leanPiSpineArity bodyLean,
        leanPiSpineBinderTypes bodyLean)
