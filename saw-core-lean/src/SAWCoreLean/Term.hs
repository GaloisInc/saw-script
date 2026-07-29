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
  , translateGoalDocWithTelescope
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
import           Control.Monad                (unless, when, zipWithM)
import qualified Control.Monad.Except         as Except
import           Control.Monad.Reader         (asks)
import           Control.Monad.State          (gets, modify)
import           Data.Foldable                (toList)
import qualified Data.IntMap.Strict           as IntMap
import qualified Data.IntSet                  as IntSet
import           Data.List                    (elemIndex, intercalate)
import qualified Data.Map                     as Map
import           Data.Maybe                   (fromMaybe, isJust, isNothing)
import qualified Data.Set                     as Set
import qualified Data.Text                    as Text
import qualified Debug.Trace
import           Prelude                      hiding (fail)
import           Prettyprinter                (Doc, hardline, vcat)

import qualified Language.Lean.AST            as Lean
import qualified Language.Lean.Pretty         as Lean

import           SAWCore.Module               (Ctor(..), CtorArg(..), CtorArgStruct(..), Def(..), ModuleMap, ResolvedName(..), lookupVarIndexInMap, resolveNameInMap)
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
import           SAWCoreLean.Calculus
import           SAWCoreLean.Obligations
import           SAWCoreLean.Signature


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

-- | Lower a type-image obligation primitive
-- ('Contracts.typeImageObligationPrimitives'): the obligation is the
-- ambient type translation of the application's OWN SAWCore type —
-- the instantiated axiom statement under T, read off the term's type
-- tag. Obligation = T(prop) by construction: it matches every
-- consumer's translation of the same proposition with zero
-- hand-mirrored emission shapes, and any untranslatable content in
-- the statement fails loudly through the ordinary translation
-- rejections. The result is the bound local evidence (a proof:
-- 'BindingRaw').
lowerTypeImageObligation ::
  TermTranslationMonad m => Ident -> Term -> m TranslatedTerm
lowerTypeImageObligation ident appTerm =
  case termSortOrType appTerm of
    Right propTm -> do
      prop <- translateTerm propTm
      tm <- withLocalProofObligation
              (Lean.Ident "h_proof_")
              prop
              pure
      pure (TranslatedTerm tm BindingRaw)
    Left _ ->
      Except.throwError (RejectedPrimitive
        (Text.pack (identName ident))
        "type-image obligation primitive's application is a sort, \
        \not a proposition — the contract table entry is wrong")

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
translateIdentWithArgsWithShape i args = do
  phase <- phaseBetaEnabled
  case rawLogicalTwin (identName i) of
    -- Raw-twin lowering (2026-07-19, vector-lemma proof-primitive
    -- batch): inside RAW translation mode the wrapped-helper and
    -- checked-application conventions have no denotation — their
    -- Lean targets take Except-wrapped formals and thread checked
    -- index evidence, neither of which exists in raw logical
    -- content (obligation statements, axiom types). Prelude idents
    -- with a DECLARED raw twin ('SpecialTreatment.rawLogicalTwin' —
    -- the raw support definition that IS the ident's raw
    -- denotation) lower to an ordinary raw application BEFORE the
    -- contract guards, which would otherwise route them into the
    -- wrapped machinery; everything else keeps its current loud
    -- raw-mode behavior.
    Just twin
      | not phase
      , identModule i == mkModuleName ["Prelude"] -> do
          argLeans <- mapM translateTerm args
          pure (TranslatedTerm
            (if null args
               then Lean.Var twin
               else Lean.App (Lean.Var twin) argLeans)
            BindingRaw)
    _ -> dispatchIdentWithArgsWithShape i args

dispatchIdentWithArgsWithShape ::
  TermTranslationMonad m => Ident -> [Term] -> m TranslatedTerm
dispatchIdentWithArgsWithShape i args
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
                -- S-2 (2026-07-25, second audit): raw-position fixes
                -- are now REJECTED rather than given the raw
                -- proof-carrying contract.
                --
                -- That contract's sole condition is uniqueness among
                -- ALL fixed points, which is purely EXTENSIONAL and
                -- therefore cannot observe SAW's operational
                -- divergence — so it is honestly dischargeable while
                -- SAW's meaning is ⊥. Witness (lane-fix):
                --   parse_core "fix Nat (\\(n : Nat) -> mulNat n 0)"
                -- routes here (FixUnrecognized, shouldWrapBinder Nat =
                -- False), and its obligation is provable in three
                -- tokens, ⟨0, rfl, fun y h => h.symm⟩, because
                -- `Nat.mul y 0` reduces to 0 — while SAW's `mulNat`
                -- recurses on its FIRST argument, so `let x = mulNat
                -- x 0 in x` must force `x` to compute `x`.
                --
                -- No checker hardening can catch this: every gate goes
                -- green honestly. The code previously hedged "believed
                -- corpus-unreachable ... and census-checked" — but a
                -- census is not a proof, and the protection it relied
                -- on is ACCIDENTAL: ordinary recursive Cryptol escapes
                -- only because its value-domain codomain is
                -- `Except String T`, where the constant-error family
                -- is a fixed point of essentially every bind-sequenced
                -- body, so uniqueness fails for divergent shapes. That
                -- does not extend to DNat / DRawProp / DRawType.
                --
                -- Reject-until-needed (user decision 2026-07-25):
                -- there are ZERO corpus uses of saw_fix_choose_raw, so
                -- this costs nothing today and fails loudly if a real
                -- example ever needs it. Re-enabling requires a
                -- productivity-gated contract, not a census — see the
                -- 0.03 fragment-semantics programme.
                Except.throwError (RejectedPrimitive "Prelude.fix"
                  ("raw-position fix (function/proof/index result): the "
                   <> "raw unique-fixed-point contract is extensional "
                   <> "and cannot observe divergence, so it is "
                   <> "dischargeable for fixes whose SAW meaning is "
                   <> "bottom. Rejected pending a productivity-gated "
                   <> "raw contract."))
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
  | i `elem` [ "Prelude.toIntMod", "Prelude.fromIntMod"
             , "Prelude.intModEq", "Prelude.intModAdd"
             , "Prelude.intModSub", "Prelude.intModMul"
             , "Prelude.intModNeg" ]
  , (modArg : _) <- args
  = do
      -- IntMod modulus gate (2026-07-23, user decision: STRICT).
      -- SAW has NO coherent `Z 0` semantics: the concrete evaluator
      -- CRASHES (toIntModOp is Haskell `x mod 0`,
      -- SAWCore.Simulator.Concrete), SBV lowers fromIntMod to SMT
      -- `rem x 0` (UNINTERPRETED in SMT-LIB Ints), and What4 applies
      -- its own mod-by-zero convention — three backends, three
      -- behaviors. The Lean realizations (Int.fmod) are total, so an
      -- ungated `IntMod 0` obligation would assign Lean semantics
      -- where SAW has none (differential/intmod_zero_boundary pins
      -- the concrete crash). The gate demands a modulus that
      -- evaluates to a CONCRETE literal >= 1; a non-literal modulus
      -- also rejects — a syntactic nonzero check on open terms would
      -- under-approximate the semantic property (the recurring
      -- seam-bug shape), and Cryptol's `Z n` (n >= 1, monomorphized
      -- to literals) never produces one.
      modLean <- withRawTranslationMode (translateTerm modArg)
      case evalNatConst modLean of
        Just 0 ->
          Except.throwError (RejectedPrimitive
            (Text.pack (identName i))
            ("IntMod modulus 0 is rejected: SAW has no coherent "
             <> "Z 0 semantics (concrete evaluation crashes with "
             <> "mod-by-zero; symbolic backends disagree), so the "
             <> "backend refuses to assign Lean semantics to it."))
        Just _ -> originalDispatchWithShape i args
        Nothing ->
          Except.throwError (RejectedPrimitive
            (Text.pack (identName i))
            ("non-literal IntMod modulus is rejected: the nonzero-"
             <> "modulus gate needs a concrete literal (Cryptol's "
             <> "Z n arrives monomorphized; polymorphic moduli "
             <> "would need proof-carrying nonzero evidence, which "
             <> "does not exist yet)."))
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
dispatchIdentWithArgsWithShape i args = originalDispatchWithShape i args

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

-- NOTE (S-2, 2026-07-25): `lowerFixProofObligation` — which
-- emitted the raw `saw_fix_unique_exists_raw` /
-- `saw_fix_choose_raw` contract for raw-position fixes — was
-- DELETED with the S-2 rejection above, not merely bypassed.
-- The contract is extensional and cannot observe divergence, so
-- leaving a reachable emitter for it would be one re-wire away
-- from reintroducing a hole every gate passes honestly. The
-- Lean-side contract remains in the support library, unused by
-- any emitter; re-enabling needs a productivity-gated
-- replacement (0.03 fragment semantics), not this function.

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
       let decl = mkDefinitionWith Lean.Noncomputable univs aliasIdent
                    body typeLean
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
       postTrans <- recursorPostArgs (recursorSort crec) motiveBody postResults
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
           , recursorFunctionResultCanPropagate (recursorSort crec) motiveBody -> do
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
              recursorFunctionResultCanPropagate (recursorSort rec) motiveBody)
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
    recursorFunctionResultCanPropagate :: Sort -> Term -> Bool
    recursorFunctionResultCanPropagate elimSort fty =
      not (null (fcArgPositions conv)) &&
      fcResultPosition conv == ExpectRuntimeValue
      where
        conv = recursorMotiveFunctionConvention elimSort fty

    -- Post-scrutinee actuals adapt at the declared motive function
    -- convention's binder positions (plan Slice 6.1): runtime-value
    -- slots lift, every raw slot splices.
    recursorPostArgs ::
      TermTranslationMonad m =>
      Sort -> Term -> [TranslatedTerm] -> m [Lean.Term]
    recursorPostArgs elimSort fty argResults =
      sequence
        [ case drop ix positions of
            ExpectRuntimeValue : _ -> adaptToRuntime result
            _                      -> pure (ttLean result)
        | (ix, result) <- zip [0..] argResults
        ]
      where
        positions =
          fcArgPositions (recursorMotiveFunctionConvention elimSort fty)

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
        -- Type-image obligation primitives (2026-07-19): lowered
        -- HERE because only the application site holds the full
        -- term whose type tag carries the instantiated axiom
        -- statement ('lowerTypeImageObligation').
        Just ident
          | findTypeImageObligation ident (length args) ->
              lowerTypeImageObligation ident t
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
       -- Audit-2 F-6: 'reservedIdents' alone was Lean keywords plus
       -- a handful of sorts, which said nothing about the ~130
       -- support-library short names the emitter writes BARE because
       -- 'implicitlyOpenedModules' are `open`ed. A generated binder
       -- named `Vec` shadowed the library `Vec` throughout a goal
       -- body full of `Vec n Bool`; instances failed loudly, but by
       -- ACCIDENT, not by construction. Seeding the emitter's own
       -- bare-name set makes 'freshVariant' rename such a binder
       -- instead. Binder names are internal to the emitted term, so
       -- this renaming is invisible to users — contrast the
       -- DEFINITION-name case (F-7), which is user-facing and
       -- refuses rather than renames.
       , _unavailableIdents = Set.unions [ reservedIdents
                                         , emitterBareNames configuration
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

translateDefDoc ::
  TranslationConfiguration ->
  ModuleMap ->
  Lean.Ident -> Term -> Term ->
  Either TranslationError (Doc ann)
translateDefDoc configuration mm name body tp =
  fst <$> translateDefDocWithArity configuration mm name body tp

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
translateDefDocWithTelescope = translateDocWithTelescope DefEmission

-- | 'translateDefDocWithTelescope' for a PROOF GOAL. Identical
-- emission, plus the two goal-shape gates described on
-- 'UnrepresentableGoalShape' (audit-2 A-2/A-9 and F-5).
--
-- The gates are goal-only on purpose: module and term emission
-- legitimately bind types and stay universe-polymorphic. It is only
-- the goal statement that has to mean exactly what the SAWCore
-- obligation means.
translateGoalDocWithTelescope ::
  TranslationConfiguration ->
  ModuleMap ->
  Lean.Ident -> Term -> Term ->
  Either TranslationError (Doc ann, Int, [Lean.Type])
translateGoalDocWithTelescope = translateDocWithTelescope GoalEmission

-- | Which of the two emission contracts 'translateDocWithTelescope'
-- is serving. See 'translateGoalDocWithTelescope'.
data EmissionKind = DefEmission | GoalEmission
  deriving (Eq, Show)

translateDocWithTelescope ::
  EmissionKind ->
  TranslationConfiguration ->
  ModuleMap ->
  Lean.Ident -> Term -> Term ->
  Either TranslationError (Doc ann, Int, [Lean.Type])
translateDocWithTelescope kind configuration mm name body tp = do
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
  -- Goal-shape gates (audit-2 A-2/A-9, F-5). Ordered so the
  -- universe report comes first: a sort-@k@ binder trips both, and
  -- the universe message names the concrete Lean shape.
  when (kind == GoalEmission) $ do
    unless (null univs) $
      Except.throwError $ UnrepresentableGoalShape
        (Text.pack ("a universe-polymorphic sort (universe parameters " ++
                    intercalate ", " univs ++ ")"))
        ("the goal def would be emitted as `" <> Text.pack (leanIdentStr name) <>
         ".{" <> Text.pack (intercalate ", " univs) <>
         "}` while its `_holds` stub names the bare `" <>
         Text.pack (leanIdentStr name) <>
         "`, proving it at one\ninferred level instead of universally — " <>
         "a strictly weaker theorem than the SAWCore obligation.")
    case leanSortBinders bodyLean of
      []       -> pure ()
      offenders ->
        Except.throwError $ UnrepresentableGoalShape
          (Text.pack ("a sort-typed binder (" ++
                      intercalate "; " offenders ++ ")"))
          ("SAWCore admits `Prop <= sort 0` cumulativity and instantiates " <>
           "a sort binder\nat propositions; Lean 4 has no term " <>
           "cumulativity, so the emitted `Type` binder\nomits that " <>
           "instantiation class and the Lean statement is strictly WEAKER.")
  -- Annotation carrier decided by 'topLevelDefConvention' (the
  -- single definition-convention authority).
  let tp'' = if wrapAnn then wrapExcept tp' else tp'
  let mainDecl = mkDefinitionWith Lean.Noncomputable univs name bodyLean tp''
      -- Each 'prettyDecl' already ends with 'hardline'; 'vcat' adds
      -- another between elements, yielding one blank line between
      -- decls.
      rendered = if null auxDecls
        then Lean.prettyDecl mainDecl
        else vcat (map Lean.prettyDecl auxDecls) <> hardline <> Lean.prettyDecl mainDecl
  pure (rendered, leanPiSpineArity bodyLean,
        leanPiSpineBinderTypes bodyLean)
