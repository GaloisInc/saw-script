{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

{- |
Module      : SAWCoreLean.Calculus
Copyright   : Galois, Inc. 2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : portable

The position/callee calculus RULES: the functions that decide,
for a given SAWCore position, which convention the calculus assigns
it. "SAWCoreLean.Convention" holds the vocabulary those rules speak
(positions, arg/result modes, binding shapes, the translation
monad); this module holds the decisions, plus the identifier
targeting that names what a decided callee is emitted as.
Extracted from "SAWCoreLean.Term" in the 2026-07-29 Family-3 split,
completing the 2026-07-17 'Convention.hs' extraction. Nothing here
recurses into the translator: every function is a decision over
already-available information, which is why the module sits below
"SAWCoreLean.Term" with no cycle.
-}

module SAWCoreLean.Calculus
  ( isVariableHeadTypeFamily
  , typeArgPositions
  , quantifierShadow
  , typeArgPositionsBinders
  , isTypeProducing
  , qualify
  , defaultIdentTarget
  , translateIdentToIdent
  , translateIdentToQualifiedIdent
  , varHeadedInstantiation
  , instantiationMode
  , phaseBetaArgModesFor
  , phaseBetaBindFromMode
  , phaseBetaFunctionValueModesFor
  , natValueResult
  , phaseBetaResultIsValue
  , phaseBetaResultShape
  , rawModeResultShape
  , functionConventionValueSlot
  , functionConventionResultIsValue
  , recursorMotiveResultPosition
  , recursorMotiveFunctionConvention
  , piFunctionConvention
  , wrappedHelperTypeIsWrapped
  , wrappedHelperFunctionValueSlot
  , wrappedHelperFunctionResultIsValue
  , leanBaseName
  , rawLogicalCalleeForIdent
  , rawLogicalCalleeForRecursor
  , isPreludeIdent
  , standaloneEqualitySubjectRep
  , subjectRepForCarrier
  , traceSubjectRep
  , eqRecConventionForStandalone
  , traceEqRecConvention
  , subjectCarrier
  , subjectTerm
  , explicitCoreNameAtArgUniverse
  , adaptTo
  , adaptToRuntime
  , adaptWrappedFormal
  , shapeConsistentWithPosition
  , positionTraceEnabled
  , termHeadLabel
  , motiveConventionFor
  , leanIdentStr
  ) where

import           Control.Lens                 (view)
import qualified Control.Monad.Except         as Except
import qualified Data.IntSet                  as IntSet
import           Data.List                    (findIndex)
import           Data.Maybe                   (isJust)
import qualified Data.Text                    as Text
import qualified Debug.Trace
import           Prelude                      hiding (fail)
import           System.Environment           (lookupEnv)
import           System.IO.Unsafe             (unsafePerformIO)

import qualified Language.Lean.AST            as Lean

import           SAWCore.Module               (Ctor(..), DataType(..), Def(..), ResolvedName(..), resolveNameInMap)
import           SAWCore.Name
import           SAWCore.Recognizer
import           SAWCore.SharedTerm
import           SAWCore.Term.Functor

import           SAWCoreLean.Convention
import           SAWCoreLean.Monad
import           SAWCoreLean.SpecialTreatment


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
--
-- A binder the inner term never mentions gets NO shadow. The shadow
-- is emitted without a type annotation, so @let y := Pure.pure y@ for
-- an unreferenced @y@ leaves Lean nothing to infer the monad from and
-- elaboration dies with @typeclass instance problem is stuck /
-- Pure (?m.N y)@. That is not a corner case: any Cryptol property
-- carrying a parameter it happens not to use hits it, including one
-- unused parameter among several used ones
-- (@\\(x : [8]) (y : [8]) -> x == x@ failed on @y@ alone). Dropping
-- the binding is safe rather than merely convenient: 'Lean.identOccursIn'
-- over-reports by construction, so a 'False' answer means the name is
-- absent from the term the @let@ would scope over, and @let n := e; b@
-- with @n@ absent from @b@ is just @b@.
--
-- Found 2026-07-31 by executing the getting-started documentation
-- rather than reading it; surveyed and filed in TODO.md the same day.
quantifierShadow ::
  [(VarName, Term)] -> [Lean.PiBinder] -> Lean.Term -> Lean.Term
quantifierShadow params piBinders body =
  foldr shadowOne body (zip params piBinders)
  where
    pureVar = Lean.Var (Lean.Ident "Pure.pure")
    shadowOne :: ((VarName, Term), Lean.PiBinder) -> Lean.Term -> Lean.Term
    shadowOne ((_, ty), Lean.PiBinder _ mName _) inner
      | shouldWrapBinder ty
      , Just name <- mName
      , Lean.identOccursIn name inner =
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
-- more.
--
-- TOMBSTONE: argumentBindPlan — Slice 4b: bind plan from emitted types, not declared modes
-- TOMBSTONE: polymorphicFormalInstantiatedExpected — Slice 4b/debts: Pi-only instantiation predicate
--
-- Two type-classification self-mirrors remain
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
--
-- TOMBSTONE: lowerRawLogicalCalleeRawMode — debts slice: mode-guard over false raw-mode records
rawModeResultShape :: Term -> Int -> BindingShape
rawModeResultShape fty nApplied
  | nApplied < length binders = BindingFunction
  | isJust (asPi ret) = BindingFunction
  | otherwise = BindingRaw
  where
    (binders, ret) = asPiList fty

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
        (Just (recursorMotiveFunctionConvention elimSort motiveBody))
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
    -- B-3 (2026-07-19, calculus-doc audit): a Prop-kinded family
    -- application is a PROPOSITION — the raw reason reflects the
    -- role. Emission-neutral (R(Raw*, tau) = T(tau)); label only.
    DVarRaw   -> ExpectRaw RawPropositionPosition

-- | The declared function convention of a function-motive recursor
-- (plan Slice 6.1): the generic Pi derivation
-- ('piFunctionConvention') plus the ELIMINATION-SORT gate the motive
-- position owns (B-4, 2026-07-19 calculus-doc audit): under Prop
-- elimination the motive's fully-applied result is a PROPOSITION
-- regardless of what the generic domain projection says about the
-- body type — in particular the backstop class (constant-headed
-- non-Eq props classify 'DValue') must not declare a wrapping
-- result. Unreachable in the pinned corpus (no Prop-eliminating
-- function-motive rows); the declared default is now correct
-- instead of merely loud. Binder positions are sort-independent by
-- construction. The emitted recursor call inhabits the translated
-- motive Pi type, so this convention is the truthful record of what
-- a fully-applied function-motive recursor produces.
recursorMotiveFunctionConvention :: Sort -> Term -> FunctionConvention
recursorMotiveFunctionConvention elimSort fty
  | elimSort == propSort =
      conv { fcResultPosition = ExpectRaw RawPropositionPosition }
  | otherwise = conv
  where
    conv = piFunctionConvention fty

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
    -- B-4 (2026-07-19, calculus-doc audit): the result position
    -- PROJECTS classifyDomain — the single domain authority —
    -- instead of re-walking its own head dispatch. Equivalence with
    -- the former local dispatch, class by class: DRawType covers the
    -- old Sort and Num arms; DRawProp the Eq arm; DValue/DVarValue
    -- are exactly 'phaseBetaResultIsValue' truth; the DNat split is
    -- that function's DNat arm ('natValueResult') followed by the
    -- old Nat-index fallthrough; DVarRaw fell through to the raw
    -- default (natValueResult is False off Nat).
    resultPos = case classifyDomain ret of
      DRawType  -> ExpectRaw RawTypePosition
      DRawProp  -> ExpectRaw RawPropositionPosition
      -- B-3 role-reflecting label: a Prop-kinded family result is a
      -- proposition (was the RawValuePosition default;
      -- emission-neutral, R(Raw*, tau) = T(tau)).
      DVarRaw   -> ExpectRaw RawPropositionPosition
      -- Unreachable ('asPiList' peels every syntactic Pi, so ret is
      -- never Pi-headed) — declared for D-totality: a function
      -- result carries its own derived convention, mirroring
      -- 'recursorMotiveResultPosition'.
      DFunction -> ExpectFunctionPosition (Just (piFunctionConvention ret))
      DNat
        | natValueResult fty -> ExpectRuntimeValue
        | otherwise          -> ExpectRaw RawIndexPosition
      DValue    -> ExpectRuntimeValue
      DVarValue -> ExpectRuntimeValue

-- | The DECLARED UseMapsToWrapped-callback convention (calculus
-- §Callee Conventions, wrapped-helper sub-case; 2026-07-18
-- exception hunt, finding 2 — reclassified 2026-07-19). The
-- AUTHORITY for these slots is the SUPPORT LIBRARY's Lean helper
-- signatures (genWithBoundsM/iteM-family callbacks), NOT the domain
-- map: those signatures wrap their Nat callback formals
-- (@Except String Nat@), so this convention deliberately deviates
-- from D's conditional-Nat rule — folding it into D would break
-- real callbacks. The deviation is DECLARED here, in one place,
-- per-class:
--
--   * 'DNat': WRAPPED (the declared deviation — helper signatures);
--   * 'DValue' / 'DVarValue': wrapped, as D says (the backstop
--     class — constant-headed non-Eq props classifying 'DValue' —
--     wraps and stays loud, same as every other consumer);
--   * 'DVarRaw': RAW — aligned to D 2026-07-19 (a Prop-kinded
--     family formal is a proof; the previous shape-blind
--     disjunction wrapped it, ill-typed downstream and only
--     loud-caught by the Prop backstop);
--   * types, propositions, functions ('DRawType' / 'DRawProp' /
--     'DFunction'): raw, as D says.
wrappedHelperTypeIsWrapped :: Term -> Bool
wrappedHelperTypeIsWrapped ty = case classifyDomain ty of
  DValue    -> True
  DVarValue -> True
  DNat      -> True   -- declared deviation: helper signatures wrap Nat
  DVarRaw   -> False  -- aligned to D: Prop-kinded family = proof, raw
  DRawType  -> False
  DRawProp  -> False
  DFunction -> False

wrappedHelperFunctionValueSlot :: [Int] -> Int -> Term -> Bool
wrappedHelperFunctionValueSlot typeIxs ix ty =
  ix `notElem` typeIxs && wrappedHelperTypeIsWrapped ty

wrappedHelperFunctionResultIsValue :: Term -> Bool
wrappedHelperFunctionResultIsValue = wrappedHelperTypeIsWrapped

-- | The final dot-component of an emitted identifier. Arithmetic
-- helpers emit unqualified (artifacts @open@ the primitives
-- namespace) while the numeral macros emit fully qualified; matching
-- the base name covers both spellings of the same helper.
leanBaseName :: Lean.Ident -> String
leanBaseName (Lean.Ident s) =
  case break (== '.') s of
    (_, '.' : rest) -> leanBaseName (Lean.Ident rest)
    (chunk, _)      -> chunk

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
-- This is one convention among several, not a universal authority —
-- but the old surround-declared entry point (which let a surround
-- like 'unsafeAssert' assert its ρ_eq directly, bypassing the
-- operand-domain read) is deleted; 'unsafeAssert' now routes its
-- operands through THIS function like every other caller (Term.hs,
-- @standaloneEqualitySubjectRep "unsafeAssert"@).
--
-- TOMBSTONE: equalityPropositionAtSubjectRep — debts slice: surround-declared rho_eq entry point
-- TOMBSTONE: subjectRepFromTranslatedOperands — Slice 5a: renamed to standaloneEqualitySubjectRep
standaloneEqualitySubjectRep ::
  TermTranslationMonad m =>
  Text.Text -> [TranslatedTerm] -> m EqualitySubjectRep
standaloneEqualitySubjectRep who operands
  | any (isFunctionShape . ttShape) operands
  , any (isWrappedShape . ttShape) operands =
      Except.throwError (RejectedPrimitive who
        "raw logical equality with a function-shaped subject on one \
        \side and a wrapped runtime computation on the other does not \
        \determine a carrier uniquely; this signals an upstream \
        \classification bug, so the backend rejects instead of \
        \coercing either side")
  | otherwise = do
      let rep | any (isFunctionShape . ttShape) operands =
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

subjectCarrier :: EqualitySubjectRep -> Lean.Term -> Lean.Term
subjectCarrier EqualitySubjectRuntimeValue ty = wrapExcept ty
subjectCarrier (EqualitySubjectRaw _) ty = ty
subjectCarrier EqualitySubjectRawFunction ty = ty
-- The type-subject carrier is the translation of a SORT — raw and
-- ambient coincide on sorts, so the caller-provided translation is
-- already the carrier.
subjectCarrier EqualitySubjectTypeImage ty = ty

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
    -- A wrapped-arrow function is a FUNCTION, not a wrapped value:
    -- its 'Except' level is on the formals and result, not on the
    -- term itself, so 'Pure.pure' would be the wrong adapter and no
    -- other one applies (2026-07-29, F-1).
    (ExpectRuntimeValue, BindingWrappedArrow{}) -> forbidden
    (ExpectRaw _, BindingRaw)             -> deliver (ttLean result) BindingRaw
    (ExpectRaw RawMotivePosition, BindingFunction) ->
      deliver (ttLean result) BindingFunction
    (ExpectRaw _, _)                      -> forbidden
    (ExpectFunctionPosition _, BindingFunction) ->
      deliver (ttLean result) BindingFunction
    -- Shape-PRESERVING, deliberately: the declared formal modes are
    -- the only record of what the body actually is, and dropping
    -- them here would restore F-1 one adaptation later.
    (ExpectFunctionPosition _, BindingWrappedArrow modes) ->
      deliver (ttLean result) (BindingWrappedArrow modes)
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
  ExpectRuntimeValue          -> not (isFunctionShape shape)
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

-- | Every binder in the term — at ANY depth, Pi or Lambda or Let —
-- whose declared type is a Lean sort OTHER than @Prop@, rendered as
-- @"name : sort"@. Drives the F-5 goal-emission gate (see
-- 'UnrepresentableGoalShape').
--
-- Why the whole term and not just 'leanPiSpineBinderTypes': the
-- narrowing is a property of the BINDER, not of the outermost
-- telescope. @(f : (a : sort 0) -> ...) -> ...@ hides one under a
-- binder type, where the spine walk reports a 'Lean.Pi' and stops.
--
-- Why 'Lean.Prop' is EXCLUDED: SAWCore's @Prop@ maps to Lean's
-- @Prop@ with no cumulativity gap, so a proposition binder is
-- faithful. Only @sort k@ binders narrow (@sort 0@, which subsumes
-- @Prop@ in SAWCore but not in Lean) or go universe-polymorphic
-- (@sort k ≥ 1@).
leanIdentStr :: Lean.Ident -> String
leanIdentStr (Lean.Ident s) = s
