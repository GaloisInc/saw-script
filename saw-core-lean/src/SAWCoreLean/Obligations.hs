{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

{- |
Module      : SAWCoreLean.Obligations
Copyright   : Galois, Inc. 2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : portable

Obligation lowering: the proof-carrying application builders, the
Nat interval domain that decides whether an @at@ bound is entailed at
the emission site (OP-2), and the local-obligation plumbing. Also the
small Lean-term builders those emitters share.
Extracted from "SAWCoreLean.Term" in the 2026-07-29 Family-3 split;
the recursive translator that CALLS these stays in
"SAWCoreLean.Term".
-}

module SAWCoreLean.Obligations
  ( buildLifted
  , buildLiftedWithShape
  , etaExpandWrappedFunctionResult
  , lowerMkStreamSound
  , buildWrappedProofCarryingApplication
  , buildRawProofCarryingApplication
  , NatInterval(..)
  , unboundedNat
  , evalNatConst
  , natIntervalOf
  , atBoundsEntailed
  , isAtIndexContract
  , lowerCheckedHelperArgsDecided
  , CheckedActual(..)
  , checkedActualTerm
  , lowerProofCarryingActuals
  , lowerCheckedApplicationHelperArgs
  , proofObligationPlaceholder
  , unsafeAssertProofScript
  , withLocalProofObligationUsing
  , withLocalProofObligation
  , withSharedLocalTerm
  , rawErrorResultShape
  , errorTermM
  , recordCtorOrderAssertion
  , withSharedTerm
  ) where

import           Control.Lens                 (over, set, view)
import           Control.Monad                (unless, zipWithM)
import qualified Control.Monad.Except         as Except
import           Control.Monad.State          (gets, modify)
import qualified Data.IntMap.Strict           as IntMap
import qualified Data.Map                     as Map
import           Data.Map                     (Map)
import           Data.Maybe                   (isJust)
import qualified Data.Set                     as Set
import           Data.Set                     (Set)
import qualified Data.Text                    as Text
import           Prelude                      hiding (fail)

import qualified Language.Lean.AST            as Lean

import           SAWCore.Name
import           SAWCore.Recognizer
import           SAWCore.SharedTerm
import           SAWCore.Term.Functor

import           SAWCoreLean.Contracts
import           SAWCoreLean.Convention
import           SAWCoreLean.Monad
import           SAWCoreLean.Calculus


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
      shape ->
        Except.throwError (ForbiddenAdaptation
          "IndexArg (raw index position)"
          (Text.pack (show shape)))
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
