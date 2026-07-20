{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

{- |
Module      : SAWCoreLean.Contracts
Copyright   : Galois, Inc. 2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : portable

The declarative proof-carrying contract tables: partial-operation
contracts (checked division/modulus/indexing families),
checked-application contracts (bounds-carrying helper conventions),
and proof-primitive contracts (obligation statements for SAWCore
proof combinators), together with their finders and the evidence
proof scripts. Pure tables plus small Lean-AST builders over the
translation monad — the @lower*@ interpreters that consume these
tables live in "SAWCoreLean.Term". Extracted from
"SAWCoreLean.Term" in the 2026-07-17 module split (SWE review
finding 2).
-}

module SAWCoreLean.Contracts
  ( module SAWCoreLean.Contracts
  ) where

import qualified Control.Monad.Except         as Except
import           Data.List                    (find)
import qualified Data.Set                     as Set
import           Data.Set                     (Set)
import           Prelude                      hiding (fail)

import qualified Language.Lean.AST            as Lean

import           SAWCore.Name

import           SAWCoreLean.Convention
import           SAWCoreLean.Monad

data PartialOpContract = PartialOpContract
  { pocModule      :: ModuleName
  , pocName        :: String
  , pocArity       :: Int
  , pocBuildProp   :: [Lean.Term] -> Lean.Term
  , pocConvention  :: PartialOpConvention
    -- | Under-applied lowering (2026-07-18 wrapper design, audited):
    -- the runtime-checked support wrapper this op lowers to at LESS
    -- than contract arity (dictionary fields, partial applications),
    -- with its declared argument modes (all value formals wrapped —
    -- the translated dictionary-field slot type; no proof argument;
    -- throws at the contract-excluded point).
  , pocRuntimeWrapper      :: Lean.Ident
  , pocRuntimeWrapperModes :: [ArgMode]
  }

data PartialOpConvention
  = PartialOpRaw Lean.Ident
    -- ^ Raw checked helper (divNat-family); argument binds are driven
    -- by 'argumentBindPlan' until Slice 4b/4c fold this into
    -- 'CalleePhaseBetaDefinition'.
  | PartialOpWrapped Lean.Ident [ArgMode]
    -- ^ Wrapped checked helper with declared per-argument modes
    -- (plan Slice 4a/4b): bitvector widths are 'IndexArg', value
    -- operands 'RuntimeArg'.

data CheckedApplicationContract = CheckedApplicationContract
  { cacModule     :: ModuleName
  , cacName       :: String
  , cacArity      :: Int
  , cacBuildProp  :: Maybe ([Lean.Term] -> Lean.Term)
  , cacHelperName :: Lean.Ident
  , cacArgModes   :: [ArgMode]
    -- ^ Declared per-argument modes (calculus §Callee Conventions,
    -- plan Slice 4a). 'ProofArg' entries are dropped from the helper
    -- argument list; 'cacBuildProp' indexes into the POST-drop list.
  , cacResultMode :: ResultMode
    -- ^ Always 'RuntimeResult' for the current checked helpers: the
    -- helper returns @Except String T@.
  }

data ProofPrimitiveContract = ProofPrimitiveContract
  { ppcModule    :: ModuleName
  , ppcName      :: String
  , ppcArity     :: Int
  , ppcArgModes  :: [ArgMode]
    -- ^ Declared per-argument modes (plan Slice 4c). Interpretation
    -- is raw-LOGICAL for every raw-family mode: 'TypeArg',
    -- 'IndexArg', 'RawValueArg', and 'ProofArg' actuals all translate
    -- under 'withRawTranslationMode' (proof primitives state
    -- propositions over raw logical terms); 'RuntimeArg' actuals
    -- adapt to wrapped runtime values. The labels document the true
    -- slot roles per the SAWCore signatures.
  , ppcBuildProp :: forall m. TermTranslationMonad m => [Lean.Term] -> m Lean.Term
  , ppcUseProof  :: forall m. TermTranslationMonad m => [Lean.Term] -> Lean.Term -> m Lean.Term
  }

partialOpContracts :: [PartialOpContract]
partialOpContracts =
  [ natBinaryPartial "divNat"    "divNat_checked"
  , natBinaryPartial "modNat"    "modNat_checked"
  , natBinaryPartial "divModNat" "divModNat_checked"
  , intBinaryPartial "intDiv"    "intDiv_checkedM"
  , intBinaryPartial "intMod"    "intMod_checkedM"
  , PartialOpContract preludeModule "ratio" 2
      (wrappedNonzeroArg (Lean.Var (Lean.Ident "Int")) 1)
      (wrappedBinary "ratio_checkedM")
      (Lean.Ident "ratio_runtimeM")
      [RuntimeArg, RuntimeArg]
  , PartialOpContract preludeModule "rationalRecip" 1
      (wrappedNonzeroArg (Lean.Var (Lean.Ident "Rational")) 0)
      (PartialOpWrapped (Lean.Ident "rationalRecip_checkedM")
        [RuntimeArg])
      (Lean.Ident "rationalRecip_runtimeM")
      [RuntimeArg]
  , bvBinaryPartial "bvUDiv" "bvUDiv_checkedM"
  , bvBinaryPartial "bvURem" "bvURem_checkedM"
  , bvSignedBinaryPartial "bvSDiv" "bvSDiv_checkedM"
  , bvSignedBinaryPartial "bvSRem" "bvSRem_checkedM"
  , cryptolSignedBVPartial "ecSDiv" "ecSDiv_checkedM"
  , cryptolSignedBVPartial "ecSMod" "ecSMod_checkedM"
  ]
  where
    preludeModule = mkModuleName ["Prelude"]
    cryptolModule = mkModuleName ["Cryptol"]
    natBinaryPartial source target =
      PartialOpContract preludeModule source 2
        (rawNonzeroArg (Lean.Var (Lean.Ident "Nat")) 1)
        (PartialOpRaw (Lean.Ident target))
        (Lean.Ident (source ++ "_runtimeM"))
        [RuntimeArg, RuntimeArg]
    intBinaryPartial source target =
      PartialOpContract preludeModule source 2
        (wrappedNonzeroArg (Lean.Var (Lean.Ident "Int")) 1)
        (wrappedBinary target)
        (Lean.Ident (source ++ "_runtimeM"))
        [RuntimeArg, RuntimeArg]
    wrappedBinary target =
      PartialOpWrapped (Lean.Ident target)
        [RuntimeArg, RuntimeArg]
    bvBinaryPartial source target =
      PartialOpContract preludeModule source 3
        (bvNonzeroArg 0 2)
        (PartialOpWrapped (Lean.Ident target)
          [IndexArg, RuntimeArg, RuntimeArg])
        (Lean.Ident (source ++ "_runtimeM"))
        [IndexArg, RuntimeArg, RuntimeArg]
    bvSignedBinaryPartial source target =
      PartialOpContract preludeModule source 3
        (bvSignedNonzeroArg 0 2)
        (PartialOpWrapped (Lean.Ident target)
          [IndexArg, RuntimeArg, RuntimeArg])
        (Lean.Ident (source ++ "_runtimeM"))
        [IndexArg, RuntimeArg, RuntimeArg]
    cryptolSignedBVPartial source target =
      PartialOpContract cryptolModule source 3
        (cryptolSignedBVNonzeroArg 0 2)
        (PartialOpWrapped (Lean.Ident target)
          [IndexArg, RuntimeArg, RuntimeArg])
        (Lean.Ident (source ++ "_runtimeM"))
        [IndexArg, RuntimeArg, RuntimeArg]

-- The old three-way 'CheckedArgRaw' bucket is split into its true
-- modes (plan Slice 4a): the width/index Nats are 'IndexArg', the
-- element type is 'TypeArg', matching the checked helpers' Lean
-- signatures (SAWCorePrimitives.lean).
checkedApplicationContracts :: [CheckedApplicationContract]
checkedApplicationContracts =
  [ vecIndexContract
      "at"
      4
      (Lean.Ident "atWithProof_checkedM")
      [IndexArg, TypeArg, RuntimeArg, IndexArg]
      0
      3
  , vecIndexContract
      "atWithProof"
      5
      (Lean.Ident "atWithProof_checkedM")
      [IndexArg, TypeArg, RuntimeArg, IndexArg, ProofArg]
      0
      3
  , vecIndexContract
      "updWithProof"
      6
      (Lean.Ident "updWithProof_checkedM")
      [IndexArg, TypeArg, RuntimeArg, IndexArg, RuntimeArg, ProofArg]
      0
      3
  , vecSliceContract
      "sliceWithProof"
      6
      (Lean.Ident "sliceWithProof_checkedM")
      [TypeArg, IndexArg, IndexArg, IndexArg, ProofArg, RuntimeArg]
      1
      2
      3
  , vecSliceContract
      "updSliceWithProof"
      7
      (Lean.Ident "updSliceWithProof_checkedM")
      [TypeArg, IndexArg, IndexArg, IndexArg, ProofArg, RuntimeArg, RuntimeArg]
      1
      2
      3
  , CheckedApplicationContract preludeModule "genWithProof" 3
      Nothing
      (Lean.Ident "genWithProof_checkedM")
      [IndexArg, TypeArg, FunctionWithNatLtArg 0]
      RuntimeResult
  ]
  where
    preludeModule = mkModuleName ["Prelude"]
    vecIndexContract source arity helper argModes nIdx iIdx =
      CheckedApplicationContract preludeModule source arity
        (Just (\helperArgs -> natLt (helperArgs !! iIdx) (helperArgs !! nIdx)))
        helper
        argModes
        RuntimeResult
    vecSliceContract source arity helper argModes nIdx offIdx lenIdx =
      CheckedApplicationContract preludeModule source arity
        (Just (\helperArgs ->
          natLe
            (Lean.App (Lean.Var (Lean.Ident "addNat"))
              [helperArgs !! offIdx, helperArgs !! lenIdx])
            (helperArgs !! nIdx)))
        helper
        argModes
        RuntimeResult

proofPrimitiveContracts :: [ProofPrimitiveContract]
-- Slot roles per the SAWCore Prelude signatures (plan Slice 4c):
-- widths are 'IndexArg', equality subjects at raw-logical positions
-- are 'RawValueArg', source proof terms are 'ProofArg', wrapped
-- runtime operands are 'RuntimeArg', carriers are 'TypeArg'.
proofPrimitiveContracts =
  [ bvAssertion "unsafeAssertBVULt" "bvult"
  , bvAssertion "unsafeAssertBVULe" "bvule"
    -- uip : (t : sort 1) -> (x y : t) -> (pf1 pf2 : Eq t x y) -> …
  , ProofPrimitiveContract preludeModule "uip" 5
      [TypeArg, RawValueArg, RawValueArg, ProofArg, ProofArg]
      uipContract
      (\_ proof -> pure proof)
    -- equalNatToEqNat : (m n : Nat) -> Eq Bool (equalNat m n) True -> …
  , ProofPrimitiveContract preludeModule "equalNatToEqNat" 3
      [RawValueArg, RawValueArg, ProofArg]
      equalNatToEqNatContract
      applyLastArg
    -- bvEqToEq : (n : Nat) -> (v1 v2 : Vec n Bool) -> Eq Bool … -> …
  , ProofPrimitiveContract preludeModule "bvEqToEq" 4
      [IndexArg, RuntimeArg, RuntimeArg, ProofArg]
      bvEqToEqContract
      applyLastArg
  , ProofPrimitiveContract preludeModule "bvEq_refl" 2
      [IndexArg, RuntimeArg]
      bvEqReflContract
      (\_ proof -> pure proof)
  , ProofPrimitiveContract preludeModule "not_bvult_zero" 2
      [IndexArg, RuntimeArg]
      notBvultZeroContract
      (\_ proof -> pure proof)
  , ProofPrimitiveContract preludeModule "bvAddZeroL" 2
      [IndexArg, RuntimeArg]
      (bvAddZeroContract True)
      (\_ proof -> pure proof)
  , ProofPrimitiveContract preludeModule "bvAddZeroR" 2
      [IndexArg, RuntimeArg]
      (bvAddZeroContract False)
      (\_ proof -> pure proof)
  , ProofPrimitiveContract preludeModule "bvNat_bvToNat" 2
      [IndexArg, RuntimeArg]
      bvNatBvToNatContract
      (\_ proof -> pure proof)
  , ProofPrimitiveContract preludeModule "eqNatAdd0" 1
      [RawValueArg]
      eqNatAdd0Contract
      (\_ proof -> pure proof)
  , ProofPrimitiveContract preludeModule "eqNatAddS" 2
      [RawValueArg, RawValueArg]
      eqNatAddSContract
      (\_ proof -> pure proof)
  , ProofPrimitiveContract preludeModule "eqNatAddComm" 2
      [RawValueArg, RawValueArg]
      eqNatAddCommContract
      (\_ proof -> pure proof)
  , ProofPrimitiveContract preludeModule "addNat_assoc" 3
      [RawValueArg, RawValueArg, RawValueArg]
      addNatAssocContract
      (\_ proof -> pure proof)
  ]
  where
    preludeModule = mkModuleName ["Prelude"]
    bvAssertion source op =
      ProofPrimitiveContract preludeModule source 3
        [IndexArg, RuntimeArg, RuntimeArg]
        (bvComparisonEqM (Lean.Ident op) (Lean.Ident "Bool.true"))
        (\_ proof -> pure proof)

-- | Type-image obligation primitives (2026-07-19, vector-lemma
-- proof-primitive batch). For these axioms the emitted obligation is
-- EXACTLY the ambient type translation of the application's own
-- SAWCore type — the instantiated axiom statement under T, read off
-- the term's type tag ('termSortOrType'). Obligation = T(prop) BY
-- CONSTRUCTION: no hand-mirrored emission shapes to drift, and the
-- statement automatically matches every consumer's translation of
-- the same proposition (runtime-subject equalities come out at
-- wrapped subjects exactly as the calculus states them). Lowered by
-- 'lowerTypeImageObligation' at the application site (which holds
-- the full term); bare or under-applied occurrences keep their
-- SpecialTreatment rejections.
typeImageObligationPrimitives :: [(ModuleName, String, Int)]
typeImageObligationPrimitives =
  [ (typeImagePreludeModule, "head_gen", 3)
  , (typeImagePreludeModule, "tail_gen", 3)
  , (typeImagePreludeModule, "foldr_nil", 5)
  , (typeImagePreludeModule, "foldl_nil", 5)
  ]

typeImagePreludeModule :: ModuleName
typeImagePreludeModule = mkModuleName ["Prelude"]

findTypeImageObligation :: Ident -> Int -> Bool
findTypeImageObligation ident nArgs =
  any
    (\(m, n, arity) ->
       identModule ident == m
         && identName ident == n
         && nArgs == arity)
    typeImageObligationPrimitives

applyLastArg ::
  TermTranslationMonad m =>
  [Lean.Term] ->
  Lean.Term ->
  m Lean.Term
applyLastArg args proof =
  case reverse args of
    (premise : _) -> pure (Lean.App proof [premise])
    [] -> pure proof

uipContract ::
  TermTranslationMonad m =>
  [Lean.Term] ->
  m Lean.Term
uipContract args =
  case args of
    [ty, lhs, rhs, proof1, proof2] -> do
      let proofTy =
            Lean.App (Lean.ExplVar (Lean.Ident "Eq")) [ty, lhs, rhs]
      pure (Lean.App (Lean.ExplVar (Lean.Ident "Eq"))
          [proofTy, proof1, proof2])
    _ ->
      Except.throwError (RejectedPrimitive "proof primitive"
        "uip contract expected exactly type, lhs, rhs, and two proof arguments")

equalNatToEqNatContract ::
  TermTranslationMonad m =>
  [Lean.Term] ->
  m Lean.Term
equalNatToEqNatContract args =
  case args of
    [m, n, _premise] -> do
      let boolTy = Lean.Var (Lean.Ident "Bool")
          natTy = Lean.Var (Lean.Ident "Nat")
          trueVal = Lean.Var (Lean.Ident "Bool.true")
          equalNatApp =
            Lean.App (Lean.Var (Lean.Ident "equalNat")) [m, n]
          premiseTy =
            boolEqAt boolTy equalNatApp trueVal
          resultTy =
            Lean.App (Lean.ExplVar (Lean.Ident "Eq")) [natTy, m, n]
      pure (Lean.Pi [Lean.PiBinder Lean.Explicit Nothing premiseTy] resultTy)
    _ ->
      Except.throwError (RejectedPrimitive "proof primitive"
        "equalNatToEqNat contract expected exactly m, n, and premise arguments")

bvEqToEqContract ::
  TermTranslationMonad m =>
  [Lean.Term] ->
  m Lean.Term
bvEqToEqContract args =
  case args of
    [width, lhs, rhs, _premise] -> do
      premiseTy <- bvComparisonEqM (Lean.Ident "bvEq") (Lean.Ident "Bool.true") [width, lhs, rhs]
      let vecTy =
            Lean.App (Lean.Var (Lean.Ident "Vec"))
              [width, Lean.Var (Lean.Ident "Bool")]
          resultTy = boolEqAt (wrapExcept vecTy) lhs rhs
      pure (Lean.Pi [Lean.PiBinder Lean.Explicit Nothing premiseTy] resultTy)
    _ ->
      Except.throwError (RejectedPrimitive "proof primitive"
        "bvEqToEq contract expected exactly width, lhs, rhs, and premise arguments")

bvEqReflContract ::
  TermTranslationMonad m =>
  [Lean.Term] ->
  m Lean.Term
bvEqReflContract args =
  case args of
    [width, value] ->
      bvComparisonEqM (Lean.Ident "bvEq") (Lean.Ident "Bool.true")
        [width, value, value]
    _ ->
      Except.throwError (RejectedPrimitive "proof primitive"
        "bvEq_refl contract expected exactly width and vector arguments")

notBvultZeroContract ::
  TermTranslationMonad m =>
  [Lean.Term] ->
  m Lean.Term
notBvultZeroContract args =
  case args of
    [width, value] -> do
      let zeroVec =
            Lean.App (Lean.Var (Lean.Ident "bvNat"))
              [width, zeroNat]
          zeroVecM =
            Lean.App (Lean.Var (Lean.Ident "Pure.pure")) [zeroVec]
      bvComparisonEqM (Lean.Ident "bvult") (Lean.Ident "Bool.false")
        [width, value, zeroVecM]
    _ ->
      Except.throwError (RejectedPrimitive "proof primitive"
        "not_bvult_zero contract expected exactly width and vector arguments")

bvAddZeroContract ::
  TermTranslationMonad m =>
  Bool ->
  [Lean.Term] ->
  m Lean.Term
bvAddZeroContract zeroOnLeft args =
  case args of
    [width, value] -> do
      let zeroVec =
            Lean.App (Lean.Var (Lean.Ident "bvNat"))
              [width, zeroNat]
          zeroVecM =
            Lean.App (Lean.Var (Lean.Ident "Pure.pure")) [zeroVec]
          vecTy =
            Lean.App (Lean.Var (Lean.Ident "Vec"))
              [width, Lean.Var (Lean.Ident "Bool")]
          (lhsArg, rhsArg)
            | zeroOnLeft = (zeroVecM, value)
            | otherwise  = (value, zeroVecM)
      addExpr <- bvBinaryM (Lean.Ident "bvAdd") width lhsArg rhsArg
      pure (boolEqAt (wrapExcept vecTy) addExpr value)
    _ ->
      Except.throwError (RejectedPrimitive "proof primitive"
        "bvAddZero contract expected exactly width and vector arguments")

bvNatBvToNatContract ::
  TermTranslationMonad m =>
  [Lean.Term] ->
  m Lean.Term
bvNatBvToNatContract args =
  case args of
    [width, value] -> do
      let vecTy =
            Lean.App (Lean.Var (Lean.Ident "Vec"))
              [width, Lean.Var (Lean.Ident "Bool")]
          toNat v =
            Lean.App (Lean.Var (Lean.Ident "bvToNat")) [width, v]
          toBv n =
            Lean.App (Lean.Var (Lean.Ident "bvNat"))
              [width, n]
      natValue <- bvUnaryM toNat value
      rebuilt <- bvUnaryM toBv natValue
      pure (boolEqAt (wrapExcept vecTy) rebuilt value)
    _ ->
      Except.throwError (RejectedPrimitive "proof primitive"
        "bvNat_bvToNat contract expected exactly width and vector arguments")

eqNatAdd0Contract ::
  TermTranslationMonad m =>
  [Lean.Term] ->
  m Lean.Term
eqNatAdd0Contract args =
  case args of
    [x] ->
      pure (natEq (addNat x zeroNat) x)
    _ ->
      Except.throwError (RejectedPrimitive "proof primitive"
        "eqNatAdd0 contract expected exactly one Nat argument")

eqNatAddSContract ::
  TermTranslationMonad m =>
  [Lean.Term] ->
  m Lean.Term
eqNatAddSContract args =
  case args of
    [x, y] ->
      pure (natEq (addNat x (succNat y)) (succNat (addNat x y)))
    _ ->
      Except.throwError (RejectedPrimitive "proof primitive"
        "eqNatAddS contract expected exactly two Nat arguments")

eqNatAddCommContract ::
  TermTranslationMonad m =>
  [Lean.Term] ->
  m Lean.Term
eqNatAddCommContract args =
  case args of
    [lhs, rhs] ->
      pure (natEq (addNat lhs rhs) (addNat rhs lhs))
    _ ->
      Except.throwError (RejectedPrimitive "proof primitive"
        "eqNatAddComm contract expected exactly two Nat arguments")

addNatAssocContract ::
  TermTranslationMonad m =>
  [Lean.Term] ->
  m Lean.Term
addNatAssocContract args =
  case args of
    [x, y, z] ->
      pure (natEq (addNat x (addNat y z)) (addNat (addNat x y) z))
    _ ->
      Except.throwError (RejectedPrimitive "proof primitive"
        "addNat_assoc contract expected exactly three Nat arguments")

natEq :: Lean.Term -> Lean.Term -> Lean.Term
natEq =
  boolEqAt (Lean.Var (Lean.Ident "Nat"))

addNat :: Lean.Term -> Lean.Term -> Lean.Term
addNat x y =
  Lean.App (Lean.Var (Lean.Ident "addNat")) [x, y]

bvBinaryM ::
  TermTranslationMonad m =>
  Lean.Ident ->
  Lean.Term ->
  Lean.Term ->
  Lean.Term ->
  m Lean.Term
bvBinaryM op width lhs rhs = do
  let avoid = Set.unions [leanTermIdents width, leanTermIdents lhs, leanTermIdents rhs]
  lhsName <- freshVariantAvoiding avoid (Lean.Ident "v_1")
  rhsName <- freshVariantAvoiding (Set.insert lhsName avoid) (Lean.Ident "v_2")
  let bindVar = Lean.Var (Lean.Ident "Bind.bind")
      pureVar = Lean.Var (Lean.Ident "Pure.pure")
      opApp =
        Lean.App (Lean.Var op)
          [width, Lean.Var lhsName, Lean.Var rhsName]
  pure $
    Lean.App bindVar
      [ lhs
      , Lean.Lambda [Lean.Binder Lean.Explicit lhsName Nothing]
          (Lean.App bindVar
            [ rhs
            , Lean.Lambda [Lean.Binder Lean.Explicit rhsName Nothing]
                (Lean.App pureVar [opApp])
            ])
      ]

bvUnaryM ::
  TermTranslationMonad m =>
  (Lean.Term -> Lean.Term) ->
  Lean.Term ->
  m Lean.Term
bvUnaryM mkBody value = do
  valueName <- freshVariantAvoiding (leanTermIdents value) (Lean.Ident "v_")
  let bindVar = Lean.Var (Lean.Ident "Bind.bind")
      pureVar = Lean.Var (Lean.Ident "Pure.pure")
  pure $
    Lean.App bindVar
      [ value
      , Lean.Lambda [Lean.Binder Lean.Explicit valueName Nothing]
          (Lean.App pureVar [mkBody (Lean.Var valueName)])
      ]

bvComparisonEqM ::
  TermTranslationMonad m =>
  Lean.Ident ->
  Lean.Ident ->
  [Lean.Term] ->
  m Lean.Term
bvComparisonEqM op expected args =
  case args of
    [width, lhs, rhs] -> do
      comparisonM <- bvBinaryM op width lhs rhs
      let boolTy = Lean.Var (Lean.Ident "Bool")
          expectedVal = Lean.Var expected
          pureVar = Lean.Var (Lean.Ident "Pure.pure")
      pure (boolEqAt (wrapExcept boolTy) comparisonM (Lean.App pureVar [expectedVal]))
    _ ->
      Except.throwError (RejectedPrimitive "proof primitive"
        "bitvector assertion contract expected exactly width, lhs, and rhs arguments")

zeroNat :: Lean.Term
zeroNat =
  Lean.Var (Lean.Ident "CryptolToLean.SAWCorePrimitives.zero_macro")

succNat :: Lean.Term -> Lean.Term
succNat n =
  Lean.App (Lean.Var (Lean.Ident "CryptolToLean.SAWCorePrimitives.succ_macro")) [n]

boolEqAt :: Lean.Term -> Lean.Term -> Lean.Term -> Lean.Term
boolEqAt ty lhs rhs =
  Lean.App (Lean.ExplVar (Lean.Ident "Eq"))
    [ty, lhs, rhs]

findPartialOpContract :: Ident -> Int -> Maybe PartialOpContract
findPartialOpContract ident nArgs =
  find matches partialOpContracts
  where
    matches contract =
         identModule ident == pocModule contract
      && identName ident == pocName contract
      && nArgs == pocArity contract

-- | Under-application finder (2026-07-18 wrapper design): the
-- contract for an op supplied with STRICTLY FEWER args than its
-- arity. Never matches at or above arity.
findPartialOpContractUnderApplied :: Ident -> Int -> Maybe PartialOpContract
findPartialOpContractUnderApplied ident nArgs =
  find (\c -> pocModule c == identModule ident
            && pocName c == identName ident
            && nArgs < pocArity c)
       partialOpContracts

findPartialOpContractArity :: Ident -> Maybe Int
findPartialOpContractArity ident =
  pocArity <$> find matches partialOpContracts
  where
    matches contract =
         identModule ident == pocModule contract
      && identName ident == pocName contract

findCheckedApplicationContract :: Ident -> Int -> Maybe CheckedApplicationContract
findCheckedApplicationContract ident nArgs =
  find matches checkedApplicationContracts
  where
    matches contract =
         identModule ident == cacModule contract
      && identName ident == cacName contract
      && nArgs == cacArity contract

findCheckedApplicationContractArity :: Ident -> Maybe Int
findCheckedApplicationContractArity ident =
  cacArity <$> find matches checkedApplicationContracts
  where
    matches contract =
         identModule ident == cacModule contract
      && identName ident == cacName contract

findCheckedApplicationContractPrefix :: Ident -> Int -> Maybe CheckedApplicationContract
findCheckedApplicationContractPrefix ident nArgs =
  find matches checkedApplicationContracts
  where
    matches contract =
         identModule ident == cacModule contract
      && identName ident == cacName contract
      && nArgs < cacArity contract

findProofPrimitiveContract :: Ident -> Int -> Maybe ProofPrimitiveContract
findProofPrimitiveContract ident nArgs =
  find matches proofPrimitiveContracts
  where
    matches contract =
         identModule ident == ppcModule contract
      && identName ident == ppcName contract
      && nArgs == ppcArity contract

notEqZero :: Lean.Term -> Lean.Term -> Lean.Term
notEqZero ty value =
  Lean.App (Lean.Var (Lean.Ident "Not"))
    [Lean.App (Lean.ExplVar (Lean.Ident "Eq"))
      [ty, value, Lean.NatLit 0]]

notEqPureZero :: Lean.Term -> Lean.Term -> Lean.Term
notEqPureZero ty value =
  Lean.App (Lean.Var (Lean.Ident "Not"))
    [Lean.App (Lean.ExplVar (Lean.Ident "Eq"))
      [ wrapExcept ty
      , value
      , Lean.App (Lean.Var (Lean.Ident "Pure.pure")) [Lean.NatLit 0]
      ]]

rawNonzeroArg :: Lean.Term -> Int -> [Lean.Term] -> Lean.Term
rawNonzeroArg ty argIdx args =
  notEqZero ty (args !! argIdx)

wrappedNonzeroArg :: Lean.Term -> Int -> [Lean.Term] -> Lean.Term
wrappedNonzeroArg ty argIdx args =
  notEqPureZero ty (args !! argIdx)

bvNonzeroArg :: Int -> Int -> [Lean.Term] -> Lean.Term
bvNonzeroArg widthIdx argIdx args =
  Lean.App (Lean.Var (Lean.Ident "bvNonzeroM"))
    [args !! widthIdx, args !! argIdx]

bvSignedNonzeroArg :: Int -> Int -> [Lean.Term] -> Lean.Term
bvSignedNonzeroArg widthIdx argIdx args =
  Lean.App (Lean.Var (Lean.Ident "bvNonzeroM"))
    [Lean.App (Lean.Var (Lean.Ident "succ_macro")) [args !! widthIdx],
     args !! argIdx]

cryptolSignedBVNonzeroArg :: Int -> Int -> [Lean.Term] -> Lean.Term
cryptolSignedBVNonzeroArg widthIdx argIdx args =
  Lean.App (Lean.Var (Lean.Ident "ecSignedBVNonzeroM"))
    [args !! widthIdx, args !! argIdx]

natLt :: Lean.Term -> Lean.Term -> Lean.Term
natLt lhs rhs =
  Lean.App (Lean.Var (Lean.Ident "LT.lt")) [lhs, rhs]

natLe :: Lean.Term -> Lean.Term -> Lean.Term
natLe lhs rhs =
  Lean.App (Lean.Var (Lean.Ident "LE.le")) [lhs, rhs]

-- | The checked arithmetic evidence chain shared by the side-condition
-- scripts (doc/2026-07-12_obligation-placement-design.md, OP-1).
-- `assumption` closes bounds present verbatim as binder hypotheses;
-- `omega` closes derived index arithmetic; the simp alternative first
-- normalizes the reducible numeral macros and Nat aliases that omega
-- otherwise atomizes — `Nat.sub_eq`/`Nat.add_eq`/`Nat.mul_eq` are
-- mandatory because omega does not recognize the bare
-- `Nat.sub`/`Nat.add`/`Nat.mul` applications the aliases unfold to.
-- `simp only … at *` errors when it makes no progress, hence the bare
-- `omega` alternative before it. The div/mod bridges (support-library
-- rfl lemmas) rewrite the SAW aliases and their proof-carrying checked
-- forms to the `/`/`%` operator spelling, the only one omega's
-- division-by-constant support recognizes. The trailing `sorry` is the
-- loud last resort for obligations that are genuinely not local
-- arithmetic (runtime-symbolic divisors, eta positions pending OP-2);
-- the check stage still rejects artifacts where it survives.
checkedEvidenceScript :: Lean.Ident -> Lean.Term
checkedEvidenceScript (Lean.Ident propName) =
  Lean.Tactic $
    "(try unfold " ++ propName ++ "); " ++
    "(first | assumption | omega | " ++
    "(simp only [natPos_macro, bit0_macro, bit1_macro, one_macro, " ++
    "zero_macro, succ_macro, subNat, addNat, mulNat, minNat, maxNat, " ++
    "divNat_eq_div, modNat_eq_mod, divNat_checked_eq_div, " ++
    "modNat_checked_eq_mod, Nat.sub_eq, Nat.add_eq, Nat.mul_eq] " ++
    "at *; omega) | skip); " ++
    "all_goals sorry"

partialOpProofScript :: Lean.Ident -> Set Lean.Ident -> Lean.Term
partialOpProofScript propName _proofIdents =
  checkedEvidenceScript propName

boundsProofScript :: Lean.Ident -> Set Lean.Ident -> Lean.Term
boundsProofScript propName _proofIdents =
  checkedEvidenceScript propName
