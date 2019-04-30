{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RecordWildCards #-}

module SAWScript.Heapster.Translation (
  testJudgmentTranslation,
  testTypeTranslation,
  ) where

import qualified Control.Lens as Lens
import Data.Functor.Const

import Data.Parameterized.Classes
import Data.Parameterized.Context
import Data.Parameterized.NatRepr
import Data.Parameterized.TraversableFC
import Lang.Crucible.Types
import SAWScript.Heapster.Permissions
import SAWScript.TopLevel
import Verifier.SAW.OpenTerm
import Verifier.SAW.Term.Functor

-- | In this file, we are defining two levels of translation:
--
-- 1. The @TypeTranslate@ family of classes captures those translations from
-- permission types to SAW types.
--
-- 2. The @JudgmentTranslate@ family of classes captures those translations from
-- permission judgments to SAW functions.
--
-- Overloading the [[ x ]] notation to mean either of those translations, we
-- will usually have, for a given permission judgment J, [[ J ]] be a SAW
-- function of type [[ ∏in ]] -> CompM [[ ∏out ]], where ∏in and ∏out are the
-- respective input and output permission sets for judgment J.

class TypeTranslate (f :: Ctx k -> k' -> *) where
  typeTranslate :: Assignment (Const OpenTerm) ctx -> f ctx a -> OpenTerm

-- class TypeTranslate' (f :: Ctx k -> *) where
--   typeTranslate' :: Assignment (Const OpenTerm) ctx -> f ctx -> OpenTerm

class TypeTranslate'' (d :: *) where
  typeTranslate'' :: d -> OpenTerm

instance TypeTranslate'' (TypeRepr a) where
  typeTranslate'' = \case
    AnyRepr                -> error "TODO"
    UnitRepr               -> dataTypeOpenTerm "Prelude.UnitType" []
    BoolRepr               -> dataTypeOpenTerm "Prelude.Bool" []
    NatRepr                -> dataTypeOpenTerm "Prelude.Nat" []
    IntegerRepr            -> error "TODO"
    RealValRepr            -> error "TODO"
    ComplexRealRepr        -> error "TODO"
    BVRepr _               -> error "TODO"
    IntrinsicRepr _ _      -> error "TODO"
    RecursiveRepr _ _      -> error "TODO"
    FloatRepr _            -> error "TODO"
    IEEEFloatRepr _        -> error "TODO"
    CharRepr               -> error "TODO"
    StringRepr             -> error "TODO"
    FunctionHandleRepr _ _ -> error "TODO"
    MaybeRepr _            -> error "TODO"
    VectorRepr _           -> error "TODO"
    StructRepr _           -> error "TODO"
    VariantRepr _          -> error "TODO"
    ReferenceRepr _        -> error "TODO"
    WordMapRepr _ _        -> error "TODO"
    StringMapRepr _        -> error "TODO"
    SymbolicArrayRepr _ _  -> error "TODO"
    SymbolicStructRepr _   -> error "TODO"

instance TypeTranslate PermExpr where
  typeTranslate ctx = \case
    PExpr_Var i                  -> getConst $ ctx ! i
    PExpr_NatLit n               -> natOpenTerm $ fromIntegral n
    PExpr_BVLit w n              ->
      let w' = natOpenTerm $ intValue w in
      let n' = natOpenTerm n in
      applyOpenTermMulti (globalOpenTerm "Prelude.bvNat") [w', n']
    PExpr_BVAdd w e1 e2          ->
      let w' = natOpenTerm $ intValue w in
      let bv1 = typeTranslate ctx e1 in
      let bv2 = typeTranslate ctx e2 in
      applyOpenTermMulti (globalOpenTerm "Prelude.bvAdd") [w', bv1, bv2]
    PExpr_LLVM_PointerExpr _ _ _ -> error "TODO"
    PExpr_LLVM_PointerBlock _ _  -> error "TODO"
    PExpr_LLVM_PointerOffset _ _ -> error "TODO"

instance TypeTranslate ValuePerm where
  typeTranslate ctx = \case
    ValPerm_True           -> flatOpenTerm UnitType
    ValPerm_Eq _           -> flatOpenTerm UnitType
    ValPerm_Or p1 p2       ->
      let t1 = typeTranslate ctx p1 in
      let t2 = typeTranslate ctx p2 in
      dataTypeOpenTerm "Prelude.Either" [t1, t2]
    ValPerm_Exists t p     ->
      dataTypeOpenTerm
      "Prelude.Sigma"
      [ lambdaOpenTerm "x" (typeTranslate'' t) (\ x -> typeTranslate (extend ctx (Const x)) p)
      ]
    ValPerm_Mu _           -> error "TODO"
    ValPerm_Var _index     -> error "TODO"
    ValPerm_LLVMWord w     ->
      let w' = natOpenTerm $ intValue w in
      dataTypeOpenTerm "Prelude.bitvector" [w']
    ValPerm_LLVMPtr _ ps _ ->
      let rs = typeTranslate ctx <$> ps in
      let basePerm = dataTypeOpenTerm "Prelude.UnitType" [] in
      let addPerm elt acc = dataTypeOpenTerm "Prelude.PairType" [elt, acc] in
      foldr addPerm basePerm rs

instance TypeTranslate LLVMShapePerm where
  typeTranslate ctx = \case
    LLVMFieldShapePerm (LLVMFieldPerm {..}) -> typeTranslate ctx llvmFieldPerm
    LLVMArrayShapePerm (LLVMArrayPerm {..}) ->
      let len = typeTranslate ctx llvmArrayLen in
      let types = typeTranslate ctx llvmArrayPtrPerm in
      dataTypeOpenTerm "Prelude.Vec" [types, len]

tests :: [(ValuePerm ctx a, OpenTerm)]
tests =

  [ ( ValPerm_True
    , flatOpenTerm UnitType
    )

  ]

testTypeTranslation :: Integer -> TopLevel ()
testTypeTranslation i =
  do sc <- getSharedContext
     let (p, t) = (tests !! fromInteger i)
     expected <- io $ completeOpenTerm sc $ t
     obtained <- io $ completeOpenTerm sc $ typeTranslate empty p
     if expected == obtained
       then io $ putStrLn "Success!"
       else io $ putStrLn $ "Error in testPermTranslation for test case " ++ show i

{-
primitive CompM : sort 0 -> sort 0;

primitive returnM : (a:sort 0) -> a -> CompM a;
primitive bindM : (a b:sort 0) -> CompM a -> (a -> CompM b) -> CompM b;

composeM : (a b c: sort 0) -> (a -> CompM b) -> (b -> CompM c) -> a -> CompM c;
composeM a b c f g x = bindM b c (f x) g;

primitive errorM : (a:sort 0) -> CompM a;
-}

-- WANT: helpers to manipulate PermSet

-- WANT: a new type class kind of like `TypeTranslate`, but that gives back functions

type OpenTermCtxt ctx = Assignment (Const OpenTerm) ctx

-- | As we build a computational term for a given permission derivation, the term
-- being built introduces in context variables, at the SAW term level, that
-- correspond to permission variables at the typing level.  This mapping keeps
-- track of those.
type PermVariableMapping ctx = Assignment (Const OpenTerm) ctx

class JudgmentTranslate' (f :: Ctx CrucibleType -> *) where
  judgmentTranslate' ::
    OpenTermCtxt ctx ->        -- ^ this context maps type variables to a SAW value
                               -- that depends on the type of the variable in question.
                               -- e.g. for @BVType@, a SAW variable that has a bitvector type
                               --      for @LLVMPointerType@, a @Unit@
    PermSet ctx ->             -- ^ permission set
    PermVariableMapping ctx -> -- ^ mapping to SAW variables, see @PermVariableMapping@
    OpenTerm ->                -- ^ output type being built
    f ctx ->                   -- ^ item being translated
    OpenTerm

atIndex :: Index ctx a -> (f a -> f a) -> Assignment f ctx -> Assignment f ctx
atIndex i = Lens.over (ixF i)

instance JudgmentTranslate' f => JudgmentTranslate' (PermElim f) where

  judgmentTranslate' ctx pctx pmap outputType = \case

    Elim_Done l -> judgmentTranslate' ctx pctx pmap outputType l

    Elim_Or index e1 e2 ->
      let perm = pctx ! index in
      let (permL, permR) = case perm of
            ValPerm_Or p1 p2 -> (p1, p2)
            _                -> error "judgmentTranslate': `Elim_Or` expects `ValPerm_Or`"
      in
      let body ve =
            let permTypeL = typeTranslate ctx permL in
            let permTypeR = typeTranslate ctx permR in
            let pctxL = elimOrLeft  pctx index in
            let pctxR = elimOrRight pctx index in
            let pmapL l = atIndex index (const $ Const l) pmap in
            let pmapR r = atIndex index (const $ Const r) pmap in
            let bodyL l = applyOpenTerm (judgmentTranslate' ctx pctxL (pmapL l) outputType e1) l in
            let bodyR r = applyOpenTerm (judgmentTranslate' ctx pctxR (pmapR r) outputType e2) r in
            applyOpenTermMulti (globalOpenTerm "Prelude.either")
            [ permTypeL                          -- a
            , permTypeR                          -- b
            , outputType                         -- c
            , lambdaOpenTerm "l" permTypeL bodyL -- a -> c
            , lambdaOpenTerm "r" permTypeR bodyR -- b -> c
            , ve                                 -- Either a b
            ]
      in
      lambdaOpenTerm "ve" outputType body

    -- need to
    -- extend assignment 1 is easy: extend from Unsafe
    -- permset needs more work, need to map over all perms,
    -- write `extPermSet`
    Elim_Exists index typ e ->
      let body ve =
            let ctx' = extend ctx (Const ve) in
            let pctx' = elimExists pctx index typ in
            let pmap' = extend (atIndex index (const $ Const ve) pmap) (Const ve) in
            applyOpenTerm (judgmentTranslate' ctx' pctx' pmap' outputType e) ve
      in
      lambdaOpenTerm "ve" outputType body

    Elim_BindField index shapeIndex e -> error "TODO"

    Elim_Copy _e1 _e2 -> error "TODO"

    Elim_Unroll _p _e -> error "TODO"

permElim0 :: PermElim (Const OpenTerm) ('EmptyCtx '::> a)
permElim0 =
  Elim_Or baseIndex
  (Elim_Done (Const (globalOpenTerm "Prelude.Bool")))
  (Elim_Done (Const (globalOpenTerm "Prelude.Nat")))

instance JudgmentTranslate' (Const OpenTerm) where
  judgmentTranslate' _ _ _ _ t = getConst t

-- TODO: fix those tests
testJudgmentTranslation :: TopLevel ()
testJudgmentTranslation = do
  sc <- getSharedContext
  io $ do
    t <- completeOpenTerm sc $
      judgmentTranslate'
      (extend empty (Const (globalOpenTerm "Prelude.Either")))
      (extend empty (ValPerm_Or ValPerm_True ValPerm_True))
      (extend empty (Const (globalOpenTerm "Prelude.Vec")))
      (globalOpenTerm "Prelude.Bool")
      permElim0
    putStrLn $ show t
