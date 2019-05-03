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

import qualified Control.Lens                   as Lens
import           Data.Functor.Const
import           Data.List
import           Data.Maybe

import           Data.Parameterized.Classes
import           Data.Parameterized.Context
import           Lang.Crucible.Types
import           SAWScript.Heapster.Permissions
import           SAWScript.TopLevel
import           Verifier.SAW.OpenTerm
import           Verifier.SAW.Term.Functor

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

-- | Translate an 'Integer' to a SAW bitvector literal
translateBVLit :: NatRepr w -> Integer -> OpenTerm
translateBVLit w i =
  applyOpenTermMulti (globalOpenTerm "Prelude.bvNat")
  [typeTranslate'' w, natOpenTerm i]

-- | Build an 'OpenTerm' for the sum of SAW bitvectors
translateBVSum :: NatRepr w -> [OpenTerm] -> OpenTerm
translateBVSum w [] = translateBVLit w 0
translateBVSum _ [t] = t
translateBVSum w (t:ts) =
  applyOpenTermMulti (globalOpenTerm "Prelude.bvAdd")
  [typeTranslate'' w, t, translateBVSum w ts]

class TypeTranslate (f :: Ctx k -> k' -> *) where
  typeTranslate :: Assignment (Const OpenTerm) ctx -> f ctx a -> OpenTerm

-- class TypeTranslate' (f :: Ctx k -> *) where
--   typeTranslate' :: Assignment (Const OpenTerm) ctx -> f ctx -> OpenTerm

class TypeTranslate'' (d :: *) where
  typeTranslate'' :: d -> OpenTerm

instance TypeTranslate'' (NatRepr w) where
  typeTranslate'' w = natOpenTerm $ intValue w

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

instance TypeTranslate PermVar where
  typeTranslate ctx x = getConst $ pvGet ctx x

instance TypeTranslate BVFactor where
  typeTranslate ctx (BVFactor w i x) =
    applyOpenTermMulti (globalOpenTerm "Prelude.bvMul")
    [typeTranslate'' w, translateBVLit w i, typeTranslate ctx x]

instance TypeTranslate PermExpr where
  typeTranslate ctx = \case
    PExpr_Var i                  -> getConst $ ctx `pvGet` i
    PExpr_BV w factors constant     ->
      translateBVSum w (translateBVLit w constant :
                        map (typeTranslate ctx) factors)
    PExpr_LLVMWord _ _ -> unitOpenTerm
    PExpr_LLVMOffset _ _ _ -> unitOpenTerm
    PExpr_Spl _ -> error "TODO"
    PExpr_Struct _ _ -> error "TODO"

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

    ValPerm_Nat_Neq0       -> error "TODO"

    ValPerm_LLVMPtr _ ps _ ->
      tupleTypeOpenTerm (typeTranslate ctx <$> ps)

instance TypeTranslate LLVMShapePerm where
  typeTranslate ctx = \case

    LLVMFieldShapePerm (LLVMFieldPerm {..}) -> typeTranslate ctx llvmFieldPerm

    LLVMArrayShapePerm (LLVMArrayPerm {..}) ->
      let len = error "TODO" in -- typeTranslate ctx llvmArrayLen in -- FIXME: this does not make sense
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

type OpenTermCtxt ctx = Assignment (Const OpenTerm) ctx

-- | As we build a computational term for a given permission derivation, the term
-- being built introduces in context variables, at the SAW term level, that
-- correspond to permission variables at the typing level.  This mapping keeps
-- track of those.
type PermVariableMapping ctx = Assignment (Const OpenTerm) ctx

data JudgmentContext ctx = JudgmentContext
  { typingContext :: OpenTermCtxt ctx
  -- ^ Maps type variables to a SAW value that depends on the type of the
  -- variable in question.  e.g. for @BVType@, a SAW variable that has a
  -- bitvector type for @LLVMPointerType@, a @Unit@
  , permissionSet :: PermSet ctx
  -- ^ Associates to each index a value permission `p`
  , permissionMap :: PermVariableMapping ctx
  -- ^ Associates to each index a SAW variable, whose type is `[[p]]` for the
  -- corresponding `p` in the permission set at that index
  , catchHandler  :: Maybe OpenTerm
  -- ^ Holds a `catch` handler whenever we are within a disjunctive judgment
  }

class JudgmentTranslate' (f :: Ctx CrucibleType -> *) where
  judgmentTranslate' ::
    JudgmentContext ctx ->
    OpenTerm ->
    -- ^ Output type being built, needed to build some terms that need to
    -- explicitly state what type they return
    f ctx ->
    -- ^ Judgment being translated
    OpenTerm
    -- ^ Returns a SAW term of type `[[Πin]] -> CompM [[Πout]]` where `Πin` is
    -- the expected permission set coming "into" this judgment (left of
    -- turnstile), and `Πout` the permission set coming "out"

atIndex :: PermVar ctx a -> (f a -> f a) -> Assignment f ctx -> Assignment f ctx
atIndex x = Lens.over (pvLens x)

nthOpenTerm :: Int -> OpenTerm -> OpenTerm
nthOpenTerm n t = goLeft $ (iterate goRight t) !! n
  where
    goLeft  = applyOpenTerm (globalOpenTerm "Prelude.Pair_fst")
    goRight = applyOpenTerm (globalOpenTerm "Prelude.Pair_snd")

instance JudgmentTranslate' f => JudgmentTranslate' (PermElim f) where

  judgmentTranslate' jctx outputType = \case

    Elim_Done l -> judgmentTranslate' jctx outputType l

    Elim_Fail ->
      fromMaybe (applyOpenTerm (globalOpenTerm "Prelude.errorM") outputType) (catchHandler jctx)

    Elim_Or index e1 e2 ->
      let tL l =
            judgmentTranslate'
            (JudgmentContext { typingContext = typingContext jctx
                             , permissionSet = elimOrLeft (permissionSet jctx) index
                             , permissionMap = atIndex index (const $ Const l) (permissionMap jctx)
                             , catchHandler  = catchHandler jctx
                             })
            outputType e1
      in
      let tR r =
            judgmentTranslate'
            (JudgmentContext { typingContext = typingContext jctx
                             , permissionSet = elimOrRight (permissionSet jctx) index
                             , permissionMap = atIndex index (const $ Const r) (permissionMap jctx)
                             , catchHandler  = catchHandler jctx
                             })
            outputType e2
      in
      let var            = pvGet (permissionMap jctx) index in
      let perm           = pvGet (permissionSet jctx) index in
      let (permL, permR) = case perm of
            ValPerm_Or p1 p2 -> (p1, p2)
            _                -> error "judgmentTranslate': `Elim_Or` expects `ValPerm_Or`"
      in
      let permTypeL      = typeTranslate (typingContext jctx) permL in
      let permTypeR      = typeTranslate (typingContext jctx) permR in
      let bodyL l        = applyOpenTerm (tL l) l in
      let bodyR r        = applyOpenTerm (tR r) r in
      applyOpenTermMulti (globalOpenTerm "Prelude.either")
      [ permTypeL                          -- a
      , permTypeR                          -- b
      , outputType                         -- c
      , lambdaOpenTerm "l" permTypeL bodyL -- a -> c
      , lambdaOpenTerm "r" permTypeR bodyR -- b -> c
      , getConst var                       -- Either a b
      ]

    Elim_Exists index typ e -> error "TODO"
      -- let var   = pvGet pmap index in
      -- let perm  = pvGet pctx index in
      -- case pvGet pctx index of
      -- ValPerm_Exists typ' p ->
      --   case testEquality typ typ' of
      --   Just Refl ->
      --     let ctx'  = extend ctx _ in
      --     let pctx' = pvSet (extendContext' oneDiff _) _ $ extendPermSet pctx _ in
      --     let pmap' = extend pmap _ in
      --     judgmentTranslate' _ _ _ outputType e -- ctx' pctx' pmap' outputType e
      --   Nothing -> error "TODO"

    Elim_Assert bv e -> error "TODO"

    Elim_BindField index offset _ e ->
      let perm     = pvGet (permissionSet jctx) index in
      let permType = typeTranslate (typingContext jctx) perm in
      case perm of
      ValPerm_LLVMPtr w fields mp ->
        let (fieldSplitting, fieldPerm, fields') =
              fromMaybe
              (error "judgmentTranslate': no permission found with the given offset")
              (remLLVMFieldAt offset fields)
        in
        let newPermVar = nextPermVar (size $ permissionSet jctx) in
        let newShapePerm = LLVMFieldShapePerm $ LLVMFieldPerm
              { llvmFieldOffset    = offset
              , llvmFieldSplitting = extendContext oneDiff fieldSplitting
              , llvmFieldPerm      = ValPerm_Eq (PExpr_Var newPermVar)
              }
        in
        let perm' =
              ValPerm_LLVMPtr
              w
              (newShapePerm : map (extendContext' oneDiff) fields')
              (extendContext' oneDiff <$> mp)
        in
        let t fieldVar =
              judgmentTranslate'
              (JudgmentContext { typingContext = extend (typingContext jctx) (Const permType)
                               , permissionSet =
                                 pvSet
                                 (weakenPermVar1 index)
                                 perm'
                                 (extendPermSet (permissionSet jctx) (extendContext' oneDiff fieldPerm))
                               , permissionMap = extend (permissionMap jctx) (Const fieldVar)
                               , catchHandler  = catchHandler jctx
                               })
              outputType e
        in
        let fieldIndex =
              fromMaybe
              (error "judgmentTranslate': no permission found with the given offset")
              (findIndex (isLLVMFieldAt offset) fields)
        in
        let var = pvGet (permissionMap jctx) index in
        applyOpenTerm
        (lambdaOpenTerm "field" permType t)
        (nthOpenTerm fieldIndex (getConst var))
      _ -> error "judgmentTranslate': `Elim_BindField` expects `ValPerm_LLVMPtr`"

    Elim_SplitField index offset _ e -> error "TODO"

    Elim_Catch e1 e2 ->
      let t2 = judgmentTranslate' jctx outputType e2 in
      judgmentTranslate' (jctx { catchHandler = Just t2 }) outputType e1

    Elim_Unroll _p _e -> error "TODO"

permElim0 :: PermElim (Const OpenTerm) ('EmptyCtx '::> a)
permElim0 =
  Elim_Or (nextPermVar zeroSize)
  (Elim_Done (Const (globalOpenTerm "Prelude.Bool")))
  (Elim_Done (Const (globalOpenTerm "Prelude.Nat")))

instance JudgmentTranslate' (Const OpenTerm) where
  judgmentTranslate' _ _ t = getConst t

-- TODO: fix those tests
testJudgmentTranslation :: TopLevel ()
testJudgmentTranslation = do
  sc <- getSharedContext
  io $ do
    t <- completeOpenTerm sc $
      judgmentTranslate'
      (JudgmentContext { typingContext = extend empty (Const (globalOpenTerm "Prelude.Either"))
                       , permissionSet = extend empty (ValPerm_Or ValPerm_True ValPerm_True)
                       , permissionMap = extend empty (Const (globalOpenTerm "Prelude.Vec"))
                       , catchHandler  = Nothing
                       }
      )
      (globalOpenTerm "Prelude.Bool")
      permElim0
    putStrLn $ show t
