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

module SAWScript.Heapster.JudgmentTranslation (
  -- testJudgmentTranslation,
  ) where

import qualified Control.Lens                     as Lens
import           Data.Functor.Const
import           Data.List
import           Data.Maybe


import           Data.Parameterized.Context
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.Types
import           SAWScript.Heapster.Permissions
import           SAWScript.Heapster.TypeTranslation
import           Verifier.SAW.OpenTerm

-- | The @JudgmentTranslate@ family of classes captures translations from
-- permission judgments to SAW functions.
--
-- Overloading the [[ x ]] notation to mean either type or judgment translation,
-- we will usually have, for a given permission judgment J, [[ J ]] be a SAW
-- function of type [[ ∏in ]] -> CompM [[ ∏out ]], where ∏in and ∏out are the
-- respective input and output permission sets for judgment J.

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
      let perm           = pvGet (permSetAsgn $ permissionSet jctx) index in
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

    Elim_Exists index typ e ->
      let typFst = typeTranslate'' typ in
      let typSnd = case pvGet (permSetAsgn $ permissionSet jctx) index of
            ValPerm_Exists _ pSnd ->
              -- I believe we can reuse @typFst@ here, rather than using the
              -- TypeRepr in @ValPerm_Exists@.
              lambdaOpenTerm "a" typFst (\ a -> typeTranslate (extend (typingContext jctx) (Const a)) pSnd))
            _ -> error "judgmentTranslate': `Elim_Exists` expects a `ValPerm_Exists`"
      in
      let t varFst varSnd =
            judgmentTranslate'
            (JudgmentContext { typingContext =
                               extend
                               (pvSet index (Const (applyOpenTerm typSnd varFst)) (typingContext jctx))
                               (Const typFst)
                             , permissionSet = elimExists (permissionSet jctx) index typ
                             , permissionMap =
                               extend
                               (pvSet index (Const varSnd) (permissionMap jctx))
                               (Const varFst)
                             , catchHandler  = catchHandler jctx
                             })
            outputType e
      in

      applyOpenTermMulti (globalOpenTerm "Prelude.Sigma__rec")

      -- (a : sort 0)
      [ typFst

      -- (b : a -> sort 0)
      , tSnd

      -- (p : Sigma a b -> sort 0)
      , lambdaOpenTerm "sigma_unused"
        (applyOpenTermMulti (globalOpenTerm "Prelude.Sigma") [typFst, tSnd])
        (\ _ -> outputType)

      -- (f : (pa : a) -> (pb : b pa) -> p (exists a b pa pb))
      , lambdaOpenTerm "sigmaFst" typFst
        (\ varFst ->
         lambdaOpenTerm "sigmaSnd" tSnd
         (\ varSnd -> t varFst varSnd)
        )

      -- (u : Sigma a b)
      , getConst $ pvGet (permissionMap jctx) index

      ]

    Elim_Assert (Constr_BVEq w e1 e2) e ->
      error "TODO"

    Elim_BindField index offset _ e ->
      let perm     = pvGet (permSetAsgn $ permissionSet jctx) index in
      let permType = typeTranslate (typingContext jctx) perm in
      case perm of
      ValPerm_LLVMPtr w fields mp ->
        let (fieldSplitting, fieldPerm, fields') =
              fromMaybe
              (error "judgmentTranslate': no permission found with the given offset")
              (remLLVMFieldAt offset fields)
        in
        let newPermVar = nextPermVar (permSetSize $ permissionSet jctx) in
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
                               -- * update at `index` with `perm'`
                               -- * extend with `fieldPerm`
                               , permissionSet =
                                 setPerm (weakenPermVar1 index) perm' $
                                 extendPermSet
                                 (permissionSet jctx)
                                 (LLVMPointerRepr w)
                                 (extendContext' oneDiff fieldPerm)
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
        -- Change the translation of pointer shapes s.t. Eq permissions do not bring up () in type
        -- [[ (0 |-> eq(x) * 4 |-> a * 8 |-> eq(y)) *  ]] = [[a]]
        -- Assumption:
        applyOpenTerm
        (lambdaOpenTerm "field" permType t)
        (nthOpenTerm fieldIndex (getConst var))
      _ -> error "judgmentTranslate': `Elim_BindField` expects `ValPerm_LLVMPtr`"

    Elim_SplitField index offset _ e ->
      let perm = pvGet (permSetAsgn $ permissionSet jctx) index in
      error "TODO"

    Elim_Catch e1 e2 ->
      let t2 = judgmentTranslate' jctx outputType e2 in
      judgmentTranslate' (jctx { catchHandler = Just t2 }) outputType e1

    Elim_Unroll _p _e ->
      error "TODO"

instance JudgmentTranslate' AnnotIntro where

  judgmentTranslate' jctx outputType (AnnotIntro {..}) = case introProof of

    Intro_Id indices -> error "TODO"

    Intro_Exists tp e' p pf -> error "TODO"

    Intro_OrL p2 pf ->
      let typLeft  = error "TODO" in
      let typRight = error "TODO" in
      applyOpenTermMulti (globalOpenTerm "Prelude.bindM")
      -- a : sort 0
      [ typLeft
      -- b : sort 0
      , typRight
      -- x : CompM a
      , judgmentTranslate' jctx outputType
        (AnnotIntro { introInPerms  = error "TODO"
                    , introOutPerms = error "TODO"
                    , introProof    = pf
                    }
        )
      -- y : a -> CompM b
      , lambdaOpenTerm "l" typLeft (\ l -> ctorOpenTerm "Prelude.Left" [ typLeft, typRight, l ])
      ]

    Intro_OrR p1 pf -> error "TODO"

    Intro_True e pf -> error "TODO"

    Intro_CastEq x e' pf -> error "TODO"

    Intro_Eq eq_pf pf -> error "TODO"

    Intro_LLVMPtr x pf -> error "TODO"

    Intro_LLVMPtr_Offset w off pf -> error "TODO"

    Intro_LLVMField off s p pf -> error "TODO"

atIndex :: PermVar ctx a -> (f a -> f a) -> Assignment f ctx -> Assignment f ctx
atIndex x = Lens.over (pvLens x)

nthOpenTerm :: Int -> OpenTerm -> OpenTerm
nthOpenTerm n t = goLeft $ (iterate goRight t) !! n
  where
    goLeft  = applyOpenTerm (globalOpenTerm "Prelude.Pair_fst")
    goRight = applyOpenTerm (globalOpenTerm "Prelude.Pair_snd")

permElim0 :: PermElim (Const OpenTerm) ('EmptyCtx '::> a)
permElim0 =
  Elim_Or (nextPermVar zeroSize)
  (Elim_Done (Const (globalOpenTerm "Prelude.Bool")))
  (Elim_Done (Const (globalOpenTerm "Prelude.Nat")))

instance JudgmentTranslate' (Const OpenTerm) where
  judgmentTranslate' _ _ t = getConst t

-- TODO: fix those tests
-- testJudgmentTranslation :: TopLevel ()
-- testJudgmentTranslation = do
--   sc <- getSharedContext
--   io $ do
--     t <- completeOpenTerm sc $
--       judgmentTranslate'
--       -- FIXME: this Either not applied does not make sense!
--       (JudgmentContext { typingContext = extend empty (Const (globalOpenTerm "Prelude.Either"))
--                        , permissionSet =
--                          extendPermSet (PermSet empty empty)
--                          _
--                          (ValPerm_Or ValPerm_True ValPerm_True)
--                        , permissionMap = extend empty (Const (globalOpenTerm "Prelude.Vec"))
--                        , catchHandler  = Nothing
--                        }
--       )
--       (globalOpenTerm "Prelude.Bool")
--       permElim0
--     putStrLn $ show t
