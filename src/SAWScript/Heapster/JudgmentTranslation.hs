{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module SAWScript.Heapster.JudgmentTranslation (
  BlocksInfo(..),
  IntroJudgmentTranslate'(..),
  JudgmentContext(..),
  JudgmentTranslate'(..),
  ResolveEntryIDs,
  SomeTypedEntryID(..),
  testJudgmentTranslation,
  ) where

import qualified Control.Lens                       as Lens
import           Data.Functor.Const
import           Data.List
import           Data.Maybe

import           Data.Parameterized.Context
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.Types
import           SAWScript.Heapster.Permissions
import           SAWScript.Heapster.TypedCrucible
import           SAWScript.Heapster.TypeTranslation
import           SAWScript.TopLevel
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
  { typeEnvironment :: OpenTermCtxt ctx
  -- ^ Associates to every variable (of type `tp`) in scope a SAW variable of type `[[tp]]`
  , permissionSet   :: PermSet ctx
  -- ^ Associates to every variable in scope a permission `p`
  , permissionMap   :: PermVariableMapping ctx
  -- ^ Associates to every variable in scope a SAW variable of type `[[p]]` for
  -- the corresponding permission in `permissionSet`
  , catchHandler    :: Maybe OpenTerm
  -- ^ Holds a `catch` handler whenever we are within a disjunctive judgment
  -- Hmm, putting those here means parameterizing blocks, which seems annoying
  -- , entryPoints  :: ResolveEntryIDs blocks
  }

data SomeTypedEntryID blocks where
  SomeTypedEntryID :: TypedEntryID blocks ghosts args -> SomeTypedEntryID blocks

type ResolveEntryIDs blocks = [(SomeTypedEntryID blocks, OpenTerm)]

data BlocksInfo blocks = BlocksInfo
  { entryPoints :: ResolveEntryIDs blocks
  }

class JudgmentTranslate' blocks (f :: Ctx CrucibleType -> *) | f -> blocks where
  judgmentTranslate' ::
    BlocksInfo blocks ->
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

instance JudgmentTranslate' blocks f => JudgmentTranslate' blocks (PermElim f) where

  judgmentTranslate' info jctx outputType = \case

    Elim_Done l -> judgmentTranslate' info jctx outputType l

    Elim_Fail ->
      fromMaybe (applyOpenTerm (globalOpenTerm "Prelude.errorM") outputType) (catchHandler jctx)

    Elim_Or index e1 e2 ->
      let tL l =
            judgmentTranslate' info
            (JudgmentContext { typeEnvironment = typeEnvironment jctx
                             , permissionSet = elimOrLeft (permissionSet jctx) index
                             , permissionMap = atIndex index (const $ Const l) (permissionMap jctx)
                             , catchHandler  = catchHandler jctx
                             })
            outputType e1
      in
      let tR r =
            judgmentTranslate' info
            (JudgmentContext { typeEnvironment = typeEnvironment jctx
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
      let permTypeL      = typeTranslate (typeEnvironment jctx) permL in
      let permTypeR      = typeTranslate (typeEnvironment jctx) permR in
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
              lambdaOpenTerm "a" typFst (\ a -> typeTranslate (extend (typeEnvironment jctx) (Const a)) pSnd)
            _ -> error "judgmentTranslate': `Elim_Exists` expects a `ValPerm_Exists`"
      in
      let t varFst varSnd =
            judgmentTranslate' info
            (JudgmentContext { typeEnvironment =
                               extend
                               (pvSet index (Const (applyOpenTerm typSnd varFst)) (typeEnvironment jctx))
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
      , typSnd

      -- (p : Sigma a b -> sort 0)
      , lambdaOpenTerm "sigma_unused"
        (applyOpenTermMulti (globalOpenTerm "Prelude.Sigma") [typFst, typSnd])
        (\ _ -> outputType)

      -- (f : (pa : a) -> (pb : b pa) -> p (exists a b pa pb))
      , lambdaOpenTerm "sigmaFst" typFst
        (\ varFst ->
         lambdaOpenTerm "sigmaSnd" typSnd
         (\ varSnd -> t varFst varSnd)
        )

      -- (u : Sigma a b)
      , getConst $ pvGet (permissionMap jctx) index

      ]

    Elim_Assert (Constr_BVEq w e1 e2) e ->
      error "TODO"

    Elim_BindField index offset _ e ->
      let perm     = pvGet (permSetAsgn $ permissionSet jctx) index in
      let permType = typeTranslate (typeEnvironment jctx) perm in
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
              judgmentTranslate' info
              (JudgmentContext { typeEnvironment = extend (typeEnvironment jctx) (Const permType)
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
        -- TODO: See changes in `Elim_BindField`, now `ps1` only contains `eq(...)` permissions and
        -- we translate those to nothing instead of unit
        applyOpenTerm
        (lambdaOpenTerm "field" permType t)
        (nthOpenTerm fieldIndex (getConst var))
      _ -> error "judgmentTranslate': `Elim_BindField` expects `ValPerm_LLVMPtr`"

    Elim_SplitField index offset _ e ->
      let perm = pvGet (permSetAsgn $ permissionSet jctx) index in
      error "TODO"

    Elim_Catch e1 e2 ->
      let t2 = judgmentTranslate' info jctx outputType e2 in
      judgmentTranslate' info (jctx { catchHandler = Just t2 }) outputType e1

    Elim_Unroll _p _e ->
      error "TODO"

isValPerm_Eq :: ValuePerm ctx a -> Bool
isValPerm_Eq (ValPerm_Eq _) = True
isValPerm_Eq _ = False

elimPair ::
  OpenTerm ->                           -- ^ type of left element
  OpenTerm ->                           -- ^ type of right element
  (OpenTerm -> OpenTerm) ->             -- ^ possibly-dependent type for the output
  OpenTerm ->                           -- ^ input pair
  (OpenTerm -> OpenTerm -> OpenTerm) -> -- ^ body (receives left and right)
  OpenTerm
elimPair typL typR typOut pair hdlr =
  applyOpenTermMulti (globalOpenTerm "Pair__rec")
  [ typL, typR
  , lambdaOpenTerm "p" (pairTypeOpenTerm typL typR) typOut
  , lambdaOpenTerm "l" typL (\ l -> lambdaOpenTerm "r" typR (\ r -> hdlr l r))
  , pair
  ]

class IntroJudgmentTranslate' (f :: Ctx CrucibleType -> *) where
  introJudgmentTranslate' ::
    JudgmentContext ctx ->
    f ctx ->
    -- ^ Judgment being translated
    OpenTerm
    -- ^ A pure SAW function returning a tuple

instance IntroJudgmentTranslate' AnnotIntro where

  introJudgmentTranslate' jctx (AnnotIntro {..}) = case introProof of

    Intro_Done -> unitOpenTerm

    Intro_Id x p pf ->
      let pf' =
            introJudgmentTranslate' jctx
            (AnnotIntro { introInPerms  = modifyPerm x (const ValPerm_True) introInPerms
                        -- This is just a list, can drop the head
                        , introOutPerms = error "TODO"
                        , introProof    = pf
                        })
      in
      tupleOpenTerm [ getConst (pvGet (permissionMap jctx) x), pf' ]

    Intro_Exists tp e' p pf ->
      let typFst = typeTranslate'' tp in
      let typSnd = error "TODO" in
      let pf' =
            introJudgmentTranslate' jctx
            (AnnotIntro { introInPerms  = introInPerms
                        , introOutPerms = error "TODO"
                        , introProof    = pf
                        })
      in
      -- FIXME: ValPerm_Eq special case?
      ctorOpenTerm "Prelude.exists"
      [ typFst
      , typSnd
      , error "TODO"
      , error "TODO"
      ]

    Intro_OrL p2 pf ->
      case introOutPerms of
      (PermSpec s e (ValPerm_Or p1 p2') : tl) ->
        let typLeft  = typeTranslate (typeEnvironment jctx) p1 in
        let typRight = typeTranslate (typeEnvironment jctx) p2' in
        -- TODO: use `testEquality` to check p2 against p2'
        ctorOpenTerm "Prelude.Left"
        [ typLeft, typRight
        , introJudgmentTranslate' jctx
          (AnnotIntro { introInPerms  = introInPerms
                      , introOutPerms = PermSpec s e p1 : tl
                      , introProof    = pf
                      }
          )
        ]
      [] -> error "Intro_OrL: empty out permissions"
      _  -> error "Intro_OrL: head permission is not ValPerm_Or"

    Intro_OrR p1 pf ->
      case introOutPerms of
      (PermSpec s e (ValPerm_Or p1' p2) : tl) ->
        let typLeft  = typeTranslate (typeEnvironment jctx) p1' in
        let typRight = typeTranslate (typeEnvironment jctx) p2 in
        ctorOpenTerm "Prelude.Right"
        [ typLeft, typRight
        , introJudgmentTranslate' jctx
          (AnnotIntro { introInPerms  = introInPerms
                      , introOutPerms = PermSpec s e p2 : tl
                      , introProof    = pf
                      }
          )
        ]
      [] -> error "Intro_OrL: empty out permissions"
      _  -> error "Intro_OrL: head permission is not ValPerm_Or"

    Intro_True e pf ->
      pairOpenTerm unitOpenTerm
      (introJudgmentTranslate' jctx
       (AnnotIntro { introInPerms  = introInPerms
                   , introOutPerms = error "TODO"
                   , introProof    = pf
                   }
       )
      )

    Intro_CastEq x e' pf ->
      introJudgmentTranslate' jctx
      (AnnotIntro { introInPerms  = introInPerms
                  , introOutPerms = introOutPerms
                  , introProof    = pf
                  }
      )

    Intro_Eq _ pf ->
      pairOpenTerm unitOpenTerm
      (introJudgmentTranslate' jctx
       (AnnotIntro { introInPerms  = introInPerms
                   , introOutPerms = error "TODO"
                   , introProof    = pf
                   }
       )
      )

    Intro_LLVMPtr _ pf ->
      pairOpenTerm unitOpenTerm
      (introJudgmentTranslate' jctx
       (AnnotIntro { introInPerms  = introInPerms
                   , introOutPerms = error "TODO"
                   , introProof    = pf
                   }
       )
      )

    Intro_LLVMPtr_Offset _ _ pf ->
      introJudgmentTranslate' jctx
      (AnnotIntro { introInPerms  = introInPerms
                  , introOutPerms = error "TODO"
                  , introProof    = pf
                  }
      )

    Intro_LLVMField off s p pf ->
      -- from pf we get (e, (x, Pout))
      -- and we build   ((e, x), Pout)
      let eType                   = error "TODO" in
      let xType                   = error "TODO" in
      let pOutType                = error "TODO" in
      let wholeInputType          = pairTypeOpenTerm xType (pairTypeOpenTerm eType pOutType) in
      let wholeOutputType         = pairTypeOpenTerm (pairTypeOpenTerm xType eType) pOutType in

      let makeResultPair e x pOut = pairOpenTerm (pairOpenTerm e x) pOut in

      let elimInnerPair e pair =
            elimPair xType pOutType (const wholeOutputType) pair
            (\ x pOut -> makeResultPair e x pOut)
      in

      let elimOuterPair pair =
            elimPair eType (pairTypeOpenTerm xType pOutType) (const wholeOutputType) pair
            (\ e rest -> elimInnerPair e rest)
      in

      applyOpenTerm
      (lambdaOpenTerm "pf" (pairTypeOpenTerm xType (pairTypeOpenTerm eType pOutType)) elimOuterPair)
      (introJudgmentTranslate' jctx
       (AnnotIntro { introInPerms  = introInPerms
                   , introOutPerms = error "TODO"
                   , introProof    = pf
                   }
       )
      )

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

-- TODO: fix those tests
testJudgmentTranslation :: TopLevel ()
testJudgmentTranslation = do
  sc <- getSharedContext
  io $ do
    putStrLn "Not implemented"
    -- t <- completeOpenTerm sc $
    --   judgmentTranslate' (error "TODO")
    --   -- FIXME: this Either not applied does not make sense!
    --   (JudgmentContext { typeEnvironment = extend empty (Const (globalOpenTerm "Prelude.Either"))
    --                    , permissionSet =
    --                      extendPermSet (PermSet empty empty)
    --                      (error "TODO")
    --                      (ValPerm_Or ValPerm_True ValPerm_True)
    --                    , permissionMap = extend empty (Const (globalOpenTerm "Prelude.Vec"))
    --                    , catchHandler  = Nothing
    --                    }
    --   )
    --   (globalOpenTerm "Prelude.Bool")
    --   permElim0
    -- putStrLn $ show t
