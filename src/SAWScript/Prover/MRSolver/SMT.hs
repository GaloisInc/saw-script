{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ImplicitParams #-}

{- |
Module      : SAWScript.Prover.MRSolver.SMT
Copyright   : Galois, Inc. 2022
License     : BSD3
Maintainer  : westbrook@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

This module implements the interface between Mr. Solver and an SMT solver,
namely 'mrProvable' and 'mrProveEq'.
-}

module SAWScript.Prover.MRSolver.SMT where

import qualified Data.Vector as V
import Control.Monad.Except

import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Verifier.SAW.Term.Functor
import Verifier.SAW.Term.Pretty
import Verifier.SAW.SharedTerm
import Verifier.SAW.Recognizer
import Verifier.SAW.OpenTerm

import qualified Verifier.SAW.Prim as Prim
import Verifier.SAW.Simulator.TermModel
import Verifier.SAW.Simulator.Prims
import Verifier.SAW.Simulator.MonadLazy

import SAWScript.Proof (termToProp, propToTerm, prettyProp)
import What4.Solver
import SAWScript.Prover.What4

import SAWScript.Prover.MRSolver.Term
import SAWScript.Prover.MRSolver.Monad


----------------------------------------------------------------------
-- * Various SMT-specific Functions on Terms
----------------------------------------------------------------------

-- | Test if a 'Term' is a 'BVVec' type
asBVVecType :: Recognizer Term (Term, Term, Term)
asBVVecType (asApplyAll ->
             (isGlobalDef "Prelude.Vec" -> Just _,
              [(asApplyAll ->
                (isGlobalDef "Prelude.bvToNat" -> Just _, [n, len])), a])) =
  Just (n, len, a)
asBVVecType _ = Nothing

-- | Apply @genBVVec@ to arguments @n@, @len@, and @a@, along with a function of
-- type @Vec n Bool -> a@
genBVVecTerm :: SharedContext -> Term -> Term -> Term -> Term -> IO Term
genBVVecTerm sc n_tm len_tm a_tm f_tm =
  let n = closedOpenTerm n_tm
      len = closedOpenTerm len_tm
      a = closedOpenTerm a_tm
      f = closedOpenTerm f_tm in
  completeOpenTerm sc $
  applyOpenTermMulti (globalOpenTerm "Prelude.genBVVec")
  [n, len, a,
   lambdaOpenTerm "i" (vectorTypeOpenTerm n boolTypeOpenTerm) $ \i ->
    lambdaOpenTerm "_" (applyGlobalOpenTerm "Prelude.is_bvult" [n, i, len]) $ \_ ->
    applyOpenTerm f i]

-- | Match a term of the form @genBVVec n len a (\ i _ -> e)@, i.e., where @e@
-- does not have the proof variable (the underscore) free
asGenBVVecTerm :: Recognizer Term (Term, Term, Term, Term)
asGenBVVecTerm (asApplyAll ->
                   (isGlobalDef "Prelude.genBVVec" -> Just _,
                    [n, len, a,
                     (asLambdaList -> ([_,_], e))]))
  | not $ inBitSet 0 $ looseVars e
  = Just (n, len, a, e)
asGenBVVecTerm _ = Nothing

type TmPrim = Prim TermModel

-- | Convert a Boolean value to a 'Term'; like 'readBackValue' but that function
-- requires a 'SimulatorConfig' which we cannot easily generate here...
boolValToTerm :: SharedContext -> Value TermModel -> IO Term
boolValToTerm _ (VBool (Left tm)) = return tm
boolValToTerm sc (VBool (Right b)) = scBool sc b
boolValToTerm _ (VExtra (VExtraTerm _tp tm)) = return tm
boolValToTerm _ v = error ("boolValToTerm: unexpected value: " ++ show v)

-- | An implementation of a primitive function that expects a @genBVVec@ term
primGenBVVec :: SharedContext -> (Term -> TmPrim) -> TmPrim
primGenBVVec sc f =
  PrimFilterFun "genBVVecPrim"
  (\case
      VExtra (VExtraTerm _ (asGenBVVecTerm -> Just (n, _, _, e))) ->
        -- Generate the function \i -> [i/1,error/0]e
        lift $
        do i_tp <- scBoolType sc >>= scVecType sc n
           let err_tm = error "primGenBVVec: unexpected variable occurrence"
           i_tm <- scLocalVar sc 0
           body <- instantiateVarList sc 0 [err_tm,i_tm] e
           scLambda sc "i" i_tp body
      _ -> mzero)
  f

-- | An implementation of a primitive function that expects a bitvector term
primBVTermFun :: SharedContext -> (Term -> TmPrim) -> TmPrim
primBVTermFun sc =
  PrimFilterFun "primBVTermFun" $
  \case
    VExtra (VExtraTerm _ w_tm) -> return w_tm
    VWord (Left (_,w_tm)) -> return w_tm
    VWord (Right bv) ->
      lift $ scBvConst sc (fromIntegral (Prim.width bv)) (Prim.unsigned bv)
    VVector vs ->
      lift $
      do tms <- traverse (boolValToTerm sc <=< force) (V.toList vs)
         tp <- scBoolType sc
         scVectorReduced sc tp tms
    v -> lift (putStrLn ("primBVTermFun: unhandled value: " ++ show v)) >> mzero

-- | Implementations of primitives for normalizing Mr Solver terms
smtNormPrims :: SharedContext -> Map Ident TmPrim
smtNormPrims sc = Map.fromList
  [
    ("Prelude.genBVVec",
     Prim (do tp <- scTypeOfGlobal sc "Prelude.genBVVec"
              VExtra <$> VExtraTerm (VTyTerm (mkSort 1) tp) <$>
                scGlobalDef sc "Prelude.genBVVec")),

    ("Prelude.atBVVec",
     PrimFun $ \_n -> PrimFun $ \_len -> tvalFun $ \a ->
      primGenBVVec sc $ \f -> primBVTermFun sc $ \ix -> PrimFun $ \_pf ->
      Prim (VExtra <$> VExtraTerm a <$> scApply sc f ix)
    ),
    ("Prelude.CompM",
     PrimFilterFun "CompM" (\case
                               TValue tv -> return tv
                               _ -> mzero) $ \tv ->
      Prim (do let ?recordEC = \_ec -> return ()
               let cfg = error "FIXME: smtNormPrims: need the simulator config"
               tv_trm <- readBackTValue sc cfg tv
               TValue <$> VTyTerm (mkSort 0) <$>
                 scGlobalApply sc "Prelude.CompM" [tv_trm]))
  ]

-- | Normalize a 'Term' using some Mr Solver specific primitives
mrNormTerm :: Term -> MRM Term
mrNormTerm t =
  debugPrint 2 "Normalizing term:" >>
  debugPrettyInCtx 2 t >>
  liftSC0 return >>= \sc ->
  liftSC0 scGetModuleMap >>= \modmap ->
  liftSC5 normalizeSharedTerm modmap (smtNormPrims sc) Map.empty Set.empty t

-- | Normalize an open term by wrapping it in lambdas, normalizing, and then
-- removing those lambdas
mrNormOpenTerm :: Term -> MRM Term
mrNormOpenTerm body =
  do ctx <- mrUVarCtx
     fun_term <- liftSC2 scLambdaList ctx body
     normed_fun <- mrNormTerm fun_term
     return (peel_lambdas (length ctx) normed_fun)
       where
         peel_lambdas :: Int -> Term -> Term
         peel_lambdas 0 t = t
         peel_lambdas i (asLambda -> Just (_, _, t)) = peel_lambdas (i-1) t
         peel_lambdas _ _ = error "mrNormOpenTerm: unexpected non-lambda term!"


----------------------------------------------------------------------
-- * Checking Provability with SMT
----------------------------------------------------------------------

-- | Test if a closed Boolean term is "provable", i.e., its negation is
-- unsatisfiable, using an SMT solver. By "closed" we mean that it contains no
-- uvars or 'MRVar's.
--
-- FIXME: use the timeout!
mrProvableRaw :: Term -> MRM Bool
mrProvableRaw prop_term =
  do sc <- mrSC
     prop <- liftSC1 termToProp prop_term
     unints <- Set.map ecVarIndex <$> getAllExtSet <$> liftSC1 propToTerm prop
     debugPrint 2 ("Calling SMT solver with proposition: " ++
                   prettyProp defaultPPOpts prop)
     sym <- liftIO $ setupWhat4_sym True
     (smt_res, _) <-
       liftIO $ proveWhat4_solver z3Adapter sym unints sc prop (return ())
     case smt_res of
       Just _ ->
         debugPrint 2 "SMT solver response: not provable" >> return False
       Nothing ->
         debugPrint 2 "SMT solver response: provable" >> return True

-- | Test if a Boolean term over the current uvars is provable given the current
-- assumptions
mrProvable :: Term -> MRM Bool
mrProvable (asBool -> Just b) = return b
mrProvable bool_tm =
  do assumps <- mrAssumptions
     prop <- liftSC2 scImplies assumps bool_tm >>= liftSC1 scEqTrue
     prop_inst <- instantiateUVarsM instUVar prop
     mrNormTerm prop_inst >>= mrProvableRaw
  where -- | Given a UVar name and type, generate a 'Term' to be passed to
        -- SMT, with special cases for BVVec and pair types
        instUVar :: LocalName -> Term -> MRM Term
        instUVar nm tp = liftSC1 scWhnf tp >>= \case
          -- For variables of type BVVec, create a @Vec n Bool -> a@ function
          -- as an ExtCns and apply genBVVec to it
          (asBVVecType -> Just (n, len, a)) -> do
             ec_tp <-
               liftSC1 completeOpenTerm $
               arrowOpenTerm "_" (applyOpenTermMulti (globalOpenTerm "Prelude.Vec")
                                  [closedOpenTerm n, boolTypeOpenTerm])
               (closedOpenTerm a)
             ec <- instUVar nm ec_tp
             liftSC4 genBVVecTerm n len a ec
          -- For tuples, recurse on all components and combine the result as a tuple
          (asTupleType -> Just tps) ->
            liftSC1 scTuple =<< traverse (instUVar nm) tps
          -- Otherwise, create a global variable with the given name and type
          tp' -> liftSC2 scFreshEC nm tp' >>= liftSC1 scExtCns


----------------------------------------------------------------------
-- * Checking Equality with SMT
----------------------------------------------------------------------

-- | Build a Boolean 'Term' stating that two 'Term's are equal. This is like
-- 'scEq' except that it works on open terms.
mrEq :: Term -> Term -> MRM Term
mrEq t1 t2 = mrTypeOf t1 >>= \tp -> mrEq' tp t1 t2

-- | Build a Boolean 'Term' stating that the second and third 'Term' arguments
-- are equal, where the first 'Term' gives their type (which we assume is the
-- same for both). This is like 'scEq' except that it works on open terms.
mrEq' :: Term -> Term -> Term -> MRM Term
mrEq' (asDataType -> Just (pn, [])) t1 t2
  | primName pn == "Prelude.Nat" = liftSC2 scEqualNat t1 t2
mrEq' (asBoolType -> Just _) t1 t2 = liftSC2 scBoolEq t1 t2
mrEq' (asIntegerType -> Just _) t1 t2 = liftSC2 scIntEq t1 t2
mrEq' (asVectorType -> Just (n, asBoolType -> Just ())) t1 t2 =
  liftSC3 scBvEq n t1 t2
mrEq' _ _ _ = error "mrEq': unsupported type"

-- | A 'Term' in an extended context of universal variables, which are listed
-- "outside in", meaning the highest deBruijn index comes first
data TermInCtx = TermInCtx [(LocalName,Term)] Term

-- | Conjoin two 'TermInCtx's, assuming they both have Boolean type
andTermInCtx :: TermInCtx -> TermInCtx -> MRM TermInCtx
andTermInCtx (TermInCtx ctx1 t1) (TermInCtx ctx2 t2) =
  do
    -- Insert the variables in ctx2 into the context of t1 starting at index 0,
    -- by lifting its variables starting at 0 by length ctx2
    t1' <- liftTermLike 0 (length ctx2) t1
    -- Insert the variables in ctx1 into the context of t1 starting at index
    -- length ctx2, by lifting its variables starting at length ctx2 by length
    -- ctx1
    t2' <- liftTermLike (length ctx2) (length ctx1) t2
    TermInCtx (ctx1++ctx2) <$> liftSC2 scAnd t1' t2'

-- | Conjoin a list of 'TermInCtx's, assuming they all have Boolean type.
allTermInCtx :: [TermInCtx] -> MRM TermInCtx
allTermInCtx [] = TermInCtx [] <$> liftSC1 scBool True
allTermInCtx [x] = pure x
allTermInCtx (x : xs) = andTermInCtx x =<< allTermInCtx xs

-- | Extend the context of a 'TermInCtx' with additional universal variables
-- bound "outside" the 'TermInCtx'
extTermInCtx :: [(LocalName,Term)] -> TermInCtx -> TermInCtx
extTermInCtx ctx (TermInCtx ctx' t) = TermInCtx (ctx++ctx') t

-- | Run an 'MRM' computation in the context of a 'TermInCtx', passing in the
-- 'Term'
withTermInCtx :: TermInCtx -> (Term -> MRM a) -> MRM a
withTermInCtx (TermInCtx [] tm) f = f tm
withTermInCtx (TermInCtx ((nm,tp):ctx) tm) f =
  withUVar nm (Type tp) $ const $ withTermInCtx (TermInCtx ctx tm) f

-- | A "simple" strategy for proving equality between two terms, which we assume
-- are of the same type, which builds an equality proposition by applying the
-- supplied function to both sides and passes this proposition to an SMT solver.
mrProveEqSimple :: (Term -> Term -> MRM Term) -> Term -> Term ->
                   MRM TermInCtx
-- NOTE: The use of mrSubstEVars instead of mrSubstEVarsStrict means that we
-- allow evars in the terms we send to the SMT solver, but we treat them as
-- uvars.
mrProveEqSimple eqf t1 t2 =
  do t1' <- mrSubstEVars t1
     t2' <- mrSubstEVars t2
     TermInCtx [] <$> eqf t1' t2'

-- | Prove that two terms are equal, instantiating evars if necessary,
-- returning true on success
mrProveEq :: Term -> Term -> MRM Bool
mrProveEq t1 t2 =
  do mrDebugPPPrefixSep 1 "mrProveEq" t1 "==" t2
     tp <- mrTypeOf t1 >>= mrSubstEVars
     varmap <- mrVars
     cond_in_ctx <- mrProveEqH varmap tp t1 t2
     res <- withTermInCtx cond_in_ctx mrProvable
     debugPrint 1 $ "mrProveEq: " ++ if res then "Success" else "Failure"
     return res

-- | Prove that two terms are equal, instantiating evars if necessary, or
-- throwing an error if this is not possible
mrAssertProveEq :: Term -> Term -> MRM ()
mrAssertProveEq t1 t2 =
  do success <- mrProveEq t1 t2
     if success then return () else
       throwMRFailure (TermsNotEq t1 t2)

-- | The main workhorse for 'mrProveEq'. Build a Boolean term expressing that
-- the third and fourth arguments, whose type is given by the second.
mrProveEqH :: Map MRVar MRVarInfo -> Term -> Term -> Term -> MRM TermInCtx

{-
mrProveEqH _ _ t1 t2
  | trace ("mrProveEqH:\n" ++ showTerm t1 ++ "\n==\n" ++ showTerm t2) False = undefined
-}

-- If t1 is an instantiated evar, substitute and recurse
mrProveEqH var_map tp (asEVarApp var_map -> Just (_, args, Just f)) t2 =
  mrApplyAll f args >>= \t1' -> mrProveEqH var_map tp t1' t2

-- If t1 is an uninstantiated evar, instantiate it with t2
mrProveEqH var_map _tp (asEVarApp var_map -> Just (evar, args, Nothing)) t2 =
  do t2' <- mrSubstEVars t2
     success <- mrTrySetAppliedEVar evar args t2'
     TermInCtx [] <$> liftSC1 scBool success

-- If t2 is an instantiated evar, substitute and recurse
mrProveEqH var_map tp t1 (asEVarApp var_map -> Just (_, args, Just f)) =
  mrApplyAll f args >>= \t2' -> mrProveEqH var_map tp t1 t2'

-- If t2 is an uninstantiated evar, instantiate it with t1
mrProveEqH var_map _tp t1 (asEVarApp var_map -> Just (evar, args, Nothing)) =
  do t1' <- mrSubstEVars t1
     success <- mrTrySetAppliedEVar evar args t1'
     TermInCtx [] <$> liftSC1 scBool success

-- For unit types, always return true
mrProveEqH _ (asTupleType -> Just []) _ _ =
  TermInCtx [] <$> liftSC1 scBool True

-- For the nat, bitvector, Boolean, and integer types, call mrProveEqSimple
mrProveEqH _ (asDataType -> Just (pn, [])) t1 t2
  | primName pn == "Prelude.Nat" =
    mrProveEqSimple (liftSC2 scEqualNat) t1 t2
mrProveEqH _ (asVectorType -> Just (n, asBoolType -> Just ())) t1 t2 =
  -- FIXME: make a better solver for bitvector equalities
  mrProveEqSimple (liftSC3 scBvEq n) t1 t2
mrProveEqH _ (asBoolType -> Just _) t1 t2 =
  mrProveEqSimple (liftSC2 scBoolEq) t1 t2
mrProveEqH _ (asIntegerType -> Just _) t1 t2 =
  mrProveEqSimple (liftSC2 scIntEq) t1 t2

-- For tuple types, prove all of the projections are equal
mrProveEqH var_map (asTupleType -> Just tps) t1 t2 =
  do let idxs = [0 .. length tps - 1]
     ts1 <- liftSC1 (\sc t -> traverse (scTupleSelector sc t) idxs) t1
     ts2 <- liftSC1 (\sc t -> traverse (scTupleSelector sc t) idxs) t2
     conds <- sequence $ zipWith3 (mrProveEqH var_map) tps ts1 ts2
     allTermInCtx conds

-- For non-bitvector vector types, prove all projections are equal by
-- quantifying over a universal index variable and proving equality at that
-- index
mrProveEqH _ (asBVVecType -> Just (n, len, tp)) t1 t2 =
  liftSC0 scBoolType >>= \bool_tp ->
  liftSC2 scVecType n bool_tp >>= \ix_tp ->
  withUVarLift "eq_ix" (Type ix_tp) (n,(len,(tp,(t1,t2)))) $
  \ix' (n',(len',(tp',(t1',t2')))) ->
  liftSC2 scGlobalApply "Prelude.is_bvult" [n', ix', len'] >>= \pf_tp ->
  withUVarLift "eq_pf" (Type pf_tp) (n',(len',(tp',(ix',(t1',t2'))))) $
  \pf'' (n'',(len'',(tp'',(ix'',(t1'',t2''))))) ->
  do t1_prj <- liftSC2 scGlobalApply "Prelude.atBVVec" [n'', len'', tp'',
                                                        t1'', ix'', pf'']
     t2_prj <- liftSC2 scGlobalApply "Prelude.atBVVec" [n'', len'', tp'',
                                                        t2'', ix'', pf'']
     var_map <- mrVars
     extTermInCtx [("eq_ix",ix_tp),("eq_pf",pf_tp)] <$>
       mrProveEqH var_map tp'' t1_prj t2_prj

-- As a fallback, for types we can't handle, just check convertibility
mrProveEqH _ _ t1 t2 =
  do success <- mrConvertible t1 t2
     TermInCtx [] <$> liftSC1 scBool success
