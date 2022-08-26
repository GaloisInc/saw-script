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
import Numeric.Natural (Natural)
import Control.Monad.Except
import qualified Control.Exception as X

import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Verifier.SAW.Term.Functor
import Verifier.SAW.Term.Pretty
import Verifier.SAW.SharedTerm
import Verifier.SAW.Recognizer
import Verifier.SAW.OpenTerm

import Verifier.SAW.Prim (EvalError(..))
import qualified Verifier.SAW.Prim as Prim
import Verifier.SAW.Simulator.Value
import Verifier.SAW.Simulator.TermModel
import Verifier.SAW.Simulator.Prims

import SAWScript.Proof (termToProp, propToTerm, prettyProp, propToSequent)
import What4.Solver
import SAWScript.Prover.What4

import SAWScript.Prover.MRSolver.Term
import SAWScript.Prover.MRSolver.Monad


----------------------------------------------------------------------
-- * Various SMT-specific Functions on Terms
----------------------------------------------------------------------

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

-- | Match a term of the form @genFromBVVec n len a v def m@
asGenFromBVVecTerm :: Recognizer Term (Term, Term, Term, Term, Term, Term)
asGenFromBVVecTerm (asApplyAll ->
                       (isGlobalDef "Prelude.genFromBVVec" -> Just _,
                        [n, len, a, v, def, m]))
  = Just (n, len, a, v, def, m)
asGenFromBVVecTerm _ = Nothing

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
      lift $ scBvLit sc (fromIntegral (Prim.width bv)) (Prim.unsigned bv)
    VVector vs ->
      lift $
      do tms <- traverse (boolValToTerm sc <=< force) (V.toList vs)
         tp <- scBoolType sc
         scVectorReduced sc tp tms
    v -> lift (putStrLn ("primBVTermFun: unhandled value: " ++ show v)) >> mzero

-- | A datatype representing either a @genFromBVVec n len _ v _ _@ term or
-- a vector literal, the latter being represented as a list of 'Term's
data FromBVVecOrLit = FromBVVec { fromBVVec_n :: Natural
                                , fromBVVec_len :: Term
                                , fromBVVec_vec :: Term }
                    | BVVecLit [Term]

-- | An implementation of a primitive function that expects either a
-- @genFromBVVec@ term or a vector literal
primFromBVVecOrLit :: SharedContext -> TValue TermModel ->
                      (FromBVVecOrLit -> TmPrim) -> TmPrim
primFromBVVecOrLit sc a =
  PrimFilterFun "primFromBVVecOrLit" $
  \case
    VExtra (VExtraTerm _ (asGenFromBVVecTerm -> Just (asNat -> Just n, len, _,
                                                      v, _, _))) ->
      return $ FromBVVec n len v
    VVector vs ->
      lift $ BVVecLit <$>
        traverse (readBackValueNoConfig "primFromBVVecOrLit" sc a <=< force)
                 (V.toList vs)
    _ -> mzero

-- | Turn a 'FromBVVecOrLit' into a BVVec term, assuming it has the given
-- bit-width (given as both a 'Natural' and a 'Term'), length, and element type
-- FIXME: Properly handle empty vector literals
bvVecFromBVVecOrLit :: SharedContext -> Natural -> Term -> Term -> Term ->
                       FromBVVecOrLit -> IO Term
bvVecFromBVVecOrLit sc n _ len _ (FromBVVec n' len' v) =
  do len_cvt_len' <- scConvertible sc True len len'
     if n == n' && len_cvt_len' then return v
     else error "bvVecFromBVVecOrLit: genFromBVVec type mismatch"
bvVecFromBVVecOrLit sc n n' len a (BVVecLit vs) =
  do body <- mkBody 0 vs
     i_tp <- scBitvector sc n
     var0 <- scLocalVar sc 0
     pf_tp <- scGlobalApply sc "Prelude.is_bvult" [n', var0, len]
     f <- scLambdaList sc [("i", i_tp), ("pf", pf_tp)] body 
     scGlobalApply sc "Prelude.genBVVec" [n', len, a, f]
  where mkBody :: Integer -> [Term] -> IO Term
        mkBody _ [] = error "bvVecFromBVVecOrLit: empty vector"
        mkBody _ [x] = return $ x
        mkBody i (x:xs) =
          do var1 <- scLocalVar sc 1
             i' <- scBvConst sc n i
             cond <- scBvEq sc n' var1 i'
             body' <- mkBody (i+1) xs
             scIte sc a cond x body'

-- | A version of 'readBackTValue' which uses 'error' as the simulator config
-- Q: Is there every a case where this will actually error?
readBackTValueNoConfig :: String -> SharedContext ->
                          TValue TermModel -> IO Term
readBackTValueNoConfig err_str sc tv =
  let ?recordEC = \_ec -> return () in
  let cfg = error $ "FIXME: need the simulator config in " ++ err_str
   in readBackTValue sc cfg tv

-- | A version of 'readBackValue' which uses 'error' as the simulator config
-- Q: Is there every a case where this will actually error?
readBackValueNoConfig :: String -> SharedContext ->
                         TValue TermModel -> Value TermModel -> IO Term
readBackValueNoConfig err_str sc tv v =
  let ?recordEC = \_ec -> return () in
  let cfg = error $ "FIXME: need the simulator config in " ++ err_str
   in readBackValue sc cfg tv v

-- | Implementations of primitives for normalizing Mr Solver terms
smtNormPrims :: SharedContext -> Map Ident TmPrim
smtNormPrims sc = Map.fromList
  [ -- Don't unfold @genBVVec@ when normalizing
    ("Prelude.genBVVec",
     Prim (do tp <- scTypeOfGlobal sc "Prelude.genBVVec"
              VExtra <$> VExtraTerm (VTyTerm (mkSort 1) tp) <$>
                scGlobalDef sc "Prelude.genBVVec")
    ),
    -- Normalize applications of @genBVVecFromVec@ to a @genFromBVVec@ term or
    -- a vector literal into the body of the @genFromBVVec@ term or @genBVVec@
    -- of an sequence of @ite@s defined by the literal, respectively
    ("Prelude.genBVVecFromVec",
     natFun $ \_m -> tvalFun $ \a -> primFromBVVecOrLit sc a $ \eith ->
      PrimFun $ \_def -> natFun $ \n -> primBVTermFun sc $ \len ->
      Prim (do n' <- scNat sc n
               a' <- readBackTValueNoConfig "smtNormPrims (genBVVecFromVec)" sc a
               tp <- scGlobalApply sc "Prelude.BVVec" [n', len, a']
               VExtra <$> VExtraTerm (VTyTerm (mkSort 0) tp) <$>
                 bvVecFromBVVecOrLit sc n n' len a' eith)
    ),
    -- Don't normalize applications of @genFromBVVec@
    ("Prelude.genFromBVVec",
     natFun $ \n -> PrimStrict $ \len -> tvalFun $ \a -> PrimStrict $ \v ->
      PrimStrict $ \def -> natFun $ \m ->
      Prim (do n' <- scNat sc n
               let len_tp = VVecType n VBoolType
               len' <- readBackValueNoConfig "smtNormPrims (genFromBVVec)" sc len_tp len
               a' <- readBackTValueNoConfig "smtNormPrims (genFromBVVec)" sc a
               bvToNat_len <- scGlobalApply sc "Prelude.bvToNat" [n', len']
               v_tp <- VTyTerm (mkSort 0) <$> scVecType sc bvToNat_len a'
               v' <- readBackValueNoConfig "smtNormPrims (genFromBVVec)" sc v_tp v
               def' <- readBackValueNoConfig "smtNormPrims (genFromBVVec)" sc a def
               m' <- scNat sc m
               tm <- scGlobalApply sc "Prelude.genFromBVVec" [n', len', a', v', def', m']
               return $ VExtra $ VExtraTerm (VVecType m a) tm)
    ),
    -- Normalize applications of @atBVVec@ to a @genBVVec@ term into an
    -- application of the body of the @genBVVec@ term to the index
    ("Prelude.atBVVec",
     PrimFun $ \_n -> PrimFun $ \_len -> tvalFun $ \a ->
      primGenBVVec sc $ \f -> primBVTermFun sc $ \ix -> PrimFun $ \_pf ->
      Prim (VExtra <$> VExtraTerm a <$> scApplyBeta sc f ix)
    ),
    -- Don't normalize applications of @CompM@
    ("Prelude.CompM",
     PrimFilterFun "CompM" (\case
                               TValue tv -> return tv
                               _ -> mzero) $ \tv ->
      Prim (do tv_trm <- readBackTValueNoConfig "smtNormPrims (CompM)" sc tv
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
     nenv <- liftIO (scGetNamingEnv sc)
     debugPrint 2 ("Calling SMT solver with proposition: " ++
                   prettyProp defaultPPOpts nenv prop)
     sym <- liftIO $ setupWhat4_sym True
     -- If there are any saw-core `error`s in the term, this will throw a
     -- Haskell error - in this case we want to just return False, not stop
     -- execution
     smt_res <- liftIO $
       (Right <$> proveWhat4_solver z3Adapter sym unints sc (propToSequent prop) (return ()))
         `X.catch` \case
           UserError msg -> return $ Left msg
           e -> X.throw e
     case smt_res of
       Left msg ->
         debugPrint 2 ("SMT solver encountered a saw-core error term: " ++ msg)
           >> return False
       Right (Just _, _) ->
         debugPrint 2 "SMT solver response: not provable" >> return False
       Right (Nothing, _) ->
         debugPrint 2 "SMT solver response: provable" >> return True

-- | Test if a Boolean term over the current uvars is provable given the current
-- assumptions
mrProvable :: Term -> MRM Bool
mrProvable (asBool -> Just b) = return b
mrProvable bool_tm =
  do assumps <- mrAssumptions
     prop <- liftSC2 scImplies assumps bool_tm >>= liftSC1 scEqTrue
     prop_inst <- mrSubstEVars prop >>= instantiateUVarsM instUVar
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
          -- For pairs, recurse on both sides and combine the result as a pair
          (asPairType -> Just (tp1, tp2)) -> do
            e1 <- instUVar nm tp1
            e2 <- instUVar nm tp2
            liftSC2 scPairValue e1 e2
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
-- FIXME: For this Nat case, the definition of 'equalNat' in @Prims.hs@ means
-- that if both sides do not have immediately clear bit-widths (e.g. either
-- side is is an application of @mulNat@) this will 'error'...
mrEq' (asNatType -> Just _) t1 t2 = liftSC2 scEqualNat t1 t2
mrEq' (asBoolType -> Just _) t1 t2 = liftSC2 scBoolEq t1 t2
mrEq' (asIntegerType -> Just _) t1 t2 = liftSC2 scIntEq t1 t2
mrEq' (asVectorType -> Just (n, asBoolType -> Just ())) t1 t2 =
  liftSC3 scBvEq n t1 t2
mrEq' (asDataType -> Just (primName -> "Cryptol.Num", _)) t1 t2 =
  liftSC1 scWhnf t1 >>= \t1' -> liftSC1 scWhnf t2 >>= \t2' -> case (t1', t2') of
    (asCtor -> Just (primName -> "Cryptol.TCNum", [t1'']),
     asCtor -> Just (primName -> "Cryptol.TCNum", [t2''])) ->
      liftSC0 scNatType >>= \nat_tp -> mrEq' nat_tp t1'' t2''
    _ -> error "mrEq': Num terms do not normalize to TCNum constructors"
mrEq' _ _ _ = error "mrEq': unsupported type"

-- | A 'Term' in an extended context of universal variables, which are listed
-- "outside in", meaning the highest deBruijn index comes first
data TermInCtx = TermInCtx [(LocalName,Term)] Term

-- | Lift a binary operation on 'Term's to one on 'TermInCtx's
liftTermInCtx2 :: (SharedContext -> Term -> Term -> IO Term) ->
                   TermInCtx -> TermInCtx -> MRM TermInCtx
liftTermInCtx2 op (TermInCtx ctx1 t1) (TermInCtx ctx2 t2) =
  do
    -- Insert the variables in ctx2 into the context of t1 starting at index 0,
    -- by lifting its variables starting at 0 by length ctx2
    t1' <- liftTermLike 0 (length ctx2) t1
    -- Insert the variables in ctx1 into the context of t1 starting at index
    -- length ctx2, by lifting its variables starting at length ctx2 by length
    -- ctx1
    t2' <- liftTermLike (length ctx2) (length ctx1) t2
    TermInCtx (ctx1++ctx2) <$> liftSC2 op t1' t2'

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
-- returning true on success - the same as @mrProveRel False@
mrProveEq :: Term -> Term -> MRM Bool
mrProveEq = mrProveRel False

-- | Prove that two terms are equal, instantiating evars if necessary, or
-- throwing an error if this is not possible - the same as
-- @mrAssertProveRel False@
mrAssertProveEq :: Term -> Term -> MRM ()
mrAssertProveEq = mrAssertProveRel False

-- | Prove that two terms are related, heterogeneously iff the first argument
-- is true, instantiating evars if necessary, returning true on success
mrProveRel :: Bool -> Term -> Term -> MRM Bool
mrProveRel het t1 t2 =
  do let nm = if het then "mrProveRel" else "mrProveEq"
     mrDebugPPPrefixSep 2 nm t1 (if het then "~=" else "==") t2
     tp1 <- mrTypeOf t1 >>= mrSubstEVars
     tp2 <- mrTypeOf t2 >>= mrSubstEVars
     cond_in_ctx <- mrProveRelH het tp1 tp2 t1 t2
     res <- withTermInCtx cond_in_ctx mrProvable
     debugPrint 2 $ nm ++ ": " ++ if res then "Success" else "Failure"
     return res

-- | Prove that two terms are related, heterogeneously iff the first argument,
-- is true, instantiating evars if necessary, or throwing an error if this is
-- not possible
mrAssertProveRel :: Bool -> Term -> Term -> MRM ()
mrAssertProveRel het t1 t2 =
  do success <- mrProveRel het t1 t2
     if success then return () else
       throwMRFailure (TermsNotRel het t1 t2)

-- | The main workhorse for 'mrProveEq' and 'mrProveRel'. Build a Boolean term
-- expressing that the fourth and fifth arguments are related, heterogeneously
-- iff the first argument is true, whose types are given by the second and
-- third arguments, respectively
mrProveRelH :: Bool -> Term -> Term -> Term -> Term -> MRM TermInCtx
mrProveRelH het tp1 tp2 t1 t2 =
  do varmap <- mrVars
     tp1' <- liftSC1 scWhnf tp1
     tp2' <- liftSC1 scWhnf tp2
     mrProveRelH' varmap het tp1' tp2' t1 t2

-- | The body of 'mrProveRelH'
-- NOTE: Don't call this function recursively, call 'mrProveRelH'
mrProveRelH' :: Map MRVar MRVarInfo -> Bool ->
                Term -> Term -> Term -> Term -> MRM TermInCtx

-- If t1 is an instantiated evar, substitute and recurse
mrProveRelH' var_map het tp1 tp2 (asEVarApp var_map -> Just (_, args, Just f)) t2 =
  mrApplyAll f args >>= \t1' -> mrProveRelH het tp1 tp2 t1' t2

-- If t1 is an uninstantiated evar, ensure the types are equal and instantiate
-- it with t2
mrProveRelH' var_map _ tp1 tp2 (asEVarApp var_map -> Just (evar, args, Nothing)) t2 =
  do tps_are_eq <- mrConvertible tp1 tp2
     if tps_are_eq then return () else
       throwMRFailure (TypesNotEq (Type tp1) (Type tp2))
     t2' <- mrSubstEVars t2
     success <- mrTrySetAppliedEVar evar args t2'
     when success $
       mrDebugPPPrefixSep 1 "setting evar" evar "to" t2
     TermInCtx [] <$> liftSC1 scBool success

-- If t2 is an instantiated evar, substitute and recurse
mrProveRelH' var_map het tp1 tp2 t1 (asEVarApp var_map -> Just (_, args, Just f)) =
  mrApplyAll f args >>= \t2' -> mrProveRelH het tp1 tp2 t1 t2'

-- If t2 is an uninstantiated evar, ensure the types are equal and instantiate
-- it with t1
mrProveRelH' var_map _ tp1 tp2 t1 (asEVarApp var_map -> Just (evar, args, Nothing)) =
  do tps_are_eq <- mrConvertible tp1 tp2
     if tps_are_eq then return () else
       throwMRFailure (TypesNotEq (Type tp1) (Type tp2))
     t1' <- mrSubstEVars t1
     success <- mrTrySetAppliedEVar evar args t1'
     when success $
       mrDebugPPPrefixSep 1 "setting evar" evar "to" t1
     TermInCtx [] <$> liftSC1 scBool success

-- For unit types, always return true
mrProveRelH' _ _ (asTupleType -> Just []) (asTupleType -> Just []) _ _ =
  TermInCtx [] <$> liftSC1 scBool True

-- For nat, bitvector, Boolean, and integer types, call mrProveEqSimple
mrProveRelH' _ _ (asNatType -> Just _) (asNatType -> Just _) t1 t2 =
  mrProveEqSimple (liftSC2 scEqualNat) t1 t2
mrProveRelH' _ _ tp1@(asVectorType -> Just (n1, asBoolType -> Just ())) 
                tp2@(asVectorType -> Just (n2, asBoolType -> Just ())) t1 t2 =
  do ns_are_eq <- mrConvertible n1 n2
     if ns_are_eq then return () else
       throwMRFailure (TypesNotEq (Type tp1) (Type tp2))
     mrProveEqSimple (liftSC3 scBvEq n1) t1 t2
mrProveRelH' _ _ (asBoolType -> Just _) (asBoolType -> Just _) t1 t2 =
  mrProveEqSimple (liftSC2 scBoolEq) t1 t2
mrProveRelH' _ _ (asIntegerType -> Just _) (asIntegerType -> Just _) t1 t2 =
  mrProveEqSimple (liftSC2 scIntEq) t1 t2

-- For BVVec types, prove all projections are related by quantifying over an
-- index variable and proving the projections at that index are related
mrProveRelH' _ het tp1@(asBVVecType -> Just (n1, len1, tpA1))
                   tp2@(asBVVecType -> Just (n2, len2, tpA2)) t1 t2 =
  mrConvertible n1 n2 >>= \ns_are_eq ->
  mrConvertible len1 len2 >>= \lens_are_eq ->
  (if ns_are_eq && lens_are_eq then return () else
     throwMRFailure (TypesNotEq (Type tp1) (Type tp2))) >>
  liftSC0 scBoolType >>= \bool_tp ->
  liftSC2 scVecType n1 bool_tp >>= \ix_tp ->
  withUVarLift "eq_ix" (Type ix_tp) (n1,(len1,(tpA1,(tpA2,(t1,t2))))) $
  \ix (n1',(len1',(tpA1',(tpA2',(t1',t2'))))) ->
  do ix_bound <- liftSC2 scGlobalApply "Prelude.bvult" [n1', ix, len1']
     pf <- liftSC2 scGlobalApply "Prelude.unsafeAssertBVULt" [n1', ix, len1']
     t1_prj <- liftSC2 scGlobalApply "Prelude.atBVVec" [n1', len1', tpA1',
                                                        t1', ix, pf]
     t2_prj <- liftSC2 scGlobalApply "Prelude.atBVVec" [n1', len1', tpA2',
                                                        t2', ix, pf]
     cond <- mrProveRelH het tpA1' tpA2' t1_prj t2_prj
     extTermInCtx [("eq_ix",ix_tp)] <$>
       liftTermInCtx2 scImplies (TermInCtx [] ix_bound) cond

-- For non-BVVec vector types where at least one side is an application of
-- genFromBVVec, wrap both sides in genBVVecFromVec and recurse
mrProveRelH' _ het tp1@(asNonBVVecVectorType -> Just (m1, tpA1))
                   tp2@(asNonBVVecVectorType -> Just (m2, tpA2))
                   t1@(asGenFromBVVecTerm -> Just (n, len, _, _, _, _)) t2 =
  do ms_are_eq <- mrConvertible m1 m2
     if ms_are_eq then return () else
       throwMRFailure (TypesNotEq (Type tp1) (Type tp2))
     len' <- liftSC2 scGlobalApply "Prelude.bvToNat" [n, len]
     tp1' <- liftSC2 scVecType len' tpA1
     tp2' <- liftSC2 scVecType len' tpA2
     t1' <- mrGenBVVecFromVec m1 tpA1 t1 "mrProveRelH (BVVec/BVVec)" n len
     t2' <- mrGenBVVecFromVec m2 tpA2 t2 "mrProveRelH (BVVec/BVVec)" n len
     mrProveRelH het tp1' tp2' t1' t2'
mrProveRelH' _ het tp1@(asNonBVVecVectorType -> Just (m1, tpA1))
                   tp2@(asNonBVVecVectorType -> Just (m2, tpA2))
                   t1 t2@(asGenFromBVVecTerm -> Just (n, len, _, _, _, _)) =
  do ms_are_eq <- mrConvertible m1 m2
     if ms_are_eq then return () else
       throwMRFailure (TypesNotEq (Type tp1) (Type tp2))
     len' <- liftSC2 scGlobalApply "Prelude.bvToNat" [n, len]
     tp1' <- liftSC2 scVecType len' tpA1
     tp2' <- liftSC2 scVecType len' tpA2
     t1' <- mrGenBVVecFromVec m1 tpA1 t1 "mrProveRelH (BVVec/BVVec)" n len
     t2' <- mrGenBVVecFromVec m2 tpA2 t2 "mrProveRelH (BVVec/BVVec)" n len
     mrProveRelH het tp1' tp2' t1' t2'

mrProveRelH' _ True tp1 tp2 t1 t2 | Just mh <- matchHet tp1 tp2 = case mh of

  -- If our relation is heterogeneous and we have a bitvector on one side and
  -- a Num on the other, ensure that the Num term is TCNum of some Nat, wrap
  -- the Nat with bvNat, and recurse
  HetBVNum n
    | Just (primName -> "Cryptol.TCNum", [t2']) <- asCtor t2 ->
    do n_tm <- liftSC1 scNat n
       t2'' <- liftSC2 scGlobalApply "Prelude.bvNat" [n_tm, t2']
       mrProveRelH True tp1 tp1 t1 t2''
    | otherwise -> throwMRFailure (TermsNotEq t1 t2)
  HetNumBV n
    | Just (primName -> "Cryptol.TCNum", [t1']) <- asCtor t1 ->
    do n_tm <- liftSC1 scNat n
       t1'' <- liftSC2 scGlobalApply "Prelude.bvNat" [n_tm, t1']
       mrProveRelH True tp1 tp1 t1'' t2
    | otherwise -> throwMRFailure (TermsNotEq t1 t2)

  -- If our relation is heterogeneous and we have a BVVec on one side and a
  -- non-BVVec vector on the other, wrap the non-BVVec vector term in
  -- genBVVecFromVec and recurse
  HetBVVecVec (n, len, _) (m, tpA2) ->
    do m' <- mrBvToNat n len
       ms_are_eq <- mrConvertible m' m
       if ms_are_eq then return () else
         throwMRFailure (TypesNotRel True (Type tp1) (Type tp2))
       len' <- liftSC2 scGlobalApply "Prelude.bvToNat" [n, len]
       tp2' <- liftSC2 scVecType len' tpA2
       t2' <- mrGenBVVecFromVec m tpA2 t2 "mrProveRelH (BVVec/Vec)" n len
       -- mrDebugPPPrefixSep 2 "mrProveRelH on BVVec/Vec: " t1 "an`d" t2'
       mrProveRelH True tp1 tp2' t1 t2'
  HetVecBVVec (m, tpA1) (n, len, _) ->
    do m' <- mrBvToNat n len
       ms_are_eq <- mrConvertible m' m
       if ms_are_eq then return () else
         throwMRFailure (TypesNotRel True (Type tp1) (Type tp2))
       len' <- liftSC2 scGlobalApply "Prelude.bvToNat" [n, len]
       tp1' <- liftSC2 scVecType len' tpA1
       t1' <- mrGenBVVecFromVec m tpA1 t1 "mrProveRelH (Vec/BVVec)" n len
       -- mrDebugPPPrefixSep 2 "mrProveRelH on Vec/BVVec: " t1' "and" t2
       mrProveRelH True tp1' tp2 t1' t2

  -- For pair types, prove both the left and right projections are related
  -- (this should be the same as the pair case below - we have to split them
  -- up because otherwise GHC 9.0's pattern match checker complains...)
  HetPair (tpL1, tpR1) (tpL2, tpR2) ->
    do t1L <- liftSC1 scPairLeft t1
       t2L <- liftSC1 scPairLeft t2
       t1R <- liftSC1 scPairRight t1
       t2R <- liftSC1 scPairRight t2
       condL <- mrProveRelH True tpL1 tpL2 t1L t2L
       condR <- mrProveRelH True tpR1 tpR2 t1R t2R
       liftTermInCtx2 scAnd condL condR

-- For pair types, prove both the left and right projections are related
-- (this should be the same as the pair case below - we have to split them
-- up because otherwise GHC 9.0's pattern match checker complains...)
mrProveRelH' _ False tp1 tp2 t1 t2
  | Just (HetPair (tpL1, tpR1) (tpL2, tpR2)) <- matchHet tp1 tp2 =
    do t1L <- liftSC1 scPairLeft t1
       t2L <- liftSC1 scPairLeft t2
       t1R <- liftSC1 scPairRight t1
       t2R <- liftSC1 scPairRight t2
       condL <- mrProveRelH False tpL1 tpL2 t1L t2L
       condR <- mrProveRelH False tpR1 tpR2 t1R t2R
       liftTermInCtx2 scAnd condL condR

-- As a fallback, for types we can't handle, just check convertibility
mrProveRelH' _ het tp1 tp2 t1 t2 =
  do success <- mrConvertible t1 t2
     if success then return () else
       if het then mrDebugPPPrefixSep 2 "mrProveRelH' could not match types: " tp1 "and" tp2 >>
                   mrDebugPPPrefixSep 2 "and could not prove convertible: " t1 "and" t2
              else mrDebugPPPrefixSep 2 "mrProveEq could not prove convertible: " t1 "and" t2
     TermInCtx [] <$> liftSC1 scBool success
