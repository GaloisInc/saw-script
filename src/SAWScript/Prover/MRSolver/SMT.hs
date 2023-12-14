{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

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

import Data.Maybe
import qualified Data.Vector as V
import Numeric.Natural (Natural)
import Control.Monad.Except
import Control.Monad.Catch (throwM, catch)
import Control.Monad.Trans.Maybe
import GHC.Generics

import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Reflection
import Data.Parameterized.BoolRepr

import Verifier.SAW.Utils (panic)
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
import Verifier.SAW.Module
import Verifier.SAW.Prelude.Constants
import Verifier.SAW.FiniteValue
import SAWScript.Proof (termToProp, propToTerm, prettyProp, propToSequent, SolveResult(..))

import SAWScript.Prover.MRSolver.Term
import SAWScript.Prover.MRSolver.Monad


----------------------------------------------------------------------
-- * Various SMT-specific Functions on Terms
----------------------------------------------------------------------

-- | Recognize a bitvector type with a potentially symbolic length
asSymBVType :: Recognizer Term Term
asSymBVType (asVectorType -> Just (n, asBoolType -> Just ())) = Just n
asSymBVType _ = Nothing

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
                    [n, len, a, f@(asLambdaList -> ([_,_], e))]))
  | not $ inBitSet 0 $ looseVars e
  = Just (n, len, a, f)
asGenBVVecTerm _ = Nothing

-- | Match a term of the form @genCryM n a f@
asGenCryMTerm :: Recognizer Term (Term, Term, Term)
asGenCryMTerm (asApplyAll -> (isGlobalDef "CryptolM.genCryM" -> Just _,
                              [n, a, f]))
  = Just (n, a, f)
asGenCryMTerm _ = Nothing

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

-- | An implementation of a primitive function that expects a term of the form
-- @genBVVec n _ a _@ or @genCryM (bvToNat n _) a _@, where @n@ is the second
-- argument, and passes to the continuation the associated function of type
-- @Vec n Bool -> a@
primGenBVVec :: SharedContext -> Natural -> (Term -> TmPrim) -> TmPrim
primGenBVVec sc n =
  PrimFilterFun "primGenBVVec" $
  \case
    VExtra (VExtraTerm _ t) -> primGenBVVecFilter sc n t
    _ -> mzero

-- | The filter function for 'primGenBVVec', and one case of 'primGenCryM'
primGenBVVecFilter :: SharedContext -> Natural ->
                      Term -> MaybeT (EvalM TermModel) Term
primGenBVVecFilter sc n (asGenBVVecTerm -> Just (asNat -> Just n', _, _, f)) | n == n' = lift $
  do i_tp <- join $ scVecType sc <$> scNat sc n <*> scBoolType sc
     let err_tm = error "primGenBVVec: unexpected variable occurrence"
     i_tm <- scLocalVar sc 0
     body <- scApplyAllBeta sc f [i_tm, err_tm]
     scLambda sc "i" i_tp body
primGenBVVecFilter sc n (asGenCryMTerm -> Just (asBvToNatKnownW ->
                                                Just (n', _), _, f)) | n == n' = lift $
  do i_tp <- join $ scVecType sc <$> scNat sc n <*> scBoolType sc
     i_tm <- scLocalVar sc 0
     body <- scApplyBeta sc f =<< scBvToNat sc n i_tm
     scLambda sc "i" i_tp body
primGenBVVecFilter _ _ t =
  error $ "primGenBVVec could not handle: " ++ showInCtx emptyMRVarCtx t

-- | An implementation of a primitive function that expects a term of the form
-- @genCryM _ a _@, @genFromBVVec ... (genBVVec _ _ a _) ...@, or
-- @genFromBVVec ... (genCryM (bvToNat _ _) a _) ...@, and passes to the
-- continuation either @Just n@ and the associated function of type
-- @Vec n Bool -> a@, or @Nothing@ and the associated function of type
-- @Nat -> a@
primGenCryM :: SharedContext -> (Maybe Natural -> Term -> TmPrim) -> TmPrim
primGenCryM sc =
  PrimFilterFun "primGenCryM"
  (\case
      VExtra (VExtraTerm _ (asGenCryMTerm -> Just (_, _, f))) ->
        return (Nothing, f)
      VExtra (VExtraTerm _ (asGenFromBVVecTerm -> Just (asNat -> Just n, _, _,
                                                        v, _, _))) ->
        (Just n,) <$> primGenBVVecFilter sc n v
      _ -> mzero
  ) . uncurry

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

-- | A datatype representing the arguments to @genBVVecFromVec@ which can be
-- normalized: a @genFromBVVec n len _ v _ _@ term, a @genCryM _ _ body@ term,
-- or a vector literal, the lattermost being represented as a list of 'Term's
data BVVecFromVecArg = FromBVVec { fromBVVec_n :: Natural
                                 , fromBVVec_len :: Term
                                 , fromBVVec_vec :: Term }
                     | GenCryM Term
                     | BVVecLit [Term]

-- | An implementation of a primitive function that expects a @genFromBVVec@
-- term, a @genCryM@ term, or a vector literal
primBVVecFromVecArg :: SharedContext -> TValue TermModel ->
                       (BVVecFromVecArg -> TmPrim) -> TmPrim
primBVVecFromVecArg sc a =
  PrimFilterFun "primFromBVVecOrLit" $
  \case
    VExtra (VExtraTerm _ (asGenFromBVVecTerm -> Just (asNat -> Just n, len, _,
                                                      v, _, _))) ->
      return $ FromBVVec n len v
    VExtra (VExtraTerm _ (asGenCryMTerm -> Just (_, _, body))) ->
      return $ GenCryM body
    VVector vs ->
      lift $ BVVecLit <$>
        traverse (readBackValueNoConfig "primFromBVVecOrLit" sc a <=< force)
                 (V.toList vs)
    _ -> mzero

-- | Turn a 'BVVecFromVecArg' into a BVVec term, assuming it has the given
-- bit-width (given as both a 'Natural' and a 'Term'), length, and element type
-- FIXME: Properly handle empty vector literals
bvVecBVVecFromVecArg :: SharedContext -> Natural -> Term -> Term -> Term ->
                        BVVecFromVecArg -> IO Term
bvVecBVVecFromVecArg sc n _ len _ (FromBVVec n' len' v) =
  do len_cvt_len' <- scConvertible sc True len len'
     if n == n' && len_cvt_len' then return v
     else error "bvVecBVVecFromVecArg: genFromBVVec type mismatch"
bvVecBVVecFromVecArg sc n _ len a (GenCryM body) =
  do len' <- scBvToNat sc n len
     scGlobalApply sc "CryptolM.genCryM" [len', a, body]
bvVecBVVecFromVecArg sc n n' len a (BVVecLit vs) =
  do body <- mkBody 0 vs
     i_tp <- scBitvector sc n
     var0 <- scLocalVar sc 0
     pf_tp <- scGlobalApply sc "Prelude.is_bvult" [n', var0, len]
     f <- scLambdaList sc [("i", i_tp), ("pf", pf_tp)] body
     scGlobalApply sc "Prelude.genBVVec" [n', len, a, f]
  where mkBody :: Integer -> [Term] -> IO Term
        mkBody _ [] = error "bvVecBVVecFromVecArg: empty vector"
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

-- | A primitive that returns a global as a term
primGlobal :: SharedContext -> Ident -> TmPrim
primGlobal sc glob =
  Prim $ do tp <- scTypeOfGlobal sc glob
            tp_tp <- scTypeOf sc tp >>= scWhnf sc
            s <- case asSort tp_tp of
              Just s -> return s
              Nothing -> fail "primGlobal: expected sort"
            VExtra <$> VExtraTerm (VTyTerm s tp) <$> scGlobalDef sc glob

-- | Implementations of primitives for normalizing Mr Solver terms
-- FIXME: eventually we need to add the current event type to this list
smtNormPrims :: SharedContext -> Map Ident TmPrim
smtNormPrims sc = Map.fromList
  [ -- Don't unfold @genBVVec@ or @genCryM when normalizing
    ("Prelude.genBVVec",
     Prim (do tp <- scTypeOfGlobal sc "Prelude.genBVVec"
              VExtra <$> VExtraTerm (VTyTerm (mkSort 1) tp) <$>
                scGlobalDef sc "Prelude.genBVVec")
    ),
    ("CryptolM.genCryM",
     Prim (do tp <- scTypeOfGlobal sc "CryptolM.genCryM"
              VExtra <$> VExtraTerm (VTyTerm (mkSort 1) tp) <$>
                scGlobalDef sc "CryptolM.genCryM")
    ),
    -- Normalize applications of @genBVVecFromVec@ to a @genFromBVVec@ term
    -- into the body of the @genFromBVVec@ term, a @genCryM@ term into a
    -- @genCryM@ term of the new length, or vector literal into a sequence
    -- of @ite@s defined by the literal
    ("Prelude.genBVVecFromVec",
     PrimFun $ \_m -> tvalFun $ \a -> primBVVecFromVecArg sc a $ \eith ->
      PrimFun $ \_def -> natFun $ \n -> primBVTermFun sc $ \len ->
      Prim (do n' <- scNat sc n
               a' <- readBackTValueNoConfig "smtNormPrims (genBVVecFromVec)" sc a
               tp <- scGlobalApply sc "Prelude.BVVec" [n', len, a']
               VExtra <$> VExtraTerm (VTyTerm (mkSort 0) tp) <$>
                 bvVecBVVecFromVecArg sc n n' len a' eith)
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
    -- Normalize applications of @atBVVec@ or @atCryM@ to a @genBVVec@ or
    -- @genCryM@ term into an application of the body of the term to the index
    ("Prelude.atBVVec",
     natFun $ \n -> PrimFun $ \_len -> tvalFun $ \a ->
      primGenBVVec sc n $ \f -> primBVTermFun sc $ \ix -> PrimFun $ \_pf ->
      Prim (do tm <- scApplyBeta sc f ix
               tm' <- smtNorm sc tm
               return $ VExtra $ VExtraTerm a tm')
    ),
    ("CryptolM.atCryM",
     PrimFun $ \_n -> tvalFun $ \a ->
      primGenCryM sc $ \nMb f -> PrimStrict $ \ix ->
      Prim (do natDT <- scRequireDataType sc preludeNatIdent
               let natPN = fmap (const $ VSort (mkSort 0)) (dtPrimName natDT)
               let nat_tp = VDataType natPN [] []
               ix' <- readBackValueNoConfig "smtNormPrims (atCryM)" sc nat_tp ix
               ix'' <- case nMb of
                         Nothing -> return ix'
                         Just n -> scNat sc n >>= \n' -> scBvNat sc n' ix'
               tm <- scApplyBeta sc f ix''
               tm' <- smtNorm sc tm
               return $ VExtra $ VExtraTerm a tm') 
    ),
    -- Don't normalize applications of @SpecM@ and its arguments
    ("SpecM.SpecM",
     PrimStrict $ \ev -> PrimStrict $ \tp ->
      Prim $
      do ev_tp <- VTyTerm (mkSort 1) <$> scDataTypeApp sc "SpecM.EvType" []
         ev_tm <- readBackValueNoConfig "smtNormPrims (SpecM)" sc ev_tp ev
         tp_tm <- readBackValueNoConfig "smtNormPrims (SpecM)" sc (VSort $
                                                                   mkSort 0) tp
         ret_tm <- scGlobalApply sc "SpecM.SpecM" [ev_tm,tp_tm]
         return $ TValue $ VTyTerm (mkSort 0) ret_tm),
    ("SpecM.VoidEv", primGlobal sc "SpecM.VoidEv")
  ]

-- | A version of 'mrNormTerm' in the 'IO' monad, and which does not add any
-- debug output
smtNorm :: SharedContext -> Term -> IO Term
smtNorm sc t =
  scGetModuleMap sc >>= \modmap ->
  normalizeSharedTerm sc modmap (smtNormPrims sc) Map.empty Set.empty t

-- | Normalize a 'Term' using some Mr Solver specific primitives
mrNormTerm :: Term -> MRM t Term
mrNormTerm t =
  debugPrint 2 "Normalizing term:" >>
  debugPrettyInCtx 2 t >>
  liftSC1 smtNorm t

-- | Normalize an open term by wrapping it in lambdas, normalizing, and then
-- removing those lambdas
mrNormOpenTerm :: Term -> MRM t Term
mrNormOpenTerm body =
  do length_ctx <- mrVarCtxLength <$> mrUVars
     fun_term <- lambdaUVarsM body
     normed_fun <- mrNormTerm fun_term
     return (peel_lambdas length_ctx normed_fun)
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
mrProvableRaw :: Term -> MRM t Bool
mrProvableRaw prop_term =
  do sc <- mrSC
     prop <- liftSC1 termToProp prop_term
     unints <- Set.map ecVarIndex <$> getAllExtSet <$> liftSC1 propToTerm prop
     nenv <- liftIO (scGetNamingEnv sc)
     debugPrint 2 ("Calling SMT solver with proposition: " ++
                   prettyProp defaultPPOpts nenv prop)
     -- If there are any saw-core `error`s in the term, this will throw a
     -- Haskell error - in this case we want to just return False, not stop
     -- execution
     smt_res <-
       (Right <$> mrAskSMT unints (propToSequent prop))
         `catch` \case
           UserError msg -> return $ Left msg
           e -> throwM e
     case smt_res of
       Left msg ->
         debugPrint 2 ("SMT solver encountered a saw-core error term: " ++ msg)
           >> return False
       Right (stats, SolveUnknown) ->
          debugPrint 2 "SMT solver response: unknown" >>
          recordUsedSolver stats prop_term >> return False
       Right (stats, SolveCounterexample cex) ->
         debugPrint 2 "SMT solver response: not provable" >>
         debugPrint 3 ("Counterexample:" ++ concatMap (\(x,v) ->
           "\n - " ++ renderSawDoc defaultPPOpts (ppTerm defaultPPOpts (Unshared (FTermF (ExtCns x)))) ++
           " = " ++ renderSawDoc defaultPPOpts (ppFirstOrderValue defaultPPOpts v)) cex) >>
         recordUsedSolver stats prop_term >> return False
       Right (stats, SolveSuccess _) ->
         debugPrint 2 "SMT solver response: provable" >>
         recordUsedSolver stats prop_term >> return True

-- | Test if a Boolean term over the current uvars is provable given the current
-- assumptions
mrProvable :: Term -> MRM t Bool
mrProvable (asBool -> Just b) = return b
mrProvable bool_tm =
  do mrUVars >>= mrDebugPPPrefix 3 "mrProvable uvars:"
     assumps <- mrAssumptions
     prop <- liftSC2 scImplies assumps bool_tm >>= liftSC1 scEqTrue
     prop_inst <- mrSubstEVars prop >>= instantiateUVarsM instUVar
     mrNormTerm prop_inst >>= mrProvableRaw
  where -- | Given a UVar name and type, generate a 'Term' to be passed to
        -- SMT, with special cases for BVVec and pair types
        instUVar :: LocalName -> Term -> MRM t Term
        instUVar nm tp = mrDebugPPPrefix 3 "instUVar" (nm, tp) >>
                         liftSC1 scWhnf tp >>= \case
          (asNonBVVecVectorType -> Just (m, a)) ->
             liftSC1 smtNorm m >>= \m' -> case asBvToNat m' of
               -- For variables of type Vec of length which normalizes to
               -- a bvToNat term, recurse and wrap the result in genFromBVVec
               Just (n, len) -> do
                 tp' <- liftSC2 scVecType m' a
                 tm' <- instUVar nm tp'
                 mrGenFromBVVec n len a tm' "instUVar" m
               -- Otherwise for variables of type Vec, create a @Nat -> a@
               -- function as an ExtCns and apply genBVVec to it
               Nothing -> do
                 nat_tp <- liftSC0 scNatType
                 tp' <- liftSC3 scPi "_" nat_tp =<< liftTermLike 0 1 a
                 tm' <- instUVar nm tp'
                 liftSC2 scGlobalApply "CryptolM.genCryM" [m, a, tm']
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
-- * SMT-Friendly Representations
----------------------------------------------------------------------

-- | A representation of some subset of the elements of a type @tp@ as elements
-- of some other type @tp_r@. The idea is that the type @tp_r@ is easier to
-- represent in SMT solvers.
--
-- This is captured formally with a function @r@ from elements of the
-- representation type @tp_r@ to the elements of type @tp@ that they represent
-- along with an equivalence relation @eq_r@ on @tp_r@ such that @r@ is
-- injective when viewed as a morphism from @eq_r@ to the natural equivalence
-- relation @equiv@ of @tp@. In more detail, this means that @eq_r@ holds
-- between two inputs to @r@ iff @equiv@ holds between their outputs. Note that
-- an injective representation need not be surjective, meaning there could be
-- elements of @tp@ that it cannot represent.
data InjectiveRepr
     -- | The identity representation of @(tp,equiv)@ by itself. Only applies to
     -- non-vector types, as vectors should be represented by one of the vector
     -- representations.
  = InjReprId
    -- | A representation of a numeric type (@Num@, @Nat@, or @Vec n Bool@) by
    -- another numeric type defined as the composition of one or more injective
    -- numeric representations. NOTE: we do not expect numeric representations
    -- to occur inside other representations like those for pairs and vectors
  | InjReprNum [InjNumRepr]
    -- | A representation of the pair type @tp1 * tp2@ by @tp_r1 * tp_r2@ using
    -- representations of @tp1@ and @tp2@
  | InjReprPair InjectiveRepr InjectiveRepr
    -- | A representation of the vector type @Vec len tp@ by the functional type
    -- @tp_len -> tp_r@ from indices to elements of the representation type
    -- @tp_r@ of @tp@, given a representation of @tp@ by @tp_r@, where the index
    -- type @tp_len@ is determined by the 'VecLength'
  | InjReprVec VecLength Term InjectiveRepr
  deriving (Generic, Show)


-- | The length of a vector, given either as a bitvector 'Term' of a
-- statically-known bitwidth or as a natural number 'Term'
data VecLength = BVVecLen Natural Term | NatVecLen Term
               deriving (Generic, Show)

-- | A representation of a numeric type (@Num@, @Nat@, or @Vec n Bool@) by
-- another numeric type defined as an injective function
data InjNumRepr
     -- | The @TCNum@ constructor as a representation of @Num@ by @Nat@
  = InjNatToNum
    -- | The @bvToNat@ function as a representation of @Nat@ by @Vec n Bool@
  | InjBVToNat Natural
  deriving (Generic, Show)

deriving instance TermLike InjectiveRepr
deriving instance TermLike InjNumRepr
deriving instance TermLike VecLength

-- | Convert a natural number expression to a 'VecLength'
asVecLen :: Term -> VecLength
asVecLen (asBvToNatKnownW -> Just (n, len)) = BVVecLen n len
asVecLen n = NatVecLen n

-- | Convert a 'VecLength' to a natural number expression
vecLenToNat :: VecLength -> MRM t Term
vecLenToNat (BVVecLen n len) = liftSC2 scBvToNat n len
vecLenToNat (NatVecLen n) = return n

-- | Get the type of an index bounded by a 'VecLength'
vecLenIxType :: VecLength -> MRM t Term
vecLenIxType (BVVecLen n _) = liftSC1 scBitvector n
vecLenIxType (NatVecLen _) = liftSC0 scNatType

-- | Test if two vector lengths are equal, and if so, generalize them to use the
-- same index type as returned by 'vecLenIxType'
vecLenUnify :: VecLength -> VecLength -> MRM t (Maybe (VecLength, VecLength))
vecLenUnify vlen1@(BVVecLen n1 len1) vlen2@(BVVecLen n2 len2)
  | n1 == n2 =
    do lens_eq <- mrProveEq len1 len2
       if lens_eq then return (Just (vlen1,vlen2))
         else return Nothing
vecLenUnify (BVVecLen _ _) (BVVecLen _ _) = return Nothing
vecLenUnify len1 len2 =
  do n1 <- vecLenToNat len1
     n2 <- vecLenToNat len2
     mrProveEq n1 n2 >>= \case
       True -> return $ Just (NatVecLen n1, NatVecLen n2)
       False -> return Nothing

-- | Given a vector length, element type, vector of that length and type, and an
-- index of type 'vecLenIxType', index into the vector
vecLenIx :: VecLength -> Term -> Term -> Term -> MRM t Term
vecLenIx (BVVecLen n len) tp v ix =
  do n_tm <- liftSC1 scNat n
     mrApplyGlobal "Prelude.atBVVecNoPf" [n_tm, len, tp, v, ix]
vecLenIx (NatVecLen n) tp v ix = mrApplyGlobal "Prelude.at" [n, tp, v, ix]

-- | Smart constructor for pair representations, that combines a pair of
-- identity representations into an identity representation on the pair type
injReprPair :: InjectiveRepr -> InjectiveRepr -> InjectiveRepr
injReprPair InjReprId InjReprId = InjReprId
injReprPair repr1 repr2 = InjReprPair repr1 repr2

-- | Test if there is a non-identity numeric representation from the first to
-- the second type
findNumRepr :: Term -> Term -> Maybe InjectiveRepr
findNumRepr (asBitvectorType -> Just n) (asNumType -> Just ()) =
  Just $ InjReprNum [InjBVToNat n, InjNatToNum]
findNumRepr (asBitvectorType -> Just n) (asNatType -> Just ()) =
  Just $ InjReprNum [InjBVToNat n]
findNumRepr (asNatType -> Just ()) (asNumType -> Just ()) =
  Just $ InjReprNum [InjNatToNum]
findNumRepr _ _ = Nothing

-- | Compose two injective representations, assuming that they do compose, i.e.,
-- that the output type of the first equals the input type of the second
injReprComp :: InjectiveRepr -> InjectiveRepr -> InjectiveRepr
injReprComp InjReprId r = r
injReprComp r InjReprId = r
injReprComp (InjReprNum steps1) (InjReprNum steps2) =
  InjReprNum (steps1 ++ steps2)
injReprComp (InjReprPair r1_l r1_r) (InjReprPair r2_l r2_r) =
  InjReprPair (injReprComp r1_l r2_l) (injReprComp r1_r r2_r)
injReprComp r1 r2 =
  panic "injReprComp" ["Representations do not compose: " ++
                       show r1 ++ " and " ++ show r2]

-- | Apply a 'InjectiveRepr' to convert an element of the representation type
-- @tp_r@ to the type @tp@ that it represents
mrApplyRepr :: InjectiveRepr -> Term -> MRM t Term
mrApplyRepr InjReprId t = return t
mrApplyRepr (InjReprNum steps) t_top = foldM applyStep t_top steps where
  applyStep t InjNatToNum = liftSC2 scCtorApp "Cryptol.TCNum" [t]
  applyStep t (InjBVToNat n) = liftSC2 scBvToNat n t
mrApplyRepr (InjReprPair repr1 repr2) t =
  do t1 <- mrApplyRepr repr1 =<< doTermProj t TermProjLeft
     t2 <- mrApplyRepr repr2 =<< doTermProj t TermProjRight
     liftSC2 scPairValueReduced t1 t2
mrApplyRepr (InjReprVec (NatVecLen n) tp repr) t =
  do nat_tp <- liftSC0 scNatType
     f <- mrLambdaLift1 ("ix", nat_tp) repr $ \x repr' ->
       mrApplyRepr repr' =<< mrApply t x
     mrApplyGlobal "Prelude.gen" [n, tp, f]
mrApplyRepr (InjReprVec (BVVecLen n len) tp repr) t =
  do bv_tp <- liftSC1 scBitvector n
     f <- mrLambdaLift1 ("ix", bv_tp) repr $ \x repr' ->
       mrApplyRepr repr' =<< mrApply t x
     n_tm <- liftSC1 scNat n
     mrApplyGlobal "Prelude.genBVVecNoPf" [n_tm, len, tp, f]


newtype MaybeTerm b = MaybeTerm { unMaybeTerm :: If b Term () }

-- | Apply a monadic 'Term' operation to a 'MaybeTerm'
mapMaybeTermM :: Monad m => BoolRepr b -> (Term -> m Term) -> MaybeTerm b ->
                 m (MaybeTerm b)
mapMaybeTermM TrueRepr f (MaybeTerm t) = MaybeTerm <$> f t
mapMaybeTermM FalseRepr _ _ = return $ MaybeTerm ()

-- | Apply a binary monadic 'Term' operation to a 'MaybeTerm'
map2MaybeTermM :: Monad m => BoolRepr b -> (Term -> Term -> m Term) ->
                  MaybeTerm b -> MaybeTerm b -> m (MaybeTerm b)
map2MaybeTermM TrueRepr f (MaybeTerm t1) (MaybeTerm t2) = MaybeTerm <$> f t1 t2
map2MaybeTermM FalseRepr _ _ _ = return $ MaybeTerm ()

instance Given (BoolRepr b) => TermLike (MaybeTerm b) where
  liftTermLike n i = mapMaybeTermM given (liftTermLike n i)
  substTermLike n s = mapMaybeTermM given (substTermLike n s)

-- | Construct an injective representation for a type @tp@ and an optional term
-- @tm@ of that type, returning the representation type @tp_r@, the optional
-- term @tm_r@ that represents @tm@, and the representation itself. If there is
-- a choice, choose the representation that works best for SMT solvers.
mkInjRepr :: BoolRepr b -> Term -> MaybeTerm b ->
             MRM t (Term, MaybeTerm b, InjectiveRepr)
mkInjRepr TrueRepr _ (MaybeTerm (asNum -> Just (Left t))) =
  do nat_tp <- liftSC0 scNatType
     (tp_r, tm_r, r) <- mkInjRepr TrueRepr nat_tp (MaybeTerm t)
     return (tp_r, tm_r, injReprComp r (InjReprNum [InjNatToNum]))
mkInjRepr TrueRepr _ (MaybeTerm (asBvToNatKnownW -> Just (n, t))) =
  do bv_tp <- liftSC1 scBitvector n
     return (bv_tp, MaybeTerm t, InjReprNum [InjBVToNat n])
mkInjRepr b (asPairType -> Just (tp1, tp2)) t =
  do tm1 <- mapMaybeTermM b (flip doTermProj TermProjLeft) t
     tm2 <- mapMaybeTermM b (flip doTermProj TermProjRight) t
     (tp_r1, tm_r1, r1) <- mkInjRepr b tp1 tm1
     (tp_r2, tm_r2, r2) <- mkInjRepr b tp2 tm2
     tp_r <- liftSC2 scPairType tp_r1 tp_r2
     tm_r <- map2MaybeTermM b (liftSC2 scPairValueReduced) tm_r1 tm_r2
     return (tp_r, tm_r, InjReprPair r1 r2)

mkInjRepr b (asVectorType -> Just (len, tp@(asBoolType -> Nothing))) tm =
  do let vlen = asVecLen len
     ix_tp <- vecLenIxType vlen
     -- NOTE: these return values from mkInjRepr all have ix free
     (tp_r', tm_r', r') <-
       give b $
       withUVarLift "ix" (Type ix_tp) (vlen,tp,tm) $ \ix (vlen',tp',tm') ->
       do tm_elem <-
            mapMaybeTermM b (\tm'' -> vecLenIx vlen' tp' tm'' ix) tm'
          mkInjRepr b tp' tm_elem
     -- r' should not have ix free, so it should be ok to substitute an error
     -- term for ix...
     r <- substTermLike 0 [error
                           "mkInjRepr: unexpected free ix variable in repr"] r'
     tp_r <- liftSC3 scPi "ix" ix_tp tp_r'
     tm_r <- mapMaybeTermM b (liftSC3 scLambda "ix" ix_tp) tm_r'
     return (tp_r, tm_r, InjReprVec vlen tp r)

mkInjRepr _ tp tm = return (tp, tm, InjReprId)


-- | Specialization of 'mkInjRepr' with no element of the represented type
mkInjReprType :: Term -> MRM t (Term, InjectiveRepr)
mkInjReprType tp =
  (\(tp_r,_,repr) -> (tp_r,repr)) <$> mkInjRepr FalseRepr tp (MaybeTerm ())

-- | Specialization of 'mkInjRepr' with an element of the represented type
mkInjReprTerm :: Term -> Term -> MRM t (Term, Term, InjectiveRepr)
mkInjReprTerm tp trm =
  (\(tp_r, tm, repr) -> (tp_r, unMaybeTerm tm, repr)) <$>
  mkInjRepr TrueRepr tp (MaybeTerm trm)


-- | Given two representations @r1@ and @r2@ along with their representation
-- types @tp_r1@ and @tp_r2, try to unify their representation types, yielding
-- new versions of those representations. That is, try to find a common type
-- @tp_r@ and representations @r1'@ and @r2'@ such that the following picture
-- holds:
--
-- >   tp1      tp2
-- >    ^        ^
-- > r1 |        | r2
-- >  tp_r1    tp_r2
-- >    ^        ^
-- > r1' \      / r2'
-- >      \    /
-- >       tp_r
--
injUnifyReprTypes :: Term -> InjectiveRepr -> Term -> InjectiveRepr ->
                     MaybeT (MRM t) (Term, InjectiveRepr, InjectiveRepr)

-- If there is a numeric coercion from one side to the other, use it to unify
-- the two input representations
injUnifyReprTypes tp1 r1 tp2 r2
  | Just r2' <- findNumRepr tp1 tp2
  = return (tp1, r1, injReprComp r2' r2)
injUnifyReprTypes tp1 r1 tp2 r2
  | Just r1' <- findNumRepr tp2 tp1
  = return (tp2, injReprComp r1' r1, r2)

-- If both representations are the identity, make sure the repr types are equal
injUnifyReprTypes tp1 InjReprId tp2 InjReprId =
  do tps_eq <- lift $ mrConvertible tp1 tp2
     if tps_eq then return (tp1, InjReprId, InjReprId)
       else mzero

-- For pair representations, unify the two sides, treating an identity
-- representation as a pair of identity representations
injUnifyReprTypes tp1 (InjReprPair r1l r1r) tp2 (InjReprPair r2l r2r)
  | Just (tp1l, tp1r) <- asPairType tp1
  , Just (tp2l, tp2r) <- asPairType tp2 =
    do (tp_r_l, r1l', r2l') <- injUnifyReprTypes tp1l r1l tp2l r2l
       (tp_r_r, r1r', r2r') <- injUnifyReprTypes tp1r r1r tp2r r2r
       tp_r <- lift $ liftSC2 scPairType tp_r_l tp_r_r
       return (tp_r, InjReprPair r1l' r1r', InjReprPair r2l' r2r')
injUnifyReprTypes tp1 InjReprId tp2 r2
  | isJust (asPairType tp1)
  = injUnifyReprTypes tp1 (InjReprPair InjReprId InjReprId) tp2 r2
injUnifyReprTypes tp1 r1 tp2 InjReprId
  | isJust (asPairType tp2)
  = injUnifyReprTypes tp1 r1 tp2 (InjReprPair InjReprId InjReprId)

-- For vector types, check that the lengths are equal and unify the element
-- representations. Note that if either side uses a natural number length
-- instead of a bitvector length, both sides will need to, since we don't
-- currently have representation that can cast from a bitvector length to an
-- equal natural number length
injUnifyReprTypes _ (InjReprVec len1 tp1 r1) _ (InjReprVec len2 tp2 r2) =
  do (len1', len2') <- MaybeT $ vecLenUnify len1 len2
     ix_tp <- lift $ vecLenIxType len1'
     (tp_r, r1', r2') <- injUnifyReprTypes tp1 r1 tp2 r2
     tp_r_fun <- lift $ mrArrowType "ix" ix_tp tp_r
     return (tp_r_fun, InjReprVec len1' tp1 r1', InjReprVec len2' tp2 r2')

injUnifyReprTypes _ _ _ _ = mzero


-- | Given two types @tp1@ and @tp2@, try to find a common type @tp@ that
-- injectively represents both of them. Pictorially, the result looks like this:
-- 
-- >  tp1      tp2
-- >   ^        ^
-- > r1 \      / r2
-- >     \    /
-- >       tp
--
-- where @r1@ and @r2@ are injective representations. The representations should
-- be maximal, meaning that they represent as much of @tp1@ and @tp2@ as
-- possible. If there is such a @tp@, return it along with the representations
-- @r1@ and @r2@. Otherwise, return 'Nothing', meaning the unification failed.
injUnifyTypes :: Term -> Term ->
                 MRM t (Maybe (Term, InjectiveRepr, InjectiveRepr))
injUnifyTypes tp1 tp2 =
  do (tp_r1, r1) <- mkInjReprType tp1
     (tp_r2, r2) <- mkInjReprType tp2
     runMaybeT $ injUnifyReprTypes tp_r1 r1 tp_r2 r2


-- | Use one injective representations @r1@ to restrict the domain of another
-- injective representation @r2@, yielding an injective representation with the
-- same representation type as @r1@ and the same type being represented as @r2@.
-- Pictorially this looks like this:
--
-- >  tp1           tp2
-- >   ^            ^
-- >    \          / r2
-- > r1  \        /
-- >      \    tpr2
-- >       \    ^
-- >        \  / r2''
-- >        tpr1
--
-- The return value is the composition of @r2''@ and @r2@. It is an error if
-- this diagram does not exist.
injReprRestrict :: Term -> InjectiveRepr -> Term -> InjectiveRepr ->
                   MRM t InjectiveRepr

-- If tp1 and tp2 are numeric types with a representation from tp1 to tp2, we
-- can pre-compose that representation with r2
injReprRestrict tp1 _ tp2 r2
  | Just r2'' <- findNumRepr tp1 tp2
  = return $ injReprComp r2'' r2

-- In all other cases, the only repr that pre-composes with r2 is the identity
-- repr, so we just return r2
injReprRestrict _ _ _ r2 = return r2


-- | Take in a type @tp_r1@, a term @tm1@ of type @tp_r1@, an injective
-- representation @r1@ with @tp_r1@ as its representation type, and a type @tp2@
-- with an element @tm2@, and try to find a type @tp_r'@ and a term @tm'@ of
-- type @tp_r'@ that represents both @r1 tm1@ and @tm2@ using representations
-- @r1'@ and @r2'@, repsectively. That is, @r1'@ should represent @tp1@ and
-- @r2'@ should represent @tp2@, both with the same representation type @tp_r'@,
-- and should satisfy
--
-- > r1' tm' = r1 tm1    and    r2' tm' = tm2
--
-- In pictures the result should look like this:
--
-- >    r1 tm1      tm2::tp2
-- >      ^            ^
-- >   r1 |           /
-- >      |          /
-- >  tm1::tp_r1    / r2'
-- >       ^       /
-- >   r1'' \     /
-- >         \   /
-- >       tm'::tp_r'
--
-- where @r1'@ is the composition of @r1''@ and @r1@.
injUnifyRepr :: Term -> Term -> InjectiveRepr -> Term -> Term ->
                MRM t (Maybe (Term, Term, InjectiveRepr, InjectiveRepr))

-- If there is a numeric repr r2 from tp_r1 to tp2, then that's our r2',
-- assuming that r2 tm1 = tm2
injUnifyRepr tp_r1 tm1 r1 tp2 tm2
  | Just r2 <- findNumRepr tp_r1 tp2 =
    do r2_tm1 <- mrApplyRepr r2 tm1
       eq_p <- mrProveEq r2_tm1 tm2
       if eq_p then
         return (Just (tp_r1, tm1, r1, r2))
         else return Nothing

-- If there is a numeric repr r1'' from tp2 to tp_r1, then we pre-compose that
-- with r1 and use the identity for r2', assuming r1'' tm2 = tm1
injUnifyRepr tp_r1 tm1 r1 tp2 tm2
  | Just r1'' <- findNumRepr tp2 tp_r1 =
    do r1_tm2 <- mrApplyRepr r1'' tm2
       eq_p <- mrProveEq tm1 r1_tm2
       if eq_p then
         return (Just (tp2, tm2, injReprComp r1'' r1, InjReprId))
         else return Nothing

-- Otherwise, build a representation r2 for tm2, check that its representation
-- type equals tp_r1, and check that r1 tm1 is related to tm2
injUnifyRepr tp_r1 tm1 r1 tp2 tm2 =
  do (tp_r2, _, r2) <- mkInjReprTerm tp2 tm2
     tps_eq <- mrConvertible tp_r1 tp_r2
     if not tps_eq then return Nothing else
       do r1_tm1 <- mrApplyRepr r1 tm1
          rel <- mrProveRel True r1_tm1 tm2
          if rel then return (Just (tp_r1, tm1, r1, r2)) else
            return Nothing


----------------------------------------------------------------------
-- * Checking Equality with SMT
----------------------------------------------------------------------

-- | Build a Boolean 'Term' stating that two 'Term's are equal. This is like
-- 'scEq' except that it works on open terms.
mrEq :: Term -> Term -> MRM t Term
mrEq t1 t2 = mrTypeOf t1 >>= \tp -> mrEq' tp t1 t2

-- | Build a Boolean 'Term' stating that the second and third 'Term' arguments
-- are equal, where the first 'Term' gives their type (which we assume is the
-- same for both). This is like 'scEq' except that it works on open terms.
mrEq' :: Term -> Term -> Term -> MRM t Term
-- FIXME: For this Nat case, the definition of 'equalNat' in @Prims.hs@ means
-- that if both sides do not have immediately clear bit-widths (e.g. either
-- side is is an application of @mulNat@) this will 'error'...
mrEq' (asNatType -> Just _) t1 t2 = liftSC2 scEqualNat t1 t2
mrEq' (asBoolType -> Just _) t1 t2 = liftSC2 scBoolEq t1 t2
mrEq' (asIntegerType -> Just _) t1 t2 = liftSC2 scIntEq t1 t2
mrEq' (asSymBVType -> Just n) t1 t2 = liftSC3 scBvEq n t1 t2
mrEq' (asNumType -> Just ()) t1 t2 =
  (,) <$> liftSC1 scWhnf t1 <*> liftSC1 scWhnf t2 >>= \case
    (asNum -> Just (Left t1'), asNum -> Just (Left t2')) ->
      liftSC0 scNatType >>= \nat_tp -> mrEq' nat_tp t1' t2'
    _ -> error "mrEq': Num terms do not normalize to TCNum constructors"
mrEq' _ _ _ = error "mrEq': unsupported type"

-- | A 'Term' in an extended context of universal variables, which are listed
-- "outside in", meaning the highest deBruijn index comes first
data TermInCtx = TermInCtx [(LocalName,Term)] Term

-- | Lift a binary operation on 'Term's to one on 'TermInCtx's
liftTermInCtx2 :: (SharedContext -> Term -> Term -> IO Term) ->
                   TermInCtx -> TermInCtx -> MRM t TermInCtx
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

-- | Run an 'MRM t' computation in the context of a 'TermInCtx', passing in the
-- 'Term'
withTermInCtx :: TermInCtx -> (Term -> MRM t a) -> MRM t a
withTermInCtx (TermInCtx [] tm) f = f tm
withTermInCtx (TermInCtx ((nm,tp):ctx) tm) f =
  withUVar nm (Type tp) $ const $ withTermInCtx (TermInCtx ctx tm) f

-- | A "simple" strategy for proving equality between two terms, which we assume
-- are of the same type, which builds an equality proposition by applying the
-- supplied function to both sides and passes this proposition to an SMT solver.
mrProveEqSimple :: (Term -> Term -> MRM t Term) -> Term -> Term ->
                   MRM t TermInCtx
-- NOTE: The use of mrSubstEVars instead of mrSubstEVarsStrict means that we
-- allow evars in the terms we send to the SMT solver, but we treat them as
-- uvars.
mrProveEqSimple eqf t1 t2 =
  do t1' <- mrSubstEVars t1
     t2' <- mrSubstEVars t2
     TermInCtx [] <$> eqf t1' t2'

-- | Prove that two terms are equal, instantiating evars if necessary,
-- returning true on success - the same as @mrProveRel False@
mrProveEq :: Term -> Term -> MRM t Bool
mrProveEq = mrProveRel False

-- | Prove that two terms are equal, instantiating evars if necessary, or
-- throwing an error if this is not possible - the same as
-- @mrAssertProveRel False@
mrAssertProveEq :: Term -> Term -> MRM t ()
mrAssertProveEq = mrAssertProveRel False

-- | Prove that two terms are related, heterogeneously iff the first argument
-- is true, instantiating evars if necessary, returning true on success
mrProveRel :: Bool -> Term -> Term -> MRM t Bool
mrProveRel het t1 t2 =
  do let nm = if het then "mrProveRel" else "mrProveEq"
     mrDebugPPPrefixSep 2 nm t1 (if het then "~=" else "==") t2
     tp1 <- mrTypeOf t1 >>= mrSubstEVars
     tp2 <- mrTypeOf t2 >>= mrSubstEVars
     tps_eq <- mrConvertible tp1 tp2
     if not het && not tps_eq
     then do mrDebugPPPrefixSep 2 (nm ++ ": Failure, types not equal:")
                                  tp1 "and" tp2
             return False
     else do cond_in_ctx <- mrProveRelH het tp1 tp2 t1 t2
             res <- withTermInCtx cond_in_ctx mrProvable
             debugPrint 2 $ nm ++ ": " ++ if res then "Success" else "Failure"
             return res

-- | Prove that two terms are related, heterogeneously iff the first argument,
-- is true, instantiating evars if necessary, or throwing an error if this is
-- not possible
mrAssertProveRel :: Bool -> Term -> Term -> MRM t ()
mrAssertProveRel het t1 t2 =
  do success <- mrProveRel het t1 t2
     if success then return () else
       throwMRFailure (TermsNotRel het t1 t2)

-- | The main workhorse for 'mrProveEq' and 'mrProveRel'. Build a Boolean term
-- over zero or more universally quantified variables expressing that the fourth
-- and fifth arguments are related, heterogeneously iff the first argument is
-- true, whose types are given by the second and third arguments, respectively
mrProveRelH :: Bool -> Term -> Term -> Term -> Term -> MRM t TermInCtx
mrProveRelH het tp1 tp2 t1 t2 =
  do varmap <- mrVars
     tp1' <- liftSC1 scWhnf tp1
     tp2' <- liftSC1 scWhnf tp2
     mrProveRelH' varmap het tp1' tp2' t1 t2

-- | The body of 'mrProveRelH'
-- NOTE: Don't call this function recursively, call 'mrProveRelH'
mrProveRelH' :: Map MRVar MRVarInfo -> Bool ->
                Term -> Term -> Term -> Term -> MRM t TermInCtx

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
mrProveRelH' _ _ tp1@(asSymBVType -> Just n1) tp2@(asSymBVType -> Just n2) t1 t2 =
  do ns_are_eq <- mrConvertible n1 n2
     if ns_are_eq then return () else
       throwMRFailure (TypesNotEq (Type tp1) (Type tp2))
     mrProveEqSimple (liftSC3 scBvEq n1) t1 t2
mrProveRelH' _ _ (asBoolType -> Just _) (asBoolType -> Just _) t1 t2 =
  mrProveEqSimple (liftSC2 scBoolEq) t1 t2
mrProveRelH' _ _ (asIntegerType -> Just _) (asIntegerType -> Just _) t1 t2 =
  mrProveEqSimple (liftSC2 scIntEq) t1 t2

-- If one side is a finite Num, treat it as a natural number
mrProveRelH' _ het _ tp2 (asNum -> Just (Left t1)) t2 =
  liftSC0 scNatType >>= \nat_tp -> mrProveRelH het nat_tp tp2 t1 t2
mrProveRelH' _ het tp1 _ t1 (asNum -> Just (Left t2)) =
  liftSC0 scNatType >>= \nat_tp -> mrProveRelH het tp1 nat_tp t1 t2

-- If one side is a bvToNat term, treat it as a bitvector
mrProveRelH' _ het _ tp2 (asBvToNat -> Just (n, t1)) t2 =
  mrBvType n >>= \bv_tp -> mrProveRelH het bv_tp tp2 t1 t2
mrProveRelH' _ het tp1 _ t1 (asBvToNat -> Just (n, t2)) =
  mrBvType n >>= \bv_tp -> mrProveRelH het tp1 bv_tp t1 t2

-- FIXME HERE NOWNOW: generalize Vec = Vec relation

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
  withUVarLift "ix" (Type ix_tp) (n1,(len1,(tpA1,(tpA2,(t1,t2))))) $
  \ix (n1',(len1',(tpA1',(tpA2',(t1',t2'))))) ->
  do ix_bound <- liftSC2 scGlobalApply "Prelude.bvult" [n1', ix, len1']
     pf_tp <- liftSC1 scEqTrue ix_bound
     pf <- mrErrorTerm pf_tp "FIXME" -- FIXME replace this with the below?
     -- pf <- liftSC2 scGlobalApply "Prelude.unsafeAssertBVULt" [n1', ix, len1']
     t1_prj <- liftSC2 scGlobalApply "Prelude.atBVVec" [n1', len1', tpA1',
                                                        t1', ix, pf]
     t2_prj <- liftSC2 scGlobalApply "Prelude.atBVVec" [n1', len1', tpA2',
                                                        t2', ix, pf]
     cond <- mrProveRelH het tpA1' tpA2' t1_prj t2_prj
     extTermInCtx [("ix",ix_tp)] <$>
       liftTermInCtx2 scImplies (TermInCtx [] ix_bound) cond

-- For pair types, prove both the left and right projections are related
mrProveRelH' _ het (asPairType -> Just (tpL1, tpR1))
                   (asPairType -> Just (tpL2, tpR2)) t1 t2 =
  do t1L <- liftSC1 scPairLeft t1
     t2L <- liftSC1 scPairLeft t2
     t1R <- liftSC1 scPairRight t1
     t2R <- liftSC1 scPairRight t2
     condL <- mrProveRelH het tpL1 tpL2 t1L t2L
     condR <- mrProveRelH het tpR1 tpR2 t1R t2R
     liftTermInCtx2 scAnd condL condR

mrProveRelH' _ _ tp1 tp2 t1 t2 =
  do success <- mrConvertible t1 t2
     if success then return () else
       do tps_eq <- mrConvertible tp1 tp2
          if not tps_eq
            then mrDebugPPPrefixSep 2 "mrProveRelH' could not match types: " tp1 "and" tp2 >>
                 mrDebugPPPrefixSep 2 "and could not prove convertible: " t1 "and" t2
            else mrDebugPPPrefixSep 2 "mrProveEq could not prove convertible: " t1 "and" t2
     TermInCtx [] <$> liftSC1 scBool success
