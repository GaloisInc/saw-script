{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}

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
import Control.Monad.Trans.Maybe
import Data.Foldable (foldrM, foldlM)
import GHC.Generics

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
import Verifier.SAW.Module
import Verifier.SAW.Prelude.Constants
import Verifier.SAW.FiniteValue

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
primGenBVVecFilter sc n (asGenCryMTerm -> Just (asBvToNat -> Just (asNat -> Just n', _), _, f)) | n == n' = lift $
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

-- | Implementations of primitives for normalizing Mr Solver terms
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
    -- Don't normalize applications of @CompM@
    ("Prelude.CompM",
     PrimFilterFun "CompM" (\case
                               TValue tv -> return tv
                               _ -> mzero) $ \tv ->
      Prim (do tv_trm <- readBackTValueNoConfig "smtNormPrims (CompM)" sc tv
               TValue <$> VTyTerm (mkSort 0) <$>
                 scGlobalApply sc "Prelude.CompM" [tv_trm]))
  ]

-- | A version of 'mrNormTerm' in the 'IO' monad, and which does not add any
-- debug output
smtNorm :: SharedContext -> Term -> IO Term
smtNorm sc t =
  scGetModuleMap sc >>= \modmap ->
  normalizeSharedTerm sc modmap (smtNormPrims sc) Map.empty Set.empty t

-- | Normalize a 'Term' using some Mr Solver specific primitives
mrNormTerm :: Term -> MRM Term
mrNormTerm t =
  debugPrint 2 "Normalizing term:" >>
  debugPrettyInCtx 2 t >>
  liftSC1 smtNorm t

-- | Normalize an open term by wrapping it in lambdas, normalizing, and then
-- removing those lambdas
mrNormOpenTerm :: Term -> MRM Term
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
       Right (Just cex, _) ->
         debugPrint 2 "SMT solver response: not provable" >>
         debugPrint 3 ("Counterexample:" ++ concatMap (\(x,v) ->
           "\n - " ++ renderSawDoc defaultPPOpts (ppTerm defaultPPOpts (Unshared (FTermF (ExtCns x)))) ++
           " = " ++ renderSawDoc defaultPPOpts (ppFirstOrderValue defaultPPOpts v)) cex) >>
         return False
       Right (Nothing, _) ->
         debugPrint 2 "SMT solver response: provable" >> return True

-- | Test if a Boolean term over the current uvars is provable given the current
-- assumptions
mrProvable :: Term -> MRM Bool
mrProvable (asBool -> Just b) = return b
mrProvable bool_tm =
  do mrUVars >>= mrDebugPPPrefix 3 "mrProvable uvars:"
     assumps <- mrAssumptions
     prop <- liftSC2 scImplies assumps bool_tm >>= liftSC1 scEqTrue
     prop_inst <- mrSubstEVars prop >>= instantiateUVarsM instUVar
     mrNormTerm prop_inst >>= mrProvableRaw
  where -- | Given a UVar name and type, generate a 'Term' to be passed to
        -- SMT, with special cases for BVVec and pair types
        instUVar :: LocalName -> Term -> MRM Term
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
-- * Finding injective conversions
----------------------------------------------------------------------

-- | An injection from @Nat@ to @Num@ ('NatToNum'), @Vec n Bool@ to @Nat@
-- ('BVToNat'), @BVVec n len a@ to @Vec m a@ ('BVVecToVec'), from one pair
-- type to another ('PairToPair'), or any composition of these using '(<>)'
-- (including the composition of none of them, the identity 'NoConv'). This
-- type is primarily used as one of the returns of 'findInjConvs'.
-- NOTE: Do not use the constructors of this type or 'SingleInjConversion'
-- directly, instead use the pattern synonyms mentioned above and '(<>)' to
-- create and compose 'InjConversion's. This ensures elements of this type
-- are always in a normal form w.r.t. 'PairToPair' injections.
newtype InjConversion = ConvComp [SingleInjConversion]
                      deriving (Generic, Show)

-- | Used in the implementation of 'InjConversion'.
-- NOTE: Do not use the constructors of this type or 'InjConversion'
-- directly, instead use the pattern synonyms mentioned in the documentation of
-- 'InjConversion' and '(<>)' to create and compose 'InjConversion's. This
-- ensures elements of this type are always in a normal form w.r.t.
-- 'PairToPair' injections.
data SingleInjConversion = SingleNatToNum
                         | SingleBVToNat Natural
                         | SingleBVVecToVec Term Term Term Term
                         | SinglePairToPair InjConversion InjConversion
                         deriving (Generic, Show)

deriving instance TermLike SingleInjConversion
deriving instance TermLike InjConversion

-- | The identity 'InjConversion'
pattern NoConv :: InjConversion
pattern NoConv = ConvComp []

-- | The injective conversion from @Nat@ to @Num@
pattern NatToNum :: InjConversion
pattern NatToNum = ConvComp [SingleNatToNum]

-- | The injective conversion from @Vec n Bool@ to @Nat@ for a given @n@
pattern BVToNat :: Natural -> InjConversion
pattern BVToNat n = ConvComp [SingleBVToNat n]

-- | The injective conversion from @BVVec n len a@ to @Vec m a@ for given
-- @n@, @len@, @a@, and @m@ (in that order), assuming @m >= bvToNat n len@
pattern BVVecToVec :: Term -> Term -> Term -> Term -> InjConversion
pattern BVVecToVec n len a m = ConvComp [SingleBVVecToVec n len a m]

-- | An injective conversion from one pair type to another, using the given
-- 'InjConversion's for the first and second projections, respectively
pattern PairToPair :: InjConversion -> InjConversion -> InjConversion
pattern PairToPair c1 c2 <- ConvComp [SinglePairToPair c1 c2]
  where PairToPair NoConv NoConv = NoConv
        PairToPair c1 c2 = ConvComp [SinglePairToPair c1 c2]

instance Semigroup InjConversion where
  (ConvComp cs1) <> (ConvComp cs2) = ConvComp (cbnPairs $ cs1 ++ cs2)
    where cbnPairs :: [SingleInjConversion] -> [SingleInjConversion]
          cbnPairs (SinglePairToPair cL1 cR1 : SinglePairToPair cL2 cR2 : cs) =
            cbnPairs (SinglePairToPair (cL1 <> cL2) (cR1 <> cR2) : cs)
          cbnPairs (s : cs) = s : cbnPairs cs
          cbnPairs [] = []

instance Monoid InjConversion where
  mempty = NoConv

-- | Return 'True' iff the given 'InjConversion' is not 'NoConv'
nonTrivialConv :: InjConversion -> Bool
nonTrivialConv (ConvComp cs) = not (null cs)

-- | Return 'True' iff the given 'InjConversion's are convertible, i.e. if
-- the two injective conversions are the compositions of the same constructors,
-- and the arguments to those constructors are convertible via 'mrConvertible'
mrConvsConvertible :: InjConversion -> InjConversion -> MRM Bool
mrConvsConvertible (ConvComp cs1) (ConvComp cs2) =
  if length cs1 /= length cs2 then return False
  else and <$> zipWithM mrSingleConvsConvertible cs1 cs2

-- | Used in the definition of 'mrConvsConvertible'
mrSingleConvsConvertible :: SingleInjConversion -> SingleInjConversion -> MRM Bool
mrSingleConvsConvertible SingleNatToNum SingleNatToNum = return True
mrSingleConvsConvertible (SingleBVToNat n1) (SingleBVToNat n2) = return $ n1 == n2
mrSingleConvsConvertible (SingleBVVecToVec n1 len1 a1 m1)
                         (SingleBVVecToVec n2 len2 a2 m2) =
  do ns_are_eq <- mrConvertible n1 n2
     lens_are_eq <- mrConvertible len1 len2
     as_are_eq <- mrConvertible a1 a2
     ms_are_eq <- mrConvertible m1 m2
     return $ ns_are_eq && lens_are_eq && as_are_eq && ms_are_eq
mrSingleConvsConvertible (SinglePairToPair cL1 cR1)
                         (SinglePairToPair cL2 cR2) =
  do cLs_are_eq <- mrConvsConvertible cL1 cL2
     cRs_are_eq <- mrConvsConvertible cR1 cR2
     return $ cLs_are_eq && cRs_are_eq
mrSingleConvsConvertible _ _ = return False

-- | Apply the given 'InjConversion' to the given term, where compositions
-- @c1 <> c2 <> ... <> cn@ are applied from right to left as in function
-- composition (i.e. @mrApplyConv (c1 <> c2 <> ... <> cn) t@ is equivalent to
-- @mrApplyConv c1 (mrApplyConv c2 (... mrApplyConv cn t ...))@)
mrApplyConv :: InjConversion -> Term -> MRM Term
mrApplyConv (ConvComp cs) = flip (foldrM go) cs
  where go :: SingleInjConversion -> Term -> MRM Term
        go SingleNatToNum t = liftSC2 scCtorApp "Cryptol.TCNum" [t]
        go (SingleBVToNat n) t = liftSC2 scBvToNat n t
        go (SingleBVVecToVec n len a m) t = mrGenFromBVVec n len a t "mrApplyConv" m
        go (SinglePairToPair c1 c2) t =
          do t1 <- mrApplyConv c1 =<< doTermProj t TermProjLeft
             t2 <- mrApplyConv c2 =<< doTermProj t TermProjRight
             liftSC2 scPairValueReduced t1 t2

-- | Try to apply the inverse of the given the conversion to the given term,
-- raising an error if this is not possible - see also 'mrApplyConv'
mrApplyInvConv :: InjConversion -> Term -> MRM Term
mrApplyInvConv (ConvComp cs) = flip (foldlM go) cs
  where go :: Term -> SingleInjConversion -> MRM Term
        go t SingleNatToNum = case asNum t of
          Just (Left t') -> return t'
          _ -> error "mrApplyInvConv: Num term does not normalize to TCNum constructor"
        go t (SingleBVToNat n) = case asBvToNat t of
          Just (asNat -> Just n', t') | n == n' -> return t'
          _ -> do n_tm <- liftSC1 scNat n
                  liftSC2 scGlobalApply "Prelude.bvNat" [n_tm, t]
        go t c@(SingleBVVecToVec n len a m) = case asGenFromBVVecTerm t of
          Just (n', len', a', t', _, m') ->
            do eq <- mrSingleConvsConvertible c (SingleBVVecToVec n' len' a' m')
               if eq then return t'
               else mrGenBVVecFromVec m a t "mrApplyInvConv" n len
          _ -> mrGenBVVecFromVec m a t "mrApplyInvConv" n len
        go t (SinglePairToPair c1 c2) =
          do t1 <- mrApplyInvConv c1 =<< doTermProj t TermProjLeft
             t2 <- mrApplyInvConv c2 =<< doTermProj t TermProjRight
             liftSC2 scPairValueReduced t1 t2

-- | If the given term can be expressed as @mrApplyInvConv c t@ for some @c@
-- and @t@, return @c@ - otherwise return @NoConv@
mrConvOfTerm :: Term -> InjConversion
mrConvOfTerm (asNum -> Just (Left t')) =
  NatToNum <> mrConvOfTerm t'
mrConvOfTerm (asBvToNat -> Just (asNat -> Just n, t')) =
  BVToNat n <> mrConvOfTerm t'
mrConvOfTerm (asGenFromBVVecTerm -> Just (n, len, a, v, _, m)) =
  BVVecToVec n len a m <> mrConvOfTerm v
mrConvOfTerm (asPairValue -> Just (t1, t2)) =
  PairToPair (mrConvOfTerm t1) (mrConvOfTerm t2)
mrConvOfTerm _ = NoConv

-- | For two types @tp1@ and @tp2@, and optionally two terms @t1 :: tp1@ and
-- @t2 :: tp2@, tries to find a type @tp@ and 'InjConversion's @c1@ and @c2@
-- such that @c1@ is an injective conversion from @tp@ to @tp1@ and @c2@ is a
-- injective conversion from @tp@ to @tp2@. This tries to make @c1@ and @c2@
-- as large as possible, using information from the given terms (i.e. using
-- 'mrConvOfTerm') where possible. In pictorial form, this function finds
-- a @tp@, @c1@, and @c2@ which satisfy the following diagram:
-- 
-- >  tp1      tp2
-- >   ^        ^
-- > c1 \      / c2
-- >     \    /
-- >       tp
--
-- Since adding a 'NatToNum' conversion does not require any choice (i.e.
-- unlike 'BVToNat', which requires choosing a bit width), if either @tp1@ or
-- @tp2@ is @Num@, a 'NatToNum' conversion will be included on the respective
-- side. Another subtlety worth noting is the difference between returning
-- @Just (tp, NoConv, NoConv)@ and @Nothing@ - the former indicates that the
-- types @tp1@ and @tp2@ are convertible, but the latter indicates that no
-- 'InjConversion' could be found.
findInjConvs :: Term -> Maybe Term -> Term -> Maybe Term ->
                MRM (Maybe (Term, InjConversion, InjConversion))
-- always add 'NatToNum' conversions
findInjConvs (asDataType -> Just (primName -> "Cryptol.Num", _)) t1 tp2 t2 =
  do tp1' <- liftSC0 scNatType
     t1' <- mapM (mrApplyInvConv NatToNum) t1
     mb_cs <- findInjConvs tp1' t1' tp2 t2
     return $ fmap (\(tp, c1, c2) -> (tp, NatToNum <> c1, c2)) mb_cs
findInjConvs tp1 t1 (asDataType -> Just (primName -> "Cryptol.Num", _)) t2 =
  do tp2' <- liftSC0 scNatType
     t2' <- mapM (mrApplyInvConv NatToNum) t2
     mb_cs <- findInjConvs tp1 t1 tp2' t2'
     return $ fmap (\(tp, c1, c2) -> (tp, c1, NatToNum <> c2)) mb_cs
-- add a 'BVToNat' conversion if the (optional) given term has a 'BVToNat'
-- conversion
findInjConvs (asNatType -> Just ())
             (Just (asBvToNat -> Just (asNat -> Just n, t1'))) tp2 t2 =
  do tp1' <- liftSC1 scBitvector n
     mb_cs <- findInjConvs tp1' (Just t1') tp2 t2
     return $ fmap (\(tp, c1, c2) -> (tp, BVToNat n <> c1, c2)) mb_cs
findInjConvs tp1 t1 (asNatType -> Just ())
                    (Just (asBvToNat -> Just (asNat -> Just n, t2'))) =
  do tp2' <- liftSC1 scBitvector n
     mb_cs <- findInjConvs tp1 t1 tp2' (Just t2')
     return $ fmap (\(tp, c1, c2) -> (tp, c1, BVToNat n <> c2)) mb_cs
-- add a 'BVToNat' conversion we have a BV on the other side, using the
-- bit-width from the other side
findInjConvs (asNatType -> Just ()) _ (asBitvectorType -> Just n) _ =
  do bv_tp <- liftSC1 scBitvector n 
     return $ Just (bv_tp, BVToNat n, NoConv)
findInjConvs (asBitvectorType -> Just n) _ (asNatType -> Just ()) _ =
  do bv_tp <- liftSC1 scBitvector n 
     return $ Just (bv_tp, NoConv, BVToNat n)
-- add a 'BVVecToVec' conversion if the (optional) given term has a
-- 'BVVecToVec' conversion
findInjConvs (asNonBVVecVectorType -> Just (m, _))
             (Just (asGenFromBVVecTerm -> Just (n, len, a, t1', _, _))) tp2 t2 =
  do len' <- liftSC2 scGlobalApply "Prelude.bvToNat" [n, len]
     tp1' <- liftSC2 scVecType len' a
     mb_cs <- findInjConvs tp1' (Just t1') tp2 t2
     return $ fmap (\(tp, c1, c2) -> (tp, BVVecToVec n len a m <> c1, c2)) mb_cs
findInjConvs tp1 t1 (asNonBVVecVectorType -> Just (m, _))
                    (Just (asGenFromBVVecTerm -> Just (n, len, a, t2', _, _))) =
  do len' <- liftSC2 scGlobalApply "Prelude.bvToNat" [n, len]
     tp2' <- liftSC2 scVecType len' a
     mb_cs <- findInjConvs tp1 t1 tp2' (Just t2')
     return $ fmap (\(tp, c1, c2) -> (tp, c1, BVVecToVec n len a m <> c2)) mb_cs
-- add a 'BVVecToVec' conversion we have a BVVec on the other side, using the
-- bit-width from the other side
findInjConvs (asNonBVVecVectorType -> Just (m, a')) _
             (asBVVecType -> Just (n, len, a)) _ =
  do len_nat <- liftSC2 scGlobalApply "Prelude.bvToNat" [n, len]
     bvvec_tp <- liftSC2 scVecType len_nat a
     lens_are_eq <- mrProveEq m len_nat
     as_are_eq <- mrConvertible a a'
     if lens_are_eq && as_are_eq
     then return $ Just (bvvec_tp, BVVecToVec n len a m, NoConv)
     else return $ Nothing
findInjConvs (asBVVecType -> Just (n, len, a)) _
             (asNonBVVecVectorType -> Just (m, a')) _ =
  do len_nat <- liftSC2 scGlobalApply "Prelude.bvToNat" [n, len]
     bvvec_tp <- liftSC2 scVecType len_nat a
     lens_are_eq <- mrProveEq m len_nat
     as_are_eq <- mrConvertible a a'
     if lens_are_eq && as_are_eq
     then return $ Just (bvvec_tp, NoConv, BVVecToVec n len a m)
     else return $ Nothing
-- add a 'pairToPair' conversion if we have pair types on both sides
findInjConvs (asPairType -> Just (tpL1, tpR1)) t1
             (asPairType -> Just (tpL2, tpR2)) t2 =
  do tL1 <- mapM (flip doTermProj TermProjLeft ) t1
     tR1 <- mapM (flip doTermProj TermProjRight) t1
     tL2 <- mapM (flip doTermProj TermProjLeft ) t2
     tR2 <- mapM (flip doTermProj TermProjRight) t2
     mb_cLs <- findInjConvs tpL1 tL1 tpL2 tL2
     mb_cRs <- findInjConvs tpR1 tR1 tpR2 tR2
     case (mb_cLs, mb_cRs) of
       (Just (tpL, cL1, cL2), Just (tpR, cR1, cR2)) ->
         do pair_tp <- liftSC2 scPairType tpL tpR
            return $ Just (pair_tp, PairToPair cL1 cR1, PairToPair cL2 cR2)
       _ -> return $ Nothing
-- otherwise, just check that the types are convertible
findInjConvs tp1 _ tp2 _ =
  do tps_are_eq <- mrConvertible tp1 tp2
     if tps_are_eq
     then return $ Just (tp1, NoConv, NoConv)
     else return $ Nothing


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
     tps_eq <- mrConvertible tp1 tp2
     if not het && not tps_eq then return False
     else do cond_in_ctx <- mrProveRelH het tp1 tp2 t1 t2
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

-- For Num, nat, bitvector, Boolean, and integer types, call mrProveEqSimple
mrProveRelH' _ _ _ _ (asNum -> Just (Left t1)) (asNum -> Just (Left t2)) =
  mrProveEqSimple (liftSC2 scEqualNat) t1 t2
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

mrProveRelH' _ het tp1 tp2 t1 t2 = findInjConvs tp1 (Just t1) tp2 (Just t2) >>= \case
  -- If we are allowing heterogeneous equality and we can find non-trivial
  -- injective conversions from a type @tp@ to @tp1@ and @tp2@, apply the
  -- inverses of these conversions to @t1@ and @t2@ and continue checking
  -- equality on the results
  Just (tp, c1, c2) | nonTrivialConv c1 || nonTrivialConv c2 -> do
    t1' <- mrApplyInvConv c1 t1
    t2' <- mrApplyInvConv c2 t2
    mrProveRelH True tp tp t1' t2'
  -- Otherwise, just check convertibility
  _ -> do
    success <- mrConvertible t1 t2
    tps_eq <- mrConvertible tp1 tp2
    if success then return () else
      if het || not tps_eq
      then mrDebugPPPrefixSep 2 "mrProveRelH' could not match types: " tp1 "and" tp2 >>
           mrDebugPPPrefixSep 2 "and could not prove convertible: " t1 "and" t2
      else mrDebugPPPrefixSep 2 "mrProveEq could not prove convertible: " t1 "and" t2
    TermInCtx [] <$> liftSC1 scBool success
