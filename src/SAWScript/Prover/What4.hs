{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}

module SAWScript.Prover.What4 where

import qualified Data.Vector as V
import           Control.Monad(filterM)
import           Data.Maybe (catMaybes)

import Verifier.SAW.SharedTerm
import Verifier.SAW.FiniteValue

import Verifier.SAW.Recognizer(asPi)

import           SAWScript.Proof(Prop, propToPredicate)
import           SAWScript.Prover.Rewrite(rewriteEqs)
import           SAWScript.Prover.SolverStats

import Data.Parameterized.Nonce

import           What4.Config
import           What4.Solver
import           What4.Interface
import           What4.Expr.GroundEval
import qualified Verifier.SAW.Simulator.What4 as W
import           Verifier.SAW.Simulator.What4.FirstOrder
import qualified What4.Expr.Builder as B


----------------------------------------------------------------


-- trivial state
data St t = St

proveWhat4_sym ::
  SolverAdapter St ->
  [String] ->
  SharedContext ->
  Bool ->
  Prop ->
  IO (Maybe [(String, FirstOrderValue)], SolverStats)
proveWhat4_sym solver un sc hashConsing t =
  do -- TODO: get rid of GlobalNonceGenerator ???
     sym <- B.newExprBuilder B.FloatRealRepr St globalNonceGenerator
     cacheTermsSetting <- getOptionSetting B.cacheTerms $ getConfiguration sym
     _ <- setOpt cacheTermsSetting hashConsing
     proveWhat4_solver solver sym un sc t


proveWhat4_z3, proveWhat4_boolector, proveWhat4_cvc4,
  proveWhat4_dreal, proveWhat4_stp, proveWhat4_yices ::
  [String]      {- ^ Uninterpreted functions -} ->
  SharedContext {- ^ Context for working with terms -} ->
  Bool          {- ^ Hash-consing of What4 terms -}->
  Prop          {- ^ A proposition to be proved -} ->
  IO (Maybe [(String, FirstOrderValue)], SolverStats)

proveWhat4_z3        = proveWhat4_sym z3Adapter
proveWhat4_boolector = proveWhat4_sym boolectorAdapter
proveWhat4_cvc4      = proveWhat4_sym cvc4Adapter
proveWhat4_dreal     = proveWhat4_sym drealAdapter
proveWhat4_stp       = proveWhat4_sym stpAdapter
proveWhat4_yices     = proveWhat4_sym yicesAdapter




-- | Check the validity of a proposition using What4.
proveWhat4_solver :: forall st t ff.
  SolverAdapter st   {- ^ Which solver to use -} ->
  B.ExprBuilder t st ff {- ^ The glorious sym -}  ->
  [String]           {- ^ Uninterpreted functions -} ->
  SharedContext      {- ^ Context for working with terms -} ->
  Prop               {- ^ A proposition to be proved/checked. -} ->
  IO (Maybe [(String, FirstOrderValue)], SolverStats)
  -- ^ (example/counter-example, solver statistics)
proveWhat4_solver solver sym unints sc goal =

  do
     -- convert goal to lambda term
     term <- propToPredicate sc goal
     -- symbolically evaluate
     (t', argNames, (bvs,lit0)) <- prepWhat4 sym sc unints term

     lit <- notPred sym lit0

     extendConfig (solver_adapter_config_options solver)
                  (getConfiguration sym)

     let stats = solverStats ("W4 ->" ++ solver_adapter_name solver)
                             (scSharedSize t')

     -- log to stdout
     let logger _ str = putStrLn str
     let logData = defaultLogData { logCallbackVerbose = logger
                                  , logReason = "SAW proof" }

     -- run solver
     solver_adapter_check_sat solver sym logData [lit] $ \ r -> case r of
         Sat (gndEvalFcn,_) -> do
           mvals <- mapM (getValues @(B.ExprBuilder t st ff) gndEvalFcn)
                         (zip bvs argNames)
           return (Just (catMaybes mvals), stats) where

         Unsat _ -> return (Nothing, stats)

         Unknown -> fail "Prover returned Unknown"


prepWhat4 ::
  forall sym. (IsSymExprBuilder sym) =>
  sym -> SharedContext -> [String] -> Term ->
  IO (Term, [String], ([Maybe (W.Labeler sym)], Pred sym))
prepWhat4 sym sc unints t0 = do
  -- Abstract over all non-function ExtCns variables
  let nonFun e = fmap ((== Nothing) . asPi) (scWhnf sc (ecType e))
  exts <- filterM nonFun (getAllExts t0)

  t' <- scAbstractExts sc exts t0 >>= rewriteEqs sc

  (argNames, lit) <- W.w4Solve sym sc mempty unints t'
  return (t', argNames, lit)


getValues :: forall sym gt. (SymExpr sym ~ B.Expr gt) => GroundEvalFn gt ->
  (Maybe (W.Labeler sym), String) -> IO (Maybe (String, FirstOrderValue))
getValues _ (Nothing, _) = return Nothing
getValues f (Just labeler, orig) = do
  fov <- getLabelValues f labeler
  return $ Just (orig,fov)


getLabelValues :: forall sym gt. (SymExpr sym ~ B.Expr gt) => GroundEvalFn gt ->
  W.Labeler sym -> IO FirstOrderValue

getLabelValues f (W.TupleLabel labels) = do
  vals <- mapM (getLabelValues f) (V.toList labels)
  return (FOVTuple vals)

getLabelValues f (W.VecLabel labels) = do
  let vty = error "TODO: compute vector type, or just store it"
  vals <- mapM (getLabelValues f) (V.toList labels)
  return (FOVVec vty vals)

getLabelValues f (W.RecLabel m) = do
  m' <- mapM (getLabelValues f) m
  return (FOVRec m')

getLabelValues f (W.BaseLabel (W.TypedExpr ty bv)) = do
  gv <- groundEval f bv
  case (groundToFOV ty gv) of
    Left err  -> fail err
    Right fov -> return fov


-- | For debugging
printValue :: (B.ExprBuilder t st ff) -> GroundEvalFn t ->
  (Maybe (W.TypedExpr (B.ExprBuilder t st ff)), String) -> IO ()
printValue _ _ (Nothing, _) = return ()
printValue _ f (Just (W.TypedExpr (ty :: BaseTypeRepr ty) (bv :: B.Expr t ty)), orig) = do
  gv <- groundEval f @ty bv
  putStr $ orig ++ "=?"
  print (groundToFOV ty gv)
