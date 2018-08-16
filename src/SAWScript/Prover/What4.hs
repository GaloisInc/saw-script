{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}

module SAWScript.Prover.What4 where

import qualified Data.Vector as V
import qualified Data.Map as Map
import           Control.Monad(filterM)
import           Data.Maybe (catMaybes)

import Verifier.SAW.SharedTerm
import Verifier.SAW.FiniteValue

import Verifier.SAW.TypedTerm(TypedTerm(..), mkTypedTerm)
import Verifier.SAW.Recognizer(asPi)

import           SAWScript.Prover.Rewrite(rewriteEqs)
import           SAWScript.Prover.Mode(ProverMode(..))
import           SAWScript.Prover.SolverStats
import           SAWScript.Prover.Util

import Verifier.SAW.Cryptol.Prims (w4Prims)

import Data.Parameterized.Nonce

import           What4.Config
import           What4.Solver
import           What4.SatResult
import           What4.Interface
import           What4.BaseTypes
import           What4.Expr.GroundEval
import qualified What4.Solver as Solver
import qualified Verifier.SAW.Simulator.What4 as W
import           Verifier.SAW.Simulator.What4.FirstOrder
import qualified What4.Expr.Builder as B

import System.IO

-- This class allows the "sim" argument to be passed implicitly,
-- allowing the What4 module to make an instance of the 'SymbolicValue' class.
import           Data.Reflection(Given(..),give)



----------------------------------------------------------------


-- trivial state
data St t = St

satWhat4_sym :: SolverAdapter St
             -> [String]
             -> SharedContext
             -> ProverMode
             -> Term
             -> IO (Maybe [(String, FirstOrderValue)], SolverStats)
satWhat4_sym solver un sc pm t = do
  -- TODO: get rid of GlobalNonceGenerator ???
  sym <- B.newExprBuilder St globalNonceGenerator
  satWhat4_solver solver sym un sc pm t


satWhat4_z3, satWhat4_boolector, satWhat4_cvc4,
  satWhat4_dreal, satWhat4_stp, satWhat4_yices ::
  [String]      {- ^ Uninterpreted functions -} ->
  SharedContext {- ^ Context for working with terms -} ->
  ProverMode    {- ^ Prove/check -} ->
  Term          {- ^ A boolean term to be proved/checked. -} ->
  IO (Maybe [(String,FirstOrderValue)], SolverStats)

satWhat4_z3        = satWhat4_sym z3Adapter
satWhat4_boolector = satWhat4_sym boolectorAdapter
satWhat4_cvc4      = satWhat4_sym cvc4Adapter
satWhat4_dreal     = satWhat4_sym drealAdapter
satWhat4_stp       = satWhat4_sym stpAdapter
satWhat4_yices     = satWhat4_sym yicesAdapter




-- | Check the satisfiability of a theorem using What4.
satWhat4_solver :: forall st t.
  SolverAdapter st   {- ^ Which solver to use -} ->
  B.ExprBuilder t st {- ^ The glorious sym -}  ->
  [String]           {- ^ Uninterpreted functions -} ->
  SharedContext      {- ^ Context for working with terms -} ->
  ProverMode         {- ^ Prove/check -} ->
  Term               {- ^ A boolean term to be proved/checked. -} ->
  IO (Maybe [(String,FirstOrderValue)], SolverStats)
  -- ^ (example/counter-example, solver statistics)
satWhat4_solver solver sym unints sc mode term =

  do
     -- symbolically evaluate
     (t', argNames, (bvs,lit0)) <- give sym $ prepWhat4 sc [] term

     lit <- case mode of
              CheckSat -> return lit0
              Prove    -> notPred sym lit0

     extendConfig (solver_adapter_config_options solver)
                  (getConfiguration sym)

     let stats = solverStats ("W4 ->" ++ solver_adapter_name solver)
                             (scSharedSize t')

     -- log to stdout
     let logger _ str = putStr str

     -- run solver
     solver_adapter_check_sat solver sym logger lit $ \ r -> case r of
         Sat (gndEvalFcn,_) -> do
           mvals <- mapM (getValues @(B.ExprBuilder t st) gndEvalFcn)
                         (zip bvs argNames)
           return (Just (catMaybes mvals), stats) where

         Unsat   -> return (Nothing, stats)

         Unknown -> fail "Prover returned Unknown"


prepWhat4 :: forall sym. (Given sym, IsSymExprBuilder sym) =>
  SharedContext -> [String] -> Term ->
  IO (Term, [String], ([Maybe (W.Labeler sym)],Pred sym))
prepWhat4 sc unints t0 = do
  -- Abstract over all non-function ExtCns variables
  let nonFun e = fmap ((== Nothing) . asPi) (scWhnf sc (ecType e))
  exts <- filterM nonFun (getAllExts t0)

  TypedTerm schema t' <-
      scAbstractExts sc exts t0 >>= rewriteEqs sc >>= mkTypedTerm sc

  checkBooleanSchema schema
  (argNames, lit) <- W.w4Solve sc w4Prims unints t'
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
printValue :: (B.ExprBuilder t st) -> GroundEvalFn t ->
  (Maybe (W.TypedExpr (B.ExprBuilder t st)), String) -> IO ()
printValue _ _ (Nothing, _) = return ()
printValue _ f (Just (W.TypedExpr (ty :: BaseTypeRepr ty) (bv :: B.Expr t ty)), orig) = do
  gv <- groundEval f @ty bv
  putStr $ orig ++ "=?"
  print (groundToFOV ty gv)
