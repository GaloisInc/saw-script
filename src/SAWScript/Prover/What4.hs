{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}

module SAWScript.Prover.What4 where


import           Control.Lens ((^.))
import           Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Text as Text
import           System.IO

import Verifier.SAW.SharedTerm
import Verifier.SAW.FiniteValue
import Verifier.SAW.SATQuery (SATQuery(..))

import           SAWScript.Proof(Sequent, sequentToSATQuery, sequentSize, CEX)
import           SAWScript.Prover.SolverStats
import           SAWScript.Value (TopLevel, io, getSharedContext)

import           Data.Parameterized.Nonce

import           What4.Config
import           What4.Solver
import           What4.Interface
import           What4.Expr.GroundEval
import           What4.Expr.VarIdentification
import           What4.ProblemFeatures
import qualified Verifier.SAW.Simulator.What4 as W
import           Verifier.SAW.Simulator.What4.FirstOrder
import qualified What4.Expr.Builder as B


----------------------------------------------------------------


-- trivial state
data St t = St

setupWhat4_sym :: Bool -> IO (B.ExprBuilder
                              GlobalNonceGenerator
                              St
                              (B.Flags B.FloatReal))
setupWhat4_sym hashConsing =
  do -- TODO: get rid of GlobalNonceGenerator ???
     sym <- B.newExprBuilder B.FloatRealRepr St globalNonceGenerator
     cacheTermsSetting <- getOptionSetting B.cacheTerms $ getConfiguration sym
     _ <- setOpt cacheTermsSetting hashConsing
     return sym

what4Theories ::
  Set VarIndex ->
  Bool ->
  Sequent ->
  TopLevel [String]
what4Theories unintSet hashConsing goal =
  getSharedContext >>= \sc -> io $
  do sym <- setupWhat4_sym hashConsing
     satq <- sequentToSATQuery sc unintSet goal
     (_varMap, lit) <- W.w4Solve sym sc satq
     let pf = (predicateVarInfo lit)^.problemFeatures
     return (evalTheories pf)

evalTheories :: ProblemFeatures -> [String]
evalTheories pf = [ nm | (nm,f) <- xs, hasProblemFeature pf f ]
 where
  xs = [ ("LinearArithmetic", useLinearArithmetic)
       , ("NonlinearArithmetic", useNonlinearArithmetic)
       , ("TranscendentalFunctions", useComputableReals)
       , ("Integers", useIntegerArithmetic)
       , ("Bitvectors", useBitvectors)
       , ("ExistsForall", useExistForall)
       , ("FirstOrderQuantifiers", useQuantifiers)
       , ("Arrays", useSymbolicArrays)
       , ("Structs", useStructs)
       , ("Strings", useStrings)
       , ("FloatingPoint", useFloatingPoint)
       ]

proveWhat4_sym ::
  SolverAdapter St ->
  Set VarIndex ->
  Bool ->
  Sequent ->
  TopLevel (Maybe CEX, SolverStats)
proveWhat4_sym solver un hashConsing t =
  getSharedContext >>= \sc -> io $
  do sym <- setupWhat4_sym hashConsing
     proveWhat4_solver solver sym un sc t (return ())

proveExportWhat4_sym ::
  SolverAdapter St ->
  Set VarIndex ->
  Bool ->
  FilePath ->
  Sequent->
  TopLevel (Maybe CEX, SolverStats)
proveExportWhat4_sym solver un hashConsing outFilePath t =
  getSharedContext >>= \sc -> io $
  do sym <- setupWhat4_sym hashConsing

     -- Write smt out
     (_, _, lit, stats) <- setupWhat4_solver solver sym un sc t
     withFile outFilePath WriteMode $ \handle ->
       solver_adapter_write_smt2 solver sym handle [lit]

     -- Assume unsat
     return (Nothing, stats)

proveWhat4_z3, proveWhat4_boolector, proveWhat4_cvc4,
  proveWhat4_dreal, proveWhat4_stp, proveWhat4_yices,
  proveWhat4_abc ::
  Set VarIndex  {- ^ Uninterpreted functions -} ->
  Bool          {- ^ Hash-consing of What4 terms -}->
  Sequent       {- ^ A proposition to be proved -} ->
  TopLevel (Maybe CEX, SolverStats)

proveWhat4_z3        = proveWhat4_sym z3Adapter
proveWhat4_boolector = proveWhat4_sym boolectorAdapter
proveWhat4_cvc4      = proveWhat4_sym cvc4Adapter
proveWhat4_dreal     = proveWhat4_sym drealAdapter
proveWhat4_stp       = proveWhat4_sym stpAdapter
proveWhat4_yices     = proveWhat4_sym yicesAdapter
proveWhat4_abc       = proveWhat4_sym externalABCAdapter

proveWhat4_z3_using ::
  String        {- ^ Solver tactic -} ->
  Set VarIndex  {- ^ Uninterpreted functions -} ->
  Bool          {- ^ Hash-consing of What4 terms -}->
  Sequent       {- ^ A proposition to be proved -} ->
  TopLevel (Maybe CEX, SolverStats)
proveWhat4_z3_using tactic un hashConsing t =
  getSharedContext >>= \sc -> io $
  do sym <- setupWhat4_sym hashConsing
     proveWhat4_solver z3Adapter sym un sc t $
       do z3TacticSetting <- getOptionSetting z3Tactic $ getConfiguration sym
          _ <- setOpt z3TacticSetting $ Text.pack tactic
          return ()

proveExportWhat4_z3, proveExportWhat4_boolector, proveExportWhat4_cvc4,
  proveExportWhat4_dreal, proveExportWhat4_stp, proveExportWhat4_yices ::
  Set VarIndex  {- ^ Uninterpreted functions -} ->
  Bool          {- ^ Hash-consing of ExportWhat4 terms -}->
  FilePath      {- ^ Path of file to write SMT to -}->
  Sequent       {- ^ A proposition to be proved -} ->
  TopLevel (Maybe CEX, SolverStats)

proveExportWhat4_z3        = proveExportWhat4_sym z3Adapter
proveExportWhat4_boolector = proveExportWhat4_sym boolectorAdapter
proveExportWhat4_cvc4      = proveExportWhat4_sym cvc4Adapter
proveExportWhat4_dreal     = proveExportWhat4_sym drealAdapter
proveExportWhat4_stp       = proveExportWhat4_sym stpAdapter
proveExportWhat4_yices     = proveExportWhat4_sym yicesAdapter


setupWhat4_solver :: forall st t ff.
  SolverAdapter st   {- ^ Which solver to use -} ->
  B.ExprBuilder t st ff {- ^ The glorious sym -}  ->
  Set VarIndex       {- ^ Uninterpreted functions -} ->
  SharedContext      {- ^ Context for working with terms -} ->
  Sequent            {- ^ A proposition to be proved/checked. -} ->
  IO ( [ExtCns Term]
     , [W.Labeler (B.ExprBuilder t st ff)]
     , Pred (B.ExprBuilder t st ff)
     , SolverStats)
setupWhat4_solver solver sym unintSet sc goal =
  do
     -- symbolically evaluate
     satq <- sequentToSATQuery sc unintSet goal
     let varList  = Map.toList (satVariables satq)
     let argNames = map fst varList
     (varMap, lit) <- W.w4Solve sym sc satq
     let bvs = map (fst . snd) varMap

     extendConfig (solver_adapter_config_options solver)
                  (getConfiguration sym)

     let stats = solverStats ("W4 ->" ++ solver_adapter_name solver)
                             (sequentSize goal)

     return (argNames, bvs, lit, stats)


-- | Check the validity of a proposition using What4.
proveWhat4_solver :: forall st t ff.
  SolverAdapter st   {- ^ Which solver to use -} ->
  B.ExprBuilder t st ff {- ^ The glorious sym -}  ->
  Set VarIndex       {- ^ Uninterpreted functions -} ->
  SharedContext      {- ^ Context for working with terms -} ->
  Sequent            {- ^ A proposition to be proved/checked. -} ->
  IO ()              {- ^ Extra setup actions -} ->
  IO (Maybe CEX, SolverStats)
  -- ^ (example/counter-example, solver statistics)
proveWhat4_solver solver sym unintSet sc goal extraSetup =
  do
     (argNames, bvs, lit, stats) <- setupWhat4_solver solver sym unintSet sc goal
     extraSetup

     -- log to stdout
     let logger _ str = putStrLn str
     let logData = defaultLogData { logCallbackVerbose = logger
                                  , logReason = "SAW proof" }

     -- run solver
     solver_adapter_check_sat solver sym logData [lit] $ \ r -> case r of
         Sat (gndEvalFcn,_) -> do
           mvals <- mapM (getValues @(B.ExprBuilder t st ff) gndEvalFcn)
                         (zip bvs argNames)
           return (Just mvals, stats) where

         Unsat _ -> return (Nothing, stats)

         Unknown -> fail "Prover returned Unknown"



getValues :: forall sym gt a. (SymExpr sym ~ B.Expr gt) => GroundEvalFn gt ->
  (W.Labeler sym, a) -> IO (a, FirstOrderValue)
getValues f (labeler, orig) = do
  fov <- W.getLabelValues f labeler
  return (orig, fov)


-- | For debugging
printValue :: (B.ExprBuilder t st ff) -> GroundEvalFn t ->
  (Maybe (W.TypedExpr (B.ExprBuilder t st ff)), String) -> IO ()
printValue _ _ (Nothing, _) = return ()
printValue _ f (Just (W.TypedExpr (ty :: BaseTypeRepr ty) (bv :: B.Expr t ty)), orig) = do
  gv <- groundEval f @ty bv
  putStr $ orig ++ "=?"
  print (groundToFOV ty gv)
