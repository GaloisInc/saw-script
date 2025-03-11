{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}

module SAWCentral.Prover.What4 where


import           Control.Lens ((^.))
import           Control.Monad.State (gets)
import           Data.List (nub)
import           Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Text as Text
import           System.IO

import Verifier.SAW.SharedTerm
import Verifier.SAW.FiniteValue
import Verifier.SAW.SATQuery (SATQuery(..))

import           SAWCentral.Proof(Sequent, sequentToSATQuery, CEX)
import           SAWCentral.Value (TopLevel, io, getSharedContext, rwWhat4PushMuxOps)

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

setupWhat4_sym ::
  Bool ->
  Bool ->
  IO (B.ExprBuilder
      GlobalNonceGenerator
      St
      (B.Flags B.FloatReal))
setupWhat4_sym hashConsing what4PushMuxOps =
  do -- TODO: get rid of GlobalNonceGenerator ???
     sym <- B.newExprBuilder B.FloatRealRepr St globalNonceGenerator
     let cfg = getConfiguration sym
     cacheTermsSetting <- getOptionSetting B.cacheTerms cfg
     _ <- setOpt cacheTermsSetting hashConsing
     pushMuxOpsSetting <- getOptionSetting B.pushMuxOpsOption cfg
     _ <- setOpt pushMuxOpsSetting what4PushMuxOps
     return sym

what4Theories ::
  Set VarIndex ->
  Bool ->
  Sequent ->
  TopLevel [String]
what4Theories unintSet hashConsing goal = do
  sc <- getSharedContext
  what4PushMuxOps <- gets rwWhat4PushMuxOps
  io $ do
     sym <- setupWhat4_sym hashConsing what4PushMuxOps
     satq <- sequentToSATQuery sc unintSet goal
     (_varMap, lits) <- W.w4Solve sym sc satq
     let pf lit = (predicateVarInfo lit)^.problemFeatures
     return (nub (concatMap evalTheories (map pf lits)))

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
  Bool ->
  SATQuery ->
  TopLevel (Maybe CEX, String)
proveWhat4_sym solver hashConsing satq = do
  sc <- getSharedContext
  what4PushMuxOps <- gets rwWhat4PushMuxOps
  io $ do
     sym <- setupWhat4_sym hashConsing what4PushMuxOps
     proveWhat4_solver solver sym sc satq (return ())

proveExportWhat4_sym ::
  SolverAdapter St ->
  Bool ->
  FilePath ->
  SATQuery ->
  TopLevel (Maybe CEX, String)
proveExportWhat4_sym solver hashConsing outFilePath satq = do
  sc <- getSharedContext
  what4PushMuxOps <- gets rwWhat4PushMuxOps
  io $ do
     sym <- setupWhat4_sym hashConsing what4PushMuxOps

     -- Write smt out
     (_, _, lits, solver_name) <- setupWhat4_solver solver sym sc satq
     withFile outFilePath WriteMode $ \handle ->
       solver_adapter_write_smt2 solver sym handle lits

     -- Assume unsat
     return (Nothing, solver_name)

proveWhat4_z3,
  proveWhat4_bitwuzla, proveWhat4_boolector,
  proveWhat4_cvc4, proveWhat4_cvc5,
  proveWhat4_dreal, proveWhat4_stp, proveWhat4_yices,
  proveWhat4_abc ::
  Bool          {- ^ Hash-consing of What4 terms -}->
  SATQuery      {- ^ The query to be proved -} ->
  TopLevel (Maybe CEX, String)

proveWhat4_z3        = proveWhat4_sym z3Adapter
proveWhat4_bitwuzla  = proveWhat4_sym bitwuzlaAdapter
proveWhat4_boolector = proveWhat4_sym boolectorAdapter
proveWhat4_cvc4      = proveWhat4_sym cvc4Adapter
proveWhat4_cvc5      = proveWhat4_sym cvc5Adapter
proveWhat4_dreal     = proveWhat4_sym drealAdapter
proveWhat4_stp       = proveWhat4_sym stpAdapter
proveWhat4_yices     = proveWhat4_sym yicesAdapter
proveWhat4_abc       = proveWhat4_sym externalABCAdapter

proveWhat4_z3_using ::
  String        {- ^ Solver tactic -} ->
  Bool          {- ^ Hash-consing of What4 terms -}->
  SATQuery      {- ^ The query to be proved -} ->
  TopLevel (Maybe CEX, String)
proveWhat4_z3_using tactic hashConsing satq = do
  sc <- getSharedContext
  what4PushMuxOps <- gets rwWhat4PushMuxOps
  io $ do
     sym <- setupWhat4_sym hashConsing what4PushMuxOps
     proveWhat4_solver z3Adapter sym sc satq $
       do z3TacticSetting <- getOptionSetting z3Tactic $ getConfiguration sym
          _ <- setOpt z3TacticSetting $ Text.pack tactic
          return ()

proveExportWhat4_z3,
  proveExportWhat4_bitwuzla, proveExportWhat4_boolector,
  proveExportWhat4_cvc4, proveExportWhat4_cvc5,
  proveExportWhat4_dreal, proveExportWhat4_stp, proveExportWhat4_yices ::
  Bool          {- ^ Hash-consing of ExportWhat4 terms -}->
  FilePath      {- ^ Path of file to write SMT to -}->
  SATQuery      {- ^ The query to be proved -} ->
  TopLevel (Maybe CEX, String)

proveExportWhat4_z3        = proveExportWhat4_sym z3Adapter
proveExportWhat4_bitwuzla  = proveExportWhat4_sym bitwuzlaAdapter
proveExportWhat4_boolector = proveExportWhat4_sym boolectorAdapter
proveExportWhat4_cvc4      = proveExportWhat4_sym cvc4Adapter
proveExportWhat4_cvc5      = proveExportWhat4_sym cvc5Adapter
proveExportWhat4_dreal     = proveExportWhat4_sym drealAdapter
proveExportWhat4_stp       = proveExportWhat4_sym stpAdapter
proveExportWhat4_yices     = proveExportWhat4_sym yicesAdapter


setupWhat4_solver :: forall st t ff.
  SolverAdapter st   {- ^ Which solver to use -} ->
  B.ExprBuilder t st ff {- ^ The glorious sym -}  ->
  SharedContext      {- ^ Context for working with terms -} ->
  SATQuery           {- ^ The query to be proved/checked. -} ->
  IO ( [ExtCns Term]
     , [W.Labeler (B.ExprBuilder t st ff)]
     , [Pred (B.ExprBuilder t st ff)]
     , String)
setupWhat4_solver solver sym sc satq =
  do
     -- symbolically evaluate
     let varList  = Map.toList (satVariables satq)
     let argNames = map fst varList
     (varMap, lits) <- W.w4Solve sym sc satq
     let bvs = map (fst . snd) varMap

     extendConfig (solver_adapter_config_options solver)
                  (getConfiguration sym)

     let solver_name = "W4 ->" ++ solver_adapter_name solver

     return (argNames, bvs, lits, solver_name)


-- | Check the validity of a proposition using What4.
proveWhat4_solver :: forall st t ff.
  SolverAdapter st   {- ^ Which solver to use -} ->
  B.ExprBuilder t st ff {- ^ The glorious sym -}  ->
  SharedContext      {- ^ Context for working with terms -} ->
  SATQuery           {- ^ The query to be proved/checked. -} ->
  IO ()              {- ^ Extra setup actions -} ->
  IO (Maybe CEX, String)
  -- ^ (example/counter-example, solver statistics)
proveWhat4_solver solver sym sc satq extraSetup =
  do
     (argNames, bvs, lits, solver_name) <- setupWhat4_solver solver sym sc satq
     extraSetup

     -- log to stdout
     let logger _ str = putStrLn str
     let logData = defaultLogData { logCallbackVerbose = logger
                                  , logReason = "SAW proof" }

     -- run solver
     solver_adapter_check_sat solver sym logData lits $ \ r -> case r of
         Sat (gndEvalFcn,_) -> do
           mvals <- mapM (getValues @(B.ExprBuilder t st ff) gndEvalFcn)
                         (zip bvs argNames)
           return (Just mvals, solver_name) where

         Unsat _ -> return (Nothing, solver_name)

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
