{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}

module SAWScript.Prover.What4 where

import Control.Monad (forM)
import System.IO

import           Data.IORef
import           Data.Set (Set)
import qualified Data.Map as Map
--import qualified Data.Text as Text
import           Data.Parameterized.TraversableFC

import Verifier.SAW.SharedTerm
import Verifier.SAW.FiniteValue

import           SAWScript.Proof(Prop, propToSATQuery, propSize, CEX)
import           SAWScript.Crucible.Common
import           SAWScript.Prover.SolverStats

import Data.Parameterized.Nonce

import           What4.Config
import           What4.Solver
import           What4.Interface
import           What4.Expr.GroundEval
--import           Verifier.SAW.Recognizer
import qualified Verifier.SAW.Simulator.Concrete as Sim
import qualified Verifier.SAW.Simulator.Value as Sim
import qualified Verifier.SAW.Simulator.What4 as W
import qualified Verifier.SAW.Simulator.What4.ReturnTrip as W
import           Verifier.SAW.Simulator.What4.FirstOrder

import qualified What4.Expr.Builder as B
import           What4.SWord (SWord(..))

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

proveWhat4_sym ::
  SolverAdapter St ->
  Set VarIndex ->
  SharedContext ->
  Bool ->
  Prop ->
  IO (Maybe CEX, SolverStats)
proveWhat4_sym solver un sc hashConsing t =
  do sym <- setupWhat4_sym hashConsing
     proveWhat4_solver solver sym un sc t

proveExportWhat4_sym ::
  SolverAdapter St ->
  Set VarIndex ->
  SharedContext ->
  Bool ->
  FilePath ->
  Prop ->
  IO (Maybe CEX, SolverStats)
proveExportWhat4_sym solver un sc hashConsing outFilePath t =
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
  SharedContext {- ^ Context for working with terms -} ->
  Bool          {- ^ Hash-consing of What4 terms -}->
  Prop          {- ^ A proposition to be proved -} ->
  IO (Maybe CEX, SolverStats)

proveWhat4_z3        = proveWhat4_sym z3Adapter
proveWhat4_boolector = proveWhat4_sym boolectorAdapter
proveWhat4_cvc4      = proveWhat4_sym cvc4Adapter
proveWhat4_dreal     = proveWhat4_sym drealAdapter
proveWhat4_stp       = proveWhat4_sym stpAdapter
proveWhat4_yices     = proveWhat4_sym yicesAdapter
proveWhat4_abc       = proveWhat4_sym externalABCAdapter

proveExportWhat4_z3, proveExportWhat4_boolector, proveExportWhat4_cvc4,
  proveExportWhat4_dreal, proveExportWhat4_stp, proveExportWhat4_yices ::
  Set VarIndex  {- ^ Uninterpreted functions -} ->
  SharedContext {- ^ Context for working with terms -} ->
  Bool          {- ^ Hash-consing of ExportWhat4 terms -}->
  FilePath      {- ^ Path of file to write SMT to -}->
  Prop          {- ^ A proposition to be proved -} ->
  IO (Maybe CEX, SolverStats)

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
  Prop               {- ^ A proposition to be proved/checked. -} ->
  IO ( [ExtCns Term]
     , [W.Labeler (B.ExprBuilder t st ff)]
     , Pred (B.ExprBuilder t st ff)
     , SolverStats)
setupWhat4_solver solver sym unintSet sc goal =
  do
     -- symbolically evaluate
     satq <- propToSATQuery sc unintSet goal
     (argNames, _argTys, bvs, lit) <- W.w4Solve sym sc satq

     extendConfig (solver_adapter_config_options solver)
                  (getConfiguration sym)

     let stats = solverStats ("W4 ->" ++ solver_adapter_name solver)
                             (propSize goal)

     return (argNames, bvs, lit, stats)


-- | Check the validity of a proposition using What4.
proveWhat4_solver :: forall st t ff.
  SolverAdapter st   {- ^ Which solver to use -} ->
  B.ExprBuilder t st ff {- ^ The glorious sym -}  ->
  Set VarIndex       {- ^ Uninterpreted functions -} ->
  SharedContext      {- ^ Context for working with terms -} ->
  Prop               {- ^ A proposition to be proved/checked. -} ->
  IO (Maybe CEX, SolverStats)
  -- ^ (example/counter-example, solver statistics)
proveWhat4_solver solver sym unintSet sc goal =
  do
     (argNames, bvs, lit, stats) <- setupWhat4_solver solver sym unintSet sc goal

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


w4_extract_uninterp :: SharedContext -> Set VarIndex -> Term -> IO (Term, Map.Map VarIndex [(Term,Term)])
w4_extract_uninterp sc unintSet tm =
  do tp <- scTypeOf sc tm
     modmap <- scGetModuleMap sc

     fot <- case Sim.asFirstOrderTypeValue (Sim.evalSharedTerm modmap mempty mempty tp) of
              Just fot -> pure fot
              Nothing  -> fail (unwords ["extract_uninterp, expected first-order type", showTerm tp])

     sym <- newSAWCoreBackend sc
     st <- sawCoreState sym

     ref <- newIORef mempty
     (v, replaceMap) <- W.w4ReplaceUninterp sym st sc modmap mempty ref unintSet tm

     tm' <- case (fot, v) of
              (FOTBit          , Sim.VBool b)       -> W.toSC sym st b
              (FOTVec _n FOTBit, Sim.VWord ZBV)     -> scBvConst sc 0 0
              (FOTVec _n FOTBit, Sim.VWord (DBV w)) -> W.toSC sym st w
              (FOTIntMod _,      Sim.VIntMod m i)   ->
                do m' <- scNat sc m
                   i' <- W.toSC sym st i
                   scToIntMod sc m' i'
              (FOTVec _n _t    , _) -> fail "extract_uninterp: TODO, vectors"
              (FOTArray _ _    , _) -> fail "extract_uninterp: TODO, arrays"
              (FOTTuple _ts    , _) -> fail "extract_uninterp: TODO, tuples"
              (FOTRec _fs      , _) -> fail "extract_uninterp: TODO, records"

              _ -> fail ("extract_uninterp: type/value mismatch " ++ show fot ++ "; " ++ show v)

     replacements <- flip traverse replaceMap $ \vals ->
                       forM vals $ \(ec,W.UnintApp _nm vs _tps) ->
                         do ectm <- scExtCns sc ec
                            vs' <- scTuple sc =<< foldMapFC (\x -> (:[]) <$> W.toSC sym st x) vs
                            return (ectm, vs')
     pure (tm',replacements)
