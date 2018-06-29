module SAWScript.Prover.What4 where

import qualified Data.Map as Map
import           Control.Monad(filterM,liftM)


import Verifier.SAW.SharedTerm
import Verifier.SAW.FiniteValue

import Verifier.SAW.TypedTerm(TypedTerm(..), mkTypedTerm)
import Verifier.SAW.Recognizer(asPiList,asPi)

import SAWScript.Prover.Rewrite(rewriteEqs)
import SAWScript.Prover.Mode(ProverMode(..))
import SAWScript.Prover.SolverStats
import SAWScript.Prover.Util

import What4.Config
import What4.SatResult
import What4.Interface
import What4.Protocol.Online
import qualified What4.Protocol.SMTLib2 as SMT2
import qualified What4.Solver.Z3 as Z3
import qualified Verifier.SAW.Simulator.What4 as W
import qualified What4.Expr.Builder as B

import Lang.Crucible.Backend.Online as Online

import Data.Parameterized.Nonce

{-
setupSolverConfig :: (IsExprBuilder sym) => sym -> IO ()
setupSolverConfig sym = do
   let cfg = getConfiguration sym
   extendConfig (solver_adapter_config_options z3Adapter) cfg
   z3PathSetter <- getOptionSetting z3Path
   res <- setOpt z3PathSetter "/usr/local/bin/z3"
   assert (null res) (return ())
-}

----------------------------------------------------------------
-- Derived from Lang/Crucible/Backend/Online
-- SCW note: I want to keep this part independent of the Crucible
-- package. But it does duplicate stuff



{-
type Backend scope solver = B.ExprBuilder scope (BackendState solver)

newtype BackendState solver scope = BackendState
    { nonceGenerator :: NonceGenerator IO scope
    , solverProc     :: !(IORef (SolverState scope solver))
    
-- | Is the solver running or not?
data SolverState scope solver =
    SolverNotStarted
  | SolverStarted (SolverProcess scope solver)

initialState :: NonceGenerator IO t -> IO (BackendState t)
initialState gen = do
        procref <- newIORefl SolverNotStarted
        return $! BackendState gen procref



type Z3OnlineBackend scope =
  OnlineBackend scope (SMT2.Writer Z3.Z3)
-}        
----------------------------------------------------------------
    
type Gt = GlobalNonceGenerator

prepWhat4 :: IsExprBuilder sym =>
   SharedContext -> Term -> sym -> IO (Term, Pred sym)
prepWhat4 sc t0 sym = do
    -- Abstract over all non-function ExtCns variables
  let nonFun e = fmap ((== Nothing) . asPi) (scWhnf sc (ecType e))
  exts <- filterM nonFun (getAllExts t0)
  TypedTerm schema t' <-
      scAbstractExts sc exts t0 >>= rewriteEqs sc >>= mkTypedTerm sc
  checkBooleanSchema schema
  
  lit <- W.solve sc t' sym
  return (t', lit)

path2Z3 :: String
path2Z3 = "/usr/local/bin/z3"
  
-- | Check the satisfiability of a theorem using What4.
satWhat4 ::
  SharedContext {- ^ Context for working with terms -} ->
  ProverMode    {- ^ Prove/check -} ->
  Term          {- ^ A boolean term to be proved/checked. -} ->
  IO (Maybe [(String,FirstOrderValue)], SolverStats)
  -- ^ (example/counter-example, solver statistics)
satWhat4 sc mode term = do
  do let gen = globalNonceGenerator
     
     Online.withZ3OnlineBackend gen $ \ sym -> do
     
       -- symbolically evaluate
       (t', lit0) <- prepWhat4 sc term sym
     
       lit <- case mode of
              CheckSat -> return lit0
              Prove    -> notPred sym lit0

       putStrLn $ show lit              

       -- dummy stats
       let stats = solverStats "What4->Z3" (scSharedSize t')

       -- log to stdout
       let logger str = putStrLn str

       
     
       -- runZ3
       -- result <- W.withZ3 sym path2Z3 logger $ \ session ->
       -- W.runCheckSat session return
       process <- Online.getSolverProcess sym

       -- interpret the result                
       checkSatisfiableWithModel process lit $ \ result -> case result of
         Sat gndEvalFcn -> return (Just labels, stats) where
           labels = error "cannot reinterpret yet"
         Unsat   -> return (Nothing, stats)
         Unknown -> fail "Prover returned Unknown"
  

{-  
  do TypedTerm schema t <-
        bindAllExts sc t0 >>= rewriteEqs sc >>= mkTypedTerm sc
     checkBooleanSchema schema
     tp <- scWhnf sc =<< scTypeOf sc t
     let (args, _) = asPiList tp
         argNames = map fst args
     RME.withBitBlastedPred sc Map.empty t $ \lit0 shapes ->
       let lit = case mode of
                   CheckSat -> lit0
                   Prove    -> RME.compl lit0
           stats = solverStats "RME" (scSharedSize t0)
       in case RME.sat lit of
            Nothing -> return (Nothing, stats)
            Just cex -> do
              let m = Map.fromList cex
              let n = sum (map sizeFiniteType shapes)
              let bs = map (maybe False id . flip Map.lookup m) $ take n [0..]
              let r = liftCexBB shapes bs
              case r of
                Left err -> fail $ "Can't parse counterexample: " ++ err
                Right vs
                  | length argNames == length vs -> do
                    let model = zip argNames (map toFirstOrderValue vs)
                    return (Just model, stats)
                  | otherwise -> fail $ unwords ["RME SAT results do not match expected arguments", show argNames, show vs]
  -}

