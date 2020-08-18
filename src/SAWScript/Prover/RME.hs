module SAWScript.Prover.RME where

import qualified Data.Map as Map

import Verifier.SAW.SharedTerm
import Verifier.SAW.FiniteValue

import qualified Verifier.SAW.Simulator.RME as RME
import qualified Verifier.SAW.Simulator.RME.Base as RME
import Verifier.SAW.Recognizer(asPiList)

import SAWScript.Proof(Prop, propToPredicate)
import SAWScript.Prover.Rewrite(rewriteEqs)
import SAWScript.Prover.SolverStats
import SAWScript.Prover.Util

-- | Bit-blast a proposition and check its validity using RME.
proveRME ::
  SharedContext {- ^ Context for working with terms -} ->
  Prop          {- ^ A proposition to be proved -} ->
  IO (Maybe [(String, FirstOrderValue)], SolverStats)
proveRME sc goal =
  do t0 <- propToPredicate sc goal
     t <- bindAllExts sc t0 >>= rewriteEqs sc
     tp <- scWhnf sc =<< scTypeOf sc t
     let (args, _) = asPiList tp
         argNames = map fst args
     RME.withBitBlastedPred sc Map.empty t $ \lit0 shapes ->
       let lit = RME.compl lit0
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
