module SAWScript.Prover.RME where

import qualified Data.Map as Map

import qualified Data.RME as RME

import Verifier.SAW.SharedTerm
import Verifier.SAW.FiniteValue

import qualified Verifier.SAW.Simulator.RME as RME

import SAWScript.Proof(Prop, propToSATQuery, propSize, CEX)
import SAWScript.Prover.SolverStats
import SAWScript.Prover.Util

-- | Bit-blast a proposition and check its validity using RME.
proveRME ::
  SharedContext {- ^ Context for working with terms -} ->
  Prop          {- ^ A proposition to be proved -} ->
  IO (Maybe CEX, SolverStats)
proveRME sc goal =
  do satq <- propToSATQuery sc mempty goal
     RME.withBitBlastedSATQuery sc Map.empty satq $ \lit shapes ->
       let stats = solverStats "RME" (propSize goal)
       in case RME.sat lit of
            Nothing -> return (Nothing, stats)
            Just cex -> do
              let m = Map.fromList cex
              let n = sum (map (sizeFiniteType . snd) shapes)
              let bs = map (maybe False id . flip Map.lookup m) $ take n [0..]
              let r = liftCexBB (map snd shapes) bs
              case r of
                Left err -> fail $ "Can't parse counterexample: " ++ err
                Right vs
                  | length shapes == length vs -> do
                    let model = zip (map fst shapes) (map toFirstOrderValue vs)
                    return (Just model, stats)
                  | otherwise -> fail $ unwords ["RME SAT results do not match expected arguments", show shapes, show vs]
