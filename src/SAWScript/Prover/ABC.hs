module SAWScript.Prover.ABC (proveABC) where

import qualified Data.Text as Text

import qualified Data.AIG as AIG

import           Verifier.SAW.FiniteValue
import           Verifier.SAW.Name
import           Verifier.SAW.SharedTerm
import qualified Verifier.SAW.Simulator.BitBlast as BBSim

import SAWScript.Proof(Prop, propToSATQuery, propSize)
import SAWScript.Prover.SolverStats (SolverStats, solverStats)
import SAWScript.Prover.Util (liftCexBB)

-- | Bit-blast a proposition and check its validity using ABC.
proveABC ::
  (AIG.IsAIG l g) =>
  AIG.Proxy l g ->
  SharedContext ->
  Prop ->
  IO (Maybe [(String, FirstOrderValue)], SolverStats)
proveABC proxy sc goal =
  do satq <- propToSATQuery sc mempty goal
     BBSim.withBitBlastedSATQuery proxy sc mempty satq $ \be lit shapes ->
       do let (ecs,fts) = unzip shapes
          let nms = map (Text.unpack . toShortName . ecName) ecs
          res <- getModel nms fts =<< AIG.checkSat be lit
          let stats = solverStats "ABC" (propSize goal)
          return (res, stats)

getModel ::
  Show name =>
  [name] ->
  [FiniteType] ->
  AIG.SatResult ->
  IO (Maybe [(name, FirstOrderValue)])
getModel argNames shapes satRes =
  case satRes of
    AIG.Unsat -> return Nothing

    AIG.Sat cex -> do
      case liftCexBB shapes cex of
        Left err -> fail ("Can't parse counterexample: " ++ err)
        Right vs

          | length argNames == length vs ->
            return (Just (zip argNames (map toFirstOrderValue vs)))

          | otherwise ->
              fail $ unwords [ "ABC SAT results do not match expected arguments"
                             , show argNames, show vs]

    AIG.SatUnknown -> fail "Unknown result from ABC"

