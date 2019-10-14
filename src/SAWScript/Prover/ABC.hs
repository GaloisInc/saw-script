module SAWScript.Prover.ABC (satABC) where


import qualified Data.AIG as AIG

import           Verifier.SAW.SharedTerm
import           Verifier.SAW.TypedTerm
import           Verifier.SAW.FiniteValue
import qualified Verifier.SAW.Simulator.BitBlast as BBSim
import           Verifier.SAW.Recognizer(asPiList)

import SAWScript.Proof(propToPredicate)
import SAWScript.Prover.SolverStats (SolverStats, solverStats)
import SAWScript.Prover.Rewrite(rewriteEqs)
import SAWScript.SAWCorePrimitives( bitblastPrimitives )
import SAWScript.Prover.Util
         (liftCexBB, checkBooleanSchema)

-- | Bit-blast a @Term@ representing a theorem and check its
-- satisfiability using ABC.
satABC ::
  (AIG.IsAIG l g) =>
  AIG.Proxy l g ->
  SharedContext ->
  Term ->
  IO (Maybe [(String,FirstOrderValue)], SolverStats)
satABC proxy sc goal =
  do t0 <- propToPredicate sc goal
     TypedTerm schema t <- (rewriteEqs sc t0 >>= mkTypedTerm sc)
     checkBooleanSchema schema
     tp <- scWhnf sc =<< scTypeOf sc t
     BBSim.withBitBlastedPred proxy sc bitblastPrimitives t $
      \be lit0 shapes ->
         do let lit = AIG.not lit0
            satRes <- getModel shapes =<< AIG.checkSat be lit
            let stats = solverStats "ABC" (scSharedSize t0)
            return (satRes, stats)


getModel ::
  Show name =>
  [(name, FiniteType)] ->
  AIG.SatResult ->
  IO (Maybe [(name, FirstOrderValue)])
getModel shapes satRes =
  case satRes of
    AIG.Unsat -> return Nothing

    AIG.Sat cex -> do
      case liftCexBB (map snd shapes) cex of
        Left err -> fail ("Can't parse counterexample: " ++ err)
        Right vs

          | length shapes == length vs ->
            return (Just (zip argNames (map toFirstOrderValue vs)))

          | otherwise ->
              fail $ unwords [ "ABC SAT results do not match expected arguments"
                             , show argNames, show vs]

    AIG.SatUnknown -> fail "Unknown result from ABC"
  where argNames = map fst shapes

