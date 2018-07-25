module SAWScript.Prover.ABC (satABC) where


import qualified Data.AIG as AIG

import           Verifier.SAW.SharedTerm
import           Verifier.SAW.TypedTerm
import           Verifier.SAW.FiniteValue
import qualified Verifier.SAW.Simulator.BitBlast as BBSim
import           Verifier.SAW.Recognizer(asPiList)

import SAWScript.Prover.Mode (ProverMode(..))
import SAWScript.Prover.SolverStats (SolverStats, solverStats)
import SAWScript.Prover.Rewrite(rewriteEqs)
import SAWScript.SAWCorePrimitives( bitblastPrimitives )
import SAWScript.Prover.Util
         (liftCexBB, bindAllExts, checkBooleanSchema)

-- | Bit-blast a @Term@ representing a theorem and check its
-- satisfiability using ABC.
satABC ::
  (AIG.IsAIG l g) =>
  AIG.Proxy l g ->
  SharedContext ->
  ProverMode ->
  Term ->
  IO (Maybe [(String,FirstOrderValue)], SolverStats)
satABC proxy sc mode t0 =
  do TypedTerm schema t <-
        (bindAllExts sc t0 >>= rewriteEqs sc >>= mkTypedTerm sc)
     checkBooleanSchema schema
     tp <- scWhnf sc =<< scTypeOf sc t
     let (args, _) = asPiList tp
         argNames = map fst args
     BBSim.withBitBlastedPred proxy sc bitblastPrimitives t $
      \be lit0 shapes ->
         do let lit = case mode of
                        CheckSat -> lit0
                        Prove    -> AIG.not lit0
            satRes <- getModel argNames shapes =<< AIG.checkSat be lit
            let stats = solverStats "ABC" (scSharedSize t0)
            return (satRes, stats)


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

