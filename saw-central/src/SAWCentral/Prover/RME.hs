module SAWCentral.Prover.RME where

import Control.Monad.IO.Class
import qualified Data.Map as Map

import qualified Data.RME as RME

import Verifier.SAW.FiniteValue

import qualified Verifier.SAW.Simulator.RME as RME
import Verifier.SAW.SATQuery (SATQuery(..))

import SAWCentral.Proof (CEX)
import SAWCentral.Prover.Util
import SAWScript.Value

-- | Bit-blast a proposition and check its validity using RME.
proveRME ::
  SATQuery {- ^ The query to be proved -} ->
  TopLevel (Maybe CEX, String)
proveRME satq = getSharedContext >>= \sc -> liftIO $
  RME.withBitBlastedSATQuery sc Map.empty satq $ \lit shapes ->
    case RME.sat lit of
      Nothing -> return (Nothing, "RME")
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
              return (Just model, "RME")
            | otherwise -> fail $ unwords ["RME SAT results do not match expected arguments", show shapes, show vs]
