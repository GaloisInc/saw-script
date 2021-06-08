module SAWScript.Prover.ABC
  ( proveABC
  , w4AbcVerilog
  , abcSatExternal
  ) where

import Control.Monad (unless)
import Control.Monad.IO.Class
import Data.Char (isSpace)
import Data.List (isPrefixOf)
import qualified Data.Map as Map
import Data.Maybe
import           Data.Set (Set)
import qualified Data.Text as Text
import Text.Read (readMaybe)

import System.Directory
import System.IO
import System.IO.Temp (emptySystemTempFile)
import System.Process (readProcessWithExitCode)

import qualified Data.AIG as AIG

import           Verifier.SAW.FiniteValue
import           Verifier.SAW.Name
import           Verifier.SAW.SharedTerm
import qualified Verifier.SAW.Simulator.BitBlast as BBSim

import SAWScript.Proof(Prop, propToSATQuery, propSize, goalProp, ProofGoal, goalType, goalNum, CEX)
import SAWScript.Prover.SolverStats (SolverStats, solverStats)
import qualified SAWScript.Prover.Exporter as Exporter
import SAWScript.Prover.Util (liftCexBB)

-- crucible-jvm
-- TODO, very weird import
import Lang.JVM.ProcessUtils (readProcessExitIfFailure)


-- | Bit-blast a proposition and check its validity using ABC.
proveABC ::
  (AIG.IsAIG l g) =>
  AIG.Proxy l g ->
  SharedContext ->
  Prop ->
  IO (Maybe CEX, SolverStats)
proveABC proxy sc goal =
  do satq <- propToSATQuery sc mempty goal
     BBSim.withBitBlastedSATQuery proxy sc mempty satq $ \be lit shapes ->
       do let (ecs,fts) = unzip shapes
          res <- getModel ecs fts =<< AIG.checkSat be lit
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


w4AbcVerilog :: MonadIO m =>
  Set VarIndex ->
  SharedContext ->
  Bool ->
  Prop ->
  m (Maybe CEX, SolverStats)
w4AbcVerilog unints sc _hashcons goal = liftIO $
       -- Create temporary files
    do let tpl = "abc_verilog.v"
           tplCex = "abc_verilog.cex"
       tmp <- emptySystemTempFile tpl
       tmpCex <- emptySystemTempFile tplCex

       satq <- propToSATQuery sc unints goal
       (argNames, argTys) <- Exporter.writeVerilogSAT sc tmp satq

       -- Run ABC and remove temporaries
       let execName = "abc"
           args = ["-q", "%read " ++ tmp ++"; %blast; &sweep -C 5000; &syn4; &cec -m; write_aiger_cex " ++ tmpCex]
       (_out, _err) <- readProcessExitIfFailure execName args
       cexText <- readFile tmpCex
       removeFile tmp
       removeFile tmpCex

       -- Parse and report results
       let stats = solverStats "abc_verilog" (propSize goal)
       res <- if all isSpace cexText
              then return Nothing
                      -- NB: reverse bits to get bit-order convention right
              else do bits <- reverse <$> parseAigerCex cexText
                      case liftCexBB (reverse argTys) bits of
                        Left parseErr -> fail parseErr
                        Right vs -> return $ Just model
                          where model = zip argNames (map toFirstOrderValue (reverse vs))
       return (res, stats)

parseAigerCex :: String -> IO [Bool]
parseAigerCex text =
  case lines text of
    [_, cex] ->
      case words cex of
        [bits, _] -> mapM bitToBool bits
        _ -> fail $ "invalid counterexample line: " ++ cex
    _ -> fail $ "invalid counterexample text: " ++ text
  where
    bitToBool '0' = return False
    bitToBool '1' = return True
    bitToBool c   = fail ("invalid bit: " ++ [c])


abcSatExternal :: MonadIO m =>
  (AIG.IsAIG l g) =>
  AIG.Proxy l g ->
  SharedContext ->
  Bool ->
  String ->
  [String] ->
  ProofGoal ->
  m (Maybe CEX, SolverStats)
abcSatExternal proxy sc doCNF execName args g = liftIO $
  do satq <- propToSATQuery sc mempty (goalProp g)
     let cnfName = goalType g ++ show (goalNum g) ++ ".cnf"
     (path, fh) <- openTempFile "." cnfName
     hClose fh -- Yuck. TODO: allow writeCNF et al. to work on handles.

     let args' = map replaceFileName args
         replaceFileName "%f" = path
         replaceFileName a = a

     BBSim.withBitBlastedSATQuery proxy sc mempty satq $ \be l shapes -> do
       variables <- (if doCNF then AIG.writeCNF else writeAIGWithMapping) be l path
       (_ec, out, err) <- readProcessWithExitCode execName args' ""
       removeFile path
       unless (null err) $
         print $ unlines ["Standard error from SAT solver:", err]
       let ls = lines out
           sls = filter ("s " `isPrefixOf`) ls
           vls = filter ("v " `isPrefixOf`) ls
       let stats = solverStats ("external SAT:" ++ execName) (propSize (goalProp g))
       case (sls, vls) of
         (["s SATISFIABLE"], _) -> do
           let bs = parseDimacsSolution variables vls
           let r = liftCexBB (map snd shapes) bs
               argNames = map (Text.unpack . toShortName . ecName . fst) shapes
               ecs = map fst shapes
           case r of
             Left msg -> fail $ "Can't parse counterexample: " ++ msg
             Right vs
               | length ecs == length vs -> do
                 return (Just (zip ecs (map toFirstOrderValue vs)), stats)
               | otherwise -> fail $ unwords ["external SAT results do not match expected arguments", show argNames, show vs]
         (["s UNSATISFIABLE"], []) ->
           return (Nothing, stats)
         _ -> fail $ "Unexpected result from SAT solver:\n" ++ out

parseDimacsSolution :: [Int]    -- ^ The list of CNF variables to return
                    -> [String] -- ^ The value lines from the solver
                    -> [Bool]
parseDimacsSolution vars ls = map lkup vars
  where
    vs :: [Int]
    vs = concatMap (filter (/= 0) . mapMaybe readMaybe . tail . words) ls
    varToPair n | n < 0 = (-n, False)
                | otherwise = (n, True)
    assgnMap = Map.fromList (map varToPair vs)
    lkup v = Map.findWithDefault False v assgnMap

writeAIGWithMapping :: AIG.IsAIG l g => g s -> l s -> FilePath -> IO [Int]
writeAIGWithMapping be l path = do
  nins <- AIG.inputCount be
  AIG.writeAiger path (AIG.Network be [l])
  return [1..nins]
