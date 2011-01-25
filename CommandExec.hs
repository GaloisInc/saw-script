module SAWScript.CommandExec where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import SAWScript.MethodAST
import qualified SBVModel.SBV as SBV
import SBVParser
import Symbolic
import Utils.IOStateT

{-
-- | Returns type of SBV program.
parseSBVType :: RecordDefMap -> SBVPgm -> ([DagType], DagType)
-- | Returns strings appearing in SBV type.
sbvRecords :: SBVPrm -> [Set String]
sbvRecords (SBVPgm (_,ir,_c, _v, _w, _ops)) = parseType ir
  where parseType (TVar _) = []
        parseType (TInt _) = []
        parseType (TApp _ tps) = concat (parseType tps)
        parseType (TRecord (unzip -> (names,schemes))) =
          Set.fromList names : rest
         where rest = concat $ map (parseType . schemeType) schemes

-}


data ExecutorState = ES {
   -- | Flag that indicates if verification commands should be executed.
    runVerification :: Bool
    -- | Maps field names to corresponding record definition.
  , recordDefs :: Map (Set String) SymRecDef
    -- | Maps function names read in from SBV file into corresponding
    -- operator definition.
  , sbvFns :: Map String OpDef
    -- | Maps rule names to corresponding rule.
  , rules :: Map String Rule
    -- | Set of currently enabled rules.
  , enabledRules :: Set String
  } deriving (Show)

type Executor a = StateT ExecutorState OpSession a

-- Given a file path, this returns the verifier commands in the file,
-- or throws an exception.
parseFile :: FilePath -> IO [VerifierCommand]
parseFile = undefined

execute :: VerifierCommand -> Executor ()
execute (ImportCommand path) = do
  -- Disable run verification.
  rv <- gets runVerification
  modify $ \s -> s { runVerification = False }
  -- Execute commands
  cmds <- liftIO $ parseFile path
  mapM_ execute cmds 
  -- Reset run verification.
  modify $ \s -> s { runVerification = rv }
execute (DefineRecord name fields) = do
  undefined
execute (LoadSBVFunction opName path) = do
  sbv <- liftIO $ SBV.loadSBV path
  let recordFn args = undefined
      uninterpFns = undefined
  (op, WEF opFn) <- lift $ parseSBVOp recordFn uninterpFns opName opName defaultPrec sbv
  modify $ \s -> s { sbvFns = Map.insert opName op (sbvFns s) }
execute (DefineJavaMethodSpec jvm) = do
  undefined
execute (DefineRule name lhs rhs) = do
  undefined
execute (DisableRule name) = do
  undefined
execute (EnableRule name) = do
  undefined
execute (BlastJavaMethodSpec specName) = do
  undefined
execute (ReduceJavaMethodSpec specName) = do
  undefined
