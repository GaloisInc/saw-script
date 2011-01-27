{-# LANGUAGE DeriveDataTypeable #-}
module SAWScript.CommandExec(runProofs) where

import Control.Exception
import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable
import Prelude hiding (catch)

import qualified Execution.Codebase as JSS
import Simulation as JSS

import MethodSpec
import SAWScript.Utils (Pos(..), SSOpts(..))
import SAWScript.MethodAST
import qualified SBVModel.SBV as SBV
import SBVParser
import Symbolic
import Utils.IOStateT
import System.Exit

-- This is the entry point from the front-end
-- The implicit assumption is that you can either return back with an exitCode;
-- or never come back with a proper call to exitWith..
runProofs :: SSOpts -> SSPgm -> IO ExitCode
runProofs ssOpts pgm = do putStrLn $ "I will run proofs starting at: " ++ show (entryPoint ssOpts)
                          putStrLn $ "There are " ++ show (Map.size pgm) ++ " script(s) to be processed."
                          return ExitSuccess

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
    -- | Java codebase
    codeBase :: JSS.Codebase 
    -- | Flag that indicates if verification commands should be executed.
  , runVerification :: Bool
    -- | Maps file paths to verifier commands.
  , parsedFiles :: Map FilePath [VerifierCommand]
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

-- | Class of exceptions thrown by SBV parser.
data ExecException = ExecException Pos String
  deriving (Show, Typeable)
 
instance Exception ExecException

type Executor a = StateT ExecutorState (OpSession IO) a

-- | Given a file path, this returns the verifier commands in the file,
-- or throws an exception.
parseFile :: FilePath -> Executor [VerifierCommand]
parseFile path = do
  m <- gets parsedFiles
  case Map.lookup path m of
    Nothing -> error $ "internal: Could not find file " ++ path
    Just cmds -> return cmds

parseASTTerm :: RewriteTerm -> TermCtor
parseASTTerm _ = undefined

-- | Return true if rule with given name already exists.
ruleExists :: String -> Executor Bool
ruleExists name = fmap (Map.member name) $ gets rules

-- | Return true if rule with given name is enabled.
ruleEnabled :: String -> Executor Bool
ruleEnabled name = fmap (Set.member name) $ gets enabledRules

-- | Execute commands from given file.
execCommands :: JSS.Codebase
             -> FilePath
             -> Map FilePath [VerifierCommand]
             -> IO ()
execCommands cb initialPath parsedFiles = do
  let initState = ES {
          codeBase = cb
        , runVerification = True
        , parsedFiles  = parsedFiles
        , recordDefs   = Map.empty
        , sbvFns       = Map.empty
        , rules        = Map.empty
        , enabledRules = Set.empty
        }
      action = do cmds <- parseFile initialPath
                  mapM_ execute cmds
                  liftIO $ putStrLn "Verification succeeded!"
  catch (runOpSession (evalStateT action initState))
    (\(ExecException pos msg) -> do
        let Pos path line col = pos
        putStrLn $ "Verification Failed!\n"
        putStrLn $ path ++ ":" ++ show line ++ ":" ++ show col ++ ":"
        putStrLn $ msg)

-- | Throw exec exception in a MonadIO.
throwIOExecException :: MonadIO m => Pos -> String -> m a
throwIOExecException pos msg = liftIO $ throwIO (ExecException pos msg)

-- | Execute command 
execute :: VerifierCommand -> Executor ()
execute (ImportCommand pos path) = do
  -- Disable run verification.
  rv <- gets runVerification
  modify $ \s -> s { runVerification = False }
  -- Execute commands
  cmds <- parseFile path
  mapM_ execute cmds 
  -- Reset run verification.
  modify $ \s -> s { runVerification = rv }
execute (DefineRecord pos name fields) = do
  undefined
execute (LoadSBVFunction pos opName path) = do
  sbv <- liftIO $ SBV.loadSBV path
  let recordFn args = undefined
      uninterpFns = undefined
  (op, WEF opFn) <- lift $ parseSBVOp recordFn uninterpFns opName opName defaultPrec sbv
  modify $ \s -> s { sbvFns = Map.insert opName op (sbvFns s) }
execute (DefineJavaMethodSpec pos jvm) = do
  undefined
execute (DefineRule pos name lhs rhs) = do
  -- Check rule does not exist.
  re <- ruleExists name
  when re $ do
    throwIOExecException pos $ "The rule " ++ name ++ " has previously been defined."
  -- Parse terms.
  let tlhs = parseASTTerm lhs
      trhs = parseASTTerm rhs
  -- TODO: Check that types are equal, and check that right-hand side variables
  -- are contained in left-hand side.
  let rl = mkRuleFromCtor name tlhs trhs
  modify $ \s -> s { rules = Map.insert name rl (rules s)
                   , enabledRules = Set.insert name (enabledRules s) }
execute (DisableRule pos name) = do
  -- Check rule exists.
  re <- ruleExists name
  when (not re) $ do
    throwIOExecException pos $ "The rule " ++ name ++ " has not been defined."
  -- Check rule is enabled.
  en <- ruleEnabled name
  when (not en) $ do
    throwIOExecException pos $ "The rule " ++ name ++ " is already disabled."
  modify $ \s -> s { enabledRules = Set.delete name (enabledRules s) }
execute (EnableRule pos name) = do
  -- Check rule exists.
  re <- ruleExists name
  when (not re) $ do
    throwIOExecException pos $ "The rule " ++ name ++ " has not been defined."
  -- Check rule is disabled.
  en <- ruleEnabled name
  when en $ do
    throwIOExecException pos $ "The rule " ++ name ++ " is already enabled."
  modify $ \s -> s { enabledRules = Set.insert name (enabledRules s) }
  {-
execute (BlastJavaMethodSpec pos specName) = do
  rv <- gets runVerification
  when rv $ do
    cb <- gets codeBase
    let spec = undefined
    lift $ blastMethodSpec cb spec
execute (ReduceJavaMethodSpec pos specName) = do
  rv <- gets runVerification
  when rv $ do
    cb <- gets codeBase
    let spec :: MethodSpec SymbolicMonad
        spec = undefined
        installOverrides :: JSS.Simulator SymbolicMonad ()
        installOverrides = undefined
    lift $ redMethodSpec cb spec installOverrides $ \t -> do
      --TODO: Attempt to reduce term t.
      throwIOExecException pos $ 
        "Verification of " ++ specName ++ " failed!\n" ++
        "The remaining proof obligation is:\n  " ++ prettyTerm t
        -}
