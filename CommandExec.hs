module SAWScript.CommandExec where

import SAWScript.MethodAST
import Utils.IOStateT

data ExecutorState = ES
  { runVerification :: Bool
  } deriving (Eq, Ord, Show)

type Executor a = StateT ExecutorState IO a

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
  cmds <- lift (parseFile path)
  mapM_ execute cmds 
  -- Reset run verification.
  modify $ \s -> s { runVerification = rv }
execute (LoadSBVFunction name path) = do
  undefined
execute (DeclareJavaMethodSpec jvm) = do
  undefined
execute (BlastJavaMethodSpec specName) = do
  undefined
execute (ReduceJavaMethodSpec specName rules) = do
  undefined
