module SAWScript
  ( llvm_load_module
  , cryptol_load
  , runSAW
  , defaultOptions
  , AIGProxy(..)
  )
where

import SAWScript.Builtins
import SAWScript.Interpreter
import SAWScript.LLVMBuiltins
import SAWScript.Options
import SAWScript.Value

runSAW :: AIGProxy -> Options -> TopLevel () -> IO ()
runSAW proxy opts a = do
  (_, ro, rw) <- buildTopLevelEnv proxy opts
  fst <$> runTopLevel a ro rw
