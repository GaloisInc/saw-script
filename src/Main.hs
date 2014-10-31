module Main where

import Control.Exception
import Data.List

import System.Exit
import System.IO
import System.Console.GetOpt
import System.Environment

import SAWScript.Options
import SAWScript.ProcessFile (processFile)
import qualified SAWScript.REPL as REPL

main :: IO ()
main = do
  argv <- getArgs
  case getOpt Permute options argv of
    (opts, files, []) -> do
      let opts' = foldl' (flip id) defaultOptions opts
      opts'' <- processEnv opts'
      {- We have two modes of operation: batch processing, handled in
      'SAWScript.ProcessFile', and a REPL, defined in 'SAWScript.REPL'. -}
      case (runInteractively opts'', files) of
        (_, []) -> REPL.run opts''
        (False, [file]) -> processFile opts'' file
                           `catch`
                           (\(ErrorCall msg) -> err msg)
        (False, _:_) -> err "Running multiple files not yet supported."
        (True, _:_) -> err ("Unable to handle files in interactive mode"
                            ++ usageInfo header options)
    (_, _, errs)      -> err (concat errs ++ usageInfo header options)
  where header = "Usage: saw [OPTION...] [-I | files...]"
        err msg = hPutStrLn stderr msg >> exitFailure
