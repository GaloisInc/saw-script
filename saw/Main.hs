{-# LANGUAGE CPP #-}
{- |
Module      : Main
Description :
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}
module Main where

import Control.Exception
import Control.Monad
import Data.Maybe

import System.IO
import System.Console.GetOpt
import System.Environment
import System.Directory

import SAWScript.Options
import SAWScript.Utils
import SAWScript.Interpreter (processFile)
import qualified SAWScript.REPL as REPL
import SAWScript.Version (shortVersionText)
import SAWScript.Value (AIGProxy(..))
#ifdef USE_BUILTIN_ABC
import qualified Data.ABC.GIA as GIA
#else
import qualified Data.AIG as AIG
#endif

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  argv <- getArgs
  case getOpt Permute options argv of
    (opts, files, []) -> do
      opts' <- foldl (>>=) (return defaultOptions) opts
      opts'' <- processEnv opts'
      case (summaryFile opts'', summaryFormat opts'') of
        (Just _, Just _) -> return ()
        (Nothing, Nothing) -> return ()
        _ -> err opts'' "Error: the '-s' option must be used in conjunction with the '-f' option to specify an output format."
      {- We have two modes of operation: batch processing, handled in
      'SAWScript.ProcessFile', and a REPL, defined in 'SAWScript.REPL'. -}
      case files of
        _ | showVersion opts'' -> hPutStrLn stderr shortVersionText
        _ | showHelp opts'' -> err opts'' (usageInfo header options)
        [] -> checkZ3 opts'' *> REPL.run opts''
        _ | runInteractively opts'' -> checkZ3 opts'' *> REPL.run opts''
        [file] -> checkZ3 opts'' *>
#if USE_BUILTIN_ABC
          processFile (AIGProxy GIA.proxy) opts'' file `catch`
#else
          processFile (AIGProxy AIG.basicProxy) opts'' file `catch`
#endif
          (\(ErrorCall msg) -> err opts'' msg)
        (_:_) -> err opts'' "Multiple files not yet supported."
    (_, _, errs) -> do hPutStrLn stderr (concat errs ++ usageInfo header options)
                       exitProofUnknown
  where header = "Usage: saw [OPTION...] [-I | file]"
        checkZ3 opts = do
          p <- findExecutable "z3"
          unless (isJust p)
            $ err opts "Error: z3 is required to run SAW, but it was not found on the system path."
        err opts msg = do
          when (verbLevel opts >= Error)
            (hPutStrLn stderr msg)
          exitProofUnknown
