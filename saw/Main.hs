{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ScopedTypeVariables #-}
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

import Data.Char (toLower)
import Data.Maybe (fromMaybe, isJust)
import Text.Read (readMaybe)

import System.Console.GetOpt
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.IO

import GHC.IO.Encoding (setLocaleEncoding)

import SAWScript.Options
import SAWScript.Utils
import SAWScript.Interpreter (processFile)
import qualified SAWScript.REPL as REPL
import qualified SAWScript.REPL.Haskeline as REPL
import qualified SAWScript.REPL.Monad as REPL
import SAWScript.Version (shortVersionText)
import SAWScript.Value (AIGProxy(..))
import SAWScript.SolverCache
import SAWScript.SolverVersions
import qualified Data.AIG.CompactGraph as AIG


pathDesc, pathDelim :: String

#ifdef mingw32_HOST_OS
pathDesc = "Semicolon-delimited list of paths"
pathDelim = ";"
#else
pathDesc = "Colon-delimited list of paths"
pathDelim = ":"
#endif

-- Try to read verbosity as either a string or number and default to 'Debug'.
readVerbosity :: String -> Verbosity
readVerbosity s | Just (n::Integer) <- readMaybe s =
     case n of
         0 -> Silent
         1 -> OnlyCounterExamples
         2 -> Error
         3 -> Warn
         4 -> Info
         _ -> Debug
readVerbosity s =
    case map toLower s of
        "silent"              -> Silent
        "counterexamples"     -> OnlyCounterExamples
        "onlycounterexamples" -> OnlyCounterExamples
        "error"               -> Error
        "warn"                -> Warn
        "warning"             -> Warn
        "info"                -> Info
        "debug"               -> Debug
        _                     -> Debug

-- | Table of option descriptions.
--
-- Uses IO so it can fail on invalid option arguments, and also so it
-- can get at the process environment.
--
options :: [OptDescr (Options -> IO Options)]
options =
  let
      addImportPath p opts =
          return opts { importPath = importPath opts ++ splitSearchPath p }
      addClassPath p opts =
          return opts { classPath = classPath opts ++ splitSearchPath p }
      addJarList p opts =
          return opts { jarList = jarList opts ++ splitSearchPath p }
      addJavaBinDirs p opts =
          return opts { javaBinDirs = javaBinDirs opts ++ splitSearchPath p }
      setVerbosity v opts =
          -- TODO: now that we're in IO we can do something if a bogus
          -- verbosity is given
          let verb = readVerbosity v in
          return opts { verbLevel = verb, printOutFn = printOutWith verb }
      setSimVerbose v opts = return opts { simVerbose = read v }
      setDetectVacuity opts = return opts { detectVacuity = True }
      setExtraChecks opts = return opts { extraChecks = True }
      setRunInteractively opts = return opts { runInteractively = True }
      setShowHelp opts = return opts { showHelp = True }
      setShowVersion opts = return opts { showVersion = True }
      setPrintShowPos opts = return opts { printShowPos = True }
      clearUseColor opts = return opts { useColor = False }
      setCleanMisVsCache mb_path opts = do
          mb_env_path <- lookupEnv "SAW_SOLVER_CACHE_PATH"
          let path = fromMaybe (fromMaybe "" mb_env_path) mb_path
          return opts { cleanMisVsCache = Just path }
      setSummaryFile file opts = return opts { summaryFile = Just file }
      setSummaryFormat fmt opts = case fmt of
          "json" -> return opts { summaryFormat = JSON }
          "pretty" -> return opts { summaryFormat = Pretty }
          _ -> do
              hPutStrLn stderr $ "Error: the argument of the '-f' option" ++
                                 " must be either 'json' or 'pretty'"
              exitFailure
  in
  [ Option "h?" ["help"]
    (NoArg setShowHelp)
    "Print this help message"
  , Option "V" ["version"]
    (NoArg setShowVersion)
    "Show the version of the SAWScript interpreter"
  , Option "c" ["classpath"]
    (ReqArg addClassPath "path")
    pathDesc
  , Option "i" ["import-path"]
    (ReqArg addImportPath "path")
    pathDesc
  , Option "" ["detect-vacuity"]
    (NoArg setDetectVacuity)
    "Checks and warns the user about contradictory assumptions. (default: false)"
  , Option "t" ["extra-type-checking"]
    (NoArg setExtraChecks)
    "Perform extra type checking of intermediate values"
  , Option "I" ["interactive"]
    (NoArg setRunInteractively)
    "Run interactively (with a REPL)"
  , Option "j" ["jars"]
    (ReqArg addJarList "path")
    pathDesc
  , Option "b" ["java-bin-dirs"]
    (ReqArg addJavaBinDirs "path")
    pathDesc
  , Option [] ["output-locations"]
    (NoArg setPrintShowPos)
     "Show the source locations that are responsible for output."
  , Option "d" ["sim-verbose"]
    (ReqArg setSimVerbose "num")
    "Set simulator verbosity level"
  , Option "v" ["verbose"]
    (ReqArg setVerbosity
     "<num 0-5 | 'silent' | 'counterexamples' | 'error' | 'warn' | 'info' | 'debug'>"
    )
    "Set verbosity level"
  , Option [] ["no-color"]
    (NoArg clearUseColor)
    "Disable ANSI color and Unicode output"
  , Option [] ["clean-mismatched-versions-solver-cache"]
    (OptArg setCleanMisVsCache "path")
    "Run clean_mismatched_versions_solver_cache with the cache given, or else the value of SAW_SOLVER_CACHE_PATH, then exit"
  , Option "s" ["summary"]
    (ReqArg setSummaryFile "filename")
    "Write a verification summary to the provided filename"
  , Option "f" ["summary-format"]
    (ReqArg setSummaryFormat
     "either 'json' or 'pretty'")
    "Specify the format in which the verification summary should be written in ('json' or 'pretty'; defaults to 'json')"
  ]

main :: IO ()
main = do
  setLocaleEncoding utf8
  hSetBuffering stdout LineBuffering
  argv <- getArgs
  case getOpt Permute options argv of
    (opts, files, []) -> do
      opts' <- foldl (>>=) (return defaultOptions) opts
      opts'' <- processEnv opts'
      {- We have two modes of operation: batch processing, handled in
      'SAWScript.ProcessFile', and a REPL, defined in 'SAWScript.REPL'. -}
      case files of
        _ | showVersion opts'' -> hPutStrLn stderr shortVersionText
        _ | showHelp opts'' -> err opts'' (usageInfo header options)
        _ | Just path <- cleanMisVsCache opts'' -> doCleanMisVsCache opts'' path
        [] -> checkZ3 opts'' *> REPL.run opts''
        _ | runInteractively opts'' -> checkZ3 opts'' *> REPL.run opts''
        [file] -> checkZ3 opts'' *>
          processFile (AIGProxy AIG.compactProxy) opts'' file subsh proofSubsh`catch`
          (\(ErrorCall msg) -> err opts'' msg)
        (_:_) -> err opts'' "Multiple files not yet supported."
    (_, _, errs) -> do hPutStrLn stderr (concat errs ++ usageInfo header options)
                       exitProofUnknown
  where subsh = Just (REPL.subshell (REPL.replBody Nothing (return ())))
        proofSubsh = Just (REPL.proof_subshell (REPL.replBody Nothing (return ())))
        header = "Usage: saw [OPTION...] [-I | file]"
        checkZ3 opts = do
          p <- findExecutable "z3"
          unless (isJust p)
            $ err opts "Error: z3 is required to run SAW, but it was not found on the system path."
        err opts msg = do
          when (verbLevel opts >= Error)
            (hPutStrLn stderr msg)
          exitProofUnknown
        doCleanMisVsCache opts path | not (null path) = do
          cache <- lazyOpenSolverCache path
          vs <- getSolverBackendVersions allBackends
          fst <$> solverCacheOp (cleanMismatchedVersionsSolverCache vs) opts cache
        doCleanMisVsCache opts _ =
          err opts "Error: either --clean-mismatched-versions-solver-cache must be given an argument or SAW_SOLVER_CACHE_PATH must be set"

