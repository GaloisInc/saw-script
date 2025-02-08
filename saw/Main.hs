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
pathDesc = "semicolon-delimited list of directories"
pathDelim = ";"
#else
pathDesc = "colon-delimited list of directories"
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

      -- wrappers for constructing the table entries more concisely
      noArg short long dispatch descr =
          Option short [long] (NoArg dispatch) descr
      optArg short long argdesc dispatch descr =
          Option short [long] (OptArg dispatch argdesc) descr
      reqArg short long argdesc dispatch descr =
          Option short [long] (ReqArg dispatch argdesc) descr
  in
  [
    noArg "h?" "help"    setShowHelp "Print this help message",
    noArg "V"  "version" setShowVersion "Print the SAWScript version and exit",
    reqArg "c" "classpath" "<path>" addClassPath "Add <path> to the Java classpath",
    reqArg "i" "import-path" "<path>" addImportPath "Add <path> to the SAWScript import path",
    noArg "" "detect-vacuity" setDetectVacuity "Check for contradictory assumptions\n  (default false)",
    noArg "t" "extra-type-checking" setExtraChecks "Perform extra type checking of intermediate values\n  (default false)",
    noArg "I" "interactive" setRunInteractively "Run interactively (with a REPL)",
    reqArg "j" "jars" "<path>" addJarList "Add <path> to the Java JAR list",
    reqArg "b" "java-bin-dirs" "<path>" addJavaBinDirs "Add <path> to the Java binary directory path",
    noArg "" "output-locations" setPrintShowPos "Show source locations triggering output",
    reqArg "d" "sim-verbose" "<num>" setSimVerbose "Set simulator verbosity level",
    reqArg "v" "verbose" "<verbosity>" setVerbosity "Set SAWScript verbosity level",
    noArg "" "no-color" clearUseColor "Disable ANSI color and Unicode output",
    optArg "" "clean-mismatched-versions-solver-cache" "<dir>"
      setCleanMisVsCache
      "Purge the solver cache and exit",
    reqArg "s" "summary" "<filename>" setSummaryFile "Write a verification summary to the given file",
    reqArg "f" "summary-format" "json|pretty" setSummaryFormat
       "Format for verification summary; default is 'json'"
  ]

usageInfo' :: String
usageInfo' =
    -- Note: the second text column begins on column 28, which leaves
    -- enough room for the verbosity descriptions while leaving as
    -- much space as possible on the right.
    let leftMax = 26
        rightPos = 28
        indent txt = (take rightPos $ repeat ' ') ++ txt
        pad txt = take rightPos (txt ++ repeat ' ')

        header = "Usage: saw [OPTION...] [-I | file]"
        -- Don't use the usage message produced by System.Console.GetOpt
        -- (usageInfo). It tries to print in three columns (short option,
        -- long option, description) and this comes out irretrievably too
        -- wide given --clean-mismatched-versions-solver-cache. Extract
        -- our own from the options table instead.
        printOption (Option shorts longs optinfo descr) =
            let
                -- First generate the option strings for the left column.
                printShort c = case optinfo of
                    NoArg _ -> ['-', c]
                    OptArg _ optdesc -> ['-', c, ' ', '['] ++ optdesc ++ "]"
                    ReqArg _ optdesc -> ['-', c, ' '] ++ optdesc
                printLong txt = case optinfo of
                    NoArg _ -> "--" ++ txt
                    OptArg _ optdesc -> "--" ++ txt ++ "[=" ++ optdesc ++ "]"
                    ReqArg _ optdesc -> "--" ++ txt ++ "=" ++ optdesc
                shorts' = map printShort shorts
                longs' = map printLong longs
                -- Group as many as will fit in the column at once.
                collect (groups, current) txt =
                    if current == "" then
                        (groups, "  " ++ txt)
                    else if length current + 2 + length txt <= leftMax then
                        (groups, current ++ ", " ++ txt)
                    else
                        (current : groups, "    " ++ txt)
                (firstgroups, lastgroup) =
                    foldl collect ([], "") $ shorts' ++ longs'
                optlines = reverse $
                    if lastgroup == "" then firstgroups
                    else lastgroup : firstgroups

                -- Split the description on \n so we can have long descriptions.
                desclines = lines descr

                -- Pad the shorter column with blanks.
                numlines = max (length optlines) (length desclines)
                optlines' = take numlines $ optlines ++ repeat ""
                desclines' = take numlines $ desclines ++ repeat ""

                -- Try to paste columns together.
                tryPasteColumns opt desc =
                    if desc == "" then Just opt
                    else if length opt <= leftMax then Just (pad opt ++ desc)
                    else Nothing
            in
            -- See if we can paste the columns successfully.
            case zipWithM tryPasteColumns optlines' desclines' of
                Nothing ->
                    -- No. Emit the option names in the left column
                    -- followed by the description in the right column.
                    optlines ++ map indent desclines
                Just someLines ->
                    -- Yes. Run with it
                    someLines
        optionLines = concatMap printOption options
        footer = [
          "where",
          "  <path> is a " ++ pathDesc,
          "  <verbosity> is 0-5 or one of:",
          "      silent (0)            Suppress output",
          "      counterexamples (1)   Print counterexamples only",
          "      error (2)             Include error messages",
          "      warn (3)              Include warnings",
          "      info (4)              Include informational messages",
          "      debug (5)             Include debug messages",
          "",
          "The --clean-mismatched-versions-solver-cache option removes entries",
          "from the given solver cache that aren't the current solver cache",
          "format version. The default cache is given by SAW_SOLVER_CACHE_PATH."
         ]
    in
    unlines $ header : optionLines ++ footer

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
        _ | showHelp opts'' -> err opts'' usageInfo'
        _ | Just path <- cleanMisVsCache opts'' -> doCleanMisVsCache opts'' path
        [] -> checkZ3 opts'' *> REPL.run opts''
        _ | runInteractively opts'' -> checkZ3 opts'' *> REPL.run opts''
        [file] -> checkZ3 opts'' *>
          processFile (AIGProxy AIG.compactProxy) opts'' file subsh proofSubsh`catch`
          (\(ErrorCall msg) -> err opts'' msg)
        (_:_) -> err opts'' "Multiple files not yet supported."
    (_, _, errs) -> do hPutStrLn stderr (concat errs ++ usageInfo')
                       exitProofUnknown
  where subsh = Just (REPL.subshell (REPL.replBody Nothing (return ())))
        proofSubsh = Just (REPL.proof_subshell (REPL.replBody Nothing (return ())))
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

