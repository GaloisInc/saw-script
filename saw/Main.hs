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

-- Try to read verbosity as either a string or number.
readVerbosity :: String -> Maybe Verbosity
readVerbosity s | Just (n::Integer) <- readMaybe s =
     case n of
         0 -> Just Silent
         1 -> Just OnlyCounterExamples
         2 -> Just Error
         3 -> Just Warn
         4 -> Just Info
         5 -> Just Debug
         _ -> Nothing
readVerbosity s =
    case map toLower s of
        "silent"              -> Just Silent
        "counterexamples"     -> Just OnlyCounterExamples
        "onlycounterexamples" -> Just OnlyCounterExamples
        "error"               -> Just Error
        "warn"                -> Just Warn
        "warning"             -> Just Warn
        "info"                -> Just Info
        "debug"               -> Just Debug
        _                     -> Nothing

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
      setVerbosity v opts = case readVerbosity v of
          Nothing -> do
              hPutStrLn stderr $ "-v: Invalid verbosity level " ++ v ++
                                 "; try --help"
              exitFailure
          Just verb ->
              return opts { verbLevel = verb, printOutFn = printOutWith verb }
      setSimVerbose v opts = case readMaybe v of
          Nothing -> do
              hPutStrLn stderr $ "-d: Invalid number " ++ v
              exitFailure
          Just verb
           | verb < 0 -> do
              hPutStrLn stderr $ "-d: Invalid verbosity " ++ v
              exitFailure
           | otherwise ->
              return opts { simVerbose = verb }
      setDetectVacuity opts = return opts { detectVacuity = True }
      setExtraChecks opts = return opts { extraChecks = True }
      setRunInteractively opts = return opts { runInteractively = True }
      setShowHelp opts = return opts { showHelp = True }
      setShowVersion opts = return opts { showVersion = True }
      setPrintShowPos opts = return opts { printShowPos = True }
      clearUseColor opts = return opts { useColor = False }
      setCleanCache mb_path opts = do
          mb_env_path <- lookupEnv "SAW_SOLVER_CACHE_PATH"
          let path = fromMaybe (fromMaybe "" mb_env_path) mb_path
          return opts { cleanMisVsCache = Just path }
      setSummaryFile file opts = return opts { summaryFile = Just file }
      setSummaryFormat fmt opts = case fmt of
          "json" -> return opts { summaryFormat = JSON }
          "pretty" -> return opts { summaryFormat = Pretty }
          _ -> do
              hPutStrLn stderr $ "-f: Invalid format " ++ fmt ++ "; expected" ++
                                 " either 'json' or 'pretty'"
              exitFailure

      -- wrappers for constructing the table entries more concisely
      noArg dispatch short long descr =
          Option short [long] (NoArg dispatch) descr
      optArg dispatch short long argname descr =
          Option short [long] (OptArg dispatch argname) descr
      reqArg dispatch short long argname descr =
          Option short [long] (ReqArg dispatch argname) descr
  in
  [
    noArg setShowHelp "h?" "help"
            "Print this help message",

    reqArg addJavaBinDirs "b" "java-bin-dirs" "<path>"
            "Add <path> to the Java binary directory path",

    reqArg addClassPath "c" "classpath" "<path>"
            "Add <path> to the Java classpath",

    reqArg setSimVerbose "d" "sim-verbose" "<num>"
            "Set simulator verbosity level",

    reqArg setSummaryFormat "f" "summary-format" "json|pretty"
            "Format for verification summary; default is 'json'",

    noArg setRunInteractively "I" "interactive"
            "Run interactively (with a REPL)",

    reqArg addImportPath "i" "import-path" "<path>"
            "Add <path> to the SAWScript import path",

    reqArg addJarList "j" "jars" "<path>"
            "Add <path> to the Java JAR list",

    reqArg setSummaryFile "s" "summary" "<filename>"
            "Write a verification summary to the given file",

    noArg setExtraChecks "t" "extra-type-checking" $
            "Perform extra type checking of intermediate values\n" ++
            "  (default false)",

    noArg setShowVersion "V" "version"
            "Print the SAWScript version and exit",

    reqArg setVerbosity "v" "verbose" "<verbosity>"
            "Set SAWScript verbosity level",

    optArg setCleanCache "" "clean-mismatched-versions-solver-cache" "<dir>"
            "Purge the solver cache and exit",

    noArg setDetectVacuity "" "detect-vacuity" $
            "Check for contradictory assumptions\n" ++
            "  (default false)",

    noArg clearUseColor "" "no-color"
            "Disable ANSI color and Unicode output",

    noArg setPrintShowPos "" "output-locations"
            "Show source locations triggering output"
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
                    OptArg _ argname -> ['-', c, ' ', '['] ++ argname ++ "]"
                    ReqArg _ argname -> ['-', c, ' '] ++ argname
                printLong txt = case optinfo of
                    NoArg _ -> "--" ++ txt
                    OptArg _ argname -> "--" ++ txt ++ "[=" ++ argname ++ "]"
                    ReqArg _ argname -> "--" ++ txt ++ "=" ++ argname
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

