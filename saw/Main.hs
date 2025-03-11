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
import Data.Maybe (fromMaybe)
import Text.Read (readMaybe)

import System.Console.GetOpt
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.IO

import GHC.IO.Encoding (setLocaleEncoding)

import SAWCentral.Options
import SAWCentral.Utils
import SAWScript.Interpreter (processFile)
import qualified SAWScript.REPL as REPL
import qualified SAWScript.REPL.Haskeline as REPL
import qualified SAWScript.REPL.Monad as REPL
import SAWCentral.Value (AIGProxy(..))
import SAWCentral.SolverCache
import SAWCentral.SolverVersions
import SAWVersion.Version (shortVersionText)
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
      setBatchFile f opts = return opts { batchFile = Just f }
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

    reqArg setBatchFile "B" "batch" "<filename>"
            "Run <filename> as if it were typed into the REPL",

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

-- | Variant version of System.Console.GetOpt.usageInfo. Should be
-- fully general if anyone wants to reuse it elsewhere.
--
-- The option descriptions are generated in a two-column format with
-- options on the left and descriptions on the right. (This differs
-- from the standard usageInfo, which generates three columns.)
--
-- Oversize options that spill into the right-hand column are
-- specifically tolerated.
--
-- Newlines in the option description text will be honored.
--
-- The second argument rightPos is column position where the
-- right-hand column starts. 32 is a good default to use in the
-- absence of other criteria.
--
-- The third argument optionDescs is the program's list of option
-- descriptions.
--
-- The first argument header and last argument footer are each zero or
-- more lines to prepend before, or append after, the generated option
-- descriptions, respectively.
--
usageInfo' :: [String] -> Int -> [OptDescr a] -> [String] -> String
usageInfo' header rightPos optionDescs footer =
    let
        -- Allow two characters as a gutter between columns.
        leftMax = rightPos - 2

        -- Indent some right-column text for when we have nothing in
        -- the left column.
        indent txt = take rightPos (repeat ' ') ++ txt

        -- Pad some left-column text for appending the right-column
        -- text.
        pad txt = take rightPos (txt ++ repeat ' ')

        -- Generate the text lines for an option.
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
                        -- first line, prepend two spaces
                        (groups, "  " ++ txt)
                    else if length current + 2 + length txt <= leftMax then
                        -- this option (including a comma) will fit on this line
                        (groups, current ++ ", " ++ txt)
                    else
                        -- start a new line, prepend four spaces
                        (current : groups, "    " ++ txt)
                (firstgroups, lastgroup) =
                    foldl collect ([], "") $ shorts' ++ longs'
                optlines = reverse $
                    if lastgroup == "" then firstgroups
                    else lastgroup : firstgroups

                -- Split the description on \n so we can have long descriptions.
                -- (These are the lines for the right column.)
                desclines = lines descr

                -- Pad the shorter column with blanks.
                numlines = max (length optlines) (length desclines)
                optlines' = take numlines $ optlines ++ repeat ""
                desclines' = take numlines $ desclines ++ repeat ""

                -- Try to paste columns together. Fail only if the
                -- left column intrudes into the right column in a
                -- line where there's actually text in the right
                -- column.
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

        -- Collect all the option lines.
        optionLines = concatMap printOption optionDescs
    in
    -- Wrap in the header and footer.
    unlines $ header ++ optionLines ++ footer

-- | Construct the usage message.
--
-- Don't use the usage message produced by System.Console.GetOpt
-- (usageInfo). It tries to print in three columns (short option, long
-- option, description) and this comes out irretrievably too wide
-- given --clean-mismatched-versions-solver-cache. Use our own variant
-- version instead.
usageText :: String
usageText =
    let header = [
          "Usage: saw [OPTION...] [-I | file]"
         ]
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
    -- Use 28 as the left-hand column width. This was chosen partly by
    -- eyeballing the results and partly based on the width of the
    -- verbosity descriptions in the footer above.
    usageInfo' header 28 options footer

-- Issue a top-level error and exit.
err :: Options -> String -> IO ()
err opts msg = do
  when (verbLevel opts >= Error) $
      hPutStrLn stderr msg
  exitProofUnknown

-- Issue a top-level warning.
warn :: Options -> String -> IO ()
warn opts msg = do
  when (verbLevel opts >= Warn) $
      hPutStrLn stderr msg

-- Load (and run) a saw-script file.
loadFile :: Options -> FilePath -> IO ()
loadFile opts file = do
  let aigProxy = AIGProxy AIG.compactProxy
      subsh = REPL.subshell (REPL.replBody Nothing (return ()))
      proofSubsh = REPL.proof_subshell (REPL.replBody Nothing (return ()))
  processFile aigProxy opts file (Just subsh) (Just proofSubsh)
    `catch`
    (\(ErrorCall msg) -> err opts msg)

main :: IO ()
main = do
  setLocaleEncoding utf8
  hSetBuffering stdout LineBuffering
  argv <- getArgs
  let (rawOpts, files, errs) = getOpt Permute options argv
  when (errs /= []) $ do
      hPutStrLn stderr (concat errs ++ usageText)
      exitProofUnknown

  opts <- do
      -- Eval the options, which are in IO and might fail/exit
      evaledOpts <- foldl (>>=) (return defaultOptions) rawOpts
      -- Add stuff from the environment
      processEnv evaledOpts

  --
  -- Check for the options that don't actually run.
  --

  when (showVersion opts) $ do
      hPutStrLn stderr shortVersionText
      exitSuccess

  when (showHelp opts) $
      err opts usageText

  -- blah, there should be a tidier way to write this (without
  -- incurring an incomplete match warning or indenting the whole rest
  -- of the function)
  let (doClean, cleanPath) = case cleanMisVsCache opts of
          Nothing -> (False, "")
          Just path -> (True, path)
  when doClean $ do
      when (null cleanPath) $ do
          err opts $ "Error: no path to clean.\n" ++
                     "Either give --clean-mismatched-versions-solver-cache" ++
                     " an argument or set SAW_SOLVER_CACHE_PATH"
      cache <- lazyOpenSolverCache cleanPath
      vs <- getSolverBackendVersions allBackends
      fst <$> solverCacheOp (cleanMismatchedVersionsSolverCache vs) opts cache
      exitSuccess

  -- Now we can check for z3.
  z3 <- findExecutable "z3"
  when (z3 == Nothing) $
      err opts $ "Error: z3 is required to run SAW, but it was not found" ++
                 " on the system path."

  --
  -- There are three ways we can run:
  --    interactively in the REPL;
  --    by loading a file through the REPL's command processor ("batch mode");
  --    by loading a saw-script file directly.
  --

  case batchFile opts of
      Nothing
       | runInteractively opts -> do
            when (files /= []) $
                -- XXX: would be nicer to load and then drop into the
                -- repl. That won't (usefully) work at the moment
                -- because there's no way to retrieve the context from
                -- loading a file and then feed it to the repl.
                warn opts "Warning: files loaded along with -I are ignored"
            REPL.run opts
       | [] <- files ->
            REPL.run opts
       | [file] <- files ->
            loadFile opts file
       | otherwise ->
            err opts "Multiple files not yet supported."
      Just f -> do
            when (runInteractively opts) $
                err opts "Error: -B and -I cannot be used together"
            when (files /= []) $
                err opts $ "Error: cannot load ordinary saw-script files" ++
                           " along with -B"
            REPL.runFromFile f opts
