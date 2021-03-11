{- |
Module      : SAWScript.Options
Description : Datatype for saw command-line options.
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SAWScript.Options where

import Data.Char (toLower)
import Data.Time
import System.Console.GetOpt
import System.Environment
import System.FilePath
import System.Exit
import System.IO
import Text.Read (readMaybe)
import Text.Show.Functions ()

import Lang.JVM.JavaTools

-- TODO: wouldn't it be better to extract the options-processing code from this file and put it in saw/Main.hs (which already does part of the options processing)? It seems that other parts of SAW only need the datatype definition below, and not the rest.
data Options = Options
  { importPath       :: [FilePath]
  , classPath        :: [FilePath]
  , jarList          :: [FilePath]
  , javaBinDirs      :: [FilePath]
  , verbLevel        :: Verbosity
  , simVerbose       :: Int
  , detectVacuity    :: Bool
  , extraChecks      :: Bool
  , runInteractively :: Bool
  , showHelp         :: Bool
  , showVersion      :: Bool
  , printShowPos     :: Bool
  , useColor         :: Bool
  , printOutFn       :: Verbosity -> String -> IO ()
  , summaryFile      :: Maybe FilePath
  , summaryFormat    :: SummaryFormat
  } deriving (Show)

-- | Verbosity is currently a linear setting (vs a mask or tree).  Any given
-- level includes the outputs of all lower levels.
data Verbosity
  = Silent
  | OnlyCounterExamples
  | Error
  | Warn
  | Info
  | Debug
  | ExtraDebug
    deriving (Show,Eq,Ord)

data SummaryFormat
  = JSON | Pretty
  deriving (Show,Eq,Ord)

defaultOptions :: Options
defaultOptions
  = Options {
      importPath = ["."]
    , classPath = ["."]
    , jarList = []
    , javaBinDirs = []
    , verbLevel = Info
    , printShowPos = False
    , printOutFn = printOutWith Info
    , simVerbose = 1
    , detectVacuity = False
    , extraChecks = False
    , runInteractively = False
    , showHelp = False
    , showVersion = False
    , useColor = True
    , summaryFile = Nothing
    , summaryFormat = Pretty
    }

printOutWith :: Verbosity -> Verbosity -> String -> IO ()
printOutWith setting level msg
    | setting >= level = do
      t <- formatTime defaultTimeLocale "%T.%3q" <$> getCurrentTime
      putStr $ "[" ++ t ++ "] " ++ msg
    | otherwise        = return ()

printOutLn :: Options -> Verbosity -> String -> IO ()
printOutLn o v s = printOutFn o v (s ++ "\n")

options :: [OptDescr (Options -> IO Options)] -- added IO to do validation here instead of later
options =
  [ Option "h?" ["help"]
    (NoArg (\opts -> return opts { showHelp = True }))
    "Print this help message"
  , Option "V" ["version"]
    (NoArg (\opts -> return opts { showVersion = True }))
    "Show the version of the SAWScript interpreter"
  , Option "c" ["classpath"]
    (ReqArg
     (\p opts -> return opts { classPath = classPath opts ++ splitSearchPath p })
     "path"
    )
    pathDesc
  , Option "i" ["import-path"]
    (ReqArg
     (\p opts -> return opts { importPath = importPath opts ++ splitSearchPath p })
     "path"
    )
    pathDesc
  , Option "t" ["detect-vacuity"]
    (NoArg
     (\opts -> return opts { detectVacuity = True }))
    "Checks and warns the user about contradictory assumptions. (default: false)"
  , Option "t" ["extra-type-checking"]
    (NoArg
     (\opts -> return opts { extraChecks = True }))
    "Perform extra type checking of intermediate values"
  , Option "I" ["interactive"]
    (NoArg
     (\opts -> return opts { runInteractively = True }))
    "Run interactively (with a REPL)"
  , Option "j" ["jars"]
    (ReqArg
     (\p opts -> return opts { jarList = jarList opts ++ splitSearchPath p })
     "path"
    )
    pathDesc
  , Option "b" ["java-bin-dirs"]
    (ReqArg
     (\p opts -> return opts { javaBinDirs = javaBinDirs opts ++ splitSearchPath p })
     "path"
    )
    pathDesc
  , Option [] ["output-locations"]
    (NoArg
     (\opts -> return opts { printShowPos = True }))
     "Show the source locations that are responsible for output."
  , Option "d" ["sim-verbose"]
    (ReqArg
     (\v opts -> return opts { simVerbose = read v })
     "num"
    )
    "Set simulator verbosity level"
  , Option "v" ["verbose"]
    (ReqArg
      (\v opts -> let verb = readVerbosity v -- TODO: now that we're in IO we can do something if a bogus verbosity is given
                 in return opts { verbLevel = verb
                         , printOutFn = printOutWith verb } )
     "<num 0-5 | 'silent' | 'counterexamples' | 'error' | 'warn' | 'info' | 'debug'>"
    )
    "Set verbosity level"
  , Option [] ["no-color"]
    (NoArg (\opts -> return opts { useColor = False }))
    "Disable ANSI color and Unicode output"
  , Option "s" ["summary"]
    (ReqArg
     (\file opts -> return opts { summaryFile = Just file })
     "filename")
    "Write a verification summary to the provided filename"
  , Option "f" ["summary-format"]
    (ReqArg
     (\fmt opts -> case fmt of
        "json" -> return opts { summaryFormat = JSON }
        "pretty" -> return opts { summaryFormat = Pretty }
        _ -> do
          hPutStrLn stderr "Error: the argument of the '-f' option must be either 'json' or 'pretty'"
          exitFailure
     )
     "either 'json' or 'pretty'")
    "Specify the format in which the verification summary should be written in ('json' or 'pretty'; defaults to 'json')"
  ]

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

-- | Perform some additional post-processing on an 'Options' value based on
-- whether certain environment variables are defined.
processEnv :: Options -> IO Options
processEnv opts = do
  curEnv <- getEnvironment
  opts' <- addJavaBinDirInducedOpts opts
  return $ foldr addSawOpt opts' curEnv
  where
    -- If a Java executable's path is specified (either by way of
    -- --java-bin-dirs or PATH, see the Haddocks for findJavaIn), then use that
    -- to detect the path to Java's standard rt.jar file and add it to the
    -- jarList on Java 8 or earlier. (Later versions of Java do not use
    -- rt.jar—see Note [Loading classes from JIMAGE files] in
    -- Lang.JVM.Codebase in crucible-jvm.)
    -- If Java's path is not specified, return the Options unchanged.
    addJavaBinDirInducedOpts :: Options -> IO Options
    addJavaBinDirInducedOpts os@Options{javaBinDirs} = do
      mbJavaPath <- findJavaIn javaBinDirs
      case mbJavaPath of
        Nothing       -> pure os
        Just javaPath -> do
          javaMajorVersion <- findJavaMajorVersion javaPath
          if javaMajorVersion >= 9
             then pure os
             else addRTJar javaPath os

    -- rt.jar lives in a standard location relative to @java.home@. At least,
    -- this is the case on every operating system I've tested.
    addRTJar :: FilePath -> Options -> IO Options
    addRTJar javaPath os = do
      mbJavaHome <- findJavaProperty javaPath "java.home"
      case mbJavaHome of
        Nothing -> fail $ "Could not find where rt.jar lives for " ++ javaPath
        Just javaHome ->
          let rtJarPath = javaHome </> "lib" </> "rt.jar" in
          pure $ os{ jarList = rtJarPath : jarList os }

    addSawOpt :: (String, String) -> Options -> Options
    addSawOpt ("SAW_IMPORT_PATH", p) os =
      os { importPath = importPath os ++ splitSearchPath p }
    addSawOpt ("SAW_JDK_JAR", p) os = os { jarList = p : jarList os }
    addSawOpt _ os = os

pathDesc, pathDelim :: String

#ifdef mingw32_HOST_OS
pathDesc = "Semicolon-delimited list of paths"
pathDelim = ";"
#else
pathDesc = "Colon-delimited list of paths"
pathDelim = ":"
#endif
