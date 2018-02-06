{- |
Module      : SAWScript.Options
Description : Datatype for saw command-line options.
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SAWScript.Options where

import Data.Char (toLower)
import System.Console.GetOpt
import System.Environment
import System.FilePath
import Text.Read (readMaybe)
import Text.Show.Functions ()

data Options = Options
  { importPath       :: [FilePath]
  , classPath        :: [FilePath]
  , jarList          :: [FilePath]
  , verbLevel        :: Verbosity
  , simVerbose       :: Int
  , extraChecks      :: Bool
  , runInteractively :: Bool
  , showHelp         :: Bool
  , showVersion      :: Bool
  , printShowPos     :: Bool
  , printOutFn       :: Verbosity -> String -> IO ()
  } deriving (Show)

-- | Verbosity is currently a linear setting (vs a mask or tree).  Any given
-- level includes the outputs of all lower levels.
data Verbosity = Silent | OnlyCounterExamples | Error | Warn | Info | Debug
    deriving (Show,Eq,Ord)

defaultOptions :: Options
defaultOptions
  = Options {
      importPath = ["."]
    , classPath = ["."]
    , jarList = []
    , verbLevel = Info
    , printShowPos = False
    , printOutFn = printOutWith Info
    , simVerbose = 1
    , extraChecks = False
    , runInteractively = False
    , showHelp = False
    , showVersion = False
    }

printOutWith :: Verbosity -> Verbosity -> String -> IO ()
printOutWith setting level msg
    | setting >= level = putStr msg
    | otherwise        = return ()

printOutLn :: Options -> Verbosity -> String -> IO ()
printOutLn o v s = printOutFn o v (s ++ "\n")

options :: [OptDescr (Options -> Options)]
options =
  [ Option "h?" ["help"]
    (NoArg (\opts -> opts { showHelp = True }))
    "Print this help message"
  , Option "V" ["version"]
    (NoArg (\opts -> opts { showVersion = True }))
    "Show the version of the SAWScript interpreter"
  , Option "c" ["classpath"]
    (ReqArg
     (\p opts -> opts { classPath = classPath opts ++ splitSearchPath p })
     "path"
    )
    pathDesc
  , Option "i" ["import-path"]
    (ReqArg
     (\p opts -> opts { importPath = importPath opts ++ splitSearchPath p })
     "path"
    )
    pathDesc
  , Option "t" ["extra-type-checking"]
    (NoArg
     (\opts -> opts { extraChecks = True }))
    "Perform extra type checking of intermediate values"
  , Option "I" ["interactive"]
    (NoArg
     (\opts -> opts { runInteractively = True }))
    "Run interactively (with a REPL)"
  , Option "j" ["jars"]
    (ReqArg
     (\p opts -> opts { jarList = jarList opts ++ splitSearchPath p })
     "path"
    )
    pathDesc
  , Option [] ["output-locations"]
    (NoArg
     (\opts -> opts { printShowPos = True }))
     "Show the source locations that are responsible for output."
  , Option "d" ["sim-verbose"]
    (ReqArg
     (\v opts -> opts { simVerbose = read v })
     "num"
    )
    "Set simulator verbosity level"
  , Option "v" ["verbose"]
    (ReqArg
     (\v opts -> let verb = readVerbosity v
                 in opts { verbLevel = verb
                         , printOutFn = printOutWith verb } )
     "<num 0-5 | 'silent' | 'counterexamples' | 'error' | 'warn' | 'info' | 'debug'>"
    )
    "Set verbosity level"
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

processEnv :: Options -> IO Options
processEnv opts = do
  curEnv <- getEnvironment
  return $ foldr addOpt opts curEnv
    where addOpt ("SAW_IMPORT_PATH", p) os =
            os { importPath = importPath os ++ splitSearchPath p }
          addOpt ("SAW_JDK_JAR", p) os = os { jarList = p : jarList opts }
          addOpt _ os = os

pathDesc, pathDelim :: String

#ifdef mingw32_HOST_OS
pathDesc = "Semicolon-delimited list of paths"
pathDelim = ";"
#else
pathDesc = "Colon-delimited list of paths"
pathDelim = ":"
#endif
