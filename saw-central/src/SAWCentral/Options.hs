{- |
Module      : SAWCentral.Options
Description : Datatype for saw command-line options.
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}

module SAWCentral.Options where

import Data.List (partition)
import Data.Time
import Text.Show.Functions ()

import System.Environment
import System.FilePath

-- | Type we use to track the command-line option settings.
data Options = Options
  { importPath       :: [FilePath]
  , classPath        :: [FilePath]
  , jarList          :: [FilePath]
  , javaBinDirs      :: [FilePath]
  , verbLevel        :: Verbosity
  , timestamping     :: TimestampSetting
  , simVerbose       :: Int
  , detectVacuity    :: Bool
  , extraChecks      :: Bool
  , batchFile        :: Maybe String
  , runInteractively :: Bool
  , showHelp         :: Bool
  , showVersion      :: Bool
  , printShowPos     :: Bool
  , useColor         :: Bool
  , cleanMisVsCache  :: Maybe FilePath
  , printOutFn       :: Verbosity -> String -> IO ()
  , summaryFile      :: Maybe FilePath
  , summaryFormat    :: SummaryFormat
  } deriving (Show)

-- | Type for tracking whether we're printing timestamps on messages.
--   (Use this instead of just Bool to avoid confusion, since this
--   module is exposed to essentially the entire SAW tree.)
data TimestampSetting = NotTimestamping | Timestamping
  deriving (Eq, Show)

-- | Verbosity is currently a linear setting (vs a mask or tree).  Any given
-- level includes the outputs of all lower levels.
data Verbosity
  = Silent
  | OnlyCounterExamples
  | Error
  | Warn
  | Info
  | Debug
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
    , timestamping = NotTimestamping
    , printShowPos = False
    , printOutFn = printOutWith Info NotTimestamping
    , simVerbose = 1
    , detectVacuity = False
    , extraChecks = False
    , batchFile = Nothing
    , runInteractively = False
    , showHelp = False
    , showVersion = False
    , useColor = True
    , cleanMisVsCache = Nothing
    , summaryFile = Nothing
    , summaryFormat = Pretty
    }

printOutWith :: Verbosity -> TimestampSetting -> Verbosity -> String -> IO ()
printOutWith setting ts level msg
    | setting >= level, ts == Timestamping = do
          t <- formatTime defaultTimeLocale "%T.%3q" <$> getCurrentTime
          putStr $ "[" ++ t ++ "] " ++ msg
    | setting >= level, ts == NotTimestamping = 
          putStr msg
    | otherwise =
          return ()

printOutLn :: Options -> Verbosity -> String -> IO ()
printOutLn o v s = printOutFn o v (s ++ "\n")

-- | Perform some additional post-processing on an 'Options' value based on
-- whether certain environment variables are defined.
--
-- XXX: this does not belong in Options.hs; it is a top-level
-- operation that's really part of main. But it's shared between saw
-- and saw-remote-api so it has to live somewhere shared, and for the
-- time being there isn't anywhere else.
processEnv :: Options -> IO Options
processEnv opts = do
  curEnv <- getEnvironment
  return $ foldr addSawOpt opts curEnv
  where
    addSawOpt :: (String, String) -> Options -> Options
    addSawOpt ("SAW_IMPORT_PATH", p) os =
      os { importPath = importPath os ++ splitSearchPath p }
    addSawOpt ("SAW_JDK_JAR", p) os = os { jarList = p : jarList os }
    addSawOpt ("CLASSPATH", p) os = os { jarList = jarList os ++ jars
                                       , classPath = classPath os ++ dirs
                                       }
                                    where
                                      es = splitSearchPath p
                                      (jars, dirs) = partition (".jar" `isExtensionOf`) es
    addSawOpt _ os = os
