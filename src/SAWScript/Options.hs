{-# LANGUAGE NamedFieldPuns      #-}
{- |
Module      : SAWScript.Options
Description : Datatype for saw command-line options.
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}

module SAWScript.Options where

import Data.List (partition)
import Data.Time
import Text.Show.Functions ()

import System.Environment
import System.FilePath

import Lang.JVM.JavaTools

-- | Type we use to track the command-line option settings.
data Options = Options
  { importPath       :: [FilePath]
  , classPath        :: [FilePath]
  , jarList          :: [FilePath]
  , javaBinDirs      :: [FilePath]
  , verbLevel        :: Verbosity
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
    , printShowPos = False
    , printOutFn = printOutWith Info
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

printOutWith :: Verbosity -> Verbosity -> String -> IO ()
printOutWith setting level msg
    | setting >= level = do
      t <- formatTime defaultTimeLocale "%T.%3q" <$> getCurrentTime
      putStr $ "[" ++ t ++ "] " ++ msg
    | otherwise        = return ()

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
    addSawOpt ("CLASSPATH", p) os = os { jarList = jarList os ++ jars
                                       , classPath = classPath os ++ dirs
                                       }
                                    where
                                      es = splitSearchPath p
                                      (jars, dirs) = partition (".jar" `isExtensionOf`) es
    addSawOpt _ os = os
