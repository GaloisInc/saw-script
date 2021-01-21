{- |
Module      : SAWScript.JavaTools
Description : Functionality for finding a Java executable and its properties.
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}

module SAWScript.JavaTools
  ( findJavaIn
  , findJavaProperty
  , findJavaMajorVersion
  ) where

import Data.List.Extra (dropPrefix, firstJust, stripInfix)
import Data.Maybe
import System.Directory

import SAWScript.ProcessUtils

-- | @'findJavaIn' javaBinDirs@ searches for an executable named @java@ in the
-- directories in @javaBinDirs@. If @javaBinDirs@ is empty, then the @PATH@ is
-- searched.
--
-- If the search finds at least one executable, then @Just@ the first result is
-- returned. If no executables are found, then @Nothing@ is returned.
findJavaIn :: [FilePath] -> IO (Maybe FilePath)
findJavaIn javaBinDirs
  | null javaBinDirs = findExecutable "java"
  | otherwise        = listToMaybe <$> findExecutablesInDirectories javaBinDirs "java"

-- | @'findJavaProperty' javaPath prop@ invokes @javaPath@ to dump its system
-- properties (see <https://docs.oracle.com/javase/tutorial/essential/environment/sysprop.html>)
-- and attempts to find the value associated with the property named @prop@.
-- If such a value is found, then @Just@ that value is returned.
-- If no property named @prop@ exists, then @Nothing@ is returned.
--
-- This will throw an exception if @javaPath@'s system properties cannot be
-- determined.
findJavaProperty :: FilePath -> String -> IO (Maybe String)
findJavaProperty javaPath propertyNeedle = do
  (_stdOut, stdErr) <- readProcessExitIfFailure javaPath ["-XshowSettings:properties", "-version"]
  let propertyHaystacks = lines stdErr
  pure $ firstJust getProperty_maybe propertyHaystacks
  where
    -- Each Java system property, as reported by
    -- @java -XshowSettings:properties@, adheres to this template:
    --
    -- "  <prop> = <value>"
    --
    -- Note the leading whitespace. As a result, stripInfix is used to detect
    -- "<prop> = " in the middle of the string and obtain the <value> after it.
    getProperty_maybe :: String -> Maybe String
    getProperty_maybe propertyHaystack =
      snd <$> stripInfix (propertyNeedle ++ " = ") propertyHaystack

-- | @'findJavaMajorVersion' javaPath@ will consult @javaPath@ to find the
-- major version number corresponding to that Java release.
findJavaMajorVersion :: FilePath -> IO Int
findJavaMajorVersion javaPath = do
  mbVersionStr <- findJavaProperty javaPath "java.version"
  case mbVersionStr of
    Nothing         -> fail $ "Could not detect the version of Java at " ++ javaPath
    Just versionStr -> pure $ read $ takeMajorVersionStr $ dropOldJavaVersionPrefix versionStr
  where
    -- e.g., if the version number is "11.0.9.1", then just take the "11" part.
    takeMajorVersionStr :: String -> String
    takeMajorVersionStr = takeWhile (/= '.')

    -- Prior to Java 9, the leading version number was always 1. For example,
    -- Java 8 would use 1.8.<...>. We only care about the 8 part, so drop the
    -- leading 1. bit.
    dropOldJavaVersionPrefix :: String -> String
    dropOldJavaVersionPrefix = dropPrefix "1."
