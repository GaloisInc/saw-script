{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}

module SAWCoreIsabelle.Options
  ( Options(..)
  , empty
  , Available
  , ImportPrefix(..)
  , TargetSelect(..)
  , withOptions
  , crySources
  , isaDestDir
  , isaImportPrefix
  , verbosity
  , keepGoing
  , cryptolDirs
  , targetSelect
  , functionStubs
  , allOptions
  , addLogger
  , addErrLogger
  , log
  , logErr
  ) where

import           Prelude hiding (log)

import qualified Control.Monad.IO.Class as IO
import qualified Cryptol.Parser.AST as Cry (ModName)
import qualified Cryptol.TypeCheck.AST as Cry

import qualified Language.Isabelle.Name as Isabelle

data ImportPrefix = NoPrefix | CryptolImage | CustomPrefix String

data TargetSelect = 
      AllModules 
    | NamedModules [String] 
    | ModuleNames [Cry.ModName]
    | TargetExpr Isabelle.Name Cry.Schema Cry.Expr

data Options = Options {
  crySources_ :: [FilePath]
, isaDestDir_ :: FilePath
, isaImportPrefix_ :: ImportPrefix
, verbosity_ :: Integer
, keepGoing_ :: Bool
, cryptolDirs_ :: [FilePath]
, targetSelect_ :: TargetSelect
, functionStubs_ :: [String]
, loggerMsg_ :: String -> IO ()
, loggerErr_ :: String -> IO ()
}

empty :: Options
empty = Options [] "" NoPrefix 0 False [] (NamedModules []) [] (\_ -> return ()) (\_ -> return ())

type Available = (?options :: Options)

crySources :: Available => [FilePath]
crySources = crySources_ ?options

isaDestDir :: Available => FilePath
isaDestDir = isaDestDir_ ?options

isaImportPrefix :: Available => ImportPrefix
isaImportPrefix = isaImportPrefix_ ?options

verbosity :: Available => Integer
verbosity = verbosity_ ?options

allOptions :: Available => Options
allOptions = ?options

keepGoing :: Available => Bool
keepGoing = keepGoing_ ?options

cryptolDirs :: Available => [FilePath]
cryptolDirs = cryptolDirs_ ?options

targetSelect :: Available => TargetSelect
targetSelect = targetSelect_ ?options

functionStubs :: Available => [String]
functionStubs = functionStubs_ ?options

log :: (Available, IO.MonadIO m) => Integer -> String -> m ()
log v msg = IO.liftIO $ if v < verbosity then loggerMsg_ ?options msg else return ()

logErr :: (Available, IO.MonadIO m) => Integer -> String -> m ()
logErr v msg = IO.liftIO $ if v < verbosity then loggerErr_ ?options msg else return ()

addLogger :: (String -> IO ()) -> Options -> Options
addLogger f opts = opts { loggerMsg_ = (\msg -> loggerMsg_ opts msg >> f msg)}

addErrLogger :: (String -> IO ()) -> Options -> Options
addErrLogger f opts = opts { loggerErr_ = (\msg -> loggerErr_ opts msg >> f msg)}

withOptions :: Options -> (Available => a) -> a
withOptions opts f = let ?options = opts in f