{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module SAWCoreIsabelle.Headless(
  runTranslator
) where

import           Prelude hiding (log)
import           Control.Exception (catch, throw, IOException)
import qualified Control.Monad.IO.Class as IO

import           Data.ByteString (ByteString)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Text.IO as T

import qualified Cryptol.Eval as Cry
import qualified Cryptol.ModuleSystem.Base as CryBase
import qualified Cryptol.ModuleSystem.Env as Cry
import           Cryptol.ModuleSystem.Monad (ModuleInput(..))
import qualified Cryptol.ModuleSystem.Monad as Cry
import           Cryptol.TypeCheck (defaultSolverConfig)
import qualified Cryptol.TypeCheck.AST as Cry
import qualified Cryptol.TypeCheck.Solver.SMT as SMT
import qualified Cryptol.Utils.Ident as Cry
import qualified Cryptol.Utils.Logger as Cry
import           Cryptol.Utils.PP (pretty)

import           SAWCoreIsabelle.Options (HasOptions, log, logErr)
import qualified SAWCoreIsabelle.Options as Options
import           SAWCoreIsabelle.Runner (RunnerError(..), processModules, fatalErr)


-- Code specific to running translator independently 
-- (i.e. no existing Cryptol environment)

debug :: (HasOptions, IO.MonadIO m) => String -> m ()
debug msg = log 2 $ "[DEBUG]: " ++ msg ++ "\n"

runTranslator :: Options.Options -> IO Bool
runTranslator opts = Options.withOptions opts $
  processFile' `catch` (\(_ :: RunnerError) -> return False)

processFile' :: HasOptions => IO Bool
processFile' = do
  let inputFiles = Options.crySources
  log 0 $ "Reading cryptol input files: \n" ++ (List.intercalate "\n" $ inputFiles) ++ "\n"

  initialEnv <- initialModuleEnv
  debug $ (show (Cry.meSearchPath initialEnv))
  let evalOpts = Cry.EvalOpts { Cry.evalLogger = Cry.quietLogger, Cry.evalPPOpts = Cry.defaultPPOpts }
  let byteReader :: FilePath -> IO ByteString = fmap T.encodeUtf8. T.readFile
  let solverConfig = defaultSolverConfig []
  s <- SMT.startSolver (return ()) solverConfig

  let moduleInput = ModuleInput
        { minpCallStacks = True
        , minpEvalOpts   = pure evalOpts
        , minpByteReader = byteReader
        , minpModuleEnv  = initialEnv
        , minpTCSolver   = s
        , minpSaveRenamed = False
        }
  let initState = LoadModulesState
        { loadedTopEntities = []
        , loadedModuleInput = moduleInput
        }

  loadedState <- loadModules inputFiles initState
  let modEnv = Cry.minpModuleEnv $ loadedModuleInput loadedState
  checkTargetSelect modEnv
  let extraDecls = (Cry.deDecls $ Cry.meDynEnv modEnv)
  let extraTys = (Map.elems $ Cry.deTySyns $ Cry.meDynEnv modEnv)
  processModules Options.allOptions (Cry.lmLoadedModules (Cry.meLoadedModules modEnv)) extraDecls extraTys


initialModuleEnv :: HasOptions => IO Cry.ModuleEnv
initialModuleEnv = do
  env <- Cry.initialModuleEnv
  return $ env { Cry.meSearchPath = Options.cryptolDirs ++ (Cry.meSearchPath env) }

data LoadModulesState  = LoadModulesState
    { loadedTopEntities :: [Cry.TCTopEntity]
    , loadedModuleInput :: Cry.ModuleInput IO
    }

loadModuleInput ::
  HasOptions =>
  FilePath ->
  Cry.ModuleInput IO ->
  IO (Cry.TCTopEntity, Cry.ModuleInput IO)
loadModuleInput file input = do
  {- note that loadModuleByPath will do nothing if the module is already loaded,
     and error if a different module is already loaded with the same name -}
  tryIO (Cry.runModuleM input (CryBase.loadModuleByPath True file)) >>= \case
    Left ioerr -> fatalErr $ "Failed to read input file: " ++ show ioerr
    Right (resultEither, warnings) -> do
      mapM_ (logErr 0 . pretty) warnings
      case resultEither of
          Left er -> logErr (-1) (pretty er) >> throw (RunnerError (pretty er))
          Right (topEntity,env) -> return $ (topEntity, input{Cry.minpModuleEnv = env})

checkTargetSelect :: HasOptions => Cry.ModuleEnv -> IO ()
checkTargetSelect env = case Options.targetSelect of
  Options.AllModules -> return ()
  Options.NamedModules namedMods -> do
    let
      loaded = Cry.lmLoadedModules (Cry.meLoadedModules env)
      loadedNames = map (T.unpack . Cry.modNameToText . Cry.lmName) loaded
    go namedMods loadedNames
  _ -> return ()
  where
    go :: [String] -> [String] -> IO ()
    go [] _ = return ()
    go (m:ms) lms | elem m lms = go ms lms
    go (m:_) _ = fatalErr $ "Could not find module " ++ show m ++ " in module imports."

loadModules ::
  HasOptions =>
  [FilePath] ->
  LoadModulesState ->
  IO (LoadModulesState)
loadModules [] st = return st
loadModules (file:files) st = do
  (topEntity, input') <- loadModuleInput file (loadedModuleInput st)
  let st' = st
        { loadedTopEntities = topEntity:(loadedTopEntities st)
        , loadedModuleInput = input'
        }
  loadModules files st'

tryIO :: IO a -> IO (Either IOException a)
tryIO f = catch (Right <$> f) (\e -> return $ Left (e :: IOException))