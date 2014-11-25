module SAWScript.ProcessFile where

import Prelude hiding (mod)

import Control.Applicative
import Control.Monad
import qualified Data.Map      as M
import qualified Data.Foldable as F
import qualified Data.Set      as S

import System.FilePath

import SAWScript.AST
import SAWScript.BuildModules as BM hiding (modName)
import SAWScript.Compiler
import SAWScript.Import
import SAWScript.Interpreter
import SAWScript.MGU (checkModule)
import SAWScript.Options



processFile :: Options -> FilePath -> IO ()

processFile opts file | takeExtensions file == ".saw" = do
  when (verbLevel opts > 0) $ putStrLn $ "Processing SAWScript file " ++ file
  {-
  loadPrelude opts $ \lms -> do
    processModule opts lms (ModuleName [] "Prelude")
  -}
  loadedModules <- loadWithPrelude opts file
  let modName = moduleNameFromPath file
  processModule opts loadedModules modName

processFile _ file = putStrLn $ "Don't know how to handle file " ++ file



processModule :: Options -> LoadedModules -> ModuleName -> IO ()
processModule opts lms modName = do
  -- TODO: merge the two representations of the prelude into one
  --  that both the renamer and the type checker can understand.
  validMod <- reportErrT $ do
                parts <- buildModules lms
                cms <- F.foldrM checkModuleWithDeps M.empty parts
                case M.lookup modName cms of
                  Just cm -> return cm
                  Nothing -> fail $ "Module " ++ show modName ++
                                    " not found in environment of checkedModules:" ++
                                    show (M.keys cms)
  interpretMain opts validMod


checkModuleWithDeps :: BM.ModuleParts
  -> M.Map ModuleName ValidModule
  -> Err (M.Map ModuleName ValidModule)
checkModuleWithDeps (BM.ModuleParts mn ee ds cs ss) cms =
  mod >>=
  checkModule >>= \cm -> return $ M.insert mn cm cms
  where
  deps :: Err (M.Map ModuleName ValidModule)
  deps = fmap M.fromList $ forM (S.toList ds) $ \n ->
           case M.lookup n cms of
             Nothing -> fail $ "Tried to compile module " ++ show mn ++
                               " before compiling its dependency, " ++ show n
             Just m  -> return (n,m)
  mod  = Module mn ee <$> deps <*> pure cs <*> pure ss
