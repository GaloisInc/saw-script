module Main where

import System.Environment (getArgs)

import Verifier.SAW

processFile :: FilePath -> IO ()
processFile file = do
  sc <- mkSharedContext preludeModule
  tm <- scReadExternal sc =<< readFile file
  putStrLn $ "Shared size: " ++ show (scSharedSize tm)
  putStrLn $ "Tree size: " ++ show (scTreeSize tm)

main :: IO ()
main = mapM_ processFile =<< getArgs
