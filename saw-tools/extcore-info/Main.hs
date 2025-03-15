{- |
Copyright   : Galois, Inc. 2012-2014
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Main where

import System.Environment (getArgs)
import GHC.IO.Encoding (setLocaleEncoding, utf8)

import Verifier.SAW

processFile :: FilePath -> IO ()
processFile file = do
  sc <- mkSharedContext
  scLoadPreludeModule sc
  tm <- scReadExternal sc =<< readFile file
  putStrLn $ "Shared size: " ++ show (scSharedSize tm)
  putStrLn $ "Tree size: " ++ show (scTreeSize tm)

main :: IO ()
main = do
  setLocaleEncoding utf8
  mapM_ processFile =<< getArgs
