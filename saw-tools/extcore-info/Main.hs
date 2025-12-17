{- |
Copyright   : Galois, Inc. 2012-2014
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Main (main) where

import System.Environment (getArgs)
import qualified Data.IORef as IORef
import GHC.IO.Encoding (setLocaleEncoding, utf8)

import qualified SAWSupport.Pretty as PPS
import SAWCore.SAWCore

processFile :: FilePath -> IO ()
processFile file = do
  ppopts <- IORef.newIORef PPS.defaultOpts
  sc <- mkSharedContext ppopts
  scLoadPreludeModule sc
  tm <- scReadExternal sc =<< readFile file
  putStrLn $ "Shared size: " ++ show (scSharedSize tm)
  putStrLn $ "Tree size: " ++ show (scTreeSize tm)

main :: IO ()
main = do
  setLocaleEncoding utf8
  mapM_ processFile =<< getArgs
