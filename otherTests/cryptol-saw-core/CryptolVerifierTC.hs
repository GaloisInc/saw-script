{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Main where

import qualified Data.ByteString as BS
import Data.Text (Text)

import Text.Heredoc (there)

import qualified Cryptol.Utils.Ident as N

import           SAWCore.SharedTerm
import qualified CryptolSAWCore.Prelude as C
import qualified CryptolSAWCore.CryptolEnv as CEnv

main :: IO ()
main =
  do sc <- mkSharedContext
     C.scLoadPreludeModule sc
     C.scLoadCryptolModule sc
     putStrLn "Loaded Cryptol.sawcore!"
     let ?fileReader = BS.readFile
     cenv0 <- CEnv.initCryptolEnv sc
     putStrLn "Translated Cryptol.cry!"
     cenv1 <- CEnv.importCryptolModule sc cenv0 (Right N.floatName) Nothing CEnv.OnlyPublic Nothing
     putStrLn "Translated Float.cry!"
     cenv2 <- CEnv.importCryptolModule sc cenv1 (Right N.arrayName) Nothing CEnv.OnlyPublic Nothing
     putStrLn "Translated Array.cry!"
     cenv3 <- CEnv.importCryptolModule sc cenv2 (Right N.suiteBName) Nothing CEnv.OnlyPublic Nothing
     putStrLn "Translated SuiteB.cry!"
     cenv4 <- CEnv.importCryptolModule sc cenv3 (Right N.primeECName) Nothing CEnv.OnlyPublic Nothing
     putStrLn "Translated PrimeEC.cry!"
     cenv5 <- CEnv.importCryptolModule sc cenv4 (Right N.preludeReferenceName) Nothing CEnv.OnlyPublic Nothing
     putStrLn "Translated Reference.cry!"
     cenv6 <- CEnv.parseDecls sc cenv5 (CEnv.InputText superclassContents "superclass.cry" 1 1)
     putStrLn "Translated superclass.cry!"
     _cenv7 <- CEnv.parseDecls sc cenv6 (CEnv.InputText instanceContents "instance.cry" 1 1)
     putStrLn "Translated instance.cry!"

superclassContents :: Text
superclassContents = [there|otherTests/cryptol-saw-core/superclass.cry|]

instanceContents :: Text
instanceContents = [there|otherTests/cryptol-saw-core/instance.cry|]
