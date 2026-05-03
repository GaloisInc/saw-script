{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Main (main) where

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
     let importCryptolModule' cenv nm =
           CEnv.importCryptolModule
             sc cenv (Right nm) Nothing False CEnv.OnlyPublic Nothing
     cenv1 <- importCryptolModule' cenv0 N.floatName
     putStrLn "Translated Float.cry!"
     cenv2 <- importCryptolModule' cenv1 N.arrayName
     putStrLn "Translated Array.cry!"
     cenv3 <- importCryptolModule' cenv2 N.suiteBName
     putStrLn "Translated SuiteB.cry!"
     cenv4 <- importCryptolModule' cenv3 N.primeECName
     putStrLn "Translated PrimeEC.cry!"
     cenv5 <- importCryptolModule' cenv4 N.preludeReferenceName
     putStrLn "Translated Reference.cry!"
     cenv6 <- CEnv.parseDecls sc cenv5 (CEnv.InputText superclassContents "superclass.cry" 1 1)
     putStrLn "Translated superclass.cry!"
     _cenv7 <- CEnv.parseDecls sc cenv6 (CEnv.InputText instanceContents "instance.cry" 1 1)
     putStrLn "Translated instance.cry!"

superclassContents :: Text
superclassContents = [there|otherTests/cryptol-saw-core/superclass.cry|]

instanceContents :: Text
instanceContents = [there|otherTests/cryptol-saw-core/instance.cry|]
