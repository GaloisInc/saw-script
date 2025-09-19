{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Main where

import qualified Data.ByteString as BS
import qualified Data.Map as Map
import Data.Text (Text)

import Text.Heredoc (there)

import qualified Cryptol.ModuleSystem.Name as N
import qualified Cryptol.Utils.Ident as N

import           SAWCore.SharedTerm
import qualified SAWCore.SCTypeCheck as TC
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
     cenv1 <- CEnv.importModule sc cenv0 (Right N.floatName) Nothing CEnv.OnlyPublic Nothing
     putStrLn "Translated Float.cry!"
     cenv2 <- CEnv.importModule sc cenv1 (Right N.arrayName) Nothing CEnv.OnlyPublic Nothing
     putStrLn "Translated Array.cry!"
     cenv3 <- CEnv.importModule sc cenv2 (Right N.suiteBName) Nothing CEnv.OnlyPublic Nothing
     putStrLn "Translated SuiteB.cry!"
     cenv4 <- CEnv.importModule sc cenv3 (Right N.primeECName) Nothing CEnv.OnlyPublic Nothing
     putStrLn "Translated PrimeEC.cry!"
     cenv5 <- CEnv.importModule sc cenv4 (Right N.preludeReferenceName) Nothing CEnv.OnlyPublic Nothing
     putStrLn "Translated Reference.cry!"
     cenv6 <- CEnv.parseDecls sc cenv5 (CEnv.InputText superclassContents "superclass.cry" 1 1)
     putStrLn "Translated superclass.cry!"
     cenv7 <- CEnv.parseDecls sc cenv6 (CEnv.InputText instanceContents "instance.cry" 1 1)
     putStrLn "Translated instance.cry!"
     mapM_ (checkTranslation sc) $ Map.assocs (CEnv.eTermEnv cenv7)
     putStrLn "Checked all terms!"

checkTranslation :: SharedContext -> (N.Name, Term) -> IO ()
checkTranslation sc (name, term) =
  do result <- TC.scTypeCheck sc term
     case result of
       Right _ -> pure ()
       Left err ->
         do putStrLn $ "Type error when checking " ++ show (N.unpackIdent (N.nameIdent name))
            putStrLn $ unlines $ TC.prettyTCError err
            fail "internal type error"

superclassContents :: Text
superclassContents = [there|otherTests/cryptol-saw-core/superclass.cry|]

instanceContents :: Text
instanceContents = [there|otherTests/cryptol-saw-core/instance.cry|]
