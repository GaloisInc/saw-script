{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

{- |
Module      : SAWCore.Parser.TH
Copyright   : Galois, Inc. 2025
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Parser.TH
 ( -- * Parser utilities.
   readModuleFromFile
   -- * Template haskell utilities.
 , defineModuleFromFile
 ) where

import Data.Text (Text)
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.IO as TLIO
import Language.Haskell.TH
#if MIN_VERSION_template_haskell(2,7,0)
import Language.Haskell.TH.Syntax (qAddDependentFile)
#endif
import System.Directory
import qualified Language.Haskell.TH.Syntax as TH (lift)

import SAWCore.Panic
import qualified SAWCore.Parser.AST as Un
import qualified SAWCore.Parser.Grammar as Un

-- | Parse an untyped module declaration from a (lazy) Text
readModule :: FilePath -> FilePath -> TL.Text -> Either Text Un.Module
readModule base path b =
  case Un.parseSAW base path b of
    Right m -> Right m
    Left err -> Left $ Un.ppParseError err

-- | Parse an untyped module from file
readModuleFromFile :: FilePath -> IO (Either Text Un.Module)
readModuleFromFile path =
  do base <- getCurrentDirectory
     txt <- TLIO.readFile path
     return $ readModule base path txt

-- | Parse an untyped module from file and panic if it fails
readBuiltinModuleFromFile :: FilePath -> IO Un.Module
readBuiltinModuleFromFile path = do
  result <- readModuleFromFile path
  case result of
    Right m -> pure m
    Left msg ->
        panic "readBuiltinModuleFromFile" [
            "Module parsing failed:",
            msg
        ]

-- | Record @path@ as a dependency for this compilation.
addDep :: FilePath -> Q ()
#if MIN_VERSION_template_haskell(2,7,0)
addDep path = qAddDependentFile path
#else
addDep path = pure ()
#endif

-- | Read a SAWCore module from @file@ at compile time, and add a TH
-- declaration of the name @str@ that is bound to that module (with
-- Haskell type 'Un.Module') at runtime.
defineModuleFromFile :: String -> FilePath -> Q [Dec]
defineModuleFromFile decNameStr path =
  do addDep path
     m <- runIO $ readBuiltinModuleFromFile path
     let decName = mkName decNameStr
     moduleTp <- [t| Un.Module |]
     body <- TH.lift m
     pure [ SigD decName moduleTp
          , FunD decName [ Clause [] (NormalB body) [] ]
          ]
