{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SAWServer.CryptolSetup
  ( cryptolLoadFile
  , cryptolLoadModule
  ) where

import Control.Exception (SomeException, try)
import Control.Monad.IO.Class
import Control.Lens
import Data.Aeson (FromJSON(..), withObject, (.:))
import qualified Data.Text as T

import qualified Cryptol.Parser.AST as P
import Cryptol.Utils.Ident (textToModName)
import SAWScript.Value (biSharedContext, rwCryptol)
import qualified Verifier.SAW.CryptolEnv as CEnv

import Argo
import qualified Argo.Doc as Doc
import SAWServer
import SAWServer.Exceptions
import SAWServer.OK

cryptolLoadModule :: CryptolLoadModuleParams -> Method SAWState OK
cryptolLoadModule (CryptolLoadModuleParams modName) =
  do sc <- biSharedContext . view sawBIC <$> getState
     cenv <- rwCryptol . view sawTopLevelRW <$> getState
     let qual = Nothing -- TODO add field to params
     let importSpec = Nothing -- TODO add field to params
     fileReader <- getFileReader
     let ?fileReader = fileReader
     cenv' <- liftIO $ try $ CEnv.importModule sc cenv (Right modName) qual importSpec
     case cenv' of
       Left (ex :: SomeException) -> raise $ cryptolError (show ex)
       Right cenv'' ->
         do modifyState $ over sawTopLevelRW $ \rw -> rw { rwCryptol = cenv'' }
            ok

data CryptolLoadModuleParams =
  CryptolLoadModuleParams P.ModName

instance FromJSON CryptolLoadModuleParams where
  parseJSON =
    withObject "params for \"SAW/Cryptol setup/load module\"" $ \o ->
    CryptolLoadModuleParams . textToModName <$> o .: "module name"

instance Doc.DescribedParams CryptolLoadModuleParams where
  parameterFieldDescription =
    [ ("module name",
       Doc.Paragraph [Doc.Text "Name of module to load."])
    ]

cryptolLoadFile :: CryptolLoadFileParams -> Method SAWState OK
cryptolLoadFile (CryptolLoadFileParams fileName) =
  do sc <- biSharedContext . view sawBIC <$> getState
     cenv <- rwCryptol . view sawTopLevelRW <$> getState
     let qual = Nothing -- TODO add field to params
     let importSpec = Nothing -- TODO add field to params
     fileReader <- getFileReader
     let ?fileReader = fileReader
     cenv' <- liftIO $ try $ CEnv.importModule sc cenv (Left fileName) qual importSpec
     case cenv' of
       Left (ex :: SomeException) -> raise $ cryptolError (show ex)
       Right cenv'' ->
         do modifyState $ over sawTopLevelRW $ \rw -> rw { rwCryptol = cenv'' }
            ok

data CryptolLoadFileParams =
  CryptolLoadFileParams FilePath

instance FromJSON CryptolLoadFileParams where
  parseJSON =
    withObject "params for \"SAW/Cryptol setup/load file\"" $ \o ->
    CryptolLoadFileParams . T.unpack <$> o .: "file"

instance Doc.DescribedParams CryptolLoadFileParams where
  parameterFieldDescription =
    [ ("file",
       Doc.Paragraph [Doc.Text "File to load as a Cryptol module."])
    ]
