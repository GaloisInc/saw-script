{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SAWServer.CryptolSetup
  ( cryptolLoadFile
  , cryptolLoadFileDescr
  , cryptolLoadModule
  , cryptolLoadModuleDescr
  ) where

import Control.Exception (SomeException, try)
import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Control.Lens ( view, over )
import Data.Aeson (FromJSON(..), withObject, (.:))
import qualified Data.Text as T

import qualified Cryptol.Parser.AST as P
import Cryptol.Utils.Ident (textToModName)
import SAWScript.Value (biSharedContext, rwCryptol)
import qualified Verifier.SAW.CryptolEnv as CEnv

import qualified Argo
import qualified Argo.Doc as Doc
import SAWServer ( SAWState, sawBIC, sawTopLevelRW )
import SAWServer.Exceptions ( cryptolError )
import SAWServer.OK ( OK, ok )

cryptolLoadModuleDescr :: Doc.Block
cryptolLoadModuleDescr =
  Doc.Paragraph [Doc.Text "Load the specified Cryptol module."]

cryptolLoadModule :: CryptolLoadModuleParams -> Argo.Command SAWState OK
cryptolLoadModule (CryptolLoadModuleParams modName) =
  do sc <- biSharedContext . view sawBIC <$> Argo.getState
     cenv <- rwCryptol . view sawTopLevelRW <$> Argo.getState
     let qual = Nothing -- TODO add field to params
     let importSpec = Nothing -- TODO add field to params
     fileReader <- Argo.getFileReader
     let ?fileReader = fileReader
     cenv' <- liftIO $ try $ CEnv.importModule sc cenv (Right modName) qual CEnv.PublicAndPrivate importSpec
     case cenv' of
       Left (ex :: SomeException) -> Argo.raise $ cryptolError (show ex)
       Right cenv'' ->
         do Argo.modifyState $ over sawTopLevelRW $ \rw -> rw { rwCryptol = cenv'' }
            ok

newtype CryptolLoadModuleParams =
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


cryptolLoadFileDescr :: Doc.Block
cryptolLoadFileDescr =
  Doc.Paragraph [Doc.Text "Load the given file as a Cryptol module."]


cryptolLoadFile :: CryptolLoadFileParams -> Argo.Command SAWState OK
cryptolLoadFile (CryptolLoadFileParams fileName) =
  do sc <- biSharedContext . view sawBIC <$> Argo.getState
     cenv <- rwCryptol . view sawTopLevelRW <$> Argo.getState
     let qual = Nothing -- TODO add field to params
     let importSpec = Nothing -- TODO add field to params
     fileReader <- Argo.getFileReader
     let ?fileReader = fileReader
     cenv' <- liftIO $ try $ CEnv.importModule sc cenv (Left fileName) qual CEnv.PublicAndPrivate importSpec
     case cenv' of
       Left (ex :: SomeException) -> Argo.raise $ cryptolError (show ex)
       Right cenv'' ->
         do Argo.modifyState $ over sawTopLevelRW $ \rw -> rw { rwCryptol = cenv'' }
            ok

newtype CryptolLoadFileParams =
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
