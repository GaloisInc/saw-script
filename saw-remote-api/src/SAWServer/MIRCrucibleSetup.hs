{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Support for interfacing with MIR-related commands in SAW.
module SAWServer.MIRCrucibleSetup
  ( mirLoadModule
  , mirLoadModuleDescr
  ) where

import Control.Lens ( view )
import Data.Aeson ( FromJSON(..), withObject, (.:) )

import SAWScript.Crucible.MIR.Builtins ( mir_load_module )

import qualified Argo
import qualified Argo.Doc as Doc
import SAWServer as Server
    ( ServerName(..),
      SAWState,
      sawTask,
      setServerVal )
import SAWServer.Exceptions ( notAtTopLevel )
import SAWServer.OK ( OK, ok )
import SAWServer.TopLevel ( tl )
import SAWServer.TrackFile ( trackFile )

data MIRLoadModuleParams
  = MIRLoadModuleParams ServerName FilePath

instance FromJSON MIRLoadModuleParams where
  parseJSON =
    withObject "params for \"SAW/MIR/load module\"" $ \o ->
    MIRLoadModuleParams <$> o .: "name" <*> o .: "module name"

instance Doc.DescribedMethod MIRLoadModuleParams OK where
  parameterFieldDescription =
    [ ("name",
        Doc.Paragraph [Doc.Text "The name to refer to the loaded module by later."])
    , ("module name",
       Doc.Paragraph [Doc.Text "The file containing the MIR JSON file to load."])
    ]
  resultFieldDescription = []

mirLoadModuleDescr :: Doc.Block
mirLoadModuleDescr =
  Doc.Paragraph [Doc.Text "Load the specified MIR module."]

-- | The implementation of the @SAW/MIR/load module@ command.
mirLoadModule :: MIRLoadModuleParams -> Argo.Command SAWState OK
mirLoadModule (MIRLoadModuleParams serverName fileName) =
  do tasks <- view sawTask <$> Argo.getState
     case tasks of
       (_:_) -> Argo.raise $ notAtTopLevel $ map fst tasks
       [] ->
         do mirMod <- tl $ mir_load_module fileName
            setServerVal serverName mirMod
            trackFile fileName
            ok
