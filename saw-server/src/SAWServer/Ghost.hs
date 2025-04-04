{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module SAWServer.Ghost
  ( createGhostVariable
  , createGhostVariableDescr
  ) where

import Data.Aeson (FromJSON(..), withObject, (.:))

import Argo
import qualified Argo.Doc as Doc
import Data.Text (Text)
import Control.Monad.State
import Data.Parameterized.Classes (knownRepr)

import Lang.Crucible.CFG.Common (freshGlobalVar)
import SAWCentral.Crucible.Common.MethodSpec (GhostGlobal)

-- XXX why are we importing what's theoretically the top-level interface from inside?
import SAWServer.SAWServer
import SAWServer.OK

createGhostVariableDescr :: Doc.Block
createGhostVariableDescr =
  Doc.Paragraph [Doc.Text "Create a ghost global variable to represent proof-specific program state."]

freshGhost :: Text -> Command SAWState GhostGlobal
freshGhost name =
  do allocator <- getHandleAlloc
     liftIO (freshGlobalVar allocator name knownRepr)

createGhostVariable :: CreateGhostParams -> Command SAWState OK
createGhostVariable (CreateGhostParams displayName serverName) =
  do setServerVal serverName =<< freshGhost displayName
     ok

data CreateGhostParams
  = CreateGhostParams Text ServerName

instance FromJSON CreateGhostParams where
  parseJSON =
    withObject "parameters for creating a ghost variable" $ \o ->
    CreateGhostParams <$> o .: "display name" <*> o.: "server name"

instance Doc.DescribedMethod CreateGhostParams OK where
  parameterFieldDescription =
    [ ("display name",
       Doc.Paragraph [Doc.Text "The name to assign to the ghost variable for display."])
    , ("server name",
       Doc.Paragraph [Doc.Text "The server name to use to access the ghost variable later."])
    ]
  resultFieldDescription = []
