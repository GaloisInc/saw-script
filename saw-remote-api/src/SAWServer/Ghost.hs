{-# LANGUAGE OverloadedStrings #-}
module SAWServer.Ghost
  ( createGhostVariable
  , createGhostVariableDescr
  ) where

import Data.Aeson (FromJSON(..), withObject, (.:))

import Argo
import qualified Argo.Doc as Doc
import Control.Monad.State
import Data.Parameterized.Classes (knownRepr)

import Lang.Crucible.CFG.Common (freshGlobalVar)
import SAWScript.Crucible.Common.MethodSpec (GhostGlobal)

import SAWServer
import SAWServer.OK

createGhostVariableDescr :: Doc.Block
createGhostVariableDescr =
  Doc.Paragraph [Doc.Text "Create a ghost global variable to represent proof-specific program state."]

freshGhost :: ServerName -> Method SAWState GhostGlobal
freshGhost (ServerName name) =
  do allocator <- getHandleAlloc
     liftIO (freshGlobalVar allocator name knownRepr)

createGhostVariable :: CreateGhostParams -> Method SAWState OK
createGhostVariable (CreateGhostParams name) =
  do setServerVal name =<< freshGhost name
     ok

data CreateGhostParams
  = CreateGhostParams ServerName

instance FromJSON CreateGhostParams where
  parseJSON =
    withObject "parameters for creating a ghost variable" $ \o ->
    CreateGhostParams <$> o .: "name"

instance Doc.DescribedParams CreateGhostParams where
  parameterFieldDescription =
    [ ("name",
       Doc.Paragraph [Doc.Text "The name to assign to the ghost variable for later reference."])
    ]
