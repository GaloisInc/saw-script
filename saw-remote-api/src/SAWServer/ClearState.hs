{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module SAWServer.ClearState
  ( clearState
  , clearStateDescr
  , clearAllStates
  , clearAllStatesDescr
  ) where

import qualified Argo
import qualified Argo.Doc as Doc
import qualified Data.Aeson as JSON
import Data.Aeson ((.:))

newtype ClearStateParams = ClearStateParams Argo.StateID

instance JSON.FromJSON ClearStateParams where
  parseJSON =
    JSON.withObject "params for \"clear state\"" $
    \o -> ClearStateParams <$> o .: "state to clear"

instance Doc.DescribedMethod ClearStateParams () where
  parameterFieldDescription =
    [("state to clear",
       Doc.Paragraph [Doc.Text "The state to clear from the server to make room for other unrelated states."])
     ]

clearStateDescr :: Doc.Block
clearStateDescr =
  Doc.Paragraph [Doc.Text "Clear a particular state from the SAW server (making room for subsequent/unrelated states)."]

clearState :: ClearStateParams -> Argo.Notification ()
clearState (ClearStateParams stateID) = Argo.destroyState stateID





data ClearAllStatesParams = ClearAllStatesParams

instance JSON.FromJSON ClearAllStatesParams where
  parseJSON =
    JSON.withObject "params for \"clear all states\"" $
    \_ -> pure ClearAllStatesParams

instance Doc.DescribedMethod ClearAllStatesParams () where
  parameterFieldDescription = []

clearAllStatesDescr :: Doc.Block
clearAllStatesDescr =
  Doc.Paragraph [Doc.Text "Clear all states from the SAW server (making room for subsequent/unrelated states)."]

clearAllStates :: ClearAllStatesParams -> Argo.Notification ()
clearAllStates ClearAllStatesParams = Argo.destroyAllStates
