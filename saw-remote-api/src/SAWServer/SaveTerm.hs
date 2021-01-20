{-# LANGUAGE OverloadedStrings #-}
module SAWServer.SaveTerm
  ( saveTerm
  , saveTermDescr
  ) where

import Data.Aeson (FromJSON(..), withObject, (.:))

import Argo
import qualified Argo.Doc as Doc

import CryptolServer.Data.Expression
import SAWServer
import SAWServer.CryptolExpression
import SAWServer.OK

saveTermDescr :: Doc.Block
saveTermDescr =
  Doc.Paragraph [Doc.Text "Save a term to be referenced later by name."]

saveTerm :: SaveTermParams -> Method SAWState OK
saveTerm (SaveTermParams name e) =
  do setServerVal name =<< getTypedTerm e
     ok

data SaveTermParams
  = SaveTermParams ServerName Expression

instance FromJSON SaveTermParams where
  parseJSON =
    withObject "parameters for saving a term" $ \o ->
    SaveTermParams <$> o .: "name"
                   <*> o .: "expression"

instance Doc.DescribedParams SaveTermParams where
  parameterFieldDescription =
    [ ("name",
       Doc.Paragraph [Doc.Text "The name to assign to the expression for later reference."])
    , ("expression",
       Doc.Paragraph [Doc.Text "The expression to save."])
    ]
