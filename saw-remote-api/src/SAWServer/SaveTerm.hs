{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module SAWServer.SaveTerm
  ( saveTerm
  , saveTermDescr
  ) where

import Data.Aeson (FromJSON(..), withObject, (.:))

import qualified Argo
import qualified Argo.Doc as Doc

import CryptolServer.Data.Expression ( Expression )
import SAWServer ( ServerName, SAWState, setServerVal )
import SAWServer.CryptolExpression ( getTypedTerm )
import SAWServer.OK ( OK, ok )

saveTermDescr :: Doc.Block
saveTermDescr =
  Doc.Paragraph [Doc.Text "Save a term to be referenced later by name."]

saveTerm :: SaveTermParams -> Argo.Command SAWState OK
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

instance Doc.DescribedMethod SaveTermParams OK where
  parameterFieldDescription =
    [ ("name",
       Doc.Paragraph [Doc.Text "The name to assign to the expression for later reference."])
    , ("expression",
       Doc.Paragraph [Doc.Text "The expression to save."])
    ]
  resultFieldDescription = []
