{-# LANGUAGE OverloadedStrings #-}
module SAWServer.SaveTerm (saveTerm) where

import Data.Aeson (FromJSON(..), withObject, (.:))

import Argo

import CryptolServer.Data.Expression
import SAWServer
import SAWServer.CryptolExpression
import SAWServer.OK

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
