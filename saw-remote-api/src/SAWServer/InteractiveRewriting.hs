{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module SAWServer.InteractiveRewriting where

import Data.Aeson

import Data.Text (Text)
import qualified Data.Text as Text

import qualified Argo
import qualified Argo.Doc as Doc

import SAWServer
import SAWServer.OK (OK, ok)
import SAWServer.TopLevel (tl)

import SAWScript.Interpreter (include_value)

includeSAWScriptDescr :: Doc.Block
includeSAWScriptDescr =
  Doc.Paragraph [Doc.Text "Include a SAWScript file."]

includeSAWScript :: IncludeSAWScriptParams -> Argo.Command SAWState OK
includeSAWScript (IncludeSAWScriptParams path) = do
  tl . include_value $ Text.unpack path
  ok

data IncludeSAWScriptParams = IncludeSAWScriptParams Text

instance FromJSON IncludeSAWScriptParams where
  parseJSON = withObject "parameters for including SAWScript source" $ \o ->
    IncludeSAWScriptParams <$> o .: "path"

instance Doc.DescribedMethod IncludeSAWScriptParams OK where
  parameterFieldDescription =
    [ ( "path"
      , Doc.Paragraph [Doc.Text "The path to the SAWScript pile to import."]
      )
    ]
  resultFieldDescription = []

readExtcoreDescr :: Doc.Block
readExtcoreDescr =
  Doc.Paragraph [Doc.Text "Read a SAWCore external term."]

readExtcoreScript :: ReadExtcoreParams -> Argo.Command SAWState OK
readExtcoreScript (ReadExtcoreParams nm path) = do
  tl . include_value $ Text.unpack path
  ok

data ReadExtcoreParams = ReadExtcoreParams ServerName Text

instance FromJSON ReadExtcoreParams where
  parseJSON = withObject "parameters for reading a SAWCore external term" $ \o ->
    ReadExtcoreParams
    <$> o .: "nm"
    <*> o .: "path"

instance Doc.DescribedMethod ReadExtcoreParams OK where
  parameterFieldDescription =
    [ ( "nm"
      , Doc.Paragraph [Doc.Text "The name to use for the term."]
      )
    , ( "path"
      , Doc.Paragraph [Doc.Text "The path to the SAWCore external file to read."]
      )
    ]
  resultFieldDescription = []
