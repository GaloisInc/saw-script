module SAWServer.NoParams (NoParams(..)) where

import Data.Aeson
import qualified Argo.Doc as Doc

data NoParams = NoParams

instance ToJSON NoParams where
  toJSON NoParams = object []

instance FromJSON NoParams where
  parseJSON = withObject "no parameters" (const (pure NoParams))

instance Doc.DescribedParams NoParams where
  parameterFieldDescription = []
