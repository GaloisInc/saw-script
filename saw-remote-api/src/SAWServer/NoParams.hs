module SAWServer.NoParams (NoParams(..)) where

import Data.Aeson

data NoParams = NoParams

instance ToJSON NoParams where
  toJSON NoParams = object []

instance FromJSON NoParams where
  parseJSON = withObject "no parameters" (const (pure NoParams))
