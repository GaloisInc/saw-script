{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Server.Config where

import Data.Aeson (FromJSON)

newtype Config = Config ()
  deriving (FromJSON)

emptyConfig :: Config
emptyConfig = Config ()
