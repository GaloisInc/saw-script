{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
module SAWServer.SetOption (setOption) where

import Control.Applicative
import Control.Lens (view, set)
import Data.Aeson (FromJSON(..), Object, withObject, (.:))
import Data.Aeson.Types (Parser)

import SAWScript.Value

import Argo

import SAWServer
import SAWServer.OK

setOption :: SetOptionParams -> Method SAWState OK
setOption opt =
  do rw <- view sawTopLevelRW <$> getState
     let updateRW = modifyState . set sawTopLevelRW
     case opt of
       EnableLaxArithmetic enabled ->
         updateRW rw { rwLaxArith = enabled }
       EnableSMTArrayMemoryModel enabled -> undefined
         updateRW rw { rwSMTArrayMemoryModel = enabled }
       EnableWhat4HashConsing enabled -> undefined
         updateRW rw { rwWhat4HashConsing = enabled }
     ok

data SetOptionParams
  = EnableLaxArithmetic Bool
  | EnableSMTArrayMemoryModel Bool
  | EnableWhat4HashConsing Bool

parseOption :: Object -> String -> Parser SetOptionParams
parseOption o name =
  case name of
    "lax arithmetic" -> EnableLaxArithmetic <$> o .: "value"
    "SMT array memory model" -> EnableSMTArrayMemoryModel <$> o .: "value"
    "What4 hash consing" -> EnableWhat4HashConsing <$> o .: "value"
    _ -> empty

instance FromJSON SetOptionParams where
  parseJSON =
    withObject "parameters for setting options" $ \o -> o .: "option" >>= parseOption o

