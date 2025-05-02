{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
module SAWServer.SetOption
  ( setOption
  , setOptionDescr
  ) where

import Control.Applicative
import Control.Lens (view, set)
import Data.Aeson (FromJSON(..), Object, withObject, (.:))
import Data.Aeson.Types (Parser)

import SAWCentral.Value

import qualified Argo
import qualified Argo.Doc as Doc

-- XXX why are we importing what's theoretically the top-level interface from inside?
import SAWServer.SAWServer ( SAWState, sawTopLevelRW )
import SAWServer.OK ( OK, ok )


setOptionDescr :: Doc.Block
setOptionDescr =
  Doc.Paragraph [Doc.Text "Set a SAW option in the server."]

setOption :: SetOptionParams -> Argo.Command SAWState OK
setOption opt =
  do rw <- view sawTopLevelRW <$> Argo.getState
     let updateRW = Argo.modifyState . set sawTopLevelRW
     case opt of
       EnableLaxArithmetic enabled ->
         updateRW rw { rwLaxArith = enabled }
       EnableLaxPointerOrdering enabled ->
         updateRW rw { rwLaxPointerOrdering = enabled }
       EnableLaxLoadsAndStores enabled ->
         updateRW rw { rwLaxLoadsAndStores = enabled }
       EnableDebugIntrinsics enabled ->
         updateRW rw { rwDebugIntrinsics = enabled }
       EnableSMTArrayMemoryModel enabled ->
         updateRW rw { rwSMTArrayMemoryModel = enabled }
       EnableWhat4HashConsing enabled ->
         updateRW rw { rwWhat4HashConsing = enabled }
       EnableWhat4Eval enabled ->
         updateRW rw { rwWhat4Eval = enabled }
     ok

data SetOptionParams
  = EnableLaxArithmetic Bool
  | EnableLaxPointerOrdering Bool
  | EnableLaxLoadsAndStores Bool
  | EnableDebugIntrinsics Bool
  | EnableSMTArrayMemoryModel Bool
  | EnableWhat4HashConsing Bool
  | EnableWhat4Eval Bool

parseOption :: Object -> String -> Parser SetOptionParams
parseOption o name =
  case name of
    "lax arithmetic" -> EnableLaxArithmetic <$> o .: "value"
    "lax pointer ordering" -> EnableLaxPointerOrdering <$> o .: "value"
    "lax loads and stores" -> EnableLaxLoadsAndStores <$> o .: "value"
    "debug intrinsics" -> EnableDebugIntrinsics <$> o .: "value"
    "SMT array memory model" -> EnableSMTArrayMemoryModel <$> o .: "value"
    "What4 hash consing" -> EnableWhat4HashConsing <$> o .: "value"
    "What4 eval" -> EnableWhat4Eval <$> o .: "value"
    _ -> empty

instance FromJSON SetOptionParams where
  parseJSON =
    withObject "parameters for setting options" $ \o -> o .: "option" >>= parseOption o


instance Doc.DescribedMethod SetOptionParams OK where
  parameterFieldDescription =
    [ ("option",
       Doc.Paragraph [Doc.Text "The option to set and its accompanying value (i.e., true or false); one of the following:"
                     , Doc.Literal "lax arithmetic", Doc.Text ", "
                     , Doc.Literal "lax pointer ordering", Doc.Text ", "
                     , Doc.Literal "lax loads and stores", Doc.Text ", "
                     , Doc.Literal "debug intrinsics", Doc.Text ", "
                     , Doc.Literal "SMT array memory model", Doc.Text ", "
                     , Doc.Literal "What4 hash consing", Doc.Text ", or "
                     , Doc.Literal "What4 eval"
                     ])
    ]
  resultFieldDescription = []
