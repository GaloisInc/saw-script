{- |
Module      : SAWScript.Yosys.IR
Description : Representation for Yosys JSON output
License     : BSD3
Maintainer  : sbreese
Stability   : experimental
-}

{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}
{-# Language LambdaCase #-}
{-# Language TupleSections #-}
{-# Language FlexibleInstances #-}
{-# Language DeriveFunctor #-}

module SAWScript.Yosys.IR where

import Control.Lens.TH (makeLenses)

import Control.Monad.IO.Class (MonadIO(..))
import Control.Exception (throw)

import Data.Map (Map)
import Data.Text (Text)
import qualified Data.Text as Text

import qualified Data.Aeson as Aeson

import SAWScript.Yosys.Utils

--------------------------------------------------------------------------------
-- ** Representing and loading the Yosys JSON IR

-- | The direction of a module port.
data Direction
  = DirectionInput
  | DirectionOutput
  | DirectionInout
  deriving (Show, Eq, Ord)
instance Aeson.FromJSON Direction where
  parseJSON (Aeson.String "input") = pure DirectionInput
  parseJSON (Aeson.String "output") = pure DirectionOutput
  parseJSON (Aeson.String "inout") = pure DirectionInout
  parseJSON v = fail $ "Failed to parse direction: " <> show v

-- | The value of a connection
data Bitrep
  = BitrepZero -- ^ Constant zero bit
  | BitrepOne -- ^ Constant one bit
  | BitrepX -- ^ Undefined bit X
  | BitrepZ -- ^ Undefined bit Z
  | Bitrep Integer -- ^ The signal bit with the given index
  deriving (Show, Eq, Ord)
instance Aeson.FromJSON Bitrep where
  parseJSON (Aeson.String "0") = pure BitrepZero
  parseJSON (Aeson.String "1") = pure BitrepOne
  parseJSON (Aeson.String "x") = pure BitrepX
  parseJSON (Aeson.String "z") = pure BitrepZ
  parseJSON vn@Aeson.Number{} = Bitrep <$> Aeson.parseJSON vn
  parseJSON v = fail $ "Failed to parse bits: " <> show v

-- ^ A module input/output port.
data Port = Port
  { _portDirection :: Direction
  , _portBits :: [Bitrep] -- ^ Which bit indices within the module are associated with the port
  , _portOffset :: Integer -- currently unused
  , _portUpto :: Bool -- currently unused
  } deriving (Show, Eq, Ord)
makeLenses ''Port
instance Aeson.FromJSON Port where
  parseJSON = Aeson.withObject "port" $ \o -> do
    _portDirection <- o Aeson..: "direction"
    _portBits <- o Aeson..: "bits"
    _portOffset <- o Aeson..:? "offset" >>= \case
      Just off -> pure off
      Nothing -> pure 0
    _portUpto <- o Aeson..:? "upto" >>= \case
      Just (Aeson.Number 1) -> pure True
      _ -> pure False
    pure Port{..}

-- | A cell within an HDL module.
data Cell bs = Cell
  { _cellHideName :: Bool -- ^ Whether the cell's name is human-readable
  , _cellType :: Text -- ^ The cell type
  , _cellParameters :: Map Text Text -- ^ Metadata parameters
  , _cellAttributes :: Aeson.Value -- currently unused
  , _cellPortDirections :: Map Text Direction -- ^ Direction for each cell connection
  , _cellConnections :: Map Text bs -- ^ Bitrep for each cell connection
  } deriving (Show, Eq, Ord, Functor)
makeLenses ''Cell
instance Aeson.FromJSON (Cell [Bitrep]) where
  parseJSON = Aeson.withObject "cell" $ \o -> do
    _cellHideName <- o Aeson..:? "hide_name" >>= \case
      Just (Aeson.Number 1) -> pure True
      _ -> pure False
    _cellType <- o Aeson..: "type"
    _cellParameters <- o Aeson..: "parameters"
    _cellAttributes <- o Aeson..: "attributes"
    _cellPortDirections <- o Aeson..: "port_directions"
    _cellConnections <- o Aeson..: "connections"
    pure Cell{..}

-- | A single HDL module.
data Module = Module
  { _moduleAttributes :: Aeson.Value -- currently unused
  , _modulePorts :: Map Text Port
  , _moduleCells :: Map Text (Cell [Bitrep])
  } deriving (Show, Eq, Ord)
makeLenses ''Module
instance Aeson.FromJSON Module where
  parseJSON = Aeson.withObject "module" $ \o -> do
    _moduleAttributes <- o Aeson..: "attributes"
    _modulePorts <- o Aeson..: "ports"
    _moduleCells <- o Aeson..: "cells"
    pure Module{..}

-- | A collection of multiple HDL modules (possibly with dependencies on each other).
data YosysIR = YosysIR
  { _yosysCreator :: Text
  , _yosysModules :: Map Text Module
  } deriving (Show, Eq, Ord)
makeLenses ''YosysIR
instance Aeson.FromJSON YosysIR where
  parseJSON = Aeson.withObject "yosys" $ \o -> do
    _yosysCreator <- o Aeson..: "creator"
    _yosysModules <- o Aeson..: "modules"
    pure YosysIR{..}

-- | Read a collection of HDL modules from a file produced by Yosys' write_json command.
loadYosysIR :: MonadIO m => FilePath -> m YosysIR
loadYosysIR p = liftIO $ Aeson.eitherDecodeFileStrict p >>= \case
  Left err -> throw . YosysError $ Text.pack err
  Right ir -> pure ir
