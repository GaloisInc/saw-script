{- |
Module      : SAWCentral.Yosys.IR
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

module SAWCentral.Yosys.IR (
    isOutput,
    Bitrep(..),
    CellTypeCombinational(..),
    CellTypeRegister(..),
    CellType(..),
    ppCellTypeCombinational,
    Cell,
      cellHideName,
      cellType,
      cellParameters,
      cellAttributes,
      cellPortDirections,
      cellConnections,
    Module,
      moduleAttributes,
      modulePorts,
      moduleCells,
      moduleNetnames,
    YosysIR,
      yosysCreator,
      yosysModules,
    loadYosysIR,
    moduleInputPorts,
    moduleOutputPorts,
    cellInputConnections,
    cellOutputConnections,
    cellIsRegister,
    renameDffInstances
  ) where

import Control.Lens.TH (makeLenses)

import Control.Lens ((^.), set)

import qualified Data.Maybe as Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text

import qualified Data.Aeson as Aeson

import SAWCentral.Yosys.Utils

--------------------------------------------------------------------------------
-- ** Representing and loading the Yosys JSON IR

-- | The direction of a module port.
data Direction
  = DirectionInput
  | DirectionOutput
  | DirectionInout
  deriving (Show, Eq, Ord)

isInput :: Direction -> Bool
isInput d =
  case d of
    DirectionInput -> True
    DirectionOutput -> False
    DirectionInout -> True

isOutput :: Direction -> Bool
isOutput d =
  case d of
    DirectionInput -> False
    DirectionOutput -> True
    DirectionInout -> True

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
  } deriving (Show, Eq, Ord)

makeLenses ''Port

instance Aeson.FromJSON Port where
  parseJSON = Aeson.withObject "port" $ \o -> do
    _portDirection <- o Aeson..: "direction"
    _portBits <- o Aeson..: "bits"
    pure Port{..}

-- | Return 'True' iff a given cell type is a primitive type
cellTypeIsPrimitive :: Text -> Bool
cellTypeIsPrimitive cellType =
  case Text.uncons cellType of
    Just ('$', _) -> True
    _ -> False

-- | Mapping from 'Text' to combinational primitive cell types.
textToCellTypeCombinational :: Map Text CellTypeCombinational
textToCellTypeCombinational =
  Map.fromList [ (ppCellTypeCombinational t, t) | t <- [minBound .. maxBound] ]

-- | Mapping from 'Text' to primitive register cell types.
textToCellTypeRegister :: Map Text CellTypeRegister
textToCellTypeRegister =
  Map.fromList [ (ppCellTypeRegister t, t) | t <- [minBound .. maxBound] ]

-- | Mapping from 'Text' to primitive cell types.
textToPrimitiveCellType :: Map Text CellType
textToPrimitiveCellType =
  fmap CellTypeRegister textToCellTypeRegister <>
  fmap CellTypeCombinational textToCellTypeCombinational

-- | All supported primitive combinational cell types.
data CellTypeCombinational
  = CellTypeNot
  | CellTypePos
  | CellTypeNeg
  | CellTypeAnd
  | CellTypeOr
  | CellTypeXor
  | CellTypeXnor
  | CellTypeReduceAnd
  | CellTypeReduceOr
  | CellTypeReduceXor
  | CellTypeReduceXnor
  | CellTypeReduceBool
  | CellTypeShl
  | CellTypeShr
  | CellTypeSshl
  | CellTypeSshr
  | CellTypeShift
  | CellTypeShiftx
  | CellTypeLt
  | CellTypeLe
  | CellTypeGt
  | CellTypeGe
  | CellTypeEq
  | CellTypeNe
  | CellTypeEqx
  | CellTypeNex
  | CellTypeAdd
  | CellTypeSub
  | CellTypeMul
  | CellTypeDiv
  | CellTypeMod
  | CellTypeLogicNot
  | CellTypeLogicAnd
  | CellTypeLogicOr
  | CellTypeMux
  | CellTypePmux
  | CellTypeBmux
  | CellTypeBUF
  deriving (Eq, Ord, Enum, Bounded)

-- | All supported primitive register cell types.
data CellTypeRegister
  = CellTypeAdff
  | CellTypeAdffe
  | CellTypeAldff
  | CellTypeAldffe
  | CellTypeDff
  | CellTypeDffe
  | CellTypeFf
  | CellTypeSdff
  | CellTypeSdffe
  deriving (Eq, Ord, Enum, Bounded)

-- | All supported cell types.
-- All types are primitives except for 'CellTypeUserType' which
-- represents user-defined submodules.
-- Invariants: 'CellTypeUnsupportedPrimitive' should only be applied
-- to names satisfying 'cellTypeIsPrimitive', and 'CellTypeUserType'
-- should only be applied to names *not* satisfying
-- 'cellTypeIsPrimitive'.
data CellType
  = CellTypeCombinational CellTypeCombinational
  | CellTypeRegister CellTypeRegister
  | CellTypeUnsupportedPrimitive CellTypeName
  | CellTypeUserType CellTypeName
  deriving (Eq, Ord)

instance Aeson.FromJSON CellType where
  parseJSON (Aeson.String s) =
    case s of
      "$dffsr"       -> fail $ show $ YosysErrorUnsupportedFF "$dffsr"
      "$sdffce"      -> fail $ show $ YosysErrorUnsupportedFF "$sdffce"
      "$dffsre"      -> fail $ show $ YosysErrorUnsupportedFF "$dffsre"
      _ | cellTypeIsPrimitive s ->
          case Map.lookup s textToPrimitiveCellType of
            Just cellType -> pure cellType
            -- XXX We should probably log a warning when generating CellTypeUnsupportedPrimitive,
            -- we can't do that here however.
            Nothing -> pure $ CellTypeUnsupportedPrimitive s
        | otherwise -> pure $ CellTypeUserType s
  parseJSON v = fail $ "Failed to parse cell type: " <> show v

ppCellTypeCombinational :: CellTypeCombinational -> Text
ppCellTypeCombinational ctc =
  case ctc of
    CellTypeNot        -> "$not"
    CellTypePos        -> "$pos"
    CellTypeNeg        -> "$neg"
    CellTypeAnd        -> "$and"
    CellTypeOr         -> "$or"
    CellTypeXor        -> "$xor"
    CellTypeXnor       -> "$xnor"
    CellTypeReduceAnd  -> "$reduce_and"
    CellTypeReduceOr   -> "$reduce_or"
    CellTypeReduceXor  -> "$reduce_xor"
    CellTypeReduceXnor -> "$reduce_xnor"
    CellTypeReduceBool -> "$reduce_bool"
    CellTypeShl        -> "$shl"
    CellTypeShr        -> "$shr"
    CellTypeSshl       -> "$sshl"
    CellTypeSshr       -> "$sshr"
    CellTypeShift      -> "$shift"
    CellTypeShiftx     -> "$shiftx"
    CellTypeLt         -> "$lt"
    CellTypeLe         -> "$le"
    CellTypeGt         -> "$gt"
    CellTypeGe         -> "$ge"
    CellTypeEq         -> "$eq"
    CellTypeNe         -> "$ne"
    CellTypeEqx        -> "$eqx"
    CellTypeNex        -> "$nex"
    CellTypeAdd        -> "$add"
    CellTypeSub        -> "$sub"
    CellTypeMul        -> "$mul"
    CellTypeDiv        -> "$div"
    CellTypeMod        -> "$mod"
    CellTypeLogicNot   -> "$logic_not"
    CellTypeLogicAnd   -> "$logic_and"
    CellTypeLogicOr    -> "$logic_or"
    CellTypeMux        -> "$mux"
    CellTypePmux       -> "$pmux"
    CellTypeBmux       -> "$bmux"
    CellTypeBUF        -> "$_BUF_"

instance Show CellTypeCombinational where
  show ctc = Text.unpack (ppCellTypeCombinational ctc)

ppCellTypeRegister :: CellTypeRegister -> Text
ppCellTypeRegister ctr =
  case ctr of
    CellTypeAdff -> "$adff"
    CellTypeAdffe -> "$adffe"
    CellTypeAldff -> "$aldff"
    CellTypeAldffe -> "$aldffe"
    CellTypeDff -> "$dff"
    CellTypeDffe -> "$dffe"
    CellTypeFf -> "$ff"
    CellTypeSdff -> "$sdff"
    CellTypeSdffe -> "$sdffe"

ppCellType :: CellType -> Text
ppCellType ct =
  case ct of
    CellTypeCombinational ctc -> ppCellTypeCombinational ctc
    CellTypeRegister ctr -> ppCellTypeRegister ctr
    CellTypeUnsupportedPrimitive t -> t
    CellTypeUserType t -> t

instance Show CellType where
  show ct = Text.unpack (ppCellType ct)

-- | A cell within an HDL module.
data Cell =
  Cell
  { _cellHideName :: Bool -- ^ Whether the cell's name is human-readable (default: False)
  , _cellType :: CellType -- ^ The cell type
    -- NB: Yosys's documentation for write_json doesn't impose any restrictions
    -- on what type parameter values may take on, so we opt to be as permissive
    -- as possible by using Aeson Values. Most of the time, these Values will
    -- be strings, but they can also be numbers on occasion (e.g., if you call
    -- write_json using the -compat-int flag).
  , _cellParameters :: Map Text Aeson.Value -- ^ Metadata parameters
  , _cellAttributes :: Maybe Aeson.Value -- currently unused
  , _cellPortDirections :: Map PortName Direction -- ^ Direction for each cell connection
  , _cellConnections :: Map PortName [Bitrep] -- ^ Bitrep for each cell connection
  }
  deriving (Show, Eq, Ord)

makeLenses ''Cell

instance Aeson.FromJSON Cell where
  parseJSON = Aeson.withObject "cell" $ \o -> do
    _cellHideName <- Maybe.maybe False (/= (0::Int)) <$> o Aeson..:? "hide_name"
    _cellType <- o Aeson..: "type"
    _cellParameters <- o Aeson..: "parameters"
    _cellAttributes <- o Aeson..:? "attributes"
    _cellPortDirections <- o Aeson..: "port_directions"
    _cellConnections <- o Aeson..: "connections"
    pure Cell{..}

-- | A description of a named internal signal within a module.
data Netname =
  Netname
  { _netnameHideName :: Bool -- ^ Whether the net's name is human-readable (default: False)
  , _netnameBits :: [Bitrep]
  } deriving (Show, Eq, Ord)

makeLenses ''Netname

instance Aeson.FromJSON Netname where
  parseJSON =
    Aeson.withObject "netname" $ \o ->
    do _netnameHideName <- Maybe.maybe False (/= (0::Int)) <$> o Aeson..:? "hide_name"
       _netnameBits <- o Aeson..: "bits"
       pure Netname{..}

-- | A single HDL module.
data Module = Module
  { _moduleAttributes :: Maybe Aeson.Value -- currently unused
  , _modulePorts :: Map PortName Port
  , _moduleCells :: Map CellInstName Cell
  , _moduleNetnames :: Map Text Netname
  } deriving (Show, Eq, Ord)

makeLenses ''Module

instance Aeson.FromJSON Module where
  parseJSON = Aeson.withObject "module" $ \o -> do
    _moduleAttributes <- o Aeson..:? "attributes"
    _modulePorts <- Maybe.fromMaybe mempty <$> o Aeson..:? "ports"
    _moduleCells <- Maybe.fromMaybe mempty <$> o Aeson..:? "cells"
    _moduleNetnames <- Maybe.fromMaybe mempty <$> o Aeson..:? "netnames"
    pure Module{..}

-- | A collection of multiple HDL modules (possibly with dependencies on each other).
data YosysIR = YosysIR
  { _yosysCreator :: Text
  , _yosysModules :: Map CellTypeName Module
  } deriving (Show, Eq, Ord)

makeLenses ''YosysIR

instance Aeson.FromJSON YosysIR where
  parseJSON = Aeson.withObject "yosys" $ \o -> do
    _yosysCreator <- Maybe.fromMaybe mempty <$> o Aeson..:? "creator"
    _yosysModules <- Maybe.fromMaybe mempty <$> o Aeson..:? "modules"
    pure YosysIR{..}

-- | Read a collection of HDL modules from a file produced by Yosys' write_json command.
loadYosysIR :: FilePath -> IO YosysIR
loadYosysIR p = Aeson.eitherDecodeFileStrict p >>= \case
  Left err -> yosysError $ YosysError $ Text.pack err
  Right ir -> pure ir

-- | Return the patterns for all of the input ports of a module
moduleInputPorts :: Module -> Map PortName [Bitrep]
moduleInputPorts m =
  Map.mapMaybe
  ( \ip ->
      if ip ^. portDirection == DirectionInput || ip ^. portDirection == DirectionInout
      then Just (ip ^. portBits)
      else Nothing
  )
  $ m ^. modulePorts

-- | Return the patterns for all of the output ports of a module
moduleOutputPorts :: Module -> Map PortName [Bitrep]
moduleOutputPorts m =
  Map.mapMaybe
  ( \ip ->
      if isOutput (ip ^. portDirection)
      then Just (ip ^. portBits)
      else Nothing
  )
  $ m ^. modulePorts

-- | Return the patterns for all of the input connections of a cell
cellInputConnections :: Cell -> Map PortName [Bitrep]
cellInputConnections c = Map.intersection (c ^. cellConnections) inp
  where
    inp = Map.filter isInput (c ^. cellPortDirections)

-- | Return the patterns for all of the output connections of a cell
cellOutputConnections :: Cell -> Map PortName [Bitrep]
cellOutputConnections c = Map.intersection (c ^. cellConnections) out
  where
    out = Map.filter isOutput (c ^. cellPortDirections)

-- | Test whether a 'Cell' is a state element ('CellTypeDff' or 'CellTypeFf').
cellIsRegister :: Cell -> Bool
cellIsRegister c =
  case c ^. cellType of
    CellTypeRegister _ -> True
    _ -> False

-- | Swap out machine-generated names of DFF cells for user-provided
-- names from the netnames section of the module, wherever possible.
-- If no suitable name exists in the netnames table, then use function
-- 'cellIdentifier' to produce a lexically-valid field name.
renameDffInstances :: Module -> Module
renameDffInstances m = set moduleCells cells' m
  where
    cells' :: Map CellInstName Cell
    cells' =
      Map.fromList $
      map (\(t, c) -> (bestName t c, c)) $
      Map.toList (m ^. moduleCells)

    netnames :: Map [Bitrep] CellInstName
    netnames =
      Map.fromList
      [ (n ^. netnameBits, t)
      | (t, n) <- Map.assocs (m ^. moduleNetnames), not (n ^. netnameHideName) ]

    bestName :: CellInstName -> Cell -> CellInstName
    bestName t c
      | cellIsRegister c =
          Maybe.fromMaybe (cellIdentifier t) $
          do bs <- Map.lookup "Q" (c ^. cellConnections)
             Map.lookup bs netnames
      | otherwise =
          t
