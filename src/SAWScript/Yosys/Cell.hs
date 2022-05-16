{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}
{-# Language ViewPatterns #-}
{-# Language LambdaCase #-}
{-# Language MultiWayIf #-}
{-# Language TupleSections #-}
{-# Language ScopedTypeVariables #-}

module SAWScript.Yosys.Cell where

import Control.Lens ((^.))
import Control.Monad (foldM)
import Control.Monad.IO.Class (MonadIO(..))

import qualified Data.Foldable as Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text

import Numeric.Natural (Natural)

import qualified Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.Name as SC

import SAWScript.Panic (panic)

import SAWScript.Yosys.Utils
import SAWScript.Yosys.IR

-- | Given a primitive Yosys cell and a map of terms for its arguments, construct a record term representing the output.
-- If the provided cell is not a primitive, return Nothing.
primCellToTerm ::
  forall m b.
  MonadIO m =>
  SC.SharedContext ->
  Cell [b] {- ^ Cell type -} ->
  Map Text SC.Term {- ^ Mapping of input names to input terms -} ->
  m (Maybe SC.Term)
primCellToTerm sc c args = case c ^. cellType of
  "$not" -> bvUnaryOp $ SC.scBvNot sc
  "$pos" -> do
    res <- input "A"
    fmap Just . cryptolRecord sc $ Map.fromList
      [ ("Y", res)
      ]
  "$neg" -> bvUnaryOp $ SC.scBvNeg sc
  "$and" -> bvNAryOp $ SC.scBvAnd sc
  "$or" -> bvNAryOp $ SC.scBvOr sc
  "$xor" -> bvNAryOp $ SC.scBvXor sc
  "$xnor" -> bvNAryOp $ \w x y -> do
    r <- SC.scBvXor sc w x y
    SC.scBvNot sc w r
  "$reduce_and" -> bvReduce True =<< do
    liftIO . SC.scLookupDef sc $ SC.mkIdent SC.preludeName "and"
  "$reduce_or" -> bvReduce False =<< do
    liftIO . SC.scLookupDef sc $ SC.mkIdent SC.preludeName "or"
  "$reduce_xor" -> bvReduce False =<< do
    liftIO . SC.scLookupDef sc $ SC.mkIdent SC.preludeName "xor"
  "$reduce_xnor" -> bvReduce True =<< do
    boolTy <- liftIO $ SC.scBoolType sc
    xEC <- liftIO $ SC.scFreshEC sc "x" boolTy
    x <- liftIO $ SC.scExtCns sc xEC
    yEC <- liftIO $ SC.scFreshEC sc "y" boolTy
    y <- liftIO $ SC.scExtCns sc yEC
    r <- liftIO $ SC.scXor sc x y
    res <- liftIO $ SC.scNot sc r
    liftIO $ SC.scAbstractExts sc [xEC, yEC] res
  "$reduce_bool" -> bvReduce False =<< do
    liftIO . SC.scLookupDef sc $ SC.mkIdent SC.preludeName "or"
  "$shl" -> bvBinaryOp $ SC.scBvShl sc
  "$shr" -> bvBinaryOp $ SC.scBvShr sc
  "$sshl" -> bvBinaryOp $ SC.scBvShl sc -- same as shl
  "$sshr" -> bvBinaryOp $ SC.scBvSShr sc
  -- "$shift" -> _
  -- "$shiftx" -> _
  "$lt" -> bvBinaryCmp $ SC.scBvULt sc
  "$le" -> bvBinaryCmp $ SC.scBvULe sc
  "$gt" -> bvBinaryCmp $ SC.scBvUGt sc
  "$ge" -> bvBinaryCmp $ SC.scBvUGe sc
  "$eq" -> bvBinaryCmp $ SC.scBvEq sc
  "$ne" -> bvBinaryCmp $ \w x y -> do
    r <- SC.scBvEq sc w x y
    SC.scNot sc r
  "$eqx" -> bvBinaryCmp $ SC.scBvEq sc
  "$nex" -> bvBinaryCmp $ \w x y -> do
    r <- SC.scBvEq sc w x y
    SC.scNot sc r
  "$add" -> bvNAryOp $ SC.scBvAdd sc
  "$sub" -> bvBinaryOp $ SC.scBvSub sc
  "$mul" -> bvNAryOp $ SC.scBvMul sc
  "$div" -> bvBinaryOp $ SC.scBvUDiv sc
  "$mod" -> bvBinaryOp $ SC.scBvURem sc
  -- "$modfloor" -> _
  "$logic_not" -> do
    w <- outputWidth
    ta <- input "A"
    anz <- liftIO $ SC.scBvNonzero sc w ta
    res <- liftIO $ SC.scNot sc anz
    fmap Just . cryptolRecord sc $ Map.fromList
      [ ("Y", res)
      ]
  "$logic_and" -> do
    w <- outputWidth
    ta <- input "A"
    tb <- input "B"
    anz <- liftIO $ SC.scBvNonzero sc w ta
    bnz <- liftIO $ SC.scBvNonzero sc w tb
    res <- liftIO $ SC.scAnd sc anz bnz
    fmap Just . cryptolRecord sc $ Map.fromList
      [ ("Y", res)
      ]
  "$logic_or" -> do
    w <- outputWidth
    ta <- input "A"
    tb <- input "B"
    anz <- liftIO $ SC.scBvNonzero sc w ta
    bnz <- liftIO $ SC.scBvNonzero sc w tb
    res <- liftIO $ SC.scOr sc anz bnz
    fmap Just . cryptolRecord sc $ Map.fromList
      [ ("Y", res)
      ]
  "$mux" -> do
    ta <- input "A"
    tb <- input "B"
    ts <- input "S"
    swidth <- connWidth "S"
    snz <- liftIO $ SC.scBvNonzero sc swidth ts
    ty <- liftIO $ SC.scBitvector sc outputWidthNat
    res <- liftIO $ SC.scIte sc ty snz tb ta
    fmap Just . cryptolRecord sc $ Map.fromList
      [ ("Y", res)
      ]
  -- "$pmux" -> _
  -- "$bmux" -> _
  -- "$demux" -> _
  -- "$lut" -> _
  -- "$slice" -> _
  -- "$concat" -> _
  _ -> pure Nothing
  where
    nm = c ^. cellType
    connWidthNat :: Text -> Natural
    connWidthNat onm =
      case Map.lookup onm $ c ^. cellConnections of
        Nothing -> panic "cellToTerm" [Text.unpack $ mconcat ["Missing expected output name for ", nm, " cell"]]
        Just bits -> fromIntegral $ length bits
    connWidth :: Text -> m SC.Term
    connWidth onm = liftIO . SC.scNat sc $ connWidthNat onm
    outputWidthNat = connWidthNat "Y"
    outputWidth = connWidth "Y"
    input :: Text -> m SC.Term
    input inpNm =
      case Map.lookup inpNm args of
        Nothing -> panic "cellToTerm" [Text.unpack $ mconcat [nm, " missing input ", inpNm]]
        Just a -> pure a
    bvUnaryOp :: (SC.Term -> SC.Term -> IO SC.Term) -> m (Maybe SC.Term)
    bvUnaryOp f = do
      t <- input "A"
      w <- outputWidth
      res <- liftIO $ f w t
      fmap Just . cryptolRecord sc $ Map.fromList
        [ ("Y", res)
        ]
    bvBinaryOp :: (SC.Term -> SC.Term -> SC.Term -> IO SC.Term) -> m (Maybe SC.Term)
    bvBinaryOp f = do
      ta <- input "A"
      tb <- input "B"
      w <- outputWidth
      res <- liftIO $ f w ta tb
      fmap Just . cryptolRecord sc $ Map.fromList
        [ ("Y", res)
        ]
    bvBinaryCmp :: (SC.Term -> SC.Term -> SC.Term -> IO SC.Term) -> m (Maybe SC.Term)
    bvBinaryCmp f = do
      ta <- input "A"
      tb <- input "B"
      w <- outputWidth
      bit <- liftIO $ f w ta tb
      boolty <- liftIO $ SC.scBoolType sc
      res <- liftIO $ SC.scSingle sc boolty bit
      fmap Just . cryptolRecord sc $ Map.fromList
        [ ("Y", res)
        ]
    bvNAryOp :: (SC.Term -> SC.Term -> SC.Term -> IO SC.Term) -> m (Maybe SC.Term)
    bvNAryOp f =
      case Foldable.toList args of
        [] -> panic "cellToTerm" [Text.unpack $ mconcat [nm, " cell given no inputs"]]
        (t:rest) -> do
          w <- outputWidth
          res <- liftIO $ foldM (f w) t rest
          fmap Just . cryptolRecord sc $ Map.fromList
            [ ("Y", res)
            ]
    bvReduce :: Bool -> SC.Term -> m (Maybe SC.Term)
    bvReduce boolIdentity boolFun = do
      t <- input "A"
      w <- outputWidth
      boolTy <- liftIO $ SC.scBoolType sc
      identity <- liftIO $ SC.scBool sc boolIdentity
      scFoldr <- liftIO . SC.scLookupDef sc $ SC.mkIdent SC.preludeName "foldr"
      bit <- liftIO $ SC.scApplyAll sc scFoldr [boolTy, boolTy, w, boolFun, identity, t]
      boolty <- liftIO $ SC.scBoolType sc
      res <- liftIO $ SC.scSingle sc boolty bit
      fmap Just . cryptolRecord sc $ Map.fromList
        [ ("Y", res)
        ]
