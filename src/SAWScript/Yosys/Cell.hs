{- |
Module      : SAWScript.Yosys.Cell
Description : Translating Yosys cells into SAWCore
License     : BSD3
Maintainer  : sbreese
Stability   : experimental
-}

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
import Control.Monad.IO.Class (MonadIO(..))
import Control.Exception (throw)

import Data.Char (digitToInt)
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
primCellToTerm sc c args = traverse (validateTerm sc typeCheckMsg) =<< case c ^. cellType of
  "$not" -> bvUnaryOp $ SC.scBvNot sc
  "$pos" -> do
    res <- input "A"
    output res
  "$neg" -> bvUnaryOp $ SC.scBvNeg sc
  "$and" -> bvBinaryOp $ SC.scBvAnd sc
  "$or" -> bvBinaryOp $ SC.scBvOr sc
  "$xor" -> bvBinaryOp $ SC.scBvXor sc
  "$xnor" -> bvBinaryOp $ \w x y -> do
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
  "$shl" -> do
    ta <- input "A"
    nb <- inputNat "B"
    w <- outputWidth
    res <- liftIO $ SC.scBvShl sc w ta nb
    output res
  "$shr" -> do
    ta <- input "A"
    nb <- inputNat "B"
    w <- outputWidth
    res <- liftIO $ SC.scBvShr sc w ta nb
    output res
  "$sshl" -> do
    ta <- input "A"
    nb <- inputNat "B"
    w <- outputWidth
    res <- liftIO $ SC.scBvShl sc w ta nb
    output res
  "$sshr" -> do
    ta <- input "A"
    nb <- inputNat "B"
    w <- outputWidth
    res <- liftIO $ SC.scBvSShr sc w ta nb
    output res
  -- "$shift" -> _
  "$shiftx" -> do
    ta <- input "A"
    tbrev <- inputRev "B"
    w <- outputWidth
    tbn <- liftIO $ SC.scGlobalApply sc "Prelude.bvToNat" [w, tbrev]
    tbneg <- liftIO $ SC.scBvNeg sc w tbrev
    tbnegn <- liftIO $ SC.scGlobalApply sc "Prelude.bvToNat" [w, tbneg]
    zero <- liftIO $ SC.scBvConst sc outputWidthNat 0
    cond <- liftIO $ SC.scBvSGe sc w tbrev zero
    tcase <- liftIO $ SC.scBvShr sc w ta tbn
    ecase <- liftIO $ SC.scBvShl sc w ta tbnegn
    ty <- liftIO $ SC.scBitvector sc outputWidthNat
    res <- if connSigned "B"
      then liftIO $ SC.scIte sc ty cond tcase ecase
      else pure tcase
    output res
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
  "$add" -> bvBinaryArithOp $ SC.scBvAdd sc
  "$sub" -> bvBinaryArithOp $ SC.scBvSub sc
  "$mul" -> bvBinaryArithOp $ SC.scBvMul sc
  "$div" -> bvBinaryArithOp $ SC.scBvUDiv sc
  "$mod" -> bvBinaryArithOp $ SC.scBvURem sc
  -- "$modfloor" -> _
  "$logic_not" -> do
    w <- outputWidth
    ta <- input "A"
    anz <- liftIO $ SC.scBvNonzero sc w ta
    res <- liftIO $ SC.scNot sc anz
    outputBit res
  "$logic_and" -> do
    w <- outputWidth
    ta <- inputRaw "A"
    tb <- inputRaw "B"
    anz <- liftIO $ SC.scBvNonzero sc w ta
    bnz <- liftIO $ SC.scBvNonzero sc w tb
    res <- liftIO $ SC.scAnd sc anz bnz
    outputBit res
  "$logic_or" -> do
    w <- outputWidth
    ta <- input "A"
    tb <- input "B"
    anz <- liftIO $ SC.scBvNonzero sc w ta
    bnz <- liftIO $ SC.scBvNonzero sc w tb
    res <- liftIO $ SC.scOr sc anz bnz
    outputBit res
  "$mux" -> do
    ta <- input "A"
    tb <- input "B"
    ts <- inputRaw "S"
    swidth <- connWidth "S"
    snz <- liftIO $ SC.scBvNonzero sc swidth ts
    ty <- liftIO $ SC.scBitvector sc outputWidthNat
    res <- liftIO $ SC.scIte sc ty snz tb ta
    output res
  "$pmux" -> throw YosysErrorUnsupportedPmux
  "$adff" -> throw $ YosysErrorUnsupportedFF "$adff"
  "$sdff" -> throw $ YosysErrorUnsupportedFF "$sdff"
  "$aldff" -> throw $ YosysErrorUnsupportedFF "$aldff"
  "$dffsr" -> throw $ YosysErrorUnsupportedFF "$dffsr"
  "$dffe" -> throw $ YosysErrorUnsupportedFF "$dffe"
  "$adffe" -> throw $ YosysErrorUnsupportedFF "$adffe"
  "$sdffe" -> throw $ YosysErrorUnsupportedFF "$sdffe"
  "$sdffce" -> throw $ YosysErrorUnsupportedFF "$sdffce"
  "$aldffe" -> throw $ YosysErrorUnsupportedFF "$aldffe"
  "$dffsre" -> throw $ YosysErrorUnsupportedFF "$dffsre"
  -- "$bmux" -> _
  -- "$demux" -> _
  -- "$lut" -> _
  -- "$slice" -> _
  -- "$concat" -> _
  _ -> pure Nothing
  where
    nm = c ^. cellType
    typeCheckMsg :: Text
    typeCheckMsg = mconcat
      [ "translating a cell with type \"", nm, "\""
      ]
    textBinNat :: Text -> Natural
    textBinNat = fromIntegral . Text.foldl' (\a x -> digitToInt x + a * 2) 0
    connSigned :: Text -> Bool
    connSigned onm =
      case Map.lookup (onm <> "_SIGNED") $ c ^. cellParameters of
        Just t -> textBinNat t > 0
        Nothing -> False
    connWidthNat :: Text -> Natural
    connWidthNat onm =
      case Map.lookup onm $ c ^. cellConnections of
        Nothing -> panic "cellToTerm" [Text.unpack $ mconcat ["Missing expected output name for ", nm, " cell"]]
        Just bits -> fromIntegral $ length bits
    connWidth :: Text -> m SC.Term
    connWidth onm = liftIO . SC.scNat sc $ connWidthNat onm
    outputWidthNat = connWidthNat "Y"
    outputWidth = connWidth "Y"
    extTrunc :: Text -> SC.Term -> m SC.Term
    extTrunc onm t = do
      let bvw = connWidthNat onm
      let width = outputWidthNat
      let signed = connSigned onm
      if
        | bvw > width -> do
            wterm <- liftIO $ SC.scNat sc width
            diffterm <- liftIO . SC.scNat sc $ bvw - width
            liftIO $ SC.scBvTrunc sc diffterm wterm t
        | width > bvw && signed -> do
            bvwpredterm <- liftIO . SC.scNat sc $ bvw - 1
            diffterm <- liftIO . SC.scNat sc $ width - bvw
            liftIO $ SC.scBvSExt sc diffterm bvwpredterm t
        | width > bvw && not signed -> do
            bvwterm <- liftIO $ SC.scNat sc bvw
            diffterm <- liftIO . SC.scNat sc $ width - bvw
            liftIO $ SC.scBvUExt sc diffterm bvwterm t
        | otherwise -> pure t
    inputRaw :: Text -> m SC.Term
    inputRaw inpNm =
      case Map.lookup inpNm args of
        Nothing -> panic "cellToTerm" [Text.unpack $ mconcat [nm, " missing input ", inpNm]]
        Just a -> pure a
    input :: Text -> m SC.Term
    input inpNm = extTrunc inpNm =<< inputRaw inpNm
    inputRev :: Text -> m SC.Term
    inputRev inpNm = do
      raw <- inputRaw inpNm
      w <- connWidth inpNm
      bool <- liftIO $ SC.scBoolType sc
      rev <- liftIO $ SC.scGlobalApply sc "Prelude.reverse" [w, bool, raw]
      extTrunc inpNm rev
    inputNat :: Text -> m SC.Term
    inputNat inpNm = do
      raw <- inputRaw inpNm
      w <- connWidth inpNm
      bool <- liftIO $ SC.scBoolType sc
      rev <- liftIO $ SC.scGlobalApply sc "Prelude.reverse" [w, bool, raw]
      -- note bvToNat is big-endian while yosys shifts expect little-endian
      liftIO $ SC.scGlobalApply sc "Prelude.bvToNat" [w, rev]
    output :: SC.Term -> m (Maybe SC.Term)
    output res = do
      eres <- extTrunc "Y" res
      fmap Just . cryptolRecord sc $ Map.fromList
        [ ("Y", eres)
        ]
    outputBit :: SC.Term -> m (Maybe SC.Term)
    outputBit res = do
      bool <- liftIO $ SC.scBoolType sc
      vres <- liftIO $ SC.scSingle sc bool res
      fmap Just . cryptolRecord sc $ Map.fromList
        [ ("Y", vres)
        ]
    bvUnaryOp :: (SC.Term -> SC.Term -> IO SC.Term) -> m (Maybe SC.Term)
    bvUnaryOp f = do
      t <- input "A"
      w <- outputWidth
      res <- liftIO $ f w t
      output res
    bvBinaryOp :: (SC.Term -> SC.Term -> SC.Term -> IO SC.Term) -> m (Maybe SC.Term)
    bvBinaryOp f = do
      w <- outputWidth
      ta <- input "A"
      tb <- input "B"
      res <- liftIO $ f w ta tb
      output res
    bvBinaryArithOp :: (SC.Term -> SC.Term -> SC.Term -> IO SC.Term) -> m (Maybe SC.Term)
    bvBinaryArithOp f = do
      w <- outputWidth
      bool <- liftIO $ SC.scBoolType sc
      ta <- inputRev "A"
      tb <- inputRev "B"
      res <- liftIO $ f w ta tb
      revres <- liftIO $ SC.scGlobalApply sc "Prelude.reverse" [w, bool, res]
      output revres
    bvBinaryCmp :: (SC.Term -> SC.Term -> SC.Term -> IO SC.Term) -> m (Maybe SC.Term)
    bvBinaryCmp f = do
      ta <- inputRaw "A"
      tb <- inputRaw "B"
      w <- connWidth "A"
      bit <- liftIO $ f w ta tb
      boolty <- liftIO $ SC.scBoolType sc
      res <- liftIO $ SC.scSingle sc boolty bit
      output res
    bvReduce :: Bool -> SC.Term -> m (Maybe SC.Term)
    bvReduce boolIdentity boolFun = do
      t <- input "A"
      w <- outputWidth
      boolTy <- liftIO $ SC.scBoolType sc
      identity <- liftIO $ SC.scBool sc boolIdentity
      scFoldr <- liftIO . SC.scLookupDef sc $ SC.mkIdent SC.preludeName "foldr"
      bit <- liftIO $ SC.scApplyAll sc scFoldr [boolTy, boolTy, w, boolFun, identity, t]
      outputBit bit
