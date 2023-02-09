{- |
Module      : SAWScript.Yosys.Cell
Description : Translating Yosys cells into SAWCore
License     : BSD3
Maintainer  : sbreese
Stability   : experimental
-}

{-# Language OverloadedStrings #-}
{-# Language MultiWayIf #-}
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

-- | A SAWCore bitvector term along with its width and whether it should be interpreted as signed.
data CellTerm = CellTerm
  { cellTermTerm :: SC.Term
  , cellTermWidth :: Natural
  , cellTermSigned :: Bool
  }

cellTermNat :: forall m. MonadIO m => SC.SharedContext -> CellTerm -> m SC.Term
cellTermNat sc (CellTerm { cellTermTerm = t, cellTermWidth = w }) = liftIO $ SC.scBvToNat sc w t

-- | Reverse the bits in the given bitvector.
-- Note that Yosys arithmetic cells treat bitvectors as "little-bit-endian", i.e. the 0-index bit is
-- least significant. SAWCore has the opposite convention, so it's important to reverse bitvectors
-- before and after each arithmetic operation in order to match Yosys' semantics.
flipEndianness :: forall m. MonadIO m => SC.SharedContext -> CellTerm -> m CellTerm
flipEndianness sc (CellTerm { cellTermTerm = t, cellTermWidth = w, cellTermSigned = s}) = do
  wt <- liftIO $ SC.scNat sc w
  bool <- liftIO $ SC.scBoolType sc
  res <- liftIO $ SC.scGlobalApply sc "Prelude.reverse" [wt, bool, t]
  pure $ CellTerm res w s

-- | Apply the appropriate (possibly signed) extension or truncation to make the given bitvector
-- match the given width.
extTrunc :: forall m. MonadIO m => SC.SharedContext -> Natural -> CellTerm -> m CellTerm
extTrunc sc width (CellTerm { cellTermTerm = t, cellTermWidth = bvw, cellTermSigned = signed}) = do
  wterm <- liftIO $ SC.scNat sc width
  bvwterm <- liftIO $ SC.scNat sc bvw
  res <- if
    | bvw > width -> do
        diffterm <- liftIO . SC.scNat sc $ bvw - width
        liftIO $ SC.scBvTrunc sc diffterm wterm t
    | width > bvw && signed -> do
        bvwpredterm <- liftIO . SC.scNat sc $ bvw - 1
        diffterm <- liftIO . SC.scNat sc $ width - bvw
        liftIO $ SC.scBvSExt sc diffterm bvwpredterm t
    | width > bvw && not signed -> do
        diffterm <- liftIO . SC.scNat sc $ width - bvw
        liftIO $ SC.scBvUExt sc diffterm bvwterm t
    | otherwise -> pure t
  pure $ CellTerm res width signed

-- | Given two bitvectors, extend the narrower bitvector to match the wider.
extMax :: forall m. MonadIO m => SC.SharedContext -> CellTerm -> CellTerm -> m (CellTerm, CellTerm)
extMax sc c1 c2 = do
  let
    w1 = cellTermWidth c1
    w2 = cellTermWidth c2
    w = max w1 w2
  res1 <- extTrunc sc w c1
  res2 <- extTrunc sc w c2
  pure (res1, res2)

liftUnary :: forall m.
  MonadIO m =>
  SC.SharedContext ->
  (SC.Term -> SC.Term -> IO SC.Term) -> -- (w : Nat) -> [w] -> [w]
  CellTerm -> m CellTerm
liftUnary sc f c@(CellTerm { cellTermTerm = t }) = do
  wt <- liftIO . SC.scNat sc $ cellTermWidth c
  res <- liftIO $ f wt t
  pure $ c { cellTermTerm = res }

liftBinary :: forall m.
  MonadIO m =>
  SC.SharedContext ->
  (SC.Term -> SC.Term -> SC.Term -> IO SC.Term) -> -- (w : Nat) -> [w] -> [w] -> [w]
  CellTerm -> CellTerm -> m CellTerm
liftBinary sc f c1@(CellTerm { cellTermTerm = t1 }) (CellTerm { cellTermTerm = t2 }) = do
  wt <- liftIO . SC.scNat sc $ cellTermWidth c1
  res <- liftIO $ f wt t1 t2
  pure $ c1 { cellTermTerm = res }

liftBinaryCmp :: forall m.
  MonadIO m =>
  SC.SharedContext ->
  (SC.Term -> SC.Term -> SC.Term -> IO SC.Term) -> -- (w : Nat) -> [w] -> [w] -> Bool
  CellTerm -> CellTerm -> m SC.Term
liftBinaryCmp sc f c1@(CellTerm { cellTermTerm = t1 }) (CellTerm { cellTermTerm = t2 }) = do
  wt <- liftIO . SC.scNat sc $ cellTermWidth c1
  liftIO $ f wt t1 t2

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
  "$not" -> bvUnaryOp . liftUnary sc $ SC.scBvNot sc
  "$pos" -> do
    res <- input "A"
    output res
  "$neg" -> bvUnaryOp . liftUnary sc $ SC.scBvNeg sc
  "$and" -> bvBinaryOp . liftBinary sc $ SC.scBvAnd sc
  "$or" -> bvBinaryOp . liftBinary sc $ SC.scBvOr sc
  "$xor" -> bvBinaryOp . liftBinary sc $ SC.scBvXor sc
  "$xnor" -> bvBinaryOp . liftBinary sc $ \w x y -> do
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
    ta <- fmap cellTermTerm . flipEndianness sc =<< input "A"
    nb <- cellTermNat sc =<< flipEndianness sc =<< input "B"
    w <- outputWidth
    res <- liftIO $ SC.scBvShl sc w ta nb
    output =<< flipEndianness sc (CellTerm res (connWidthNat "A") (connSigned "A"))
  "$shr" -> do
    ta <- fmap cellTermTerm . flipEndianness sc =<< input "A"
    nb <- cellTermNat sc =<< flipEndianness sc =<< input "B"
    w <- outputWidth
    res <- liftIO $ SC.scBvShr sc w ta nb
    output =<< flipEndianness sc (CellTerm res (connWidthNat "A") (connSigned "A"))
  "$sshl" -> do
    ta <- fmap cellTermTerm . flipEndianness sc =<< input "A"
    nb <- cellTermNat sc =<< flipEndianness sc =<< input "B"
    w <- outputWidth
    res <- liftIO $ SC.scBvShl sc w ta nb
    output =<< flipEndianness sc (CellTerm res (connWidthNat "A") (connSigned "A"))
  "$sshr" -> do
    ta <- fmap cellTermTerm . flipEndianness sc =<< input "A"
    nb <- cellTermNat sc =<< flipEndianness sc =<< input "B"
    w <- outputWidth
    res <- liftIO $ SC.scBvSShr sc w ta nb
    output =<< flipEndianness sc (CellTerm res (connWidthNat "A") (connSigned "A"))
  -- "$shift" -> _
  "$shiftx" -> do
    let w = max (connWidthNat "A") (connWidthNat "B")
    wt <- liftIO $ SC.scNat sc w
    CellTerm ta _ _ <- extTrunc sc w =<< flipEndianness sc =<< input "A"
    CellTerm tb _ _ <- extTrunc sc w =<< flipEndianness sc =<< input "B"
    zero <- liftIO $ SC.scBvConst sc w 0
    tbn <- liftIO $ SC.scBvToNat sc w tb
    tbneg <- liftIO $ SC.scBvNeg sc wt tb
    tbnegn <- liftIO $ SC.scBvToNat sc w tbneg
    cond <- liftIO $ SC.scBvSGe sc wt tb zero
    tcase <- liftIO $ SC.scBvShr sc wt ta tbn
    ecase <- liftIO $ SC.scBvShl sc wt ta tbnegn
    ty <- liftIO . SC.scBitvector sc $ connWidthNat "A"
    res <- if connSigned "B"
      then liftIO $ SC.scIte sc ty cond tcase ecase
      else pure tcase
    output =<< flipEndianness sc (CellTerm res (connWidthNat "A") (connSigned "A"))
  "$lt" -> bvBinaryCmp . liftBinaryCmp sc $ SC.scBvULt sc
  "$le" -> bvBinaryCmp . liftBinaryCmp sc $ SC.scBvULe sc
  "$gt" -> bvBinaryCmp . liftBinaryCmp sc $ SC.scBvUGt sc
  "$ge" -> bvBinaryCmp . liftBinaryCmp sc $ SC.scBvUGe sc
  "$eq" -> bvBinaryCmp . liftBinaryCmp sc $ SC.scBvEq sc
  "$ne" -> bvBinaryCmp . liftBinaryCmp sc $ \w x y -> do
    r <- SC.scBvEq sc w x y
    SC.scNot sc r
  "$eqx" -> bvBinaryCmp . liftBinaryCmp sc $ SC.scBvEq sc
  "$nex" -> bvBinaryCmp . liftBinaryCmp sc $ \w x y -> do
    r <- SC.scBvEq sc w x y
    SC.scNot sc r
  "$add" -> bvBinaryOp . liftBinary sc $ SC.scBvAdd sc
  "$sub" -> bvBinaryOp . liftBinary sc $ SC.scBvSub sc
  "$mul" -> bvBinaryOp . liftBinary sc $ SC.scBvMul sc
  "$div" -> bvBinaryOp . liftBinary sc $ SC.scBvUDiv sc
  "$mod" -> bvBinaryOp . liftBinary sc $ SC.scBvURem sc
  -- "$modfloor" -> _
  "$logic_not" -> do
    w <- connWidth "A"
    ta <- cellTermTerm <$> input "A"
    anz <- liftIO $ SC.scBvNonzero sc w ta
    res <- liftIO $ SC.scNot sc anz
    outputBit res
  "$logic_and" -> bvBinaryCmp . liftBinaryCmp sc $ \w x y -> do
    xnz <- liftIO $ SC.scBvNonzero sc w x
    ynz <- liftIO $ SC.scBvNonzero sc w y
    liftIO $ SC.scAnd sc xnz ynz
  "$logic_or" -> bvBinaryCmp . liftBinaryCmp sc $ \w x y -> do
    xnz <- liftIO $ SC.scBvNonzero sc w x
    ynz <- liftIO $ SC.scBvNonzero sc w y
    liftIO $ SC.scOr sc xnz ynz
  "$mux" -> do
    ta <- cellTermTerm <$> input "A"
    tb <- cellTermTerm <$> input "B"
    ts <- cellTermTerm <$> input "S"
    swidth <- connWidth "S"
    snz <- liftIO $ SC.scBvNonzero sc swidth ts
    let width = connWidthNat "Y"
    ty <- liftIO $ SC.scBitvector sc width
    res <- liftIO $ SC.scIte sc ty snz tb ta
    output $ CellTerm res (connWidthNat "A") (connSigned "A")
  "$pmux" -> do
    ta <- cellTermTerm <$> input "A"
    tb <- cellTermTerm <$> input "B"
    ts <- cellTermTerm <$> input "S"

    width <- connWidth "A"
    widthBv <- liftIO . SC.scBitvector sc $ connWidthNat "A"
    swidth <- connWidth "S"
    bool <- liftIO $ SC.scBoolType sc
    nat <- liftIO $ SC.scNatType sc
    splitb <- liftIO $ SC.scSplit sc swidth width bool tb
    zero <- liftIO $ SC.scNat sc 0
    accTy <- liftIO $ SC.scPairType sc nat widthBv
    defaultAcc <- liftIO $ SC.scPairValue sc zero ta

    bitEC <- liftIO $ SC.scFreshEC sc "bit" bool
    accEC <- liftIO $ SC.scFreshEC sc "acc" accTy
    fun <- liftIO . SC.scAbstractExts sc [bitEC, accEC] =<< do
      bit <- liftIO $ SC.scExtCns sc bitEC
      acc <- liftIO $ SC.scExtCns sc accEC
      idx <- liftIO $ SC.scPairLeft sc acc
      aval <- liftIO $ SC.scPairRight sc acc
      bval <- liftIO $ SC.scAtWithDefault sc swidth widthBv aval splitb idx
      newidx <- liftIO $ SC.scAddNat sc idx width
      newval <- liftIO $ SC.scIte sc widthBv bit bval aval
      liftIO $ SC.scPairValue sc newidx newval

    scFoldr <- liftIO . SC.scLookupDef sc $ SC.mkIdent SC.preludeName "foldr"
    resPair <- liftIO $ SC.scApplyAll sc scFoldr [bool, accTy, swidth, fun, defaultAcc, ts]
    res <- liftIO $ SC.scPairRight sc resPair
    output $ CellTerm res (connWidthNat "A") (connSigned "Y")
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
    outputWidth = connWidth "Y"

    input :: Text -> m CellTerm
    input inpNm = case Map.lookup inpNm args of
      Nothing -> panic "cellToTerm" [Text.unpack $ mconcat [nm, " missing input ", inpNm]]
      Just a -> pure $ CellTerm a (connWidthNat inpNm) (connSigned inpNm)

    output :: CellTerm -> m (Maybe SC.Term)
    output (CellTerm ct cw _) = do
      let res = CellTerm ct cw (connSigned "Y")
      eres <- extTrunc sc (connWidthNat "Y") =<< flipEndianness sc res
      CellTerm t _ _ <- flipEndianness sc eres
      fmap Just . cryptolRecord sc $ Map.fromList
        [ ("Y", t)
        ]

    outputBit :: SC.Term -> m (Maybe SC.Term)
    outputBit res = do
      bool <- liftIO $ SC.scBoolType sc
      vres <- liftIO $ SC.scSingle sc bool res
      fmap Just . cryptolRecord sc $ Map.fromList
        [ ("Y", vres)
        ]

    -- convert input to big endian
    bvUnaryOp :: (CellTerm -> m CellTerm) -> m (Maybe SC.Term)
    bvUnaryOp f = do
      t <- flipEndianness sc =<< input "A"
      res <- f t
      output =<< flipEndianness sc res
    -- convert inputs to big endian and extend inputs to output width
    bvBinaryOp :: (CellTerm -> CellTerm -> m CellTerm) -> m (Maybe SC.Term)
    bvBinaryOp f = do
      let w = connWidthNat "Y"
      ta <- extTrunc sc w =<< flipEndianness sc =<< input "A"
      tb <- extTrunc sc w =<< flipEndianness sc =<< input "B"
      res <- f ta tb
      output =<< flipEndianness sc res
    -- convert inputs to big endian and extend inputs to max input width, output is a single bit
    bvBinaryCmp :: (CellTerm -> CellTerm -> m SC.Term) -> m (Maybe SC.Term)
    bvBinaryCmp f = do
      ta <- flipEndianness sc =<< input "A"
      tb <- flipEndianness sc =<< input "B"
      res <- uncurry f =<< extMax sc ta tb
      outputBit res
    bvReduce :: Bool -> SC.Term -> m (Maybe SC.Term)
    bvReduce boolIdentity boolFun = do
      CellTerm t _ _ <- input "A"
      w <- connWidth "A"
      boolTy <- liftIO $ SC.scBoolType sc
      identity <- liftIO $ SC.scBool sc boolIdentity
      scFoldr <- liftIO . SC.scLookupDef sc $ SC.mkIdent SC.preludeName "foldr"
      bit <- liftIO $ SC.scApplyAll sc scFoldr [boolTy, boolTy, w, boolFun, identity, t]
      outputBit bit
