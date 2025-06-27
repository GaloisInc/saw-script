{- |
Module      : SAWCentral.Yosys.Cell
Description : Translating Yosys cells into SAWCore
License     : BSD3
Maintainer  : sbreese
Stability   : experimental
-}

{-# Language OverloadedStrings #-}
{-# Language MultiWayIf #-}
{-# Language ScopedTypeVariables #-}

module SAWCentral.Yosys.Cell where

import Control.Lens ((^.))
import Control.Monad.IO.Class (MonadIO(..))

import Data.Char (digitToInt)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text

import Numeric.Natural (Natural)

import qualified SAWCore.SharedTerm as SC
import qualified SAWCore.Name as SC

import SAWCentral.Panic (panic)

import SAWCentral.Yosys.Utils
import SAWCentral.Yosys.IR

-- | A SAWCore bitvector term along with its width and whether it should be interpreted as signed.
data CellTerm = CellTerm
  { cellTermTerm :: SC.Term
  , cellTermWidth :: Natural
  , cellTermSigned :: Bool
  }

cellTermNat :: forall m. MonadIO m => SC.SharedContext -> CellTerm -> m SC.Term
cellTermNat sc (CellTerm { cellTermTerm = t, cellTermWidth = w }) = liftIO $ SC.scBvToNat sc w t

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

-- | Given a primitive Yosys cell and a map of terms for its
-- arguments, construct a record term representing the output. If the
-- provided cell is not a primitive, return Nothing.
primCellToTerm ::
  forall m b.
  MonadIO m =>
  SC.SharedContext ->
  Cell [b] {- ^ Cell type -} ->
  Map Text SC.Term {- ^ Mapping of input names to input terms -} ->
  m (Maybe SC.Term)
primCellToTerm sc c args = do
  mm <- primCellToMap sc c args
  mt <- traverse (cryptolRecord sc) mm
  traverse (validateTerm sc typeCheckMsg) mt
  where
    typeCheckMsg :: Text
    typeCheckMsg = mconcat
      [ "translating a cell with type \""
      , Text.pack $ show $ c ^. cellType
      , "\""
      ]

primCellToMap ::
  forall m b.
  MonadIO m =>
  SC.SharedContext ->
  Cell [b] {- ^ Cell type -} ->
  Map Text SC.Term {- ^ Mapping of input names to input terms -} ->
  m (Maybe (Map Text SC.Term))
primCellToMap sc c args = case c ^. cellType of
  CellTypeNot -> bvUnaryOp . liftUnary sc $ SC.scBvNot sc
  CellTypePos -> do
    res <- input "A"
    output res
  CellTypeNeg -> bvUnaryOp . liftUnary sc $ SC.scBvNeg sc
  CellTypeAnd -> bvBinaryOp . liftBinary sc $ SC.scBvAnd sc
  CellTypeOr -> bvBinaryOp . liftBinary sc $ SC.scBvOr sc
  CellTypeXor -> bvBinaryOp . liftBinary sc $ SC.scBvXor sc
  CellTypeXnor -> bvBinaryOp . liftBinary sc $ \w x y -> do
    r <- SC.scBvXor sc w x y
    SC.scBvNot sc w r
  CellTypeReduceAnd -> bvReduce True =<< do
    liftIO . SC.scGlobalDef sc $ SC.mkIdent SC.preludeName "and"
  CellTypeReduceOr -> bvReduce False =<< do
    liftIO . SC.scGlobalDef sc $ SC.mkIdent SC.preludeName "or"
  CellTypeReduceXor -> bvReduce False =<< do
    liftIO . SC.scGlobalDef sc $ SC.mkIdent SC.preludeName "xor"
  CellTypeReduceXnor -> bvReduce True =<< do
    boolTy <- liftIO $ SC.scBoolType sc
    xEC <- liftIO $ SC.scFreshEC sc "x" boolTy
    x <- liftIO $ SC.scExtCns sc xEC
    yEC <- liftIO $ SC.scFreshEC sc "y" boolTy
    y <- liftIO $ SC.scExtCns sc yEC
    r <- liftIO $ SC.scXor sc x y
    res <- liftIO $ SC.scNot sc r
    liftIO $ SC.scAbstractExts sc [xEC, yEC] res
  CellTypeReduceBool -> bvReduce False =<< do
    liftIO . SC.scGlobalDef sc $ SC.mkIdent SC.preludeName "or"
  CellTypeShl -> do
    ta <- fmap cellTermTerm $ input "A"
    nb <- cellTermNat sc =<< input "B"
    w <- outputWidth
    res <- liftIO $ SC.scBvShl sc w ta nb
    output (CellTerm res (connWidthNat "A") (connSigned "A"))
  CellTypeShr -> do
    ta <- fmap cellTermTerm $ input "A"
    nb <- cellTermNat sc =<< input "B"
    w <- outputWidth
    res <- liftIO $ SC.scBvShr sc w ta nb
    output (CellTerm res (connWidthNat "A") (connSigned "A"))
  CellTypeSshl -> do
    ta <- fmap cellTermTerm $ input "A"
    nb <- cellTermNat sc =<< input "B"
    w <- outputWidth
    res <- liftIO $ SC.scBvShl sc w ta nb
    output (CellTerm res (connWidthNat "A") (connSigned "A"))
  CellTypeSshr -> do
    ta <- fmap cellTermTerm $ input "A"
    nb <- cellTermNat sc =<< input "B"
    w <- outputWidth
    res <- liftIO $ SC.scBvSShr sc w ta nb
    output (CellTerm res (connWidthNat "A") (connSigned "A"))
  -- "$shift" -> _
  CellTypeShiftx -> do
    let w = max (connWidthNat "A") (connWidthNat "B")
    wt <- liftIO $ SC.scNat sc w
    CellTerm ta _ _ <- extTrunc sc w =<< input "A"
    CellTerm tb _ _ <- extTrunc sc w =<< input "B"
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
    output (CellTerm res (connWidthNat "A") (connSigned "A"))
  CellTypeLt -> bvBinaryCmp . liftBinaryCmp sc $ SC.scBvULt sc
  CellTypeLe -> bvBinaryCmp . liftBinaryCmp sc $ SC.scBvULe sc
  CellTypeGt -> bvBinaryCmp . liftBinaryCmp sc $ SC.scBvUGt sc
  CellTypeGe -> bvBinaryCmp . liftBinaryCmp sc $ SC.scBvUGe sc
  CellTypeEq -> bvBinaryCmp . liftBinaryCmp sc $ SC.scBvEq sc
  CellTypeNe -> bvBinaryCmp . liftBinaryCmp sc $ \w x y -> do
    r <- SC.scBvEq sc w x y
    SC.scNot sc r
  CellTypeEqx -> bvBinaryCmp . liftBinaryCmp sc $ SC.scBvEq sc
  CellTypeNex -> bvBinaryCmp . liftBinaryCmp sc $ \w x y -> do
    r <- SC.scBvEq sc w x y
    SC.scNot sc r
  CellTypeAdd -> bvBinaryOp . liftBinary sc $ SC.scBvAdd sc
  CellTypeSub -> bvBinaryOp . liftBinary sc $ SC.scBvSub sc
  CellTypeMul -> bvBinaryOp . liftBinary sc $ SC.scBvMul sc
  CellTypeDiv -> bvBinaryOp . liftBinary sc $ SC.scBvUDiv sc
  CellTypeMod -> bvBinaryOp . liftBinary sc $ SC.scBvURem sc
  -- "$modfloor" -> _
  CellTypeLogicNot -> do
    w <- connWidth "A"
    ta <- cellTermTerm <$> input "A"
    anz <- liftIO $ SC.scBvNonzero sc w ta
    res <- liftIO $ SC.scNot sc anz
    outputBit res
  CellTypeLogicAnd -> bvBinaryCmp . liftBinaryCmp sc $ \w x y -> do
    xnz <- liftIO $ SC.scBvNonzero sc w x
    ynz <- liftIO $ SC.scBvNonzero sc w y
    liftIO $ SC.scAnd sc xnz ynz
  CellTypeLogicOr -> bvBinaryCmp . liftBinaryCmp sc $ \w x y -> do
    xnz <- liftIO $ SC.scBvNonzero sc w x
    ynz <- liftIO $ SC.scBvNonzero sc w y
    liftIO $ SC.scOr sc xnz ynz
  CellTypeMux -> do
    ta <- cellTermTerm <$> input "A"
    tb <- cellTermTerm <$> input "B"
    ts <- cellTermTerm <$> input "S"
    swidth <- connWidth "S"
    snz <- liftIO $ SC.scBvNonzero sc swidth ts
    let width = connWidthNat "Y"
    ty <- liftIO $ SC.scBitvector sc width
    res <- liftIO $ SC.scIte sc ty snz tb ta
    output $ CellTerm res (connWidthNat "A") (connSigned "A")
  CellTypePmux -> do
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

    scFoldr <- liftIO . SC.scGlobalDef sc $ SC.mkIdent SC.preludeName "foldr"
    resPair <- liftIO $ SC.scApplyAll sc scFoldr [bool, accTy, swidth, fun, defaultAcc, ts]
    res <- liftIO $ SC.scPairRight sc resPair
    output $ CellTerm res (connWidthNat "A") (connSigned "Y")
  CellTypeBmux -> do
    ia <- input "A"
    is <- input "S"
    let swidth = cellTermWidth is
    let ywidth = connWidthNat "Y"
    -- Split input A into chunks
    chunks <- liftIO (SC.scNat sc (2 ^ swidth))
    ywidth' <- liftIO (SC.scNat sc ywidth)
    bool <- liftIO (SC.scBoolType sc)
    splitA <- liftIO (SC.scSplit sc chunks ywidth' bool (cellTermTerm ia))
    -- reverse to put index 0 on the left
    outputType <- liftIO (SC.scBitvector sc ywidth)
    revA <- liftIO (SC.scGlobalApply sc "Prelude.reverse" [chunks, outputType, splitA])
    -- Select chunk from output
    ixWidth <- liftIO (SC.scNat sc swidth)
    elt <- liftIO (SC.scBvAt sc chunks outputType ixWidth revA (cellTermTerm is))
    output (CellTerm elt ywidth (connSigned "Y"))
  -- "$demux" -> _
  -- "$lut" -> _
  -- "$slice" -> _
  -- "$concat" -> _
  CellTypeDff -> pure Nothing
  CellTypeFf -> pure Nothing
  CellTypeUnsupportedPrimitive _ -> pure Nothing
  CellTypeUserType _ -> pure Nothing
  where
    nm :: Text
    nm = Text.pack $ show $ c ^. cellType

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
        Nothing -> panic "cellToTerm" ["Missing expected output name for " <> nm <> " cell"]
        Just bits -> fromIntegral $ length bits
    connWidth :: Text -> m SC.Term
    connWidth onm = liftIO . SC.scNat sc $ connWidthNat onm
    outputWidth = connWidth "Y"

    input :: Text -> m CellTerm
    input inpNm = case Map.lookup inpNm args of
      Nothing -> panic "cellToTerm" [nm <> " missing input " <> inpNm]
      Just a -> pure $ CellTerm a (connWidthNat inpNm) (connSigned inpNm)

    output :: CellTerm -> m (Maybe (Map Text SC.Term))
    output (CellTerm ct cw _) = do
      let res = CellTerm ct cw (connSigned "Y")
      CellTerm t _ _ <- extTrunc sc (connWidthNat "Y") res
      pure . Just $ Map.fromList
        [ ("Y", t)
        ]

    outputBit :: SC.Term -> m (Maybe (Map Text SC.Term))
    outputBit res = do
      bool <- liftIO $ SC.scBoolType sc
      vres <- liftIO $ SC.scSingle sc bool res
      pure . Just $ Map.fromList
        [ ("Y", vres)
        ]

    -- convert input to big endian
    bvUnaryOp :: (CellTerm -> m CellTerm) -> m (Maybe (Map Text SC.Term))
    bvUnaryOp f = do
      t <- input "A"
      res <- f t
      output res
    -- extend inputs to output width
    bvBinaryOp :: (CellTerm -> CellTerm -> m CellTerm) -> m (Maybe (Map Text SC.Term))
    bvBinaryOp f = do
      let w = connWidthNat "Y"
      ta <- extTrunc sc w =<< input "A"
      tb <- extTrunc sc w =<< input "B"
      res <- f ta tb
      output res
    -- extend inputs to max input width, output is a single bit
    bvBinaryCmp :: (CellTerm -> CellTerm -> m SC.Term) -> m (Maybe (Map Text SC.Term))
    bvBinaryCmp f = do
      ta <- input "A"
      tb <- input "B"
      res <- uncurry f =<< extMax sc ta tb
      outputBit res
    bvReduce :: Bool -> SC.Term -> m (Maybe (Map Text SC.Term))
    bvReduce boolIdentity boolFun = do
      CellTerm t _ _ <- input "A"
      w <- connWidth "A"
      boolTy <- liftIO $ SC.scBoolType sc
      identity <- liftIO $ SC.scBool sc boolIdentity
      scFoldr <- liftIO . SC.scGlobalDef sc $ SC.mkIdent SC.preludeName "foldr"
      bit <- liftIO $ SC.scApplyAll sc scFoldr [boolTy, boolTy, w, boolFun, identity, t]
      outputBit bit
