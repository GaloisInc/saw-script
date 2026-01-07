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

import qualified Data.Aeson as Aeson
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

cellTermNat :: SC.SharedContext -> CellTerm -> IO SC.Term
cellTermNat sc (CellTerm { cellTermTerm = t, cellTermWidth = w }) = SC.scBvToNat sc w t

-- | Apply the appropriate (possibly signed) extension or truncation to make the given bitvector
-- match the given width.
extTrunc :: SC.SharedContext -> Natural -> CellTerm -> IO CellTerm
extTrunc sc width (CellTerm { cellTermTerm = t, cellTermWidth = bvw, cellTermSigned = signed}) =
  do wterm <- SC.scNat sc width
     bvwterm <- SC.scNat sc bvw
     res <- if
       | bvw > width ->
           do diffterm <- SC.scNat sc $ bvw - width
              SC.scBvTrunc sc diffterm wterm t
       | width > bvw && signed ->
           do bvwpredterm <- SC.scNat sc $ bvw - 1
              diffterm <- SC.scNat sc $ width - bvw
              SC.scBvSExt sc diffterm bvwpredterm t
       | width > bvw && not signed ->
           do diffterm <- SC.scNat sc $ width - bvw
              SC.scBvUExt sc diffterm bvwterm t
       | otherwise -> pure t
     pure $ CellTerm res width signed

-- | Given two bitvectors, extend the narrower bitvector to match the wider.
extMax :: SC.SharedContext -> CellTerm -> CellTerm -> IO (CellTerm, CellTerm)
extMax sc c1 c2 =
  do let
       w1 = cellTermWidth c1
       w2 = cellTermWidth c2
       w = max w1 w2
     res1 <- extTrunc sc w c1
     res2 <- extTrunc sc w c2
     pure (res1, res2)

liftUnary ::
  SC.SharedContext ->
  (SC.Term -> SC.Term -> IO SC.Term) -> -- (w : Nat) -> [w] -> [w]
  CellTerm -> IO CellTerm
liftUnary sc f c@(CellTerm { cellTermTerm = t }) =
  do wt <- SC.scNat sc $ cellTermWidth c
     res <- f wt t
     pure $ c { cellTermTerm = res }

liftBinary ::
  SC.SharedContext ->
  (SC.Term -> SC.Term -> SC.Term -> IO SC.Term) -> -- (w : Nat) -> [w] -> [w] -> [w]
  CellTerm -> CellTerm -> IO CellTerm
liftBinary sc f c1@(CellTerm { cellTermTerm = t1 }) (CellTerm { cellTermTerm = t2 }) =
  do wt <- SC.scNat sc $ cellTermWidth c1
     res <- f wt t1 t2
     pure $ c1 { cellTermTerm = res }

liftBinaryCmp ::
  SC.SharedContext ->
  (SC.Term -> SC.Term -> SC.Term -> IO SC.Term) -> -- (w : Nat) -> [w] -> [w] -> Bool
  CellTerm -> CellTerm -> IO SC.Term
liftBinaryCmp sc f c1@(CellTerm { cellTermTerm = t1 }) (CellTerm { cellTermTerm = t2 }) =
  do wt <- SC.scNat sc $ cellTermWidth c1
     f wt t1 t2

-- | Given a primitive Yosys cell and a map of terms for its
-- arguments, construct a record term representing the output. If the
-- provided cell is not a primitive, return Nothing.
primCellToTerm ::
  forall b.
  SC.SharedContext ->
  Cell [b] {- ^ Cell type -} ->
  Map Text SC.Term {- ^ Mapping of input names to input terms -} ->
  IO (Maybe SC.Term)
primCellToTerm sc c args =
  do mm <- primCellToMap sc c args
     traverse (cryptolRecord sc) mm

primCellToMap ::
  forall b.
  SC.SharedContext ->
  Cell [b] {- ^ Cell type -} ->
  Map Text SC.Term {- ^ Mapping of input names to input terms -} ->
  IO (Maybe (Map Text SC.Term))
primCellToMap sc c args =
  case c ^. cellType of
    CellTypeNot -> bvUnaryOp . liftUnary sc $ SC.scBvNot sc
    CellTypePos ->
      do res <- input "A"
         output res
    CellTypeNeg -> bvUnaryOp . liftUnary sc $ SC.scBvNeg sc
    CellTypeAnd -> bvBinaryOp . liftBinary sc $ SC.scBvAnd sc
    CellTypeOr -> bvBinaryOp . liftBinary sc $ SC.scBvOr sc
    CellTypeXor -> bvBinaryOp . liftBinary sc $ SC.scBvXor sc
    CellTypeXnor ->
      bvBinaryOp $ liftBinary sc $ \w x y ->
      do r <- SC.scBvXor sc w x y
         SC.scBvNot sc w r
    CellTypeReduceAnd ->
      do r <- SC.scGlobalDef sc $ SC.mkIdent SC.preludeName "and"
         bvReduce True r
    CellTypeReduceOr ->
      do r <- SC.scGlobalDef sc $ SC.mkIdent SC.preludeName "or"
         bvReduce False r
    CellTypeReduceXor ->
      do r <- SC.scGlobalDef sc $ SC.mkIdent SC.preludeName "xor"
         bvReduce False r
    CellTypeReduceXnor ->
      do boolTy <- SC.scBoolType sc
         x <- SC.scFreshVariable sc "x" boolTy
         y <- SC.scFreshVariable sc "y" boolTy
         r <- SC.scXor sc x y
         res <- SC.scNot sc r
         t <- SC.scAbstractTerms sc [x, y] res
         bvReduce True t
    CellTypeReduceBool ->
      do r <- SC.scGlobalDef sc $ SC.mkIdent SC.preludeName "or"
         bvReduce False r
    CellTypeShl ->
      do let wa = connWidthNat "A"
         let wy = connWidthNat "Y"
         let w = max wa wy
         wt <- SC.scNat sc w
         ta <- extTrunc sc w =<< input "A"
         nb <- cellTermNat sc =<< input "B"
         res <- SC.scBvShl sc wt (cellTermTerm ta) nb
         output (CellTerm res w (connSigned "A"))
    CellTypeShr ->
      do let wa = connWidthNat "A"
         let wy = connWidthNat "Y"
         let w = max wa wy
         wt <- SC.scNat sc w
         ta <- extTrunc sc w =<< input "A"
         nb <- cellTermNat sc =<< input "B"
         res <- SC.scBvShr sc wt (cellTermTerm ta) nb
         output (CellTerm res w (connSigned "A"))
    CellTypeSshl ->
      do let wa = connWidthNat "A"
         let wy = connWidthNat "Y"
         let w = max wa wy
         wt <- SC.scNat sc w
         ta <- extTrunc sc w =<< input "A"
         nb <- cellTermNat sc =<< input "B"
         res <- SC.scBvShl sc wt (cellTermTerm ta) nb
         output (CellTerm res w (connSigned "A"))
    CellTypeSshr ->
      do let wa = connWidthNat "A"
         let wy = connWidthNat "Y"
         let w = max wa wy
         wtpred <- SC.scNat sc $ w - 1
         ta <- extTrunc sc w =<< input "A"
         nb <- cellTermNat sc =<< input "B"
         res <- SC.scBvSShr sc wtpred (cellTermTerm ta) nb
         output (CellTerm res w (connSigned "A"))
    CellTypeShift ->
      do let wa = connWidthNat "A"
         let wb = connWidthNat "B"
         let wy = connWidthNat "Y"
         let w = max wa wy
         wt <- SC.scNat sc w
         wbt <- SC.scNat sc wb
         CellTerm ta _ _ <- extTrunc sc w =<< input "A"
         CellTerm tb _ _ <- input "B"
         tbn <- SC.scBvToNat sc wb tb
         tcase <- if connSigned "A"
                  then do wtpred <- SC.scNat sc $ w - 1
                          SC.scBvSShr sc wtpred ta tbn
                  else SC.scBvShr sc wt ta tbn
         res <- if connSigned "B"
                then do
                  zero <- SC.scBvConst sc wb 0
                  cond <- SC.scBvSGe sc wbt tb zero
                  tbneg <- SC.scBvNeg sc wbt tb
                  tbnegn <- SC.scBvToNat sc wb tbneg
                  ecase <- SC.scBvShl sc wt ta tbnegn
                  ty <- SC.scBitvector sc w
                  SC.scIte sc ty cond tcase ecase
                else pure tcase
         output (CellTerm res w (connSigned "A"))
    CellTypeShiftx ->
      do let w = max (connWidthNat "A") (connWidthNat "B")
         wt <- SC.scNat sc w
         CellTerm ta _ _ <- extTrunc sc w =<< input "A"
         CellTerm tb _ _ <- extTrunc sc w =<< input "B"
         zero <- SC.scBvConst sc w 0
         tbn <- SC.scBvToNat sc w tb
         tbneg <- SC.scBvNeg sc wt tb
         tbnegn <- SC.scBvToNat sc w tbneg
         cond <- SC.scBvSGe sc wt tb zero
         tcase <- SC.scBvShr sc wt ta tbn
         ecase <- SC.scBvShl sc wt ta tbnegn
         ty <- SC.scBitvector sc $ connWidthNat "A"
         res <-
           if connSigned "B"
           then SC.scIte sc ty cond tcase ecase
           else pure tcase
         output (CellTerm res (connWidthNat "A") (connSigned "A"))
    CellTypeLt -> bvBinaryCmp . liftBinaryCmp sc $ SC.scBvULt sc
    CellTypeLe -> bvBinaryCmp . liftBinaryCmp sc $ SC.scBvULe sc
    CellTypeGt -> bvBinaryCmp . liftBinaryCmp sc $ SC.scBvUGt sc
    CellTypeGe -> bvBinaryCmp . liftBinaryCmp sc $ SC.scBvUGe sc
    CellTypeEq -> bvBinaryCmp . liftBinaryCmp sc $ SC.scBvEq sc
    CellTypeNe ->
      bvBinaryCmp $ liftBinaryCmp sc $ \w x y ->
      do r <- SC.scBvEq sc w x y
         SC.scNot sc r
    CellTypeEqx -> bvBinaryCmp . liftBinaryCmp sc $ SC.scBvEq sc
    CellTypeNex ->
      bvBinaryCmp $ liftBinaryCmp sc $ \w x y ->
      do r <- SC.scBvEq sc w x y
         SC.scNot sc r
    CellTypeAdd -> bvBinaryOp . liftBinary sc $ SC.scBvAdd sc
    CellTypeSub -> bvBinaryOp . liftBinary sc $ SC.scBvSub sc
    CellTypeMul -> bvBinaryOp . liftBinary sc $ SC.scBvMul sc
    CellTypeDiv -> bvBinaryOp . liftBinary sc $ SC.scBvUDiv sc
    CellTypeMod -> bvBinaryOp . liftBinary sc $ SC.scBvURem sc
    -- "$modfloor" -> _
    CellTypeLogicNot ->
      do w <- connWidth "A"
         ta <- cellTermTerm <$> input "A"
         anz <- SC.scBvNonzero sc w ta
         res <- SC.scNot sc anz
         outputBit res
    CellTypeLogicAnd ->
      bvBinaryCmp $ liftBinaryCmp sc $ \w x y ->
      do xnz <- SC.scBvNonzero sc w x
         ynz <- SC.scBvNonzero sc w y
         SC.scAnd sc xnz ynz
    CellTypeLogicOr ->
      bvBinaryCmp $ liftBinaryCmp sc $ \w x y ->
      do xnz <- SC.scBvNonzero sc w x
         ynz <- SC.scBvNonzero sc w y
         SC.scOr sc xnz ynz
    CellTypeMux ->
      do ta <- cellTermTerm <$> input "A"
         tb <- cellTermTerm <$> input "B"
         ts <- cellTermTerm <$> input "S"
         swidth <- connWidth "S"
         snz <- SC.scBvNonzero sc swidth ts
         let width = connWidthNat "Y"
         ty <- SC.scBitvector sc width
         res <- SC.scIte sc ty snz tb ta
         output $ CellTerm res (connWidthNat "A") (connSigned "A")
    CellTypePmux ->
      do ta <- cellTermTerm <$> input "A"
         tb <- cellTermTerm <$> input "B"
         ts <- cellTermTerm <$> input "S"

         width <- connWidth "A"
         widthBv <- SC.scBitvector sc $ connWidthNat "A"
         swidth <- connWidth "S"
         bool <- SC.scBoolType sc
         nat <- SC.scNatType sc
         splitb <- SC.scSplit sc swidth width bool tb
         zero <- SC.scNat sc 0
         accTy <- SC.scPairType sc nat widthBv
         defaultAcc <- SC.scPairValue sc zero ta

         bit <- SC.scFreshVariable sc "bit" bool
         acc <- SC.scFreshVariable sc "acc" accTy
         body <-
           do idx <- SC.scPairLeft sc acc
              aval <- SC.scPairRight sc acc
              bval <- SC.scAtWithDefault sc swidth widthBv aval splitb idx
              newidx <- SC.scAddNat sc idx width
              newval <- SC.scIte sc widthBv bit bval aval
              SC.scPairValue sc newidx newval
         fun <- SC.scAbstractTerms sc [bit, acc] body

         scFoldr <- SC.scGlobalDef sc $ SC.mkIdent SC.preludeName "foldr"
         resPair <- SC.scApplyAll sc scFoldr [bool, accTy, swidth, fun, defaultAcc, ts]
         res <- SC.scPairRight sc resPair
         output $ CellTerm res (connWidthNat "A") (connSigned "Y")
    CellTypeBmux ->
      do ia <- input "A"
         is <- input "S"
         let swidth = cellTermWidth is
         let ywidth = connWidthNat "Y"
         -- Split input A into chunks
         chunks <- SC.scNat sc (2 ^ swidth)
         ywidth' <- SC.scNat sc ywidth
         bool <- SC.scBoolType sc
         splitA <- SC.scSplit sc chunks ywidth' bool (cellTermTerm ia)
         -- reverse to put index 0 on the left
         outputType <- SC.scBitvector sc ywidth
         revA <- SC.scGlobalApply sc "Prelude.reverse" [chunks, outputType, splitA]
         -- Select chunk from output
         ixWidth <- SC.scNat sc swidth
         elt <- SC.scBvAt sc chunks outputType ixWidth revA (cellTermTerm is)
         output (CellTerm elt ywidth (connSigned "Y"))
    -- "$demux" -> _
    -- "$lut" -> _
    -- "$slice" -> _
    -- "$concat" -> _
    CellTypeDff -> pure Nothing
    CellTypeFf -> pure Nothing
    CellTypeBUF ->
      do res <- input "A"
         output res
    CellTypeCheck -> pure Nothing
    CellTypePrint -> pure Nothing
    CellTypeScopeinfo -> pure Nothing
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
        Just (Aeson.Number n) -> n > 0
        Just (Aeson.String t) -> textBinNat t > 0
        Just v ->
          -- XXX This should not be a panic, as it is possible to trigger this
          -- with a malformed input file.
          panic "cellToTerm"
            [ "Expected SIGNED parameter to be a number or a string,"
            , "but encountered " <> Text.pack (show v)
            ]
        Nothing -> False
    connWidthNat :: Text -> Natural
    connWidthNat onm =
      case Map.lookup onm $ c ^. cellConnections of
        -- XXX This should not be a panic, as it is possible to trigger this
        -- with a malformed input file.
        Nothing -> panic "cellToTerm" ["Missing expected output name for " <> nm <> " cell"]
        Just bits -> fromIntegral $ length bits
    connWidth :: Text -> IO SC.Term
    connWidth onm = SC.scNat sc $ connWidthNat onm

    input :: Text -> IO CellTerm
    input inpNm =
      case Map.lookup inpNm args of
        -- XXX This should not be a panic, as it is possible to trigger this
        -- with a malformed input file.
        Nothing -> panic "cellToTerm" [nm <> " missing input " <> inpNm]
        Just a -> pure $ CellTerm a (connWidthNat inpNm) (connSigned inpNm)

    output :: CellTerm -> IO (Maybe (Map Text SC.Term))
    output (CellTerm ct cw _) =
      do let res = CellTerm ct cw (connSigned "Y")
         CellTerm t _ _ <- extTrunc sc (connWidthNat "Y") res
         pure . Just $ Map.fromList
           [ ("Y", t)
           ]

    outputBit :: SC.Term -> IO (Maybe (Map Text SC.Term))
    outputBit res =
      do bool <- SC.scBoolType sc
         vres <- SC.scSingle sc bool res
         pure . Just $ Map.fromList
           [ ("Y", vres)
           ]

    -- convert input to big endian
    bvUnaryOp :: (CellTerm -> IO CellTerm) -> IO (Maybe (Map Text SC.Term))
    bvUnaryOp f =
      do let w = connWidthNat "Y"
         ta <- extTrunc sc w =<< input "A"
         res <- f ta
         output res
    -- extend inputs to output width
    bvBinaryOp :: (CellTerm -> CellTerm -> IO CellTerm) -> IO (Maybe (Map Text SC.Term))
    bvBinaryOp f =
      do let w = connWidthNat "Y"
         ta <- extTrunc sc w =<< input "A"
         tb <- extTrunc sc w =<< input "B"
         res <- f ta tb
         output res
    -- extend inputs to max input width, output is a single bit
    bvBinaryCmp :: (CellTerm -> CellTerm -> IO SC.Term) -> IO (Maybe (Map Text SC.Term))
    bvBinaryCmp f =
      do ta <- input "A"
         tb <- input "B"
         res <- uncurry f =<< extMax sc ta tb
         outputBit res
    bvReduce :: Bool -> SC.Term -> IO (Maybe (Map Text SC.Term))
    bvReduce boolIdentity boolFun =
      do CellTerm t _ _ <- input "A"
         w <- connWidth "A"
         boolTy <- SC.scBoolType sc
         identity <- SC.scBool sc boolIdentity
         scFoldr <- SC.scGlobalDef sc $ SC.mkIdent SC.preludeName "foldr"
         bit <- SC.scApplyAll sc scFoldr [boolTy, boolTy, w, boolFun, identity, t]
         outputBit bit
