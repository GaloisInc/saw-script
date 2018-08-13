------------------------------------------------------------------------
-- |
-- Module      : Verifier.SAW.Simulator.What4.SWord
-- Copyright   : Galois, Inc. 2018
-- License     : BSD3
-- Maintainer  : sweirich@galois.com
-- Stability   : experimental
-- Portability : non-portable (language extensions)
--
-- A wrapper for What4 bitvectors so that the width is not tracked
-- statically.
-- This library is intended for use as a backend for saw-core. Therefore
-- it does not wrap all of the bitvector operations from the What4.Interface.
------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PartialTypeSignatures #-}

-- To allow implicitly provided nats
{-# LANGUAGE AllowAmbiguousTypes #-}


-- TODO: module exports?
module Verifier.SAW.Simulator.What4.SWord where


-- TODO: improve treatment of partiality. Currently, dynamic
-- failures (e.g. due to failing width checks) use 'fail' from
-- the IO monad. Perhaps this is what we want, as the saw-core
-- code should come in type checked.

-- Question: Why do the functions in What4.Interface take
-- NatRepr's as arguments instead of implicit KnownNats ?
-- We then could use TypeApplications instead of constructing
-- reprs.
-- Overall, the operations below are a bit random about whether they
-- require an implicit or explicit type argument.

import           Data.Vector (Vector)
import qualified Data.Vector as V

import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           GHC.TypeLits

import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some(Some(..))
import           Verifier.SAW.Simulator.What4.PosNat

import           What4.Interface(SymBV,Pred,SymInteger,IsExpr,SymExpr,IsExprBuilder)
import qualified What4.Interface as W


-------------------------------------------------------------
--
-- | A What4 symbolic bitvector where the size does not appear in the type
data SWord sym where

  DBV :: (IsExpr (SymExpr sym), KnownNat w, 1<=w) => SymBV sym w -> SWord sym
  -- a bit-vector with positive length

  ZBV :: SWord sym
  -- a zero-length bit vector. i.e. 0


instance Show (SWord sym) where
  show (DBV bv) = show $ W.printSymExpr bv
  show ZBV      = "0:[0]"

-------------------------------------------------------------

-- | Return the signed value if this is a constant bitvector
bvAsSignedInteger :: forall sym. IsExprBuilder sym => SWord sym -> Maybe Integer
bvAsSignedInteger ZBV = Just 0
bvAsSignedInteger (DBV (bv :: SymBV sym w)) =
  W.asSignedBV bv

-- | Return the unsigned value if this is a constant bitvector
bvAsUnsignedInteger :: forall sym. IsExprBuilder sym => SWord sym -> Maybe Integer
bvAsUnsignedInteger ZBV = Just 0
bvAsUnsignedInteger (DBV (bv :: SymBV sym w)) =
  W.asUnsignedBV bv

-- | Convert an integer to an unsigned bitvector.
--   Result is undefined if integer is outside of range.
integerToBV :: forall sym width. (Integral width, IsExprBuilder sym) =>
  sym ->  SymInteger sym -> width -> IO (SWord sym)
integerToBV sym i w
  | Just (Some (PosNat wr)) <- somePosNat (toInteger w)
  = DBV <$> W.integerToBV sym i wr
  | 0 == toInteger w
  = return ZBV
  | otherwise
  = fail "integerToBV: invalid arg"

-- | Interpret the bit-vector as an unsigned integer
bvToInteger :: forall sym. (IsExprBuilder sym) =>
  sym -> SWord sym -> IO (SymInteger sym)
bvToInteger sym ZBV      = W.intLit sym 0
bvToInteger sym (DBV bv) = W.bvToInteger sym bv

-- | Interpret the bit-vector as a signed integer
sbvToInteger :: forall sym. (IsExprBuilder sym) =>
  sym -> SWord sym -> IO (SymInteger sym)
sbvToInteger sym ZBV      = W.intLit sym 0
sbvToInteger sym (DBV bv) = W.sbvToInteger sym bv


-- | Get the width of a bitvector
intSizeOf :: forall sym. SWord sym -> Int
intSizeOf (DBV (_ :: SymBV sym w)) =
  fromIntegral (natValue (knownNat @w))
intSizeOf ZBV = 0

-- | Get the width of a bitvector
bvWidth :: SWord sym -> Int
bvWidth = intSizeOf

-- | Create a bitvector with the given width and value
bvLit :: forall sym. IsExprBuilder sym =>
  sym -> Int -> Integer -> IO (SWord sym)
bvLit _ w _
  | w == 0
  = return ZBV
bvLit sym w dat
  | Just (Some (PosNat rw)) <- somePosNat (toInteger w)
  = DBV <$> W.bvLit sym rw dat
  | otherwise
  = fail "bvLit: size of bitvector is < 0 or >= maxInt"

-- | Returns true if the corresponding bit in the bitvector is set.
bvAt :: forall sym. IsExprBuilder sym => sym
  -> SWord sym
  -> Int  -- ^ Index of bit (0 is the most significant bit)
  -> IO (Pred sym)
bvAt sym (DBV (bv :: SymBV sym w)) i = do
  let w   = toInteger (natValue (knownNat @w))
  let idx = w - 1 - toInteger i
  W.testBitBV sym idx bv
bvAt _ ZBV _ = fail "cannot index into empty bitvector"
  -- TODO: or could return 0?

-- | Concatenate two bitvectors.
bvJoin  :: forall sym. IsExprBuilder sym => sym
  -> SWord sym
  -- ^ most significant bits
  -> SWord sym
  -- ^ least significant bits
  -> IO (SWord sym)
bvJoin _ x ZBV = return x
bvJoin _ ZBV x = return x
bvJoin sym (DBV (bv1 :: SymBV sym w1)) (DBV (bv2 :: SymBV sym w2))
  | PosNat _ <- addPosNat @w1 @w2
  = DBV <$> W.bvConcat sym bv1 bv2

-- | Select a subsequence from a bitvector.
-- idx = w - (m + n)
-- This fails if idx + n is >= w
bvSlice :: forall sym. IsExprBuilder sym => sym
  -> Int
  -- ^ Starting index, from 0 as most significant bit
  -> Int
  -- ^ Number of bits to take (must be > 0)
  -> SWord sym -> IO (SWord sym)
bvSlice sym m n (DBV (bv :: SymBV sym w))
  | Just (Some (PosNat nr)) <- somePosNat (toInteger n),
    Just (Some mr)          <- someNat (toInteger m),
    let wr  = knownNat @w,
    Just LeqProof <- testLeq (addNat mr nr)  wr,
    let idx = subNat wr (addNat mr nr),
    Just LeqProof <- testLeq (addNat idx nr) wr
  = DBV <$> W.bvSelect sym idx nr bv
  | otherwise
  = fail $
      "invalid arguments to slice: " ++ show m ++ " " ++ show n
        ++ " from vector of length " ++ show (knownNat @w)
bvSlice _ _ _ ZBV = return ZBV

-- | Ceiling (log_2 x)
-- adapted from saw-core-sbv/src/Verifier/SAW/Simulator/SBV.hs
w_bvLg2 :: forall sym w. (IsExprBuilder sym, KnownNat w, 1 <= w) =>
   sym -> SymBV sym w -> IO (SymBV sym w)
w_bvLg2 sym x = go 0
  where
    size :: Integer
    size = natValue (knownNat @w)
    lit :: Integer -> IO (SymBV sym w)
    lit n = W.bvLit sym (knownNat @w) n
    go :: Integer -> IO (SymBV sym w)
    go i | i < size = do
           x' <- lit (2 ^ i)
           b' <- W.bvUle sym x x'
           th <- lit (toInteger i)
           el <- go (i + 1)
           W.bvIte sym b' th el
         | otherwise    = lit i

-- | If-then-else applied to bitvectors.
bvIte :: forall sym. IsExprBuilder sym =>
  sym -> Pred sym -> SWord sym -> SWord sym -> IO (SWord sym)
bvIte _ _ ZBV ZBV
  = return ZBV
bvIte sym p (DBV (bv1 :: SymBV sym w1)) (DBV (bv2 :: SymBV sym w2))
  | Just Refl <- testEquality (knownNat @w1) (knownNat @w2)
  = DBV <$> W.bvIte sym p bv1 bv2
bvIte _ _ _ _
  = fail "bit-vectors don't have same length"


----------------------------------------------------------------------
-- Convert to/from Vectors
----------------------------------------------------------------------

-- | for debugging
showVec :: forall sym. (W.IsExpr (W.SymExpr sym)) => Vector (Pred sym) -> String
showVec vec =
  show (PP.list (V.toList (V.map W.printSymExpr vec)))

-- | explode a bitvector into a vector of booleans
bvUnpack :: forall sym. IsExprBuilder sym =>
  sym -> SWord sym -> IO (Vector (Pred sym))
bvUnpack _   ZBV = return V.empty
bvUnpack sym (DBV (bv :: SymBV sym w)) = do
  let w :: Integer
      w = natValue (knownNat @w)
  V.generateM (fromIntegral w)
              (\i -> W.testBitBV sym (w - 1 - toInteger i) bv)

-- | convert a vector of booleans to a bitvector
bvPack :: forall sym. (W.IsExpr (W.SymExpr sym), IsExprBuilder sym) =>
  sym -> Vector (Pred sym) -> IO (SWord sym)
bvPack sym vec = do
  vec' <- V.mapM (\p -> do
                     v1 <- bvLit sym 1 1
                     v2 <- bvLit sym 1 0
                     bvIte sym p v1 v2) vec
  V.foldM (\x y -> bvJoin sym x y) ZBV vec'

----------------------------------------------------------------------
-- Generic wrapper for unary operators
----------------------------------------------------------------------

-- | Type of unary operation on bitvectors
type SWordUn =
  forall sym. IsExprBuilder sym =>
  sym -> SWord sym -> IO (SWord sym)

-- | Convert a unary operation on length indexed bvs to a unary operation
-- on `SWord`
bvUn ::  forall sym. IsExprBuilder sym =>
   (forall w. (KnownNat w, 1 <= w) => sym -> SymBV sym w -> IO (SymBV sym w)) ->
   sym -> SWord sym -> IO (SWord sym)
bvUn f sym (DBV (bv :: SymBV sym w)) = DBV <$> f sym bv
bvUn _ _  ZBV = return ZBV

----------------------------------------------------------------------
-- Generic wrapper for binary operators that take two words
-- of the same length
----------------------------------------------------------------------

-- | type of binary operation that returns a bitvector
type SWordBin =
  forall sym. IsExprBuilder sym =>
  sym -> SWord sym -> SWord sym -> IO (SWord sym)
-- | type of binary operation that returns a boolean
type PredBin =
  forall sym. IsExprBuilder sym =>
  sym -> SWord sym -> SWord sym -> IO (Pred sym)


-- | convert binary operations that return bitvectors
bvBin  :: forall sym. IsExprBuilder sym =>
  (forall w. 1 <= w => sym -> SymBV sym w -> SymBV sym w -> IO (SymBV sym w)) ->
  sym -> SWord sym -> SWord sym -> IO (SWord sym)
bvBin f sym (DBV (bv1 :: SymBV sym w1)) (DBV (bv2 :: SymBV sym w2))
  | Just Refl <- testEquality (knownNat @w1) (knownNat @w2)
  = DBV <$> f sym bv1 bv2
bvBin _ _ ZBV ZBV
  = return ZBV
bvBin _ _ _ _
  = fail "bit vectors must have same length"


-- | convert binary operations that return booleans (Pred)
bvBinPred  :: forall sym. IsExprBuilder sym =>
  (forall w. 1 <= w => sym -> SymBV sym w -> SymBV sym w -> IO (Pred sym)) ->
  sym -> SWord sym -> SWord sym -> IO (Pred sym)
bvBinPred f sym (DBV (bv1:: SymBV sym w1)) (DBV (bv2 :: SymBV sym w2))
  | Just Refl <- testEquality (knownNat @w1) (knownNat @w2)
  = f sym bv1 bv2
  | otherwise
  = fail $ "bit vectors must have same length" ++ show (knownNat @w1) ++ " " ++ show (knownNat @w2)
bvBinPred _ _ ZBV ZBV
  = fail "no zero-length bit vectors here"
bvBinPred _ _ _ _
  = fail $ "bit vectors must have same length"



 -- Bitvector logical

-- | Bitwise complement
bvNot :: SWordUn
bvNot = bvUn W.bvNotBits

-- | Bitwise logical and.
bvAnd :: SWordBin
bvAnd = bvBin W.bvAndBits

-- | Bitwise logical or.
bvOr :: SWordBin
bvOr = bvBin W.bvOrBits

-- | Bitwise logical exclusive or.
bvXor :: SWordBin
bvXor = bvBin W.bvXorBits

 -- Bitvector arithmetic

-- | 2's complement negation.
bvNeg :: SWordUn
bvNeg = bvUn W.bvNeg

-- | Add two bitvectors.
bvAdd :: SWordBin
bvAdd = bvBin W.bvAdd

-- | Subtract one bitvector from another.
bvSub :: SWordBin
bvSub = bvBin W.bvSub

-- | Multiply one bitvector by another.
bvMul :: SWordBin
bvMul = bvBin W.bvMul


-- | Unsigned bitvector division.
--
--   The result is undefined when @y@ is zero,
--   but is otherwise equal to @floor( x / y )@.
bvUDiv :: SWordBin
bvUDiv = bvBin W.bvUdiv


-- | Unsigned bitvector remainder.
--
--   The result is undefined when @y@ is zero,
--   but is otherwise equal to @x - (bvUdiv x y) * y@.
bvURem :: SWordBin
bvURem = bvBin W.bvUrem

-- | Signed bitvector division.  The result is truncated to zero.
--
--   The result of @bvSdiv x y@ is undefined when @y@ is zero,
--   but is equal to @floor(x/y)@ when @x@ and @y@ have the same sign,
--   and equal to @ceiling(x/y)@ when @x@ and @y@ have opposite signs.
--
--   NOTE! However, that there is a corner case when dividing @MIN_INT@ by
--   @-1@, in which case an overflow condition occurs, and the result is instead
--   @MIN_INT@.
bvSDiv :: SWordBin
bvSDiv = bvBin W.bvSdiv

-- | Signed bitvector remainder.
--
--   The result of @bvSrem x y@ is undefined when @y@ is zero, but is
--   otherwise equal to @x - (bvSdiv x y) * y@.
bvSRem :: SWordBin
bvSRem = bvBin W.bvSrem

bvLg2 :: SWordUn
bvLg2 = bvUn w_bvLg2

 -- Bitvector comparisons

-- | Return true if bitvectors are equal.
bvEq   :: PredBin
bvEq = bvBinPred W.bvEq

-- | Signed less-than-or-equal.
bvsle  :: PredBin
bvsle = bvBinPred W.bvSle

-- | Signed less-than.
bvslt  :: PredBin
bvslt = bvBinPred W.bvSlt

-- | Unsigned less-than-or-equal.
bvule  :: PredBin
bvule = bvBinPred W.bvUle

-- | Unsigned less-than.
bvult  :: PredBin
bvult = bvBinPred W.bvUlt

-- | Signed greater-than-or-equal.
bvsge  :: PredBin
bvsge = bvBinPred W.bvSge

-- | Signed greater-than.
bvsgt  :: PredBin
bvsgt = bvBinPred W.bvSgt

-- | Unsigned greater-than-or-equal.
bvuge  :: PredBin
bvuge = bvBinPred W.bvUge

-- | Unsigned greater-than.
bvugt  :: PredBin
bvugt = bvBinPred W.bvUgt

----------------------------------------
-- Bitvector rotations
----------------------------------------

-- | Rotate left by a concrete integer value
bvRolInt :: forall sym. IsExprBuilder sym => sym ->
              SWord sym -> Integer -> IO (SWord sym)
bvRolInt sym (DBV (bv :: SymBV sym w)) i = do
  i' <- W.intLit sym i
  DBV <$> bvRotateL' sym bv i'
bvRolInt _sym ZBV _i = return ZBV

-- | Rotate right by a concrete integer value
bvRorInt :: forall sym. IsExprBuilder sym => sym ->
              SWord sym -> Integer -> IO (SWord sym)
bvRorInt sym (DBV (bv :: SymBV sym w)) i = do
  i' <- W.intLit sym i
  DBV <$> bvRotateR' sym bv i'
bvRorInt _sym ZBV _i = return ZBV

-- | Rotate left by a symbolic bitvector
--
-- The two bitvectors do not need to be the same length
bvRol    :: forall sym. IsExprBuilder sym => sym ->
              SWord sym -> SWord sym -> IO (SWord sym)
bvRol sym (DBV (bv :: SymBV sym w1)) (DBV (i :: SymBV sym w2)) = do
  i' <- W.bvToInteger sym i
  DBV <$> bvRotateL' sym bv i'
bvRol _sym ZBV _i = return ZBV
bvRol _sym (DBV bv) ZBV = return $ DBV bv

-- | Rotate right by a symbolic bitvector
--
-- The two bitvectors do not need to be the same length
bvRor    :: forall sym. IsExprBuilder sym => sym ->
              SWord sym -> SWord sym -> IO (SWord sym)
bvRor sym (DBV (bv :: SymBV sym w1)) (DBV (i :: SymBV sym w2)) = do
  i' <- W.bvToInteger sym i
  DBV <$> bvRotateR' sym bv i'
bvRor _sym ZBV _i = return ZBV
bvRor _sym (DBV bv) ZBV = return $ DBV bv

-- | Worker function for left rotations
--
-- Defined from the concrete implementation
--
-- bvRotateL (BV w x) i = Prim.bv w ((x `shiftL` j) .|. (x `shiftR` (w - j)))
--    where j = fromInteger (i `mod` toInteger w)
bvRotateL' :: forall sym w1. (KnownNat w1, IsExprBuilder sym, 1 <= w1) => sym ->
             SymBV sym w1 -> SymInteger sym -> IO (SymBV sym w1)
bvRotateL' sym x i' = do

    w' <- W.intLit sym w

    j <- W.intMod sym i' w'

    jj <- W.natToInteger sym j

    jjj <- W.integerToBV sym jj (knownNat @w1)

    x1 <- bvShiftL sym pfalse x jjj

    wmj <- W.intSub sym w' jj
    wmjjj <- W.integerToBV sym wmj (knownNat @w1)

    x2 <- bvShiftR sym (W.bvLshr sym) pfalse x wmjjj
    W.bvOrBits sym x1 x2
  where
    pfalse :: Pred sym
    pfalse = W.falsePred sym

    w = natValue (knownNat @w1)

-- | Worker function for right rotations
--
-- Defined from the concrete implementation
bvRotateR' :: forall sym w1. (KnownNat w1, IsExprBuilder sym, 1 <= w1) => sym ->
             SymBV sym w1 -> SymInteger sym -> IO (SymBV sym w1)
bvRotateR' sym x i = do
  ii <- W.intNeg sym i
  bvRotateL' sym x ii
----------------------------------------
-- Bitvector shifts (prims)
----------------------------------------

-- | logical shift left, amount specified by concrete integer
bvShlInt :: forall sym. IsExprBuilder sym => sym ->
              Pred sym -> SWord sym -> Integer -> IO (SWord sym)
bvShlInt sym p (DBV (bv :: SymBV sym w)) x
  = DBV <$> bvShl' sym (knownNat @w) p bv x
bvShlInt _ _ ZBV _
  = return ZBV

-- | logical (unsigned) shift right, specified by concrete integer
bvShrInt :: forall sym. IsExprBuilder sym => sym ->
              Pred sym -> SWord sym -> Integer -> IO (SWord sym)
bvShrInt sym p (DBV (bv :: SymBV sym w)) x
  = DBV <$> bvShr' sym (W.bvLshr sym) (knownNat @w) p bv x
bvShrInt _ _ ZBV _
  = return ZBV

-- | arithmetic (signed) shift right
bvSShrInt :: forall sym. IsExprBuilder sym => sym ->
              Pred sym -> SWord sym -> Integer -> IO (SWord sym)
bvSShrInt sym p (DBV (bv :: SymBV sym w)) x
  = DBV <$> bvShr' sym (W.bvAshr sym) (knownNat @w) p bv x
bvSShrInt _ _ ZBV _
  = return ZBV


-- | logical shift left, amount specified by (symbolic) bitvector
bvShl    :: forall sym. IsExprBuilder sym => sym
              -> Pred sym
              -> SWord sym
              -- ^ shift this
              -> SWord sym
              -- ^ amount to shift by
              -> IO (SWord sym)
bvShl sym p (DBV (bv1 :: SymBV sym w1)) (DBV (bv2 :: SymBV sym w2))
  | Just Refl <- testEquality (knownNat @w1) (knownNat @w2)
  = DBV <$> bvShiftL sym p bv1 bv2
  -- amount to shift by is smaller
  | Just LeqProof <- testLeq (addNat (knownNat @w2) (knownNat @1)) (knownNat @w1)
  = do bv2' <- W.bvZext sym (knownNat @w1) bv2
       DBV <$> bvShiftL sym p bv1 bv2'
  | otherwise
  = fail $ "bvShl: bit vectors must have same length "
            ++ show (knownNat @w1) ++ " " ++ show (knownNat @w2)
bvShl _ _ ZBV ZBV
  = return ZBV
bvShl _ _ _ _
  = fail $ "bvShl: bitvectors do not have the same length"


-- | logical shift right
bvShr    :: forall sym. IsExprBuilder sym => sym ->
              Pred sym -> SWord sym -> SWord sym -> IO (SWord sym)
bvShr  sym p (DBV (bv1 :: SymBV sym w1)) (DBV (bv2 :: SymBV sym w2))
  | Just Refl <- testEquality (knownNat @w1) (knownNat @w2)
  = DBV <$> bvShiftR sym (W.bvLshr sym) p bv1 bv2
  | Just LeqProof <- testLeq (addNat (knownNat @w2) (knownNat @1)) (knownNat @w1)
  = do bv2' <- W.bvZext sym (knownNat @w1) bv2
       DBV <$> bvShiftR sym (W.bvLshr sym) p bv1 bv2'
  | otherwise
  = fail $ "bvShr: bitvectors do not have the same length "
         ++ show (knownNat @w1) ++ " " ++ show (knownNat @w2)
bvShr _ _ ZBV ZBV
  = return ZBV
bvShr _ _ _ _
  = fail $ "bvShr: bitvectors do not have the same length"


-- | arithmetic shift right
bvSShr    :: forall sym. IsExprBuilder sym => sym ->
              Pred sym -> SWord sym -> SWord sym -> IO (SWord sym)
bvSShr  sym p (DBV (bv1 :: SymBV sym w1)) (DBV (bv2 :: SymBV sym w2))
  | Just Refl <- testEquality (knownNat @w1) (knownNat @w2)
  = DBV <$> bvShiftR sym (W.bvAshr sym) p bv1 bv2
  | Just LeqProof <- testLeq (addNat (knownNat @w2) (knownNat @1)) (knownNat @w1)
  = do bv2' <- W.bvSext sym (knownNat @w1) bv2
       DBV <$> bvShiftR sym (W.bvAshr sym) p bv1 bv2'
  | otherwise
  = fail $ "bvSShr: bitvectors do not have the same length: "
           ++ show (knownNat @w1) ++ " " ++ show (knownNat @w2)
bvSShr _ _ ZBV ZBV
  = return ZBV
bvSShr _ _ _ _
  = fail $ "bvSShr: bitvectors do not have the same length: "


----------------------------------------
-- Shift operations
----------------------------------------

-- If the predicate is true, invert the bitvector, shift then
-- invert again. (Following SBV definition). This means that
-- the predicate controls whether the newly added bit is a one
-- or a zero.

bvShiftL :: forall sym w. (IsExprBuilder sym, 1 <= w) => sym ->
  Pred sym -> SymBV sym w -> SymBV sym w -> IO (SymBV sym w)
bvShiftL sym b x j = do
  nx   <- W.bvNotBits sym x
  snx  <- W.bvShl sym nx j
  nsnx <- W.bvNotBits sym snx
  W.bvIte sym b nsnx =<< W.bvShl sym x j

bvShl' :: (IsExprBuilder sym, 1 <= w) => sym ->
  NatRepr w -> Pred sym -> SymBV sym w -> Integer -> IO (SymBV sym w)
bvShl' sym rep b x i = do
  j   <- W.bvLit sym rep i   -- what if i is too big for rep bits?
  bvShiftL sym b x j


-- The shr argument should be W.bvAshr or W.bvLshr, depending
-- on whether to use arithmetic or logical shift right

bvShiftR :: forall sym w. (IsExprBuilder sym, 1 <= w) => sym ->
  (SymBV sym w -> SymBV sym w -> IO (SymBV sym w)) ->
  Pred sym -> SymBV sym w -> SymBV sym w -> IO (SymBV sym w)
bvShiftR sym shr b x j = do
  nx   <- W.bvNotBits sym x
  snx  <- shr nx j
  nsnx <- W.bvNotBits sym snx
  W.bvIte sym b nsnx =<< shr x j

bvShr' :: (IsExprBuilder sym, 1 <= w) => sym ->
  (SymBV sym w -> SymBV sym w -> IO (SymBV sym w)) ->
  NatRepr w -> Pred sym -> SymBV sym w -> Integer -> IO (SymBV sym w)
bvShr' sym shr rep b x i = do
  j   <- W.bvLit sym rep i
  bvShiftR sym shr b x j
