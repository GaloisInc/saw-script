{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE EmptyDataDecls #-}

{- |
Module      : Verifier.SAW.Simulator.SBV
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}
module Verifier.SAW.Simulator.SBV
  ( sbvSATQuery
  , SValue
  , Labeler(..)
  , sbvCodeGen_definition
  , sbvCodeGen
  , toWord
  , toBool
  , getLabels
  , module Verifier.SAW.Simulator.SBV.SWord
  ) where

import Data.SBV.Dynamic

import Verifier.SAW.Simulator.SBV.SWord

import Control.Lens ((<&>))

import Data.Bits
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text
import Data.Vector (Vector)
import qualified Data.Vector as V

import Data.Traversable as T
#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import Control.Monad.IO.Class
import Control.Monad.State as ST
import Numeric.Natural (Natural)

import qualified Verifier.SAW.Prim as Prim
import qualified Verifier.SAW.Recognizer as R
import qualified Verifier.SAW.Simulator as Sim
import qualified Verifier.SAW.Simulator.Prims as Prims
import Verifier.SAW.SATQuery
import Verifier.SAW.SharedTerm
import Verifier.SAW.Simulator.Value
import Verifier.SAW.TypedAST (FieldName, toShortName, identBaseName)
import Verifier.SAW.FiniteValue
            (FirstOrderType(..), FirstOrderValue(..)
            , fovVec, firstOrderTypeOf, asFirstOrderType
            )

import Verifier.SAW.Utils (panic)

data SBV

type instance EvalM SBV = IO
type instance VBool SBV = SBool
type instance VWord SBV = SWord
type instance VInt  SBV = SInteger
type instance Extra SBV = SbvExtra

type SValue = Value SBV
type SPrim  = Prims.Prim SBV
--type SThunk = Thunk SBV

data SbvExtra =
  SStream (Natural -> IO SValue) (IORef (Map Natural SValue))

instance Show SbvExtra where
  show (SStream _ _) = "<SStream>"

pure1 :: Applicative f => (a -> b) -> a -> f b
pure1 f x = pure (f x)

pure2 :: Applicative f => (a -> b -> c) -> a -> b -> f c
pure2 f x y = pure (f x y)

pure3 :: Applicative f => (a -> b -> c -> d) -> a -> b -> c -> f d
pure3 f x y z = pure (f x y z)

prims :: Prims.BasePrims SBV
prims =
  Prims.BasePrims
  { Prims.bpAsBool  = svAsBool
  , Prims.bpUnpack  = svUnpack
  , Prims.bpPack    = pure1 symFromBits
  , Prims.bpBvAt    = pure2 svAt
  , Prims.bpBvLit   = pure2 literalSWord
  , Prims.bpBvSize  = intSizeOf
  , Prims.bpBvJoin  = pure2 svJoin
  , Prims.bpBvSlice = pure3 svSlice
    -- Conditionals
  , Prims.bpMuxBool  = pure3 svIte
  , Prims.bpMuxWord  = pure3 svIte
  , Prims.bpMuxInt   = pure3 svIte
  , Prims.bpMuxExtra = muxSbvExtra
    -- Booleans
  , Prims.bpTrue   = svTrue
  , Prims.bpFalse  = svFalse
  , Prims.bpNot    = pure1 svNot
  , Prims.bpAnd    = pure2 svAnd
  , Prims.bpOr     = pure2 svOr
  , Prims.bpXor    = pure2 svXOr
  , Prims.bpBoolEq = pure2 svEqual
    -- Bitvector logical
  , Prims.bpBvNot  = pure1 svNot
  , Prims.bpBvAnd  = pure2 svAnd
  , Prims.bpBvOr   = pure2 svOr
  , Prims.bpBvXor  = pure2 svXOr
    -- Bitvector arithmetic
  , Prims.bpBvNeg  = pure1 svUNeg
  , Prims.bpBvAdd  = pure2 svPlus
  , Prims.bpBvSub  = pure2 svMinus
  , Prims.bpBvMul  = pure2 svTimes
  , Prims.bpBvUDiv = pure2 svQuot
  , Prims.bpBvURem = pure2 svRem
  , Prims.bpBvSDiv = \x y -> pure (svUnsign (svQuot (svSign x) (svSign y)))
  , Prims.bpBvSRem = \x y -> pure (svUnsign (svRem (svSign x) (svSign y)))
  , Prims.bpBvLg2  = pure1 sLg2
    -- Bitvector comparisons
  , Prims.bpBvEq   = pure2 svEqual
  , Prims.bpBvsle  = \x y -> pure (svLessEq (svSign x) (svSign y))
  , Prims.bpBvslt  = \x y -> pure (svLessThan (svSign x) (svSign y))
  , Prims.bpBvule  = pure2 svLessEq
  , Prims.bpBvult  = pure2 svLessThan
  , Prims.bpBvsge  = \x y -> pure (svGreaterEq (svSign x) (svSign y))
  , Prims.bpBvsgt  = \x y -> pure (svGreaterThan (svSign x) (svSign y))
  , Prims.bpBvuge  = pure2 svGreaterEq
  , Prims.bpBvugt  = pure2 svGreaterThan
    -- Bitvector shift/rotate
  , Prims.bpBvRolInt = pure2 svRol'
  , Prims.bpBvRorInt = pure2 svRor'
  , Prims.bpBvShlInt = pure3 svShl'
  , Prims.bpBvShrInt = pure3 svShr'
  , Prims.bpBvRol    = pure2 svRotateLeft
  , Prims.bpBvRor    = pure2 svRotateRight
  , Prims.bpBvShl    = pure3 svShiftL
  , Prims.bpBvShr    = pure3 svShiftR
    -- Bitvector misc
  , Prims.bpBvPopcount = pure1 svPopcount
  , Prims.bpBvCountLeadingZeros = pure1 svCountLeadingZeros
  , Prims.bpBvCountTrailingZeros = pure1 svCountTrailingZeros
  , Prims.bpBvForall = unsupportedSBVPrimitive "bvForall"
    -- Integer operations
  , Prims.bpIntAdd = pure2 svPlus
  , Prims.bpIntSub = pure2 svMinus
  , Prims.bpIntMul = pure2 svTimes
  , Prims.bpIntDiv = pure2 svQuot
  , Prims.bpIntMod = pure2 svRem
  , Prims.bpIntNeg = pure1 svUNeg
  , Prims.bpIntAbs = pure1 svAbs
  , Prims.bpIntEq  = pure2 svEqual
  , Prims.bpIntLe  = pure2 svLessEq
  , Prims.bpIntLt  = pure2 svLessThan
  , Prims.bpIntMin = unsupportedSBVPrimitive "bpIntMin"
  , Prims.bpIntMax = unsupportedSBVPrimitive "bpIntMax"
    -- Array operations
  , Prims.bpArrayConstant = unsupportedSBVPrimitive "bpArrayConstant"
  , Prims.bpArrayLookup = unsupportedSBVPrimitive "bpArrayLookup"
  , Prims.bpArrayUpdate = unsupportedSBVPrimitive "bpArrayUpdate"
  , Prims.bpArrayEq = unsupportedSBVPrimitive "bpArrayEq"
  }

unsupportedSBVPrimitive :: String -> a
unsupportedSBVPrimitive = Prim.unsupportedPrimitive "SBV"

constMap :: Map Ident SPrim
constMap =
  Map.union (Prims.constMap prims) $
  Map.fromList
  [
  -- Shifts
    ("Prelude.bvShl" , bvShLOp)
  , ("Prelude.bvShr" , bvShROp)
  , ("Prelude.bvSShr", bvSShROp)
  -- Integers
  , ("Prelude.intToNat", intToNatOp)
  , ("Prelude.natToInt", natToIntOp)
  , ("Prelude.intToBv" , intToBvOp)
  , ("Prelude.bvToInt" , bvToIntOp)
  , ("Prelude.sbvToInt", sbvToIntOp)
  -- Integers mod n
  , ("Prelude.toIntMod"  , toIntModOp)
  , ("Prelude.fromIntMod", fromIntModOp)
  , ("Prelude.intModEq"  , intModEqOp)
  , ("Prelude.intModAdd" , intModBinOp svPlus)
  , ("Prelude.intModSub" , intModBinOp svMinus)
  , ("Prelude.intModMul" , intModBinOp svTimes)
  , ("Prelude.intModNeg" , intModUnOp svUNeg)
  -- Streams
  , ("Prelude.MkStream", mkStreamOp)
  , ("Prelude.streamGet", streamGetOp)
  -- Misc
  , ("Prelude.expByNat", Prims.expByNatOp prims)
  ]

------------------------------------------------------------
-- Coercion functions
--

bitVector :: Int -> Integer -> SWord
bitVector w i = literalSWord w i

symFromBits :: Vector SBool -> SWord
symFromBits v = V.foldl svJoin (bitVector 0 0) (V.map svToWord1 v)

toMaybeBool :: SValue -> Maybe SBool
toMaybeBool (VBool b) = Just b
toMaybeBool _  = Nothing

toBool :: SValue -> SBool
toBool (VBool b) = b
toBool sv = error $ unwords ["toBool failed:", show sv]

toWord :: SValue -> IO SWord
toWord (VWord w) = return w
toWord (VVector vv) = symFromBits <$> traverse (fmap toBool . force) vv
toWord x = fail $ unwords ["Verifier.SAW.Simulator.SBV.toWord", show x]

toMaybeWord :: SValue -> IO (Maybe SWord)
toMaybeWord (VWord w) = return (Just w)
toMaybeWord (VVector vv) = ((symFromBits <$>) . T.sequence) <$> traverse (fmap toMaybeBool . force) vv
toMaybeWord _ = return Nothing

-- | Flatten an SValue to a sequence of components, each of which is
-- either a symbolic word or a symbolic boolean. If the SValue
-- contains any values built from data constructors, then return them
-- encoded as a String.
flattenSValue :: String -> SValue -> IO ([SVal], String)
flattenSValue nm v = do
  mw <- toMaybeWord v
  case mw of
    Just w -> return ([w], "")
    Nothing ->
      case v of
        VUnit                     -> return ([], "")
        VPair x y                 -> do (xs, sx) <- flattenSValue nm =<< force x
                                        (ys, sy) <- flattenSValue nm =<< force y
                                        return (xs ++ ys, sx ++ sy)
        VRecordValue elems        -> do (xss, sxs) <-
                                          unzip <$>
                                          mapM (flattenSValue nm <=< force . snd) elems
                                        return (concat xss, concat sxs)
        VVector (V.toList -> ts)  -> do (xss, ss) <- unzip <$> traverse (force >=> flattenSValue nm) ts
                                        return (concat xss, concat ss)
        VBool sb                  -> return ([sb], "")
        VInt si                   -> return ([si], "")
        VIntMod 0 si              -> return ([si], "")
        VIntMod n si              -> return ([svRem si (svInteger KUnbounded (toInteger n))], "")
        VWord sw                  -> return (if intSizeOf sw > 0 then [sw] else [], "")
        VCtorApp i ps ts          -> do (xss, ss) <- unzip <$> traverse (force >=> flattenSValue nm) (ps++ts)
                                        return (concat xss, "_" ++ (Text.unpack (identBaseName (primName i))) ++ concat ss)
        VNat n                    -> return ([], "_" ++ show n)
        TValue (suffixTValue -> Just s)
                                  -> return ([], s)
        VFun _ _ -> fail $ "Cannot create uninterpreted higher-order function " ++ show nm
        _ -> fail $ "Cannot create uninterpreted function " ++ show nm ++ " with argument " ++ show v

vWord :: SWord -> SValue
vWord lv = VWord lv

vBool :: SBool -> SValue
vBool l = VBool l

vInteger :: SInteger -> SValue
vInteger x = VInt x

------------------------------------------------------------
-- Function constructors

wordFun :: (SWord -> SPrim) -> SPrim
wordFun = Prims.wordFun (pure1 symFromBits)

------------------------------------------------------------
-- Indexing operations

-- | Lifts a strict mux operation to a lazy mux
lazyMux :: (SBool -> a -> a -> IO a) -> (SBool -> IO a -> IO a -> IO a)
lazyMux muxFn c tm fm =
  case svAsBool c of
    Just True  -> tm
    Just False -> fm
    Nothing    -> do
      t <- tm
      f <- fm
      muxFn c t f

-- selectV merger maxValue valueFn index returns valueFn v when index has value v
-- if index is greater than maxValue, it returns valueFn maxValue. Use the ite op from merger.
selectV :: (SBool -> b -> b -> b) -> Natural -> (Natural -> b) -> SWord -> b
selectV merger maxValue valueFn vx =
  case svAsInteger vx of
    Just i
      | i >= 0    -> valueFn (fromInteger i)
      | otherwise -> panic "selectV" ["expected nonnegative integer", show i]
    Nothing -> impl (intSizeOf vx) 0
  where
    impl _ x | x > maxValue || x < 0 = valueFn maxValue
    impl 0 y = valueFn y
    impl i y = merger (svTestBit vx j) (impl j (y `setBit` j)) (impl j y) where j = i - 1

-- Big-endian version of svTestBit
svAt :: SWord -> Int -> SBool
svAt x i = svTestBit x (intSizeOf x - 1 - i)

svUnpack :: SWord -> IO (Vector SBool)
svUnpack x = return (V.generate (intSizeOf x) (svAt x))

asWordList :: [SValue] -> Maybe [SWord]
asWordList = go id
 where
  go f [] = Just (f [])
  go f (VWord x : xs) = go (f . (x:)) xs
  go _ _ = Nothing

svSlice :: Int -> Int -> SWord -> SWord
svSlice i j x = svExtract (w - i - 1) (w - i - j) x
  where w = intSizeOf x

----------------------------------------
-- Shift operations

-- | op : (n : Nat) -> Vec n Bool -> Nat -> Vec n Bool
bvShiftOp :: (SWord -> SWord -> SWord) -> (SWord -> Int -> SWord) -> SPrim
bvShiftOp bvOp natOp =
  Prims.constFun $
  wordFun $ \x ->
  Prims.strictFun $ \y ->
  Prims.Prim $
    case y of
      VNat i | j < toInteger (maxBound :: Int) -> return (vWord (natOp x (fromInteger j)))
        where j = toInteger i `min` toInteger (intSizeOf x)
      VBVToNat _ v -> fmap (vWord . bvOp x) (toWord v)
      _        -> error $ unwords ["Verifier.SAW.Simulator.SBV.bvShiftOp", show y]

-- bvShl : (w : Nat) -> Vec w Bool -> Nat -> Vec w Bool;
bvShLOp :: SPrim
bvShLOp = bvShiftOp svShiftLeft svShl

-- bvShR : (w : Nat) -> Vec w Bool -> Nat -> Vec w Bool;
bvShROp :: SPrim
bvShROp = bvShiftOp svShiftRight svShr

-- bvSShR : (w : Nat) -> Vec w Bool -> Nat -> Vec w Bool;
bvSShROp :: SPrim
bvSShROp = bvShiftOp bvOp natOp
  where
    bvOp w x = svUnsign (svShiftRight (svSign w) x)
    natOp w i = svUnsign (svShr (svSign w) i)

-----------------------------------------
-- Integer/bitvector conversions

-- primitive intToNat : Integer -> Nat;
-- intToNat x == max 0 x
intToNatOp :: SPrim
intToNatOp =
  Prims.intFun $ \i ->
  Prims.PrimValue $
    case svAsInteger i of
      Just i'
        | 0 <= i'   -> VNat (fromInteger i')
        | otherwise -> VNat 0
      Nothing ->
        let z  = svInteger KUnbounded 0
            i' = svIte (svLessThan i z) z i
         in VIntToNat (VInt i')

-- primitive natToInt :: Nat -> Integer;
natToIntOp :: SPrim
natToIntOp =
  Prims.natFun $ \n ->
  Prims.PrimValue $
    VInt (literalSInteger (toInteger n))

-- primitive bvToInt : (n : Nat) -> Vec n Bool -> Integer;
bvToIntOp :: SPrim
bvToIntOp =
  Prims.constFun $
  wordFun $ \v ->
  Prims.PrimValue $
   case svAsInteger v of
      Just i ->  VInt (literalSInteger i)
      Nothing -> VInt (svFromIntegral KUnbounded v)

-- primitive sbvToInt : (n : Nat) -> Vec n Bool -> Integer;
sbvToIntOp :: SPrim
sbvToIntOp =
  Prims.constFun $
  wordFun $ \v ->
  Prims.PrimValue $
   case svAsInteger (svSign v) of
      Just i  -> VInt (literalSInteger i)
      Nothing -> VInt (svFromIntegral KUnbounded (svSign v))

-- primitive intToBv : (n : Nat) -> Integer -> Vec n Bool;
intToBvOp :: SPrim
intToBvOp =
  Prims.natFun $ \n ->
  Prims.intFun $ \x ->
  Prims.PrimValue $
    case svAsInteger x of
      Just i  -> VWord $ literalSWord (fromIntegral n) i
      Nothing -> VWord $ svFromIntegral (KBounded False (fromIntegral n)) x

------------------------------------------------------------
-- Rotations and shifts

svRol' :: SWord -> Integer -> SWord
svRol' x i = svRol x (fromInteger (i `mod` toInteger (intSizeOf x)))

svRor' :: SWord -> Integer -> SWord
svRor' x i = svRor x (fromInteger (i `mod` toInteger (intSizeOf x)))

svShl' :: SBool -> SWord -> Integer -> SWord
svShl' b x i = svIte b (svNot (svShl (svNot x) j)) (svShl x j)
  where j = fromInteger (i `min` toInteger (intSizeOf x))

svShr' :: SBool -> SWord -> Integer -> SWord
svShr' b x i = svIte b (svNot (svShr (svNot x) j)) (svShr x j)
  where j = fromInteger (i `min` toInteger (intSizeOf x))

svShiftL :: SBool -> SWord -> SWord -> SWord
svShiftL b x i = svIte b (svNot (svShiftLeft (svNot x) i)) (svShiftLeft x i)

svShiftR :: SBool -> SWord -> SWord -> SWord
svShiftR b x i = svIte b (svNot (svShiftRight (svNot x) i)) (svShiftRight x i)

------------------------------------------------------------
-- Integers mod n

toIntModOp :: SPrim
toIntModOp =
  Prims.natFun $ \n ->
  Prims.intFun $ \x ->
  Prims.PrimValue $
    VIntMod n x

fromIntModOp :: SPrim
fromIntModOp =
  Prims.natFun $ \n ->
  Prims.intModFun $ \x ->
  Prims.PrimValue $
    VInt (svRem x (literalSInteger (toInteger n)))

intModEqOp :: SPrim
intModEqOp =
  Prims.natFun $ \n ->
  Prims.intModFun $ \x ->
  Prims.intModFun $ \y ->
  Prims.PrimValue $
    let modulus = literalSInteger (toInteger n)
     in VBool (svEqual (svRem (svMinus x y) modulus) (literalSInteger 0))

intModBinOp :: (SInteger -> SInteger -> SInteger) -> SPrim
intModBinOp f =
  Prims.natFun $ \n ->
  Prims.intModFun $ \x ->
  Prims.intModFun $ \y ->
  Prims.PrimValue $
    VIntMod n (normalizeIntMod n (f x y))

intModUnOp :: (SInteger -> SInteger) -> SPrim
intModUnOp f =
  Prims.natFun $ \n ->
  Prims.intModFun $ \x ->
  Prims.PrimValue $
    VIntMod n (normalizeIntMod n (f x))

normalizeIntMod :: Natural -> SInteger -> SInteger
normalizeIntMod n x =
  case svAsInteger x of
    Nothing -> x
    Just i -> literalSInteger (i `mod` toInteger n)

------------------------------------------------------------
-- Stream operations

-- MkStream :: (a :: sort 0) -> (Nat -> a) -> Stream a;
mkStreamOp :: SPrim
mkStreamOp =
  Prims.constFun $
  Prims.strictFun $ \f -> Prims.Prim $
    do r <- newIORef Map.empty
       return $ VExtra (SStream (\n -> apply f (ready (VNat n))) r)

-- streamGet :: (a :: sort 0) -> Stream a -> Nat -> a;
streamGetOp :: SPrim
streamGetOp =
  Prims.tvalFun   $ \tp ->
  Prims.strictFun $ \xs ->
  Prims.strictFun $ \ix ->
  Prims.Prim $ case ix of
    VNat n -> lookupSStream xs n
    VBVToNat _ w ->
      do ilv <- toWord w
         selectV (lazyMux (muxBVal tp)) ((2 ^ intSizeOf ilv) - 1) (lookupSStream xs) ilv
    v -> panic "SBV.streamGetOp" ["Expected Nat value", show v]


lookupSStream :: SValue -> Natural -> IO SValue
lookupSStream (VExtra s) n = lookupSbvExtra s n
lookupSStream _ _ = fail "expected Stream"

lookupSbvExtra :: SbvExtra -> Natural -> IO SValue
lookupSbvExtra (SStream f r) n =
  do m <- readIORef r
     case Map.lookup n m of
       Just v  -> return v
       Nothing -> do v <- f n
                     writeIORef r (Map.insert n v m)
                     return v

------------------------------------------------------------
-- Misc operations

svPopcount :: SWord -> SWord
svPopcount xs = if w == 0 then zero else foldr1 svPlus [ svIte b one zero | b <- bits ]
 where
 bits = svBlastLE xs
 w    = length bits
 one  = literalSWord w 1
 zero = literalSWord w 0

svCountLeadingZeros :: SWord -> SWord
svCountLeadingZeros xs = go 0 bits
 where
 bits = svBlastBE xs
 w    = length bits
 go !i []     = literalSWord w i
 go !i (b:bs) = svIte b (literalSWord w i) (go (i+1) bs)

svCountTrailingZeros :: SWord -> SWord
svCountTrailingZeros xs = go 0 bits
 where
 bits = svBlastLE xs
 w    = length bits
 go !i []     = literalSWord w i
 go !i (b:bs) = svIte b (literalSWord w i) (go (i+1) bs)

-- | Ceiling (log_2 x)
sLg2 :: SWord -> SWord
sLg2 x = go 0
  where
    lit n = literalSWord (intSizeOf x) n
    go i | i < intSizeOf x = svIte (svLessEq x (lit (2^i))) (lit (toInteger i)) (go (i + 1))
         | otherwise       = lit (toInteger i)

------------------------------------------------------------
-- Ite ops

muxBVal :: TValue SBV -> SBool -> SValue -> SValue -> IO SValue
muxBVal = Prims.muxValue prims

muxSbvExtra :: TValue SBV -> SBool -> SbvExtra -> SbvExtra -> IO SbvExtra
muxSbvExtra (VDataType (primName -> "Prelude.Stream") [TValue tp] []) c x y =
  do let f i = do xi <- lookupSbvExtra x i
                  yi <- lookupSbvExtra y i
                  muxBVal tp c xi yi
     r <- newIORef Map.empty
     return (SStream f r)
muxSbvExtra tp _ _ _ = panic "muxSbvExtra" ["Type mismatch", show tp]

------------------------------------------------------------
-- External interface

-- | Abstract constants with names in the list 'unints' are kept as
-- uninterpreted constants; all others are unfolded.
sbvSolveBasic :: SharedContext -> Map Ident SPrim -> Set VarIndex -> Term -> IO SValue
sbvSolveBasic sc addlPrims unintSet t = do
  m <- scGetModuleMap sc

  let extcns (EC ix nm ty) = parseUninterpreted [] (Text.unpack (toShortName nm) ++ "#" ++ show ix) ty
  let uninterpreted ec
        | Set.member (ecVarIndex ec) unintSet = Just (extcns ec)
        | otherwise                           = Nothing
  let neutral _env nt = fail ("sbvSolveBasic: could not evaluate neutral term: " ++ show nt)
  let primHandler pn msg env _tv =
         fail $ unlines
           [ "Could not evaluate primitive " ++ show (primName pn)
           , "On argument " ++ show (length env)
           , Text.unpack msg
           ]
  cfg <- Sim.evalGlobal m (Map.union constMap addlPrims) extcns uninterpreted neutral primHandler
  Sim.evalSharedTerm cfg t

parseUninterpreted :: [SVal] -> String -> TValue SBV -> IO SValue
parseUninterpreted cws nm ty =
  case ty of
    (VPiType fnm _ body)
      -> return $
         VFun fnm $ \x ->
           do x' <- force x
              (cws', suffix) <- flattenSValue nm x'
              t2 <- applyPiBody body (ready x')
              parseUninterpreted (cws ++ cws') (nm ++ suffix) t2

    VBoolType
      -> return $ vBool $ mkUninterpreted KBool cws nm

    VIntType
      -> return $ vInteger $ mkUninterpreted KUnbounded cws nm

    VIntModType n
      -> return $ VIntMod n $ mkUninterpreted KUnbounded cws nm

    (VVecType n VBoolType)
      -> return $ vWord $ mkUninterpreted (KBounded False (fromIntegral n)) cws nm

    (VVecType n ety)
      -> do xs <- sequence $
                  [ parseUninterpreted cws (nm ++ "@" ++ show i) ety
                  | i <- [0 .. n-1] ]
            return (VVector (V.fromList (map ready xs)))

    VUnitType
      -> return VUnit

    (VPairType ty1 ty2)
      -> do x1 <- parseUninterpreted cws (nm ++ ".L") ty1
            x2 <- parseUninterpreted cws (nm ++ ".R") ty2
            return (VPair (ready x1) (ready x2))

    (VRecordType elem_tps)
      -> (VRecordValue <$>
          mapM (\(f,tp) ->
                 (f,) <$> ready <$>
                 parseUninterpreted cws (nm ++ "." ++ Text.unpack f) tp) elem_tps)

    _ -> fail $ "could not create uninterpreted type for " ++ show ty

mkUninterpreted :: Kind -> [SVal] -> String -> SVal
mkUninterpreted k args nm = svUninterpreted k nm' Nothing args
  where nm' = "|" ++ nm ++ "|" -- enclose name to allow primes and other non-alphanum chars

sbvSATQuery :: SharedContext -> Map Ident SPrim -> SATQuery -> IO ([Labeler], [ExtCns Term], Symbolic SBool)
sbvSATQuery sc addlPrims query =
  do true <- liftIO (scBool sc True)
     t <- liftIO (foldM (scAnd sc) true (satAsserts query))
     let qvars = Map.toList (satVariables query)
     let unintSet = satUninterp query
     let ecVars (ec, fot) = newVars (Text.unpack (toShortName (ecName ec))) fot

     (labels, vars) <-
       flip evalStateT 0 $ unzip <$>
       mapM ecVars qvars

     m <- liftIO (scGetModuleMap sc)

     return (labels, map fst qvars,
       do vars' <- sequence vars
          let varMap = Map.fromList (zip (map (ecVarIndex . fst) qvars) vars')

          let mkUninterp (EC ix nm ty) =
                parseUninterpreted [] (Text.unpack (toShortName nm) ++ "#" ++ show ix) ty
          let extcns ec
                | Just v <- Map.lookup (ecVarIndex ec) varMap = pure v
                | otherwise = mkUninterp ec
          let uninterpreted ec
                | Set.member (ecVarIndex ec) unintSet = Just (mkUninterp ec)
                | otherwise                           = Nothing
          let neutral _env nt = fail ("sbvSATQuery: could not evaluate neutral term: " ++ show nt)
          let primHandler pn msg env _tv =
                 fail $ unlines
                   [ "Could not evaluate primitive " ++ show (primName pn)
                   , "On argument " ++ show (length env)
                   , Text.unpack msg
                   ]

          cfg  <- liftIO (Sim.evalGlobal m (Map.union constMap addlPrims) extcns uninterpreted neutral primHandler)
          bval <- liftIO (Sim.evalSharedTerm cfg t)

          case bval of
            VBool b -> return b
            _ -> fail $ "sbvSATQuery: non-boolean result type. " ++ show bval
      )

data Labeler
   = BoolLabel String
   | IntegerLabel String
   | WordLabel String
   | ZeroWidthWordLabel
   | VecLabel (Vector Labeler)
   | TupleLabel (Vector Labeler)
   | RecLabel (Map FieldName Labeler)
     deriving (Show)

nextId :: StateT Int IO String
nextId = ST.get >>= (\s -> modify (+1) >> return ("x" ++ show s))

nextId' :: String -> StateT Int IO String
nextId' nm = nextId <&> \s -> s ++ "_" ++ nm

unzipMap :: Map k (a, b) -> (Map k a, Map k b)
unzipMap m = (fmap fst m, fmap snd m)

newVars :: String -> FirstOrderType -> StateT Int IO (Labeler, Symbolic SValue)
newVars nm fot =
  case fot of
    FOTBit ->
      nextId' nm <&> \s -> (BoolLabel s, vBool <$> existsSBool s)
    FOTInt ->
      nextId' nm <&> \s -> (IntegerLabel s, vInteger <$> existsSInteger s)
    FOTIntMod n ->
      nextId' nm <&> \s -> (IntegerLabel s, VIntMod n <$> existsSInteger s)
    FOTVec 0 FOTBit ->
      pure (ZeroWidthWordLabel, pure (vWord (literalSWord 0 0)))
    FOTVec n FOTBit ->
      nextId' nm <&> \s -> (WordLabel s, vWord <$> existsSWord s (fromIntegral n))
    FOTVec n tp ->
      do let f i = newVars (nm ++ "." ++ show i) tp
         (labels, vals) <- V.unzip <$> V.generateM (fromIntegral n) f
         pure (VecLabel labels, VVector <$> traverse (fmap ready) vals)
    FOTArray{} ->
      fail "FOTArray unimplemented for backend"
    FOTTuple ts ->
      do let f i t = newVars (nm ++ "." ++ show i) t
         (labels, vals) <- V.unzip <$> V.imapM f (V.fromList ts)
         pure (TupleLabel labels, vTuple <$> traverse (fmap ready) (V.toList vals))
    FOTRec tm ->
      do let f k t = newVars (nm ++ "." ++ Text.unpack k) t
         (labels, vals) <- unzipMap <$> (Map.traverseWithKey f tm)
         pure (RecLabel labels, vRecord <$> traverse (fmap ready) vals)


getLabels ::
  [Labeler] ->
  Map String CV ->
  [ExtCns Term] -> Maybe [(ExtCns Term,FirstOrderValue)]

getLabels ls d args
  | length args == length xs = Just (zip args xs)
  | otherwise = error $ unwords
                [ "SBV SAT results do not match expected arguments "
                , show (map (toShortName . ecName) args), show xs]

  where
  xs = fmap getLabel ls

  getLabel (BoolLabel s)    = FOVBit (cvToBool (d Map.! s))
  getLabel (IntegerLabel s) = FOVInt (cvToInteger (d Map.! s))

  getLabel (WordLabel s)    = FOVWord (cvKind cv) (cvToInteger cv)
    where cv = d Map.! s

  getLabel ZeroWidthWordLabel = FOVWord 0 0

  getLabel (VecLabel ns)
    | V.null ns = error "getLabel of empty vector"
    | otherwise = fovVec t vs
    where vs = map getLabel (V.toList ns)
          t  = firstOrderTypeOf (head vs)

  getLabel (TupleLabel ns) = FOVTuple $ map getLabel (V.toList ns)
  getLabel (RecLabel ns) = FOVRec $ fmap getLabel ns

  cvKind cv =
    case kindOf cv of
      KBounded _ k -> fromIntegral k
      _                -> error "cvKind"

  cvToInteger cv =
    case cvVal cv of
      CInteger i -> i
      _               -> error "cvToInteger"


------------------------------------------------------------
-- Code Generation

newCodeGenVars :: (Natural -> Bool) -> FirstOrderType -> StateT Int IO (SBVCodeGen SValue)
newCodeGenVars _checkSz FOTBit = nextId <&> \s -> (vBool <$> svCgInput KBool s)
newCodeGenVars _checkSz FOTInt = nextId <&> \s -> (vInteger <$> svCgInput KUnbounded s)
newCodeGenVars _checkSz (FOTIntMod _) = nextId <&> \s -> (vInteger <$> svCgInput KUnbounded s)
newCodeGenVars checkSz (FOTVec n FOTBit)
  | n == 0    = nextId <&> \_ -> return (vWord (literalSWord 0 0))
  | checkSz n = nextId <&> \s -> vWord <$> cgInputSWord s (fromIntegral n)
  | otherwise = nextId <&> \s -> fail $ "Invalid codegen bit width for input variable \'" ++ s ++ "\': " ++ show n
newCodeGenVars checkSz (FOTVec n (FOTVec m FOTBit))
  | m == 0    = nextId <&> \_ -> return (VVector $ V.fromList $ replicate (fromIntegral n) (ready $ vWord (literalSWord 0 0)))
  | checkSz m = do
      let k = KBounded False (fromIntegral m)
      vals <- nextId <&> \s -> svCgInputArr k (fromIntegral n) s
      return (VVector . V.fromList . fmap (ready . vWord) <$> vals)
  | otherwise = nextId <&> \s -> fail $ "Invalid codegen bit width for input variable array \'" ++ s ++ "\': " ++ show n
newCodeGenVars checkSz (FOTVec n tp) = do
  vals <- V.replicateM (fromIntegral n) (newCodeGenVars checkSz tp)
  return (VVector <$> traverse (fmap ready) vals)
newCodeGenVars _ (FOTArray{}) = fail "FOTArray unimplemented for backend"
newCodeGenVars checkSz (FOTTuple ts) = do
  vals <- traverse (newCodeGenVars checkSz) ts
  return (vTuple <$> traverse (fmap ready) vals)
newCodeGenVars checkSz (FOTRec tm) = do
  vals <- traverse (newCodeGenVars checkSz) tm
  return (vRecord <$> traverse (fmap ready) vals)

cgInputSWord :: String -> Int -> SBVCodeGen SWord
cgInputSWord s n = svCgInput (KBounded False n) s

argTypes :: SharedContext -> Term -> IO ([Term], Term)
argTypes sc t = do
  t' <- scWhnf sc t
  case t' of
    (R.asPi -> Just (_, t1, t2)) -> do
       (ts,res) <- argTypes sc t2
       return (t1:ts, res)
    _ -> return ([], t')

sbvCodeGen_definition
  :: SharedContext
  -> Map Ident SPrim
  -> Set VarIndex
  -> Term
  -> (Natural -> Bool) -- ^ Allowed word sizes
  -> IO (SBVCodeGen (), [FirstOrderType], FirstOrderType)
sbvCodeGen_definition sc addlPrims unintSet t checkSz = do
  ty <- scTypeOf sc t
  (argTs,resTy) <- argTypes sc ty
  shapes <- traverse (asFirstOrderType sc) argTs
  resultShape <- asFirstOrderType sc resTy
  bval <- sbvSolveBasic sc addlPrims unintSet t
  vars <- evalStateT (traverse (newCodeGenVars checkSz) shapes) 0
  let codegen = do
        args <- traverse (fmap ready) vars
        bval' <- liftIO (applyAll bval args)
        sbvSetResult checkSz resultShape bval'
  return (codegen, shapes, resultShape)


sbvSetResult :: (Natural -> Bool)
             -> FirstOrderType
             -> SValue
             -> SBVCodeGen ()
sbvSetResult _checkSz FOTBit (VBool b) = do
   svCgReturn b
sbvSetResult checkSz (FOTVec n FOTBit) v
   | n == 0    = return ()
   | checkSz n = do
      w <- liftIO $ toWord v
      svCgReturn w
   | otherwise =
      fail $ "Invalid word size in result: " ++ show n
sbvSetResult checkSz ft v = do
   void $ sbvSetOutput checkSz ft v 0


sbvSetOutput :: (Natural -> Bool)
             -> FirstOrderType
             -> SValue
             -> Int
             -> SBVCodeGen Int
sbvSetOutput _checkSz FOTBit (VBool b) i = do
   svCgOutput ("out_"++show i) b
   return $! i+1
sbvSetOutput checkSz (FOTVec n FOTBit) v i
   | n == 0    = return i
   | checkSz n = do
       w <- liftIO $ toWord v
       svCgOutput ("out_"++show i) w
       return $! i+1
   | otherwise =
       fail $ "Invalid word size in output " ++ show i ++ ": " ++ show n

sbvSetOutput checkSz (FOTVec n t) (VVector xv) i = do
   xs <- liftIO $ traverse force $ V.toList xv
   unless (toInteger n == toInteger (length xs)) $
     fail "sbvCodeGen: vector length mismatch when setting output values"
   case asWordList xs of
     Just ws -> do svCgOutputArr ("out_"++show i) ws
                   return $! i+1
     Nothing -> foldM (\i' x -> sbvSetOutput checkSz t x i') i xs
sbvSetOutput _checkSz (FOTTuple []) VUnit i =
   return i
sbvSetOutput checkSz (FOTTuple [t]) v i = sbvSetOutput checkSz t v i
sbvSetOutput checkSz (FOTTuple (t:ts)) (VPair l r) i = do
   l' <- liftIO $ force l
   r' <- liftIO $ force r
   sbvSetOutput checkSz t l' i >>= sbvSetOutput checkSz (FOTTuple ts) r'

sbvSetOutput _checkSz (FOTRec fs) VUnit i | Map.null fs = do
   return i

sbvSetOutput _checkSz (FOTRec fs) (VRecordValue []) i | Map.null fs = return i

sbvSetOutput checkSz (FOTRec fs) (VRecordValue ((fn,x):rest)) i = do
   x' <- liftIO $ force x
   case Map.lookup fn fs of
     Just t -> do
       let fs' = Map.delete fn fs
       sbvSetOutput checkSz t x' i >>=
         sbvSetOutput checkSz (FOTRec fs') (VRecordValue rest)
     Nothing -> fail "sbvCodeGen: type mismatch when setting record output value"

sbvSetOutput _checkSz _ft _v _i = do
   fail "sbvCode gen: type mismatch when setting output values"


sbvCodeGen :: SharedContext
           -> Map Ident SPrim
           -> Set VarIndex
           -> Maybe FilePath
           -> String
           -> Term
           -> IO ()
sbvCodeGen sc addlPrims unintSet path fname t = do
  -- The SBV C code generator expects only these word sizes
  let checkSz n = n `elem` [8,16,32,64]

  (codegen,_,_) <- sbvCodeGen_definition sc addlPrims unintSet t checkSz
  compileToC path fname codegen
