------------------------------------------------------------------------
-- |
-- Module      : Verifier.SAW.Simulator.What4
-- Copyright   : Galois, Inc. 2012-2015
-- License     : BSD3
-- Maintainer  : sweirich@galois.com
-- Stability   : experimental
-- Portability : non-portable (language extensions)
--
-- A symbolic simulator for saw-core terms using What4.
-- (This module is derived from Verifier.SAW.Simulator.SBV)
------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds#-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TypeApplications #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- WithKnownNat
{-# OPTIONS_GHC -Wno-warnings-deprecations #-}


module Verifier.SAW.Simulator.What4
  ( w4Solve
  , w4SolveBasic
  , SymFnCache
  , TypedExpr(..)
  , SValue
  , Labeler(..)
  , w4Eval
  , w4EvalBasic
  ) where



import qualified Control.Arrow as A

import Data.Bits
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Vector (Vector)
import qualified Data.Vector as V

import Data.Traversable as T
#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import Control.Monad.State as ST
import Numeric.Natural (Natural)

import Data.Reflection (Given(..), give)

-- saw-core
import qualified Verifier.SAW.Recognizer as R
import qualified Verifier.SAW.Simulator as Sim
import qualified Verifier.SAW.Simulator.Prims as Prims
import Verifier.SAW.SharedTerm
import Verifier.SAW.Simulator.Value
import Verifier.SAW.TypedAST (FieldName, ModuleMap, identName)
import Verifier.SAW.FiniteValue (FirstOrderType(..))

-- what4
import           What4.Interface(SymExpr,Pred,SymInteger, IsExpr,
                                 IsExprBuilder,IsSymExprBuilder)
import qualified What4.Interface as W
import           What4.BaseTypes

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import Data.Parameterized.Context (Assignment)
import Data.Parameterized.Some
import Data.Parameterized.TraversableFC (FunctorFC(fmapFC))

-- crucible-saw
import qualified Lang.Crucible.Backend.SAWCore as CS

-- saw-core-what4
import Verifier.SAW.Simulator.What4.SWord
import Verifier.SAW.Simulator.What4.PosNat
import Verifier.SAW.Simulator.What4.FirstOrder

---------------------------------------------------------------------
-- empty datatype to index (open) type families
-- for this backend
data What4 (sym :: *)

-- type abbreviations for uniform naming
type SBool sym = Pred sym
type SInt  sym = SymInteger sym

type instance EvalM (What4 sym) = IO
type instance VBool (What4 sym) = SBool sym
type instance VWord (What4 sym) = SWord sym
type instance VInt  (What4 sym) = SInt  sym
type instance Extra (What4 sym) = What4Extra sym

type SValue sym = Value (What4 sym)

-- Constraint
type Sym sym = (Given sym, IsSymExprBuilder sym)

---------------------------------------------------------------------

data What4Extra sym =
  SStream (Integer -> IO (SValue sym)) (IORef (Map Integer (SValue sym)))

instance Show (What4Extra sym) where
  show (SStream _ _) = "<SStream>"

---------------------------------------------------------------------
--
-- Basic primitive table for What4 data
--

prims :: forall sym. (Sym sym) =>
   Prims.BasePrims (What4 sym)
prims =
  let sym :: sym = given in
  Prims.BasePrims
  { Prims.bpAsBool  = W.asConstantPred
    -- Bitvectors
  , Prims.bpUnpack  = bvUnpack sym
  , Prims.bpPack    = bvPack   sym
  , Prims.bpBvAt    = bvAt     sym
  , Prims.bpBvLit   = bvLit    sym
  , Prims.bpBvSize  = intSizeOf
  , Prims.bpBvJoin  = bvJoin   sym
  , Prims.bpBvSlice = bvSlice  sym
    -- Conditionals
  , Prims.bpMuxBool  = W.itePred sym
  , Prims.bpMuxWord  = bvIte     sym
  , Prims.bpMuxInt   = W.intIte  sym
  , Prims.bpMuxExtra = muxWhat4Extra
    -- Booleans
  , Prims.bpTrue   = W.truePred  sym
  , Prims.bpFalse  = W.falsePred sym
  , Prims.bpNot    = W.notPred   sym
  , Prims.bpAnd    = W.andPred   sym
  , Prims.bpOr     = W.orPred    sym
  , Prims.bpXor    = W.xorPred   sym
  , Prims.bpBoolEq = W.isEq      sym
    -- Bitvector logical
  , Prims.bpBvNot  = bvNot  sym
  , Prims.bpBvAnd  = bvAnd  sym
  , Prims.bpBvOr   = bvOr   sym
  , Prims.bpBvXor  = bvXor  sym
    -- Bitvector arithmetic
  , Prims.bpBvNeg  = bvNeg  sym
  , Prims.bpBvAdd  = bvAdd  sym
  , Prims.bpBvSub  = bvSub  sym
  , Prims.bpBvMul  = bvMul  sym
  , Prims.bpBvUDiv = bvUDiv sym
  , Prims.bpBvURem = bvURem sym
  , Prims.bpBvSDiv = bvSDiv sym
  , Prims.bpBvSRem = bvSRem sym
  , Prims.bpBvLg2  = bvLg2  sym
    -- Bitvector comparisons
  , Prims.bpBvEq   = bvEq  sym
  , Prims.bpBvsle  = bvsle sym
  , Prims.bpBvslt  = bvslt sym
  , Prims.bpBvule  = bvule sym
  , Prims.bpBvult  = bvult sym
  , Prims.bpBvsge  = bvsge sym
  , Prims.bpBvsgt  = bvsgt sym
  , Prims.bpBvuge  = bvuge sym
  , Prims.bpBvugt  = bvugt sym
    -- Bitvector shift/rotate
  , Prims.bpBvRolInt = bvRolInt sym
  , Prims.bpBvRorInt = bvRorInt sym
  , Prims.bpBvShlInt = bvShlInt sym
  , Prims.bpBvShrInt = bvShrInt sym
  , Prims.bpBvRol    = bvRol sym
  , Prims.bpBvRor    = bvRor sym
  , Prims.bpBvShl    = bvShl sym
  , Prims.bpBvShr    = bvShr sym
    -- Bitvector misc
  , Prims.bpBvPopcount = bvPopcount sym
  , Prims.bpBvCountLeadingZeros = bvCountLeadingZeros sym
  , Prims.bpBvCountTrailingZeros = bvCountTrailingZeros sym
  , Prims.bpBvForall = bvForall sym
    -- Integer operations
  , Prims.bpIntAbs = W.intAbs sym
  , Prims.bpIntAdd = W.intAdd sym
  , Prims.bpIntSub = W.intSub sym
  , Prims.bpIntMul = W.intMul sym
  , Prims.bpIntDiv = W.intDiv sym
  , Prims.bpIntMod = W.intMod sym
  , Prims.bpIntNeg = W.intNeg sym
  , Prims.bpIntEq  = W.intEq sym
  , Prims.bpIntLe  = W.intLe sym
  , Prims.bpIntLt  = W.intLt sym
  , Prims.bpIntMin = intMin  sym
  , Prims.bpIntMax = intMax  sym
  }


constMap :: forall sym. (Sym sym) => Map Ident (SValue sym)
constMap =
  Map.union (Prims.constMap prims) $
  Map.fromList
  [
  -- Shifts
    ("Prelude.bvShl" , bvShLOp)
  , ("Prelude.bvShr" , bvShROp)
  , ("Prelude.bvSShr", bvSShROp)
  -- Integers
  --XXX , ("Prelude.intToNat", Prims.intToNatOp)
  , ("Prelude.natToInt", natToIntOp)
  , ("Prelude.intToBv" , intToBvOp)
  , ("Prelude.bvToInt" , bvToIntOp)
  , ("Prelude.sbvToInt", sbvToIntOp)
  -- Integers mod n
  , ("Prelude.IntMod"    , constFun VIntType)
  , ("Prelude.toIntMod"  , constFun (VFun force))
  , ("Prelude.fromIntMod", fromIntModOp sym)
  , ("Prelude.intModEq"  , intModEqOp sym)
  , ("Prelude.intModAdd" , intModBinOp sym W.intAdd)
  , ("Prelude.intModSub" , intModBinOp sym W.intSub)
  , ("Prelude.intModMul" , intModBinOp sym W.intMul)
  , ("Prelude.intModNeg" , intModUnOp sym W.intNeg)
  -- Streams
  , ("Prelude.MkStream", mkStreamOp)
  , ("Prelude.streamGet", streamGetOp)
  , ("Prelude.bvStreamGet", bvStreamGetOp)
  ]
  where sym = given :: sym

-----------------------------------------------------------------------
-- Implementation of constMap primitives

toBool :: SValue sym -> IO (SBool sym)
toBool (VBool b) = return b
toBool x         = fail $ unwords ["Verifier.SAW.Simulator.What4.toBool", show x]

toWord :: forall sym. (Sym sym) =>
          SValue sym -> IO (SWord sym)
toWord (VWord w)    = return w
toWord (VVector vv) = do
  -- vec :: Vector (SBool sym))
  vec1 <- T.traverse force vv
  vec2 <- T.traverse toBool vec1
  bvPack (given :: sym) vec2
toWord x            = fail $ unwords ["Verifier.SAW.Simulator.What4.toWord", show x]

wordFun :: (Sym sym) =>
           (SWord sym -> IO (SValue sym)) -> SValue sym
wordFun f = strictFun (\x -> f =<< toWord x)

--
-- Integer bit/vector conversions
--

-- primitive natToInt :: Nat -> Integer;
natToIntOp :: forall sym. (Sym sym) => SValue sym
natToIntOp =
  Prims.natFun' "natToInt" $ \n ->
    VInt <$> W.intLit (given :: sym) (toInteger n)

-- interpret bitvector as unsigned integer
-- primitive bvToInt :: (n::Nat) -> bitvector n -> Integer;
bvToIntOp :: forall sym. (Sym sym) => SValue sym
bvToIntOp = constFun $ wordFun $ \(v :: SWord sym) -> do
  VInt <$> bvToInteger (given :: sym) v

-- interpret bitvector as signed integer
-- primitive sbvToInt :: (n::Nat) -> bitvector n -> Integer;
sbvToIntOp :: forall sym. (Sym sym) => SValue sym
sbvToIntOp = constFun $ wordFun $ \v -> do
   VInt <$> sbvToInteger (given :: sym) v

-- primitive intToBv :: (n::Nat) -> Integer -> bitvector n;
intToBvOp :: forall sym. (Sym sym) => SValue sym
intToBvOp =
  Prims.natFun' "intToBv n" $ \n -> return $
  Prims.intFun "intToBv x" $ \(x :: SymInteger sym) ->
    VWord <$> integerToBV (given :: sym) x n


--
-- Shifts
--

-- | op :: (n :: Nat) -> bitvector n -> Nat -> bitvector n
bvShiftOp :: (Sym sym) =>
             (SWord sym -> SWord sym -> IO (SWord sym)) ->
             (SWord sym -> Integer   -> IO (SWord sym)) -> SValue sym
bvShiftOp bvOp natOp =
  constFun  $                  -- additional argument? the size?
  wordFun   $ \x ->            -- word to shift
  return $
  strictFun $ \y ->            -- amount to shift as a nat
    case y of
      VNat i   -> VWord <$> natOp x j
        where j = i `min` toInteger (intSizeOf x)
      VToNat v -> VWord <$> (bvOp x =<< toWord v)
      _        -> error $ unwords ["Verifier.SAW.Simulator.What4.bvShiftOp", show y]

-- bvShl :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvShLOp :: forall sym. (Sym sym) => SValue sym
bvShLOp = bvShiftOp (bvShl    given (W.falsePred @sym given))
                    (bvShlInt given (W.falsePred @sym given))

-- bvShR :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvShROp :: forall sym. (Sym sym) => SValue sym
bvShROp = bvShiftOp (bvShr    given (W.falsePred @sym given))
                    (bvShrInt given (W.falsePred @sym given))


-- bvShR :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvSShROp :: forall sym. (Sym sym) => SValue sym
bvSShROp = bvShiftOp (bvSShr    given (W.falsePred @sym given))
                     (bvSShrInt given (W.falsePred @sym given))


--
-- missing integer operations
--

intMin :: (IsExprBuilder sym) => sym -> SInt sym -> SInt sym -> IO (SInt sym)
intMin sym i1 i2 = do
  p <- W.intLt sym i1 i2
  W.intIte sym p i1 i2

intMax :: (IsExprBuilder sym) => sym -> SInt sym -> SInt sym -> IO (SInt sym)
intMax sym i1 i2 = do
  p <- W.intLt sym i1 i2
  W.intIte sym p i2 i1

------------------------------------------------------------
-- Integers mod n

fromIntModOp :: IsExprBuilder sym => sym -> SValue sym
fromIntModOp sym =
  Prims.natFun $ \n -> return $
  Prims.intFun "fromIntModOp" $ \x ->
  VInt <$> (W.intMod sym x =<< W.intLit sym (toInteger n))

intModEqOp :: IsExprBuilder sym => sym -> SValue sym
intModEqOp sym =
  Prims.natFun $ \n -> return $
  Prims.intFun "intModEqOp" $ \x -> return $
  Prims.intFun "intModEqOp" $ \y ->
  do modulus <- W.intLit sym (toInteger n)
     d <- W.intSub sym x y
     r <- W.intMod sym d modulus
     z <- W.intLit sym 0
     VBool <$> W.intEq sym r z

intModBinOp ::
  IsExprBuilder sym => sym ->
  (sym -> SInt sym -> SInt sym -> IO (SInt sym)) -> SValue sym
intModBinOp sym f =
  Prims.natFun $ \n -> return $
  Prims.intFun "intModBinOp x" $ \x -> return $
  Prims.intFun "intModBinOp y" $ \y ->
  VInt <$> (normalizeIntMod sym n =<< f sym x y)

intModUnOp ::
  IsExprBuilder sym => sym ->
  (sym -> SInt sym -> IO (SInt sym)) -> SValue sym
intModUnOp sym f =
  Prims.natFun $ \n -> return $
  Prims.intFun "intModUnOp" $ \x ->
  VInt <$> (normalizeIntMod sym n =<< f sym x)

normalizeIntMod :: IsExprBuilder sym => sym -> Natural -> SInt sym -> IO (SInt sym)
normalizeIntMod sym n x =
  case W.asInteger x of
    Nothing -> return x
    Just i -> W.intLit sym (i `mod` toInteger n)

------------------------------------------------------------
-- Stream operations

-- MkStream :: (a :: sort 0) -> (Nat -> a) -> Stream a;
mkStreamOp :: SValue sym
mkStreamOp =
  constFun $
  strictFun $ \f -> do
    r <- newIORef Map.empty
    return $ VExtra (SStream (\n -> apply f (ready (VNat n))) r)

-- streamGet :: (a :: sort 0) -> Stream a -> Nat -> a;
streamGetOp :: SValue sym
streamGetOp =
  constFun $
  strictFun $ \xs -> return $
  Prims.natFun'' "streamGetOp" $ \n -> lookupSStream xs (toInteger n)

-- bvStreamGet :: (a :: sort 0) -> (w :: Nat) -> Stream a -> bitvector w -> a;
bvStreamGetOp :: forall sym. (IsExpr (SymExpr sym), Sym sym) => SValue sym
bvStreamGetOp =
  constFun $
  constFun $
  strictFun $ \xs -> return $
  wordFun $ \ilv ->
  selectV (lazyMux @sym muxBVal) ((2 ^ intSizeOf ilv) - 1) (lookupSStream xs) ilv

lookupSStream :: SValue sym -> Integer -> IO (SValue sym)
lookupSStream (VExtra (SStream f r)) n = do
   m <- readIORef r
   case Map.lookup n m of
     Just v  -> return v
     Nothing -> do v <- f n
                   writeIORef r (Map.insert n v m)
                   return v
lookupSStream _ _ = fail "expected Stream"


muxBVal :: forall sym. (Sym sym) =>
  SBool sym -> SValue sym -> SValue sym -> IO (SValue sym)
muxBVal = Prims.muxValue prims

muxWhat4Extra ::
  forall sym. (Sym sym) =>
  SBool sym -> What4Extra sym -> What4Extra sym -> IO (What4Extra sym)
muxWhat4Extra c x y =
  do let f i = do xi <- lookupSStream (VExtra x) i
                  yi <- lookupSStream (VExtra y) i
                  muxBVal c xi yi
     r <- newIORef Map.empty
     return (SStream f r)


-- | Lifts a strict mux operation to a lazy mux
lazyMux :: (IsExpr (SymExpr sym)) =>
  (SBool sym  -> a -> a -> IO a) -> (SBool sym -> IO a -> IO a -> IO a)
lazyMux muxFn c tm fm =
  case W.asConstantPred c of
    Just True  -> tm
    Just False -> fm
    Nothing    -> do
      t <- tm
      f <- fm
      muxFn c t f

-- selectV merger maxValue valueFn index returns valueFn v when index has value v
-- if index is greater than maxValue, it returns valueFn maxValue. Use the ite op from merger.
selectV :: forall sym a b. (Sym sym, Ord a, Num a, Bits a) =>
  (SBool sym -> IO b -> IO b -> IO b) -> a -> (a -> IO b) -> SWord sym -> IO b
selectV merger maxValue valueFn vx =
  case bvAsUnsignedInteger vx of
    Just i  -> valueFn (fromIntegral i)
    Nothing -> impl (intSizeOf vx) 0
  where
    impl :: Int -> a -> IO b
    impl _ x | x > maxValue || x < 0 = valueFn maxValue
    impl 0 y = valueFn y
    impl i y = do
      p <- bvAt (given :: sym) vx j
      merger p (impl j (y `setBit` j)) (impl j y) where j = i - 1

----------------------------------------------------------------------
-- | A basic symbolic simulator/evaluator: interprets a saw-core Term as
-- a symbolic value

w4SolveBasic ::
  forall sym. (Given sym, IsSymExprBuilder sym) =>
  ModuleMap ->
  Map Ident (SValue sym) {- ^ additional primitives -} ->
  IORef (SymFnCache sym) {- ^ cache for uninterpreted function symbols -} ->
  [String] {- ^ 'unints' Constants in this list are kept uninterpreted -} ->
  Term {- ^ term to simulate -} ->
  IO (SValue sym)
w4SolveBasic m addlPrims ref unints t =
  do let unintSet = Set.fromList unints
     let sym = given :: sym
     let extcns (EC ix nm ty) = parseUninterpreted sym ref (nm ++ "_" ++ show ix) Ctx.empty ty
     let uninterpreted ec
           | Set.member (ecName ec) unintSet = Just (extcns ec)
           | otherwise                       = Nothing
     cfg <- Sim.evalGlobal m (constMap `Map.union` addlPrims) extcns uninterpreted
     Sim.evalSharedTerm cfg t


----------------------------------------------------------------------
-- Uninterpreted function cache

data SymFnWrapper sym :: Ctx.Ctx BaseType -> * where
  SymFnWrapper :: !(W.SymFn sym args ret) -> SymFnWrapper sym (args Ctx.::> ret)

type SymFnCache sym = Map W.SolverSymbol (MapF (Assignment BaseTypeRepr) (SymFnWrapper sym))

lookupSymFn ::
  W.SolverSymbol -> Assignment BaseTypeRepr args -> BaseTypeRepr ty ->
  SymFnCache sym -> Maybe (W.SymFn sym args ty)
lookupSymFn s args ty cache =
  do m <- Map.lookup s cache
     SymFnWrapper fn <- MapF.lookup (Ctx.extend args ty) m
     return fn

insertSymFn ::
  W.SolverSymbol -> Assignment BaseTypeRepr args -> BaseTypeRepr ty ->
  W.SymFn sym args ty -> SymFnCache sym -> SymFnCache sym
insertSymFn s args ty fn = Map.alter upd s
  where
    upd Nothing = Just (MapF.singleton (Ctx.extend args ty) (SymFnWrapper fn))
    upd (Just m) = Just (MapF.insert (Ctx.extend args ty) (SymFnWrapper fn) m)

mkSymFn ::
  forall sym args ret. (IsSymExprBuilder sym) =>
  sym -> IORef (SymFnCache sym) ->
  String -> Assignment BaseTypeRepr args -> BaseTypeRepr ret ->
  IO (W.SymFn sym args ret)
mkSymFn sym ref nm args ret =
  case W.userSymbol nm of
    Left err -> fail $ show err ++ ": Cannot create uninterpreted constant " ++ nm
    Right s  ->
      do cache <- readIORef ref
         case lookupSymFn s args ret cache of
           Just fn -> return fn
           Nothing ->
             do fn <- W.freshTotalUninterpFn sym s args ret
                writeIORef ref (insertSymFn s args ret fn cache)
                return fn

----------------------------------------------------------------------
-- Given a constant nm of (saw-core) type ty, construct an uninterpreted
-- constant with that type.
-- Importantly: The types of these uninterpreted values are *not*
-- limited to What4 BaseTypes or FirstOrderTypes.

parseUninterpreted ::
  forall sym args.
  (IsSymExprBuilder sym) =>
  sym -> IORef (SymFnCache sym) ->
  String -> Assignment (SymExpr sym) args -> SValue sym -> IO (SValue sym)
parseUninterpreted sym ref nm args ty =
  case ty of
    VPiType _ f
      -> return $
         strictFun $ \x -> do
           (nm', Some args') <- flattenSValue (nm, Some args) x
           t2 <- f (ready x)
           parseUninterpreted sym ref nm' args' t2

    VBoolType
      -> VBool <$> mkUninterpreted sym ref nm args BaseBoolRepr

    VIntType
      -> VInt  <$> mkUninterpreted sym ref nm args BaseIntegerRepr

    -- 0 width bitvector is a constant
    VVecType (VNat 0) VBoolType
      -> return $ VWord ZBV

    VVecType (VNat n) VBoolType
      | Just (Some (PosNat w)) <- somePosNat n
      -> (VWord . DBV) <$> mkUninterpreted sym ref nm args (BaseBVRepr w)

    VVecType (VNat n) ety
      ->  do xs <- sequence $
                  [ parseUninterpreted sym ref (nm ++ "_a" ++ show i) args ety
                  | i <- [0 .. n-1] ]
             return (VVector (V.fromList (map ready xs)))

    VUnitType
      -> return VUnit

    VPairType ty1 ty2
      -> do x1 <- parseUninterpreted sym ref (nm ++ "_L") args ty1
            x2 <- parseUninterpreted sym ref (nm ++ "_R") args ty2
            return (VPair (ready x1) (ready x2))

    (VRecordType elem_tps)
      -> (VRecordValue <$>
          mapM (\(f,tp) ->
                 (f,) <$> ready <$>
                 parseUninterpreted sym ref (nm ++ "_" ++ f) args tp) elem_tps)


    _ -> fail $ "could not create uninterpreted symbol of type " ++ show ty


mkUninterpreted ::
  forall sym args t. (IsSymExprBuilder sym) =>
  sym -> IORef (SymFnCache sym) ->
  String -> Assignment (SymExpr sym) args -> BaseTypeRepr t ->
  IO (SymExpr sym t)
mkUninterpreted sym ref nm args ret =
  do fn <- mkSymFn sym ref nm (fmapFC W.exprType args) ret
     W.applySymFn sym fn args


-- | Flatten an 'SValue' to a sequence of components, each of which is
-- a symbolic value of a base type (e.g. word or boolean), and append
-- them onto the end of the given 'Assignment'. If the 'SValue'
-- contains any values built from data constructors, then encode them
-- as suffixes on the given 'String'.
flattenSValue ::
  forall sym.
  (String, Some (Assignment (SymExpr sym))) ->
  SValue sym ->
  IO (String, Some (Assignment (SymExpr sym)))
flattenSValue args0@(nm, Some xs) v =
  case v of
    VUnit                     -> return args0
    VPair x y                 -> do args1 <- flattenSValue args0 =<< force x
                                    args2 <- flattenSValue args1 =<< force y
                                    return args2
    VRecordValue elems        -> foldM flattenSValue args0 =<< traverse (force . snd) elems
    VVector xv                -> foldM flattenSValue args0 =<< traverse force xv
    VBool sb                  -> return (nm, Some (Ctx.extend xs sb))
    VInt si                   -> return (nm, Some (Ctx.extend xs si))
    VWord (DBV sw)            -> return (nm, Some (Ctx.extend xs sw))
    VWord ZBV                 -> return args0
    VCtorApp i xv             -> foldM flattenSValue args' =<< traverse force xv
                                   where args' = (nm ++ "_" ++ identName i, Some xs)
    VNat n                    -> return (nm ++ "_" ++ show n, Some xs)
    _ -> fail $ "Could not create argument for " ++ show v

------------------------------------------------------------

w4Solve ::
  forall sym. (IsSymExprBuilder sym) =>
  sym -> SharedContext -> Map Ident (SValue sym) -> [String] -> Term ->
  IO ([String], ([Maybe (Labeler sym)], SBool sym))
w4Solve sym sc ps unints t = give sym $ do
  modmap <- scGetModuleMap sc
  ref <- newIORef Map.empty
  let eval = w4SolveBasic modmap ps ref unints
  ty <- eval =<< scTypeOf sc t

  -- get the names of the arguments to the function
  let argNames = map fst (fst (R.asLambdaList t))
  let moreNames = [ "var" ++ show (i :: Integer) | i <- [0 ..] ]

  -- and their types
  argTs <- asPredType ty

  -- construct symbolic expressions for the variables
  vars' <-
    flip evalStateT 0 $
    sequence (zipWith (newVarsForType ref) argTs (argNames ++ moreNames))

  -- symbolically evaluate
  bval <- eval t

  -- apply and existentially quantify
  let (bvs, vars) = unzip vars'
  let vars'' = fmap ready vars
  bval' <- applyAll bval vars''

  prd <- case bval' of
           VBool b -> return b
           _ -> fail $ "solve: non-boolean result type. " ++ show bval'
  return (argNames, (bvs, prd))


--
-- Pull out argument types until bottoming out at a bool type
--
asPredType :: IsSymExprBuilder sv => SValue sv -> IO [SValue sv]
asPredType v =
  case v of
    VBoolType -> return []
    VPiType v1 f ->
      do v2 <- f (error "asPredType: unsupported dependent SAW-Core type")
         vs <- asPredType v2
         return (v1 : vs)
    _ -> fail $ "non-boolean result type: " ++ show v

--
-- Convert a saw-core type expression to a FirstOrder type expression
--
vAsFirstOrderType :: forall sv. IsSymExprBuilder sv => SValue sv -> Maybe FirstOrderType
vAsFirstOrderType v =
  case v of
    VBoolType
      -> return FOTBit
    VIntType
      -> return FOTInt
    VVecType (VNat n) v2
      -> FOTVec (fromInteger n) <$> vAsFirstOrderType v2
    VUnitType
      -> return (FOTTuple [])
    VPairType v1 v2
      -> do t1 <- vAsFirstOrderType v1
            t2 <- vAsFirstOrderType v2
            case t2 of
              FOTTuple ts -> return (FOTTuple (t1 : ts))
              _ -> Nothing
    VRecordType tps
      -> (FOTRec <$> Map.fromList <$>
          mapM (\(f,tp) -> (f,) <$> vAsFirstOrderType tp) tps)
    _ -> Nothing

------------------------------------------------------------------------------

-- | Generate a new symbolic value (a variable) from a given first-order-type


data TypedExpr sym where
  TypedExpr :: BaseTypeRepr ty -> SymExpr sym ty -> TypedExpr sym


-- | Generate a new variable from a given BaseType

freshVar :: forall sym ty. (IsSymExprBuilder sym, Given sym) =>
  BaseTypeRepr ty -> String -> IO (TypedExpr sym)
freshVar ty str =
  case W.userSymbol str of
    Right solverSymbol -> do
      c <- W.freshConstant (given :: sym) solverSymbol ty
      return (TypedExpr ty c)
    Left _ ->
      fail $ "Cannot create solver symbol " ++ str

nextId :: StateT Int IO String
nextId = ST.get >>= (\s-> modify (+1) >> return ("x" ++ show s))


newVarsForType :: forall sym. (Given sym, IsSymExprBuilder sym) =>
  IORef (SymFnCache sym) ->
  SValue sym -> String -> StateT Int IO (Maybe (Labeler sym), SValue sym)
newVarsForType ref v nm =
  case vAsFirstOrderType v of
    Just fot -> do
      do (te,sv) <- newVarFOT fot
         return (Just te, sv)

    Nothing ->
      do sv <- lift $ parseUninterpreted sym ref nm Ctx.empty v
         return (Nothing, sv)
  where sym = given :: sym

myfun ::(Map String (Labeler sym, SValue sym)) -> (Map String (Labeler sym), Map String (SValue sym))
myfun = fmap fst A.&&& fmap snd

data Labeler sym
   = BaseLabel  (TypedExpr sym)
   | VecLabel   (Vector (Labeler sym))
   | TupleLabel (Vector (Labeler sym))
   | RecLabel   (Map FieldName (Labeler sym))


newVarFOT :: forall sym. (IsSymExprBuilder sym, Given sym) =>
   FirstOrderType -> StateT Int IO (Labeler sym, SValue sym)

newVarFOT (FOTTuple ts) = do
  (labels,vals) <- V.unzip <$> traverse newVarFOT (V.fromList ts)
  args <- traverse (return . ready) (V.toList vals)
  return (TupleLabel labels, vTuple args)

newVarFOT (FOTVec n tp)
  | tp /= FOTBit
  = do (labels,vals) <- V.unzip <$> V.replicateM (fromIntegral n) (newVarFOT tp)
       args <- traverse @Vector @(StateT Int IO) (return . ready) vals
       return (VecLabel labels, VVector args)

newVarFOT (FOTRec tm)
  = do (labels, vals) <- myfun <$> traverse newVarFOT tm
       args <- traverse (return . ready) (vals :: (Map String (SValue sym)))
       return (RecLabel labels, vRecord args)

newVarFOT fot
  | Some r <- fotToBaseType fot
  = do nm <- nextId
       te <- lift $ freshVar r nm
       sv <- lift $ typedToSValue te
       return (BaseLabel te, sv)



typedToSValue :: (IsExpr (SymExpr sym)) => TypedExpr sym -> IO (SValue sym)
typedToSValue (TypedExpr ty expr) =
  case ty of
    BaseBoolRepr         -> return $ VBool expr
    BaseIntegerRepr      -> return $ VInt  expr
    (BaseBVRepr w)       -> return $ withKnownNat w $ VWord (DBV expr)
    _                    -> fail "Cannot handle"

----------------------------------------------------------------------
-- Evaluation through crucible-saw backend


-- | Simplify a saw-core term by evaluating it through the saw backend
-- of what4.
w4Eval ::
  forall n solver fs.
  CS.SAWCoreBackend n solver fs -> SharedContext ->
  Map Ident (SValue (CS.SAWCoreBackend n solver fs)) -> [String] -> Term ->
  IO ([String], ([Maybe (Labeler (CS.SAWCoreBackend n solver fs))], SBool (CS.SAWCoreBackend n solver fs)))
w4Eval sym sc ps unints t =
  do modmap <- scGetModuleMap sc
     ref <- newIORef Map.empty
     let eval = w4EvalBasic sym sc modmap ps ref unints
     ty <- eval =<< scTypeOf sc t

     -- get the names of the arguments to the function
     let argNames = map fst (fst (R.asLambdaList t))
     let moreNames = [ "var" ++ show (i :: Integer) | i <- [0 ..] ]

     -- and their types
     argTs <- asPredType ty

     -- construct symbolic expressions for the variables
     vars' <-
       give sym $
       flip evalStateT 0 $
       sequence (zipWith (newVarsForType ref) argTs (argNames ++ moreNames))

     -- symbolically evaluate
     bval <- eval t

     -- apply and existentially quantify
     let (bvs, vars) = unzip vars'
     let vars'' = fmap ready vars
     bval' <- applyAll bval vars''

     prd <- case bval' of
              VBool b -> return b
              _ -> fail $ "solve: non-boolean result type. " ++ show bval'
     return (argNames, (bvs, prd))

-- | Simplify a saw-core term by evaluating it through the saw backend
-- of what4.
w4EvalBasic ::
  forall n solver fs.
  CS.SAWCoreBackend n solver fs ->
  SharedContext ->
  ModuleMap ->
  Map Ident (SValue (CS.SAWCoreBackend n solver fs)) {- ^ additional primitives -} ->
  IORef (SymFnCache (CS.SAWCoreBackend n solver fs)) {- ^ cache for uninterpreted function symbols -} ->
  [String] {- ^ 'unints' Constants in this list are kept uninterpreted -} ->
  Term {- ^ term to simulate -} ->
  IO (SValue (CS.SAWCoreBackend n solver fs))
w4EvalBasic sym sc m addlPrims ref unints t =
  do let unintSet = Set.fromList unints
     let extcns tf (EC ix nm ty) =
           do trm <- ArgTermConst <$> scTermF sc tf
              parseUninterpretedSAW sym sc ref trm (nm ++ "_" ++ show ix) Ctx.empty ty
     let uninterpreted tf ec
           | Set.member (ecName ec) unintSet = Just (extcns tf ec)
           | otherwise                       = Nothing
     cfg <- Sim.evalGlobal' m (give sym constMap `Map.union` addlPrims) extcns uninterpreted
     Sim.evalSharedTerm cfg t

-- | Given a constant nm of (saw-core) type ty, construct an
-- uninterpreted constant with that type. The 'Term' argument should
-- be an open term, which should have the designated return type when
-- the local variables have the corresponding types from the
-- 'Assignment'.
parseUninterpretedSAW ::
  forall n solver fs args.
  CS.SAWCoreBackend n solver fs -> SharedContext ->
  IORef (SymFnCache (CS.SAWCoreBackend n solver fs)) ->
  ArgTerm {- ^ representation of function applied to arguments -} ->
  String {- ^ name of uninterpreted function -} ->
  Assignment (SymExpr (CS.SAWCoreBackend n solver fs)) args {- ^ arguments to uninterpreted function -} ->
  SValue (CS.SAWCoreBackend n solver fs) {- ^ return type -} ->
  IO (SValue (CS.SAWCoreBackend n solver fs))
parseUninterpretedSAW sym sc ref trm nm args ty =
  case ty of
    VPiType t1 f
      -> return $
         strictFun $ \x -> do
           (nm', Some args') <- flattenSValue (nm, Some args) x
           arg <- mkArgTerm sc t1 x
           let trm' = ArgTermApply trm arg
           t2 <- f (ready x)
           parseUninterpretedSAW sym sc ref trm' nm' args' t2

    VBoolType
      -> VBool <$> mkUninterpretedSAW sym ref trm nm args BaseBoolRepr

    VIntType
      -> VInt  <$> mkUninterpretedSAW sym ref trm nm args BaseIntegerRepr

    -- 0 width bitvector is a constant
    VVecType (VNat 0) VBoolType
      -> return $ VWord ZBV

    VVecType (VNat n) VBoolType
      | Just (Some (PosNat w)) <- somePosNat n
      -> (VWord . DBV) <$> mkUninterpretedSAW sym ref trm nm args (BaseBVRepr w)

    VVecType (VNat n) ety
      ->  do ety' <- termOfSValue sc ety
             let mkElem i =
                   do let trm' = ArgTermAt n ety' trm i
                      let nm' = nm ++ "_a" ++ show i
                      parseUninterpretedSAW sym sc ref trm' nm' args ety
             xs <- traverse mkElem [0 .. n-1]
             return (VVector (V.fromList (map ready xs)))

    VUnitType
      -> return VUnit

    VPairType ty1 ty2
      -> do let trm1 = ArgTermPairLeft trm
            let trm2 = ArgTermPairRight trm
            x1 <- parseUninterpretedSAW sym sc ref trm1 (nm ++ "_L") args ty1
            x2 <- parseUninterpretedSAW sym sc ref trm2 (nm ++ "_R") args ty2
            return (VPair (ready x1) (ready x2))
{-
    VRecordType elem_tps
      -> (VRecordValue <$>
          mapM (\(f,tp) ->
                 (f,) <$> ready <$>
                 parseUninterpretedSAW sym ref (nm ++ "_" ++ f) args tp) elem_tps)
-}

    _ -> fail $ "could not create uninterpreted symbol of type " ++ show ty

mkUninterpretedSAW ::
  forall n solver fs args t.
  CS.SAWCoreBackend n solver fs -> IORef (SymFnCache (CS.SAWCoreBackend n solver fs)) ->
  ArgTerm -> String -> Assignment (SymExpr (CS.SAWCoreBackend n solver fs)) args -> BaseTypeRepr t ->
  IO (SymExpr (CS.SAWCoreBackend n solver fs) t)
mkUninterpretedSAW sym ref trm nm args ret =
  do fn <- mkSymFn sym ref nm (fmapFC W.exprType args) ret
     CS.sawRegisterSymFunInterp sym fn (reconstructArgTerm trm)
     W.applySymFn sym fn args

-- | An 'ArgTerm' is a description of how to reassemble a saw-core
-- term from a list of the atomic components it is composed of.
data ArgTerm
  = ArgTermVar
  | ArgTermBVZero -- ^ scBvNat 0 0
  | ArgTermVector Term [ArgTerm] -- ^ element type, elements
  | ArgTermUnit
  | ArgTermPair ArgTerm ArgTerm
  | ArgTermRecord [(String, ArgTerm)]
  | ArgTermConst Term
  | ArgTermApply ArgTerm ArgTerm
  | ArgTermAt Integer Term ArgTerm Integer
    -- ^ length, element type, list, index
  | ArgTermPairLeft ArgTerm
  | ArgTermPairRight ArgTerm

-- | Reassemble a saw-core term from an 'ArgTerm' and a list of parts.
-- The length of the list should be equal to the number of
-- 'ArgTermVar' constructors in the 'ArgTerm'.
reconstructArgTerm :: ArgTerm -> SharedContext -> [Term] -> IO Term
reconstructArgTerm atrm sc ts =
  do (t, unused) <- parse atrm ts
     unless (null unused) $ fail "reconstructArgTerm: too many function arguments"
     return t
  where
    parse :: ArgTerm -> [Term] -> IO (Term, [Term])
    parse at ts0 =
      case at of
        ArgTermVar ->
          case ts0 of
            x : ts1 -> return (x, ts1)
            [] -> fail "reconstructArgTerm: too few function arguments"
        ArgTermBVZero ->
          do z <- scNat sc 0
             x <- scBvNat sc z z
             return (x, ts0)
        ArgTermVector ty ats ->
          do (xs, ts1) <- parseList ats ts0
             x <- scVector sc ty xs
             return (x, ts1)
        ArgTermUnit ->
          do x <- scUnitValue sc
             return (x, ts0)
        ArgTermPair at1 at2 ->
          do (x1, ts1) <- parse at1 ts0
             (x2, ts2) <- parse at2 ts1
             x <- scPairValue sc x1 x2
             return (x, ts2)
        ArgTermRecord flds ->
          do let (tags, ats) = unzip flds
             (xs, ts1) <- parseList ats ts0
             x <- scRecord sc (Map.fromList (zip tags xs))
             return (x, ts1)
        ArgTermConst x ->
          do return (x, ts0)
        ArgTermApply at1 at2 ->
          do (x1, ts1) <- parse at1 ts0
             (x2, ts2) <- parse at2 ts1
             x <- scApply sc x1 x2
             return (x, ts2)
        ArgTermAt n ty at1 i ->
          do n' <- scNat sc (fromInteger n)
             (x1, ts1) <- parse at1 ts0
             i' <- scNat sc (fromInteger i)
             x <- scAt sc n' ty x1 i'
             return (x, ts1)
        ArgTermPairLeft at1 ->
          do (x1, ts1) <- parse at1 ts0
             x <- scPairLeft sc x1
             return (x, ts1)
        ArgTermPairRight at1 ->
          do (x1, ts1) <- parse at1 ts0
             x <- scPairRight sc x1
             return (x, ts1)

    parseList :: [ArgTerm] -> [Term] -> IO ([Term], [Term])
    parseList [] ts0 = return ([], ts0)
    parseList (at : ats) ts0 =
      do (x, ts1) <- parse at ts0
         (xs, ts2) <- parseList ats ts1
         return (x : xs, ts2)

-- | Given a type and value encoded as 'SValue's, construct an
-- 'ArgTerm' that builds a term of that type from local variables with
-- base types. The number of 'ArgTermVar' constructors should match
-- the number of arguments returned by 'flattenSValue'.
mkArgTerm :: SharedContext -> SValue sym -> SValue sym -> IO ArgTerm
mkArgTerm sc ty val =
  case (ty, val) of
    (VBoolType, VBool _) -> return ArgTermVar
    (VIntType, VInt _)   -> return ArgTermVar
    (_, VWord ZBV)       -> return ArgTermBVZero     -- 0-width bitvector is a constant
    (_, VWord (DBV _))   -> return ArgTermVar
    (VUnitType, VUnit)   -> return ArgTermUnit

    (VVecType _ ety, VVector vv) ->
      do vs <- traverse force (V.toList vv)
         xs <- traverse (mkArgTerm sc ety) vs
         ety' <- termOfSValue sc ety
         return (ArgTermVector ety' xs)

    (VPairType ty1 ty2, VPair v1 v2) ->
      do x1 <- mkArgTerm sc ty1 =<< force v1
         x2 <- mkArgTerm sc ty2 =<< force v2
         return (ArgTermPair x1 x2)

    (VRecordType tys, VRecordValue flds) | map fst tys == map fst flds ->
      do let tags = map fst tys
         vs <- traverse (force . snd) flds
         xs <- sequence [ mkArgTerm sc t v | (t, v) <- zip (map snd tys) vs ]
         return (ArgTermRecord (zip tags xs))

    (_, VCtorApp i vv) ->
      do xs <- traverse (termOfSValue sc <=< force) (V.toList vv)
         x <- scCtorApp sc i xs
         return (ArgTermConst x)

    _ -> fail $ "could not create uninterpreted function argument of type " ++ show ty

termOfSValue :: SharedContext -> SValue sym -> IO Term
termOfSValue sc val =
  case val of
    VUnit -> scUnitValue sc
    VBoolType -> scBoolType sc
    VIntType -> scIntegerType sc
    VUnitType -> scUnitType sc
    VVecType (VNat n) a ->
      do n' <- scNat sc (fromInteger n)
         a' <- termOfSValue sc a
         scVecType sc n' a'
    VPairType a b
      -> do a' <- termOfSValue sc a
            b' <- termOfSValue sc b
            scPairType sc a' b'
    VRecordType flds
      -> do flds' <- traverse (traverse (termOfSValue sc)) flds
            scRecordType sc flds'
    VNat n
      -> scNat sc (fromInteger n)
    _ -> fail $ "termOfSValue: " ++ show val
