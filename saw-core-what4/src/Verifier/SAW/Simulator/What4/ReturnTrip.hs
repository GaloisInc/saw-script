-----------------------------------------------------------------------
-- |
-- Module           : Verifier.SAW.Simulator.What4.ReturnTrip
-- Description      : Translation from What4 back to SawCore
-- Copyright        : (c) Galois, Inc 2014-2021
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}

module Verifier.SAW.Simulator.What4.ReturnTrip
  ( newSAWCoreState
  , SAWCoreState(..)
  , SAWExpr(..)
  , baseSCType
  , bindSAWTerm
  , toSC
  , sawCreateVar
  , sawRegisterSymFunInterp
  , getInputs
  ) where

import           Control.Lens
import           Control.Monad
import qualified Data.BitVector.Sized as BV
import           Data.IORef
import           Data.List (elemIndex)
import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC
import           Data.Ratio
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Word(Word64)
import           Data.Text (Text)
import qualified Data.Text as Text

import           What4.BaseTypes
import           What4.Interface
import qualified What4.Expr.ArrayUpdateMap as AUM
import qualified What4.Expr.Builder as B
import qualified What4.Expr.BoolMap as BM
import qualified What4.Expr.WeightedSum as WSum
import qualified What4.SemiRing as B
import           What4.Symbol

import qualified Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.TypedAST as SC
import           Verifier.SAW.Utils (panic)

data SAWCoreState n
  = SAWCoreState
    { saw_ctx       :: SC.SharedContext                         -- ^ the main SAWCore datastructure for building shared terms
    , saw_inputs    :: IORef (Seq (SC.ExtCns SC.Term ))
      -- ^ a record of all the symbolic input variables created so far,
      --   in the order they were created

    , saw_symMap :: IORef (Map Word64 (SC.SharedContext -> [SC.Term] -> IO SC.Term))
      -- ^ What to do with uninterpreted functions.
      -- The key is the "indexValue" of the "symFunId" for the function

    , saw_elt_cache :: B.IdxCache n SAWExpr
      -- ^ cache mapping a What4 variable nonce to its corresponding SAWCore term.

    , saw_elt_cache_r :: IORef (IntMap (Some (B.Expr n)))
      -- ^ reverse cache mapping a SAWCore TermIndex to its corresponding What4 variable.
      -- 'saw_elt_cache' and 'saw_elt_cache_r' implement a bidirectional map between
      -- SAWCore terms and What4 variables.

    }

newSAWCoreState ::
  SC.SharedContext ->
  IO (SAWCoreState n)
newSAWCoreState sc =
  do inpr <- newIORef Seq.empty
     ch   <- B.newIdxCache
     ch_r <- newIORef IntMap.empty
     mr   <- newIORef Map.empty
     return SAWCoreState
            { saw_ctx = sc
            , saw_inputs = inpr
            , saw_symMap = mr
            , saw_elt_cache = ch
            , saw_elt_cache_r = ch_r
            }

data SAWExpr (bt :: BaseType) where
  SAWExpr :: !SC.Term -> SAWExpr bt

  -- This is a term that represents an integer, but has an
  -- implicit integer-to-real conversion.
  IntToRealSAWExpr :: !(SAWExpr BaseIntegerType) -> SAWExpr BaseRealType

getInputs :: SAWCoreState n -> IO (Seq (SC.ExtCns SC.Term))
getInputs st = readIORef (saw_inputs st)

baseSCType :: 
  sym ->
  SC.SharedContext ->
  BaseTypeRepr tp ->
  IO SC.Term
baseSCType sym sc bt =
  case bt of
    BaseBoolRepr -> SC.scBoolType sc
    BaseBVRepr w -> SC.scBitvector sc $ fromIntegral (natValue w)
    BaseIntegerRepr -> SC.scIntegerType sc
    BaseArrayRepr indexTypes range
      | Ctx.Empty Ctx.:> idx_type <- indexTypes ->
        do sc_idx_type <- baseSCType sym sc idx_type
           sc_elm_type <- baseSCType sym sc range
           SC.scArrayType sc sc_idx_type sc_elm_type
      | otherwise ->
        unsupported sym "SAW backend does not support multidimensional Arrays: baseSCType"
    BaseFloatRepr _ ->
      unsupported sym "SAW backend does not support IEEE-754 floating point values: baseSCType"
    BaseStringRepr _ ->
      unsupported sym "SAW backend does not support string values: baseSCType"
    BaseComplexRepr  ->
      unsupported sym "SAW backend does not support complex values: baseSCType"
    BaseRealRepr     ->
      unsupported sym "SAW backend does not support real values: baseSCType"
    BaseStructRepr ts ->
      SC.scTupleType sc =<< baseSCTypes ts
  where
    baseSCTypes :: Ctx.Assignment BaseTypeRepr args -> IO [SC.Term]
    baseSCTypes Ctx.Empty = return []
    baseSCTypes (xs Ctx.:> x) =
      do ts <- baseSCTypes xs
         t <- baseSCType sym sc x
         return (ts ++ [t])

-- | Create a new symbolic variable.
sawCreateVar :: SAWCoreState n
             -> Text -- ^ the name of the variable
             -> SC.Term
             -> IO SC.Term
sawCreateVar st nm tp = do
  let sc = saw_ctx st
  ec <- SC.scFreshEC sc nm tp
  t <- SC.scFlatTermF sc (SC.ExtCns ec)
  modifyIORef (saw_inputs st) (\xs -> xs Seq.|> ec)
  return t

bindSAWTerm ::
  B.ExprBuilder n st fs ->
  SAWCoreState n ->
  BaseTypeRepr bt ->
  SC.Term ->
  IO (B.Expr n bt)
bindSAWTerm sym st bt t = do
  ch_r <- readIORef $ saw_elt_cache_r st
  let midx =
        case t of
          SC.STApp { SC.stAppIndex = idx } -> Just idx
          SC.Unshared _ -> Nothing
  case midx >>= flip IntMap.lookup ch_r of
    Just (Some var) -> do
      Just Refl <- return $ testEquality bt (B.exprType var)
      return var
    Nothing -> do
      sbVar@(B.BoundVarExpr bv) <- freshConstant sym emptySymbol bt
      B.insertIdxValue (saw_elt_cache st) (B.bvarId bv) (SAWExpr t)
      case midx of
        Just i -> modifyIORef' (saw_elt_cache_r st) $ IntMap.insert i (Some sbVar)
        Nothing -> pure ()
      return sbVar

-- | Register an interpretation for a symbolic function. This is not
-- used during simulation, but rather, when we translate Crucible
-- values back into SAW. The interpretation function takes a list of
-- arguments in regular (left-to-right) order.
sawRegisterSymFunInterp ::
  SAWCoreState n ->
  B.ExprSymFn n args ret ->
  (SC.SharedContext -> [SC.Term] -> IO SC.Term) ->
  IO ()
sawRegisterSymFunInterp st f i =
  modifyIORef (saw_symMap st) (Map.insert (indexValue (B.symFnId f)) i)

toSC :: B.ExprBuilder n st fs -> SAWCoreState n -> B.Expr n tp -> IO SC.Term
toSC sym st elt = evaluateExpr sym st (saw_ctx st) (saw_elt_cache st) elt


-- | Create a Real SAWELT value from a Rational.
--
-- This fails on non-integer expressions.
scRealLit ::
  sym ->
  SC.SharedContext ->
  Rational ->
  IO (SAWExpr BaseRealType)
scRealLit sym sc r
  | denominator r /= 1 =
    unsupported sym "SAW backend does not support real values"
  | otherwise =
    IntToRealSAWExpr <$> scIntLit sc (numerator r)

-- | Create a SAWCore term with type 'Integer' from a Haskell Integer.
scIntLit :: SC.SharedContext -> Integer -> IO (SAWExpr BaseIntegerType)
scIntLit sc i
  | i >= 0 =
    SAWExpr <$> (SC.scNatToInt sc =<< SC.scNat sc (fromInteger i))
  | otherwise =
    SAWExpr <$> (SC.scIntNeg sc =<< SC.scNatToInt sc =<< SC.scNat sc (fromInteger (negate i)))

scBvLit :: SC.SharedContext -> NatRepr w -> BV.BV w -> IO (SAWExpr (BaseBVType w))
scBvLit sc w bv = SAWExpr <$> SC.scBvConst sc (natValue w) (BV.asUnsigned bv)


scRealCmpop ::
  (SC.SharedContext -> SAWExpr BaseIntegerType -> SAWExpr BaseIntegerType -> IO (SAWExpr BaseBoolType)) ->
  sym ->
  SC.SharedContext ->
  SAWExpr BaseRealType ->
  SAWExpr BaseRealType ->
  IO (SAWExpr BaseBoolType)
scRealCmpop intOp _ sc (IntToRealSAWExpr x) (IntToRealSAWExpr y) =
  intOp sc x y
scRealCmpop _ sym _ _ _ =
  unsupported sym "SAW backend does not support real values"

scRealBinop ::
  (SC.SharedContext -> SAWExpr BaseIntegerType -> SAWExpr BaseIntegerType -> IO (SAWExpr BaseIntegerType)) ->
  sym ->
  SC.SharedContext ->
  SAWExpr BaseRealType ->
  SAWExpr BaseRealType ->
  IO (SAWExpr BaseRealType)
scRealBinop intOp _ sc (IntToRealSAWExpr x) (IntToRealSAWExpr y) =
  IntToRealSAWExpr <$> intOp sc x y
scRealBinop _ sym _ _ _ =
  unsupported sym "SAW backend does not support real values"


scIntBinop ::
  (SC.SharedContext -> SC.Term -> SC.Term -> IO SC.Term) {- ^ operation on integers -} ->
  SC.SharedContext ->
  SAWExpr BaseIntegerType ->
  SAWExpr BaseIntegerType ->
  IO (SAWExpr BaseIntegerType)
scIntBinop intOp sc (SAWExpr x) (SAWExpr y) =
  SAWExpr <$> intOp sc x y

scIntCmpop ::
  (SC.SharedContext -> SC.Term -> SC.Term -> IO SC.Term) {- ^ operation on integers -} ->
  SC.SharedContext ->
  SAWExpr BaseIntegerType ->
  SAWExpr BaseIntegerType ->
  IO (SAWExpr BaseBoolType)
scIntCmpop intOp sc (SAWExpr x) (SAWExpr y) =
  SAWExpr <$> intOp sc x y

scAddReal ::
  sym ->
  SC.SharedContext ->
  SAWExpr BaseRealType ->
  SAWExpr BaseRealType ->
  IO (SAWExpr BaseRealType)
scAddReal = scRealBinop scAddInt

scAddInt :: SC.SharedContext
            -> SAWExpr BaseIntegerType
            -> SAWExpr BaseIntegerType
            -> IO (SAWExpr BaseIntegerType)
scAddInt = scIntBinop SC.scIntAdd


scMulReal ::
  sym ->
  SC.SharedContext ->
  SAWExpr BaseRealType ->
  SAWExpr BaseRealType ->
  IO (SAWExpr BaseRealType)
scMulReal = scRealBinop scMulInt

scMulInt ::    SC.SharedContext
            -> SAWExpr BaseIntegerType
            -> SAWExpr BaseIntegerType
            -> IO (SAWExpr BaseIntegerType)
scMulInt = scIntBinop SC.scIntMul

scIteReal ::
  sym ->
  SC.SharedContext ->
  SC.Term ->
  SAWExpr BaseRealType ->
  SAWExpr BaseRealType ->
  IO (SAWExpr BaseRealType)
scIteReal sym sc p = scRealBinop (\sc' -> scIteInt sc' p) sym sc

scIteInt :: SC.SharedContext
            -> SC.Term
            -> SAWExpr BaseIntegerType
            -> SAWExpr BaseIntegerType
            -> IO (SAWExpr BaseIntegerType)
scIteInt sc p = scIntBinop
    (\sc' x y -> SC.scIntegerType sc >>= \tp -> SC.scIte sc' tp p x y)
    sc

scIte ::
  sym ->
  SC.SharedContext ->
  BaseTypeRepr tp ->
  SAWExpr BaseBoolType ->
  SAWExpr tp ->
  SAWExpr tp ->
  IO (SAWExpr tp)
scIte sym sc tp (SAWExpr p) x y =
  case tp of
    BaseRealRepr    -> scIteReal sym sc p x y
    BaseIntegerRepr -> scIteInt sc p x y
    _ ->
      do tp' <- baseSCType sym sc tp
         x' <- termOfSAWExpr sym sc x
         y' <- termOfSAWExpr sym sc y
         SAWExpr <$> SC.scIte sc tp' p x' y'


scRealEq ::
  sym ->
  SC.SharedContext ->
  SAWExpr BaseRealType ->
  SAWExpr BaseRealType ->
  IO (SAWExpr BaseBoolType)
scRealEq = scRealCmpop scIntEq

scIntEq :: SC.SharedContext
        -> SAWExpr BaseIntegerType
        -> SAWExpr BaseIntegerType
        -> IO (SAWExpr BaseBoolType)
scIntEq = scIntCmpop SC.scIntEq

scBoolEq ::
  SC.SharedContext ->
  SAWExpr BaseBoolType ->
  SAWExpr BaseBoolType ->
  IO (SAWExpr BaseBoolType)
scBoolEq sc (SAWExpr x) (SAWExpr y) = SAWExpr <$> SC.scBoolEq sc x y

scEq ::
  sym ->
  SC.SharedContext ->
  BaseTypeRepr tp ->
  SAWExpr tp ->
  SAWExpr tp ->
  IO (SAWExpr BaseBoolType)
scEq sym sc tp x y =
  case tp of
    BaseBoolRepr    -> scBoolEq sc x y
    BaseRealRepr    -> scRealEq sym sc x y
    BaseIntegerRepr -> scIntEq sc x y
    BaseBVRepr w    ->
      do let SAWExpr x' = x
         let SAWExpr y' = y
         w' <- SC.scNat sc $ fromIntegral (natValue w)
         SAWExpr <$> SC.scBvEq sc w' x' y'
    _ -> unsupported sym ("SAW backend: equality comparison on unsupported type:" ++ show tp)


scRealLe, scRealLt ::
  sym ->
  SC.SharedContext ->
  SAWExpr BaseRealType ->
  SAWExpr BaseRealType ->
  IO (SAWExpr BaseBoolType)
scRealLe = scRealCmpop scIntLe
scRealLt = scRealCmpop scIntLt

scIntLe, scIntLt ::
  SC.SharedContext ->
  SAWExpr BaseIntegerType ->
  SAWExpr BaseIntegerType ->
  IO (SAWExpr BaseBoolType)
scIntLe = scIntCmpop SC.scIntLe
scIntLt = scIntCmpop SC.scIntLt

scBvAdd ::
  SC.SharedContext ->
  NatRepr w ->
  SAWExpr (BaseBVType w) ->
  SAWExpr (BaseBVType w) ->
  IO (SAWExpr (BaseBVType w))
scBvAdd sc w (SAWExpr x) (SAWExpr y) =
  do n <- SC.scNat sc (natValue w)
     SAWExpr <$> SC.scBvAdd sc n x y

scBvNot ::
  SC.SharedContext ->
  NatRepr w ->
  SAWExpr (BaseBVType w) ->
  IO (SAWExpr (BaseBVType w))
scBvNot sc w (SAWExpr x) =
  do n <- SC.scNat sc (natValue w)
     SAWExpr <$> SC.scBvNot sc n x

scBvMul ::
  SC.SharedContext ->
  NatRepr w ->
  SAWExpr (BaseBVType w) ->
  SAWExpr (BaseBVType w) ->
  IO (SAWExpr (BaseBVType w))
scBvMul sc w (SAWExpr x) (SAWExpr y) =
  do n <- SC.scNat sc (natValue w)
     SAWExpr <$> SC.scBvMul sc n x y

scBvAnd ::
  SC.SharedContext ->
  NatRepr w ->
  SAWExpr (BaseBVType w) ->
  SAWExpr (BaseBVType w) ->
  IO (SAWExpr (BaseBVType w))
scBvAnd sc w (SAWExpr x) (SAWExpr y) =
  do n <- SC.scNat sc (natValue w)
     SAWExpr <$> SC.scBvAnd sc n x y

scBvXor ::
  SC.SharedContext ->
  NatRepr w ->
  SAWExpr (BaseBVType w) ->
  SAWExpr (BaseBVType w) ->
  IO (SAWExpr (BaseBVType w))
scBvXor sc w (SAWExpr x) (SAWExpr y) =
  do n <- SC.scNat sc (natValue w)
     SAWExpr <$> SC.scBvXor sc n x y

termOfSAWExpr ::
  sym ->
  SC.SharedContext ->
  SAWExpr tp -> IO SC.Term
termOfSAWExpr sym _sc expr =
  case expr of
    SAWExpr t -> return t
    IntToRealSAWExpr _
      -> unsupported sym "SAW backend does not support real values"

applyExprSymFn ::
  forall n st fs args ret.
  B.ExprBuilder n st fs ->
  SAWCoreState n ->
  SC.SharedContext ->
  B.ExprSymFn n args ret ->
  Ctx.Assignment SAWExpr args ->
  IO (SAWExpr ret)
applyExprSymFn sym st sc fn args =
  do mp <- readIORef (saw_symMap st)
     mk <-
       case Map.lookup (indexValue (B.symFnId fn)) mp of
         Nothing -> panic "SAWCore.applyExprSymFn"
                    [ "Unknown symbolic function."
                    , "*** Name: " ++ show fn
                    ]
         Just mk -> return mk
     ts <- evaluateAsgn args
     SAWExpr <$> mk sc (reverse ts)
  where
    evaluateAsgn :: Ctx.Assignment SAWExpr args' -> IO [SC.Term]
    evaluateAsgn Ctx.Empty = return []
    evaluateAsgn (xs Ctx.:> x) =
      do vs <- evaluateAsgn xs
         v <- termOfSAWExpr sym sc x
         return (v : vs)

{- | Declare that we don't support something or other.
This aborts the current path of execution, and adds a proof
obligation to ensure that we won't get there.
These proof obligations are all tagged with "Unsupported", so that
users of the library can choose if they will try to discharge them,
fail in some other way, or just ignore them. -}
unsupported :: {- OnlineSolver solver => -} sym -> String -> IO a
unsupported _sym x = fail ("Unsupported " <> x) -- TODO, something better here....


evaluateExpr :: forall n st tp fs.
  B.ExprBuilder n st fs->
  SAWCoreState n ->
  SC.SharedContext ->
  B.IdxCache n SAWExpr ->
  B.Expr n tp ->
  IO SC.Term
evaluateExpr sym st sc cache = f []
  where
    -- Evaluate the element, and expect the result to have the same type.
    f :: [Maybe SolverSymbol] -> B.Expr n tp' -> IO SC.Term
    f env elt = termOfSAWExpr sym sc =<< eval env elt

    eval :: [Maybe SolverSymbol] -> B.Expr n tp' -> IO (SAWExpr tp')
    eval env elt = B.idxCacheEval cache elt (go env elt)

    realFail :: IO a
    realFail = unsupported sym "SAW backend does not support real values"

    cplxFail :: IO a
    cplxFail = unsupported sym "SAW backend does not support complex values"

    floatFail :: IO a
    floatFail = unsupported sym "SAW backend does not support floating-point values"

    stringFail :: IO a
    stringFail = unsupported sym "SAW backend does not support string values"

    unimplemented :: String -> IO a
    unimplemented x = unsupported sym $ "SAW backend: not implemented: " ++ x

    go :: [Maybe SolverSymbol] -> B.Expr n tp' -> IO (SAWExpr tp')

    go _ (B.BoolExpr b _) = SAWExpr <$> SC.scBool sc b

    go _ (B.SemiRingLiteral sr x _) =
      case sr of
        B.SemiRingBVRepr _ w  -> scBvLit sc w x
        B.SemiRingIntegerRepr -> scIntLit sc x
        B.SemiRingRealRepr    -> scRealLit sym sc x

    go _ (B.StringExpr{}) =
      unsupported sym "SAW backend does not support string values"

    go _ (B.FloatExpr{}) =
      unsupported sym "SAW backend does not support floating-point values"

    go env (B.BoundVarExpr bv) =
      case B.bvarKind bv of
        B.UninterpVarKind -> do
          tp <- baseSCType sym sc (B.bvarType bv)
          SAWExpr <$> sawCreateVar st nm tp
            where nm = solverSymbolAsText $ B.bvarName bv
        B.LatchVarKind ->
          unsupported sym "SAW backend does not support latch variables"
        B.QuantifierVarKind -> do
          case elemIndex (Just $ B.bvarName bv) env of
            Nothing -> unsupported sym $ "unbound quantifier variable " <> nm
            Just idx -> SAWExpr <$> SC.scLocalVar sc idx
            where nm = Text.unpack $ solverSymbolAsText $ B.bvarName bv

    go env (B.NonceAppExpr p) =
      case B.nonceExprApp p of
        B.Annotation _tpr _n x ->
          eval env x

        B.Forall bvar body ->
          case B.bvarType bvar of
            BaseBVRepr wrepr -> do
              w <- SC.scNat sc $ natValue wrepr
              ty <- SC.scVecType sc w =<< SC.scBoolType sc
              SAWExpr <$>
                (SC.scBvForall sc w
                 =<< SC.scLambda sc nm ty =<< f (Just (B.bvarName bvar):env) body)
              where nm = solverSymbolAsText $ B.bvarName bvar
            _ -> unsupported sym "SAW backend only supports universal quantifiers over bitvectors"
        B.Exists{} ->
          unsupported sym "SAW backend does not support existential quantifiers"
        B.ArrayFromFn{} -> unimplemented "ArrayFromFn"
        B.MapOverArrays{} -> unimplemented "MapOverArrays"
        B.ArrayTrueOnEntries{} -> unimplemented "ArrayTrueOnEntries"
        B.FnApp fn asgn ->
          do args <- traverseFC (eval env) asgn
             applyExprSymFn sym st sc fn args

    go env a0@(B.AppExpr a) =
      let nyi = unsupported sym $
                  "Expression form not yet implemented in SAWCore backend:\n"
                        ++ show a0
      in
      case B.appExprApp a of
        B.BaseIte bt _ c xe ye -> join (scIte sym sc bt <$> eval env c <*> eval env xe <*> eval env ye)
        B.BaseEq bt xe ye -> join (scEq sym sc bt <$> eval env xe <*> eval env ye)

        B.SemiRingLe sr xe ye ->
          case sr of
            B.OrderedSemiRingRealRepr    -> join (scRealLe sym sc <$> eval env xe <*> eval env ye)
            B.OrderedSemiRingIntegerRepr -> join (scIntLe sc <$> eval env xe <*> eval env ye)

        B.NotPred x ->
          goNeg env x

        B.ConjPred xs ->
          case BM.viewBoolMap xs of
            BM.BoolMapUnit -> SAWExpr <$> SC.scBool sc True
            BM.BoolMapDualUnit -> SAWExpr <$> SC.scBool sc False
            BM.BoolMapTerms (t:|ts) ->
              let pol (x,BM.Positive) = f env x
                  pol (x,BM.Negative) = termOfSAWExpr sym sc =<< goNeg env x
              in SAWExpr <$> join (foldM (SC.scAnd sc) <$> pol t <*> mapM pol ts)

        B.SemiRingProd pd ->
           case WSum.prodRepr pd of
             B.SemiRingRealRepr ->
               do pd' <- WSum.prodEvalM (scMulReal sym sc) (eval env) pd
                  maybe (scRealLit sym sc 1) return pd'
             B.SemiRingIntegerRepr ->
               do pd' <- WSum.prodEvalM (scMulInt sc) (eval env) pd
                  maybe (scIntLit sc 1) return pd'
             B.SemiRingBVRepr B.BVArithRepr w ->
               do n <- SC.scNat sc (natValue w)
                  pd' <- WSum.prodEvalM (SC.scBvMul sc n) (f env) pd
                  maybe (scBvLit sc w (BV.one w)) (return . SAWExpr) pd'
             B.SemiRingBVRepr B.BVBitsRepr w ->
               do n <- SC.scNat sc (natValue w)
                  pd' <- WSum.prodEvalM (SC.scBvAnd sc n) (f env) pd
                  maybe (scBvLit sc w (BV.maxUnsigned w)) (return . SAWExpr) pd'

        B.SemiRingSum ss ->
          case WSum.sumRepr ss of
            B.SemiRingRealRepr -> WSum.evalM add smul (scRealLit sym sc) ss
               where add x y = scAddReal sym sc x y
                     smul 1  e = eval env e
                     smul sm e = join $ scMulReal sym sc <$> scRealLit sym sc sm <*> eval env e
            B.SemiRingIntegerRepr -> WSum.evalM add smul (scIntLit sc) ss
               where add x y = scAddInt sc x y
                     smul 1  e = eval env e
                     smul sm e = join $ scMulInt sc <$> scIntLit sc sm <*> eval env e
            B.SemiRingBVRepr B.BVArithRepr w -> WSum.evalM add smul (scBvLit sc w) ss
               where add x y          = scBvAdd sc w x y
                     smul (BV.BV 1) e = eval env e
                     smul sm e        = join (scBvMul sc w <$> scBvLit sc w sm <*> eval env e)
            B.SemiRingBVRepr B.BVBitsRepr w
               | ss^.WSum.sumOffset == one -> scBvNot sc w =<< bitwise_eval (ss & WSum.sumOffset .~ BV.zero w)
               | otherwise -> bitwise_eval ss

              where one = BV.maxUnsigned w
                    bitwise_eval = WSum.evalM add smul (scBvLit sc w)
                    add x y = scBvXor sc w x y
                    smul sm e
                       | sm == one = eval env e
                       | otherwise = join (scBvAnd sc w <$> scBvLit sc w sm <*> eval env e)

        B.RealIsInteger{} -> unsupported sym "SAW backend does not support real values"

        B.BVOrBits w bs ->
          do n <- SC.scNat sc (natValue w)
             bs' <- traverse (f env) (B.bvOrToList bs)
             case bs' of
               [] -> scBvLit sc w (BV.zero w)
               x:xs -> SAWExpr <$> foldM (SC.scBvOr sc n) x xs

        B.BVFill w p ->
          do bit <- SC.scBoolType sc
             n <- SC.scNat sc (natValue w)
             x <- f env p
             SAWExpr <$> SC.scGlobalApply sc (SC.mkIdent SC.preludeName "replicate") [n, bit, x]

        B.BVTestBit i bv -> fmap SAWExpr $ do
             w <- SC.scNat sc (natValue (bvWidth bv))
             bit <- SC.scBoolType sc
             -- NB, SAWCore's `scAt` is big endian
             let j = natValue (bvWidth bv) - i - 1
             join (SC.scAt sc w bit <$> f env bv <*> SC.scNat sc j)

        B.BVSlt x y -> fmap SAWExpr $ do
             w <- SC.scNat sc (natValue (bvWidth x))
             join (SC.scBvSLt sc w <$> f env x <*> f env y)
        B.BVUlt x y -> fmap SAWExpr $ do
             w <- SC.scNat sc (natValue (bvWidth x))
             join (SC.scBvULt sc w <$> f env x <*> f env y)

        B.BVUnaryTerm{} -> unsupported sym "SAW backend does not support the unary bitvector representation"

        B.BVUdiv _ x y -> fmap SAWExpr $ do
           n <- SC.scNat sc (natValue (bvWidth x))
           join (SC.scBvUDiv sc n <$> f env x <*> f env y)
        B.BVUrem _ x y -> fmap SAWExpr $ do
           n <- SC.scNat sc (natValue (bvWidth x))
           join (SC.scBvURem sc n <$> f env x <*> f env y)
        B.BVSdiv _ x y -> fmap SAWExpr $ do
           -- NB: bvSDiv applies 'Succ' to its width argument, so we
           -- need to subtract 1 to make the types match.
           n <- SC.scNat sc (natValue (bvWidth x) - 1)
           join (SC.scBvSDiv sc n <$> f env x <*> f env y)
        B.BVSrem _ x y -> fmap SAWExpr $ do
           -- NB: bvSDiv applies 'Succ' to its width argument, so we
           -- need to subtract 1 to make the types match.
           n <- SC.scNat sc (natValue (bvWidth x) - 1)
           join (SC.scBvSRem sc n <$> f env x <*> f env y)
        B.BVShl _ x y -> fmap SAWExpr $ do
           let w = natValue (bvWidth x)
           n <- SC.scNat sc w
           join (SC.scBvShl sc n <$> f env x <*> (SC.scBvToNat sc w =<< f env y))
        B.BVLshr _ x y -> fmap SAWExpr $ do
           let w = natValue (bvWidth x)
           n <- SC.scNat sc w
           join (SC.scBvShr sc n <$> f env x <*> (SC.scBvToNat sc w =<< f env y))
        B.BVAshr _ x y -> fmap SAWExpr $ do
           let w = natValue (bvWidth x)
           -- NB: bvSShr applies a `Succ` to its width argument, so we subtract
           --     1 here to make things match up.
           n <- SC.scNat sc (w - 1)
           join (SC.scBvSShr sc n <$> f env x <*> (SC.scBvToNat sc w =<< f env y))
        B.BVRol w x y -> fmap SAWExpr $ do
           n <- SC.scNat sc (natValue w)
           bit <- SC.scBoolType sc
           x' <- f env x
           y' <- SC.scBvToNat sc (natValue w) =<< f env y
           SC.scGlobalApply sc (SC.mkIdent SC.preludeName "rotateL") [n,bit,x',y']
        B.BVRor w x y -> fmap SAWExpr $ do
           n <- SC.scNat sc (natValue w)
           bit <- SC.scBoolType sc
           x' <- f env x
           y' <- SC.scBvToNat sc (natValue w) =<< f env y
           SC.scGlobalApply sc (SC.mkIdent SC.preludeName "rotateR") [n,bit,x',y']
        B.BVConcat _ x y -> fmap SAWExpr $ do
           m <- SC.scNat sc (natValue (bvWidth x))
           n <- SC.scNat sc (natValue (bvWidth y))
           t <- SC.scBoolType sc
           join (SC.scAppend sc m n t <$> f env x <*> f env y)
        B.BVSelect start num x -> fmap SAWExpr $ do
           i <- SC.scNat sc (natValue (bvWidth x) - natValue num - natValue start)
           n <- SC.scNat sc (natValue num)
           o <- SC.scNat sc (natValue start)
           t <- SC.scBoolType sc
           x' <- f env x
           SC.scSlice sc t i n o x'
        B.BVZext w' x -> fmap SAWExpr $ do
          let w = bvWidth x
          n <- SC.scNat sc (natValue w)
          m <- SC.scNat sc (natValue w' - natValue w)
          x' <- f env x
          SC.scBvUExt sc m n x'
        B.BVSext w' x -> fmap SAWExpr $ do
          let w = bvWidth x
          -- NB: width - 1 to make SAWCore types work out
          n <- SC.scNat sc (natValue w - 1)
          m <- SC.scNat sc (natValue w' - natValue w)
          x' <- f env x
          SC.scBvSExt sc m n x'
        B.BVPopcount w x ->
          do n  <- SC.scNat sc (natValue w)
             x' <- f env x
             SAWExpr <$> SC.scBvPopcount sc n x'
        B.BVCountLeadingZeros w x ->
          do n  <- SC.scNat sc (natValue w)
             x' <- f env x
             SAWExpr <$> SC.scBvCountLeadingZeros sc n x'
        B.BVCountTrailingZeros w x ->
          do n  <- SC.scNat sc (natValue w)
             x' <- f env x
             SAWExpr <$> SC.scBvCountTrailingZeros sc n x'

        -- Note: SAWCore supports only unidimensional arrays. As a result, What4 multidimensional
        -- arrays cannot be translated to SAWCore.
        B.ArrayMap indexTypes range updates arr
          | Ctx.Empty Ctx.:> idx_type <- indexTypes ->
            do sc_idx_type <- baseSCType sym sc idx_type
               sc_elm_type <- baseSCType sym sc range
               sc_arr <- f env arr
               SAWExpr <$> foldM
                 (\sc_acc_arr (Ctx.Empty Ctx.:> idx_lit, elm) ->
                   do sc_idx <- f env =<< indexLit sym idx_lit
                      sc_elm <- f env elm
                      SC.scArrayUpdate sc sc_idx_type sc_elm_type sc_acc_arr sc_idx sc_elm)
                 sc_arr
                 (AUM.toList updates)
          | otherwise -> unimplemented "multidimensional ArrayMap"

        B.ConstantArray indexTypes range v
          | Ctx.Empty Ctx.:> idx_type <- indexTypes ->
            do sc_idx_type <- baseSCType sym sc idx_type
               sc_elm_type <- baseSCType sym sc range
               sc_elm <- f env v
               SAWExpr <$> SC.scArrayConstant sc sc_idx_type sc_elm_type sc_elm
          | otherwise -> unimplemented "multidimensional ConstantArray"

        B.SelectArray range arr indexTerms
          | Ctx.Empty Ctx.:> idx <- indexTerms
          , idx_type <- exprType idx ->
            do sc_idx_type <- baseSCType sym sc idx_type
               sc_elm_type <- baseSCType sym sc range
               sc_arr <- f env arr
               sc_idx <- f env idx
               SAWExpr <$> SC.scArrayLookup sc sc_idx_type sc_elm_type sc_arr sc_idx
          | otherwise -> unimplemented "multidimensional SelectArray"

        B.UpdateArray range indexTypes arr indexTerms v
          | Ctx.Empty Ctx.:> idx_type <- indexTypes
          , Ctx.Empty Ctx.:> idx <- indexTerms ->
            do sc_idx_type <- baseSCType sym sc idx_type
               sc_elm_type <- baseSCType sym sc range
               sc_arr <- f env arr
               sc_idx <- f env idx
               sc_elm <- f env v
               SAWExpr <$> SC.scArrayUpdate sc sc_idx_type sc_elm_type sc_arr sc_idx sc_elm
          | otherwise -> unimplemented "multidimensional UpdateArray"

        B.IntDiv x y ->
          do x' <- f env x
             y' <- f env y
             SAWExpr <$> SC.scIntDiv sc x' y'
        B.IntMod x y ->
          do x' <- f env x
             y' <- f env y
             SAWExpr <$> SC.scIntMod sc x' y'
        B.IntAbs x ->
          eval env x >>= \case
            SAWExpr z -> SAWExpr <$> (SC.scIntAbs sc z)

        B.IntDivisible x 0 ->
          do x' <- f env x
             SAWExpr <$> (SC.scIntEq sc x' =<< SC.scIntegerConst sc 0)
        B.IntDivisible x k ->
          do x' <- f env x
             k' <- SC.scIntegerConst sc (toInteger k)
             z  <- SC.scIntMod sc x' k'
             SAWExpr <$> (SC.scIntEq sc z =<< SC.scIntegerConst sc 0)

        B.IntegerToBV x w ->
          do n <- SC.scNat sc (natValue w)
             SAWExpr <$> (SC.scIntToBv sc n =<< f env x)

        B.BVToInteger x ->
          do n <- SC.scNat sc (natValue (bvWidth x))
             SAWExpr <$> (SC.scBvToInt sc n =<< f env x)

        B.SBVToInteger x ->
          do n <- SC.scNat sc (natValue (bvWidth x))
             SAWExpr <$> (SC.scSbvToInt sc n =<< f env x)

        -- Proper support for real and complex numbers will require additional
        -- work on the SAWCore side
        B.IntegerToReal x -> IntToRealSAWExpr . SAWExpr <$> f env x
        B.RealToInteger x ->
          eval env x >>= \case
            IntToRealSAWExpr x' -> return x'
            _ -> realFail

        ------------------------------------------------------------------------
        -- Floating point operations

        B.FloatNeg{}  -> floatFail
        B.FloatAbs{}  -> floatFail
        B.FloatSqrt{}  -> floatFail
        B.FloatAdd{}  -> floatFail
        B.FloatSub{}  -> floatFail
        B.FloatMul{}  -> floatFail
        B.FloatDiv{}  -> floatFail
        B.FloatRem{}  -> floatFail
        B.FloatFMA{}  -> floatFail
        B.FloatFpEq{}  -> floatFail
        B.FloatLe{}  -> floatFail
        B.FloatLt{}  -> floatFail
        B.FloatIsNaN{}  -> floatFail
        B.FloatIsInf{}  -> floatFail
        B.FloatIsZero{}  -> floatFail
        B.FloatIsPos{}  -> floatFail
        B.FloatIsNeg{}  -> floatFail
        B.FloatIsSubnorm{}  -> floatFail
        B.FloatIsNorm{}  -> floatFail
        B.FloatCast{}  -> floatFail
        B.FloatRound{} -> floatFail
        B.FloatFromBinary{}  -> floatFail
        B.BVToFloat{}  -> floatFail
        B.SBVToFloat{}  -> floatFail
        B.RealToFloat{}  -> floatFail
        B.FloatToBV{} -> floatFail
        B.FloatToSBV{} -> floatFail
        B.FloatToReal{} -> floatFail
        B.FloatToBinary{} -> floatFail

        B.RoundReal{} -> realFail
        B.RoundEvenReal{} -> realFail
        B.FloorReal{} -> realFail
        B.CeilReal{} -> realFail
        B.RealDiv{} -> realFail
        B.RealSqrt{} -> realFail
        B.Pi{} -> realFail
        B.RealSin{} -> realFail
        B.RealCos{} -> realFail
        B.RealSinh{} -> realFail
        B.RealCosh{} -> realFail
        B.RealExp{} -> realFail
        B.RealLog{} -> realFail
        B.RealATan2{} -> realFail

        B.Cplx{}     -> cplxFail
        B.RealPart{} -> cplxFail
        B.ImagPart{} -> cplxFail

        B.StringLength{} -> stringFail
        B.StringAppend{} -> stringFail
        B.StringContains{} -> stringFail
        B.StringIsPrefixOf{} -> stringFail
        B.StringIsSuffixOf{} -> stringFail
        B.StringIndexOf{} -> stringFail
        B.StringSubstring{} -> stringFail

        B.StructCtor{} -> nyi -- FIXME
        B.StructField{} -> nyi -- FIXME

    -- returns the logical negation of the result of 'go'
    -- negations are pushed inside conjunctions and less-than-or-equal
    goNeg :: [Maybe SolverSymbol] -> B.Expr n BaseBoolType -> IO (SAWExpr BaseBoolType)
    goNeg env expr =
      case expr of
        -- negation of (x /\ y) becomes (~x \/ ~y)
        B.AppExpr (B.appExprApp -> B.ConjPred xs) ->
          case BM.viewBoolMap xs of
            BM.BoolMapUnit -> SAWExpr <$> SC.scBool sc False
            BM.BoolMapDualUnit -> SAWExpr <$> SC.scBool sc True
            BM.BoolMapTerms (t:|ts) ->
              let pol (x, BM.Positive) = termOfSAWExpr sym sc =<< goNegAtom env x
                  pol (x, BM.Negative) = f env x
              in SAWExpr <$> join (foldM (SC.scOr sc) <$> pol t <*> mapM pol ts)
        _ -> goNegAtom env expr

    -- returns the logical negation of the result of 'go'
    -- negations are pushed inside less-than-or-equal
    goNegAtom :: [Maybe SolverSymbol] -> B.Expr n BaseBoolType -> IO (SAWExpr BaseBoolType)
    goNegAtom env expr =
      case expr of
        -- negation of (x <= y) becomes (y < x)
        B.AppExpr (B.appExprApp -> B.SemiRingLe sr xe ye) ->
          case sr of
            B.OrderedSemiRingRealRepr    -> join (scRealLt sym sc <$> eval env ye <*> eval env xe)
            B.OrderedSemiRingIntegerRepr -> join (scIntLt sc <$> eval env ye <*> eval env xe)
        _ -> SAWExpr <$> (SC.scNot sc =<< f env expr)

