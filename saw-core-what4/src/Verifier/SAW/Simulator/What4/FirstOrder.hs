------------------------------------------------------------------------
-- |
-- Module      : Verifier.SAW.Simulator.What4.FirstOrder
-- Copyright   : Galois, Inc. 2012-2015
-- License     : BSD3
-- Maintainer  : sweirich@galois.com
-- Stability   : experimental
-- Portability : non-portable (language extensions)
--
-- Connect What4's 'BaseType' with saw-core's 'FirstOrderType'
-- (both types and values of Base/FirstOrder type)
-- TODO NOTE: support for tuples, arrays and records is not complete
-- but is also unused in Verifier.SAW.Simulator.What4
------------------------------------------------------------------------
{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}

module Verifier.SAW.Simulator.What4.FirstOrder
  (
    fotToBaseType,
    typeReprToFOT,
    groundToFOV
  ) where

import qualified Data.BitVector.Sized as BV
import qualified Data.Map as Map
import Data.Foldable.WithIndex (ifoldlM)
import Data.Parameterized.TraversableFC (FoldableFC(..))
import Data.Parameterized.Some(Some(..))
import Data.Parameterized.Context hiding (replicate)

import Verifier.SAW.Simulator.What4.PosNat

import Verifier.SAW.FiniteValue (FirstOrderType(..),FirstOrderValue(..))

import What4.BaseTypes
import What4.IndexLit
import What4.Expr.GroundEval

---------------------------------------------------------------------

-- | Convert a type expression from SAW-core to What4
fotToBaseType :: FirstOrderType -> Maybe (Some BaseTypeRepr)
fotToBaseType FOTBit
  = Just (Some BaseBoolRepr)
fotToBaseType FOTInt
  = Just (Some BaseIntegerRepr)
fotToBaseType (FOTIntMod _n)
  = Just (Some BaseIntegerRepr)
fotToBaseType (FOTVec nat FOTBit)
  | Just (Some (PosNat nr)) <- somePosNat nat
  = Just (Some (BaseBVRepr nr))
  | otherwise = Nothing

fotToBaseType (FOTVec nat fot)
  | Just (Some assn) <- listToAssn (replicate (fromIntegral nat) fot)
  = Just (Some (BaseStructRepr assn))
fotToBaseType (FOTArray fot1 fot2)
  | Just (Some ty1) <- fotToBaseType fot1
  , Just (Some ty2) <- fotToBaseType fot2
  = Just (Some (BaseArrayRepr (Empty :> ty1) ty2))
fotToBaseType (FOTTuple fots)
  | Just (Some assn) <- listToAssn fots
  = Just (Some (BaseStructRepr assn))

-- TODO: convert to What4 records ?!
fotToBaseType _ = Nothing

listToAssn :: [FirstOrderType] -> Maybe (Some (Assignment BaseTypeRepr))
listToAssn [] = Just (Some empty)
listToAssn (fot:rest) =
  case (fotToBaseType fot, listToAssn rest) of
    (Just (Some bt), Just (Some assn)) -> Just (Some (extend assn bt))
    _ -> Nothing

---------------------------------------------------------------------
-- | Convert a type expression from What4 to SAW-core

typeReprToFOT :: BaseTypeRepr ty -> Either String FirstOrderType
typeReprToFOT BaseBoolRepr            = pure FOTBit
typeReprToFOT BaseIntegerRepr         = pure FOTInt
typeReprToFOT (BaseBVRepr w)          = pure $ FOTVec (natValue w) FOTBit
typeReprToFOT BaseRealRepr            = Left "No FO Real"
typeReprToFOT BaseComplexRepr         = Left "No FO Complex"
typeReprToFOT (BaseStringRepr _)      = Left "No FO String"
typeReprToFOT (BaseArrayRepr (Empty :> ty) b)
  | Right fot1 <- typeReprToFOT ty
  , Right fot2 <- typeReprToFOT b
  = pure $ FOTArray fot1 fot2
typeReprToFOT ty@(BaseArrayRepr _ctx _b) = Left $ "Unsupported FO Array: " ++ show ty
typeReprToFOT (BaseFloatRepr _)       = Left "No FO Floating point"
typeReprToFOT (BaseStructRepr ctx)    = FOTTuple <$> assnToList ctx

assnToList :: Assignment BaseTypeRepr ctx -> Either String [FirstOrderType]
assnToList = foldrFC g (Right []) where
  g :: BaseTypeRepr x -> Either String [FirstOrderType] -> Either String [FirstOrderType]
  g ty l = (:) <$> typeReprToFOT ty <*> l


---------------------------------------------------------------------
-- | Convert between What4 GroundValues and saw-core FirstOrderValues

groundToFOV :: BaseTypeRepr ty -> GroundValue ty -> Either String FirstOrderValue
groundToFOV BaseBoolRepr    b         = pure $ FOVBit b
groundToFOV BaseIntegerRepr i         = pure $ FOVInt i
groundToFOV (BaseBVRepr w) bv         = pure $ FOVWord (natValue w) (BV.asUnsigned bv)
groundToFOV BaseRealRepr    _         = Left "Real is not FOV"
groundToFOV BaseComplexRepr         _ = Left "Complex is not FOV"
groundToFOV (BaseStringRepr _)      _ = Left "String is not FOV"
groundToFOV (BaseFloatRepr _)       _ = Left "Floating point is not FOV"
groundToFOV (BaseArrayRepr _ _) (ArrayMapping _) =
    -- We don't have a way to represent ArrayMapping in FirstOrderValue
    -- (see note in FiniteValue.hs where FirstOrderValue's defined)
    Left "Unsupported FOV Array (values only available by lookup)"
groundToFOV (BaseArrayRepr (Empty :> ty_idx) ty_val) (ArrayConcrete dfl values) = do
    ty_idx' <- typeReprToFOT ty_idx
    dfl' <- groundToFOV ty_val dfl
    let convert idx values' v = do
          let idx' = indexToFOV idx
          v' <- groundToFOV ty_val v
          return $ Map.insert idx' v' values'
    values' <- ifoldlM convert Map.empty values
    pure $ FOVArray ty_idx' dfl' values'
groundToFOV (BaseArrayRepr _ _) _ =
    Left "Unsupported FOV array (unexpected key type)"
groundToFOV (BaseStructRepr ctx) tup  = FOVTuple <$> tupleToList ctx tup

indexToFOV :: Assignment IndexLit (EmptyCtx ::> ty) -> FirstOrderValue
indexToFOV (Empty :> IntIndexLit k) =
    FOVInt k
indexToFOV (Empty :> BVIndexLit w k) =
    FOVWord (natValue w) (BV.asUnsigned k)


tupleToList :: Assignment BaseTypeRepr ctx ->
             Assignment GroundValueWrapper ctx -> Either String [FirstOrderValue]
tupleToList (viewAssign -> AssignEmpty) (viewAssign -> AssignEmpty) = Right []
tupleToList (viewAssign -> AssignExtend rs r) (viewAssign -> AssignExtend gvs gv) =
  (:) <$> groundToFOV r (unGVW gv) <*> tupleToList rs gvs
#if !MIN_VERSION_GLASGOW_HASKELL(8,10,0,0)
tupleToList _ _ = error "GADTs should rule this out."
#endif
