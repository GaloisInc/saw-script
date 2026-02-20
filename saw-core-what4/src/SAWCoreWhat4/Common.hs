{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds#-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module SAWCoreWhat4.Common
  ( What4
  , SArray(..)
  , SBool
  , SInt
  , SValue
  , SPrim
  , Sym
  , What4Extra(..)
  , vAsFirstOrderType
  , valueAsBaseType
  , termOfTValue
  , termOfSValue
  ) where

import Data.IORef
import Data.Kind (Type)
import Data.Map (Map)
import Numeric.Natural (Natural)

-- saw-core
import SAWCore.SharedTerm
import SAWCore.FiniteValue (FirstOrderType(..))
import qualified SAWCore.Simulator.Prims as Prims
import SAWCore.Simulator.Value



-- what4
import           What4.Interface(Pred,SymInteger,IsSymExprBuilder)
import qualified What4.Interface as W
import           What4.SFloat (SFloat(..))
import           What4.SWord (SWord(..))

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Some

-- saw-core-what4
import SAWCoreWhat4.FirstOrder

---------------------------------------------------------------------
-- empty datatype to index (open) type families
-- for this backend
data What4 (sym :: Type)

-- | A What4 symbolic array where the domain and co-domain types do not appear
--   in the type
data SArray sym where
  SArray ::
    W.IsExpr (W.SymExpr sym) =>
    W.SymArray sym (Ctx.EmptyCtx Ctx.::> itp) etp ->
    SArray sym

-- type abbreviations for uniform naming
type SBool sym = Pred sym
type SInt  sym = SymInteger sym

type instance EvalM (What4 sym) = IO
type instance VBool (What4 sym) = SBool sym
type instance VWord (What4 sym) = SWord sym
type instance VInt  (What4 sym) = SInt  sym
type instance VFloat (What4 sym) = SFloat sym
type instance VArray (What4 sym) = SArray sym
type instance Extra (What4 sym) = What4Extra sym

type SValue sym = Value (What4 sym)
type SPrim sym  = Prims.Prim (What4 sym)

-- Constraint
type Sym sym = IsSymExprBuilder sym

---------------------------------------------------------------------

data What4Extra sym =
  SStream (Natural -> IO (SValue sym)) (IORef (Map Natural (SValue sym)))

instance Show (What4Extra sym) where
  show (SStream _ _) = "<SStream>"


instance Show (SArray sym) where
  show (SArray arr) = show $ W.printSymExpr arr

--
-- Convert a saw-core type expression to a FirstOrder type expression
--
vAsFirstOrderType :: IsSymExprBuilder sym => TValue (What4 sym) -> Maybe FirstOrderType
vAsFirstOrderType v = asFirstOrderTypeTValue v

valueAsBaseType :: IsSymExprBuilder sym => TValue (What4 sym) -> Maybe (Some W.BaseTypeRepr)
valueAsBaseType v = fotToBaseType =<< vAsFirstOrderType v

termOfTValue :: SharedContext -> TValue (What4 sym) -> IO Term
termOfTValue sc val =
  case val of
    VBoolType -> scBoolType sc
    VIntType -> scIntegerType sc
    VRationalType -> scRationalType sc
    VFloatType e p ->
      do e' <- scNat sc e
         p' <- scNat sc p
         scFloatType sc e' p'
    VVecType n a ->
      do n' <- scNat sc n
         a' <- termOfTValue sc a
         scVecType sc n' a'
    VDataType (ModuleIdentifier "Prelude.UnitType") [] []
      -> scUnitType sc
    VDataType (ModuleIdentifier "Prelude.PairType") [TValue a, TValue b] []
      -> do a' <- termOfTValue sc a
            b' <- termOfTValue sc b
            scPairType sc a' b'
    VDataType (ModuleIdentifier "Prelude.EmptyType") [] []
      -> scRecordType sc []
    VDataType (ModuleIdentifier "Prelude.RecordType")
      [VString fname, TValue a, TValue b] []
      -> do fname' <- scString sc fname
            a' <- termOfTValue sc a
            b' <- termOfTValue sc b
            scGlobalApply sc "Prelude.RecordType" [fname', a', b']
    _ -> fail $ "termOfTValue: " ++ show val

termOfSValue :: SharedContext -> SValue sym -> IO Term
termOfSValue sc val =
  case val of
    VCtorApp 0 _ []
      -> scUnitValue sc
    VNat n
      -> scNat sc n
    TValue tv -> termOfTValue sc tv
    _ -> fail $ "termOfSValue: " ++ show val
