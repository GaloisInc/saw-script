{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RecordWildCards #-}

module SAWScript.Heapster.ValueTranslation (
  ValueTranslate(..),
  ValueTranslate''(..),
  ) where

import           Data.Functor.Const

import           Data.Parameterized.Context
import           Lang.Crucible.Types
import           SAWScript.Heapster.Permissions
import           Verifier.SAW.OpenTerm

-- | Translate an 'Integer' to a SAW bitvector literal
translateBVLit :: NatRepr w -> Integer -> OpenTerm
translateBVLit w i =
  applyOpenTermMulti (globalOpenTerm "Prelude.bvNat")
  [valueTranslate'' w, natOpenTerm i]

-- | Build an 'OpenTerm' for the sum of SAW bitvectors
translateBVSum :: NatRepr w -> [OpenTerm] -> OpenTerm
translateBVSum w [] = translateBVLit w 0
translateBVSum _ [t] = t
translateBVSum w (t:ts) =
  applyOpenTermMulti (globalOpenTerm "Prelude.bvAdd")
  [valueTranslate'' w, t, translateBVSum w ts]

class ValueTranslate (f :: Ctx k -> k' -> *) where
  valueTranslate :: Assignment (Const OpenTerm) ctx -> f ctx a -> OpenTerm

class ValueTranslate'' (d :: *) where
  valueTranslate'' :: d -> OpenTerm

instance ValueTranslate'' (NatRepr w) where
  valueTranslate'' w = natOpenTerm $ intValue w

instance ValueTranslate PermExpr where
  valueTranslate ctx = \case
    PExpr_Var i                 -> getConst $ ctx `pvGet` i
    PExpr_BV w factors constant ->
      translateBVSum w (translateBVLit w constant :
                        map (valueTranslate ctx) factors)
    PExpr_LLVMWord _ _          -> unitOpenTerm
    PExpr_LLVMOffset _ _ _      -> unitOpenTerm
    PExpr_Spl _                 -> error "TODO"
    PExpr_Struct _ _            -> error "TODO"

instance ValueTranslate BVFactor where
  valueTranslate ctx (BVFactor w i x) =
    applyOpenTermMulti (globalOpenTerm "Prelude.bvMul")
    [valueTranslate'' w, translateBVLit w i, valueTranslate ctx x]

instance ValueTranslate PermVar where
  valueTranslate ctx x = getConst $ pvGet ctx x
