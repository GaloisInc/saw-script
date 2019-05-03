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

module SAWScript.Heapster.TypeTranslation (
  TypeTranslate(..),
  TypeTranslate''(..),
  ) where

import           Data.Functor.Const

import           Data.Parameterized.Context
import           Lang.Crucible.Types
import           SAWScript.Heapster.Permissions
import           SAWScript.TopLevel
import           Verifier.SAW.OpenTerm
import           Verifier.SAW.Term.Functor

-- | The @TypeTranslate@ family of type classes captures translations from
-- permission types to SAW types.  The idea is to translate imperative
-- structures into a functional version of their shape.

-- | Translate an 'Integer' to a SAW bitvector literal
translateBVLit :: NatRepr w -> Integer -> OpenTerm
translateBVLit w i =
  applyOpenTermMulti (globalOpenTerm "Prelude.bvNat")
  [typeTranslate'' w, natOpenTerm i]

-- | Build an 'OpenTerm' for the sum of SAW bitvectors
translateBVSum :: NatRepr w -> [OpenTerm] -> OpenTerm
translateBVSum w [] = translateBVLit w 0
translateBVSum _ [t] = t
translateBVSum w (t:ts) =
  applyOpenTermMulti (globalOpenTerm "Prelude.bvAdd")
  [typeTranslate'' w, t, translateBVSum w ts]

class TypeTranslate (f :: Ctx k -> k' -> *) where
  typeTranslate :: Assignment (Const OpenTerm) ctx -> f ctx a -> OpenTerm

-- class TypeTranslate' (f :: Ctx k -> *) where
--   typeTranslate' :: Assignment (Const OpenTerm) ctx -> f ctx -> OpenTerm

class TypeTranslate'' (d :: *) where
  typeTranslate'' :: d -> OpenTerm

instance TypeTranslate'' (NatRepr w) where
  typeTranslate'' w = natOpenTerm $ intValue w

instance TypeTranslate'' (TypeRepr a) where
  typeTranslate'' = \case
    AnyRepr                -> error "TODO"
    UnitRepr               -> dataTypeOpenTerm "Prelude.UnitType" []
    BoolRepr               -> dataTypeOpenTerm "Prelude.Bool" []
    NatRepr                -> dataTypeOpenTerm "Prelude.Nat" []
    IntegerRepr            -> error "TODO"
    RealValRepr            -> error "TODO"
    ComplexRealRepr        -> error "TODO"
    BVRepr _               -> error "TODO"
    IntrinsicRepr _ _      -> error "TODO"
    RecursiveRepr _ _      -> error "TODO"
    FloatRepr _            -> error "TODO"
    IEEEFloatRepr _        -> error "TODO"
    CharRepr               -> error "TODO"
    StringRepr             -> error "TODO"
    FunctionHandleRepr _ _ -> error "TODO"
    MaybeRepr _            -> error "TODO"
    VectorRepr _           -> error "TODO"
    StructRepr _           -> error "TODO"
    VariantRepr _          -> error "TODO"
    ReferenceRepr _        -> error "TODO"
    WordMapRepr _ _        -> error "TODO"
    StringMapRepr _        -> error "TODO"
    SymbolicArrayRepr _ _  -> error "TODO"
    SymbolicStructRepr _   -> error "TODO"

instance TypeTranslate PermVar where
  typeTranslate ctx x = getConst $ pvGet ctx x

instance TypeTranslate BVFactor where
  typeTranslate ctx (BVFactor w i x) =
    applyOpenTermMulti (globalOpenTerm "Prelude.bvMul")
    [typeTranslate'' w, translateBVLit w i, typeTranslate ctx x]

instance TypeTranslate PermExpr where
  typeTranslate ctx = \case
    PExpr_Var i                  -> getConst $ ctx `pvGet` i
    PExpr_BV w factors constant     ->
      translateBVSum w (translateBVLit w constant :
                        map (typeTranslate ctx) factors)
    PExpr_LLVMWord _ _ -> unitOpenTerm
    PExpr_LLVMOffset _ _ _ -> unitOpenTerm
    PExpr_Spl _ -> error "TODO"
    PExpr_Struct _ _ -> error "TODO"

instance TypeTranslate ValuePerm where
  typeTranslate ctx = \case

    ValPerm_True           -> flatOpenTerm UnitType

    ValPerm_Eq _           -> flatOpenTerm UnitType

    ValPerm_Or p1 p2       ->
      let t1 = typeTranslate ctx p1 in
      let t2 = typeTranslate ctx p2 in
      dataTypeOpenTerm "Prelude.Either" [t1, t2]

    ValPerm_Exists t p     ->
      dataTypeOpenTerm
      "Prelude.Sigma"
      [ lambdaOpenTerm "x" (typeTranslate'' t) (\ x -> typeTranslate (extend ctx (Const x)) p)
      ]

    ValPerm_Mu _           -> error "TODO"

    ValPerm_Var _index     -> error "TODO"

    ValPerm_Nat_Neq0       -> error "TODO"

    ValPerm_LLVMPtr _ ps _ ->
      tupleTypeOpenTerm (typeTranslate ctx <$> ps)

instance TypeTranslate LLVMShapePerm where
  typeTranslate ctx = \case

    LLVMFieldShapePerm (LLVMFieldPerm {..}) -> typeTranslate ctx llvmFieldPerm

    LLVMArrayShapePerm (LLVMArrayPerm {..}) ->
      let len = error "TODO" in -- typeTranslate ctx llvmArrayLen in -- FIXME: this does not make sense
      let types = typeTranslate ctx llvmArrayPtrPerm in
      dataTypeOpenTerm "Prelude.Vec" [types, len]

tests :: [(ValuePerm ctx a, OpenTerm)]
tests =

  [ ( ValPerm_True
    , flatOpenTerm UnitType
    )

  ]

testTypeTranslation :: Integer -> TopLevel ()
testTypeTranslation i =
  do sc <- getSharedContext
     let (p, t) = (tests !! fromInteger i)
     expected <- io $ completeOpenTerm sc $ t
     obtained <- io $ completeOpenTerm sc $ typeTranslate empty p
     if expected == obtained
       then io $ putStrLn "Success!"
       else io $ putStrLn $ "Error in testPermTranslation for test case " ++ show i
