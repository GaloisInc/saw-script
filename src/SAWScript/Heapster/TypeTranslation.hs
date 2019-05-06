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
  TypeTranslate'(..),
  TypeTranslate''(..),
  testTypeTranslation,
  ) where

import           Data.Functor.Const

import           Data.Parameterized.Context
import           Lang.Crucible.Types
import           SAWScript.Heapster.Permissions
import           SAWScript.Heapster.ValueTranslation
import           SAWScript.TopLevel
import           Verifier.SAW.OpenTerm
import           Verifier.SAW.Term.Functor

-- | The @TypeTranslate@ family of type classes captures translations from
-- permission types to SAW types.  The idea is to translate imperative
-- structures into a functional version of their shape.

class TypeTranslate (f :: Ctx k -> k' -> *) where
  typeTranslate :: Assignment (Const OpenTerm) ctx -> f ctx a -> OpenTerm

class TypeTranslate' (f :: Ctx k -> *) where
  typeTranslate' :: Assignment (Const OpenTerm) ctx -> f ctx -> OpenTerm

class TypeTranslate'' (d :: *) where
  typeTranslate'' :: d -> OpenTerm

instance TypeTranslate'' (TypeRepr a) where
  typeTranslate'' = \case
    AnyRepr                -> error "TODO"
    UnitRepr               -> dataTypeOpenTerm "Prelude.UnitType" []
    BoolRepr               -> dataTypeOpenTerm "Prelude.Bool" []
    NatRepr                -> dataTypeOpenTerm "Prelude.Nat" []
    IntegerRepr            -> error "TODO"
    RealValRepr            -> error "TODO"
    ComplexRealRepr        -> error "TODO"
    BVRepr w               -> dataTypeOpenTerm "Prelude.bitvector" [valueTranslate'' w]
    IntrinsicRepr _ _      -> error "TODO"
    RecursiveRepr _ _      -> error "TODO"
    FloatRepr _            -> dataTypeOpenTerm "Prelude.Float" []
    IEEEFloatRepr _        -> error "TODO"
    CharRepr               -> error "TODO"
    StringRepr             -> dataTypeOpenTerm "Prelude.String" []
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

instance TypeTranslate ValuePerm where
  typeTranslate ctx = \case

    ValPerm_True           -> flatOpenTerm UnitType

    ValPerm_Eq _           -> flatOpenTerm UnitType

    ValPerm_Or p1 p2       ->
      let t1 = typeTranslate ctx p1 in
      let t2 = typeTranslate ctx p2 in
      dataTypeOpenTerm "Prelude.Either" [t1, t2]

    ValPerm_Exists t p     ->
      let typA = typeTranslate'' t in
      dataTypeOpenTerm
      "Prelude.Sigma"
      [ typA
      , lambdaOpenTerm "a" typA (\ a -> typeTranslate (extend ctx (Const a)) p)
      ]

    ValPerm_Mu _           -> error "TODO"

    ValPerm_Var _index     -> error "TODO"

    ValPerm_Nat_Neq0       -> error "TODO"

    ValPerm_LLVMPtr _ ps _ ->
      -- TODO: Do we remove ValPerm_Eqs here?
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

instance TypeTranslate' (PermSpec EmptyCtx) where
  typeTranslate' ctx (PermSpec _ _ p) = typeTranslate ctx p

instance TypeTranslate' PermSet where
  typeTranslate' ctx ps =
    tupleTypeOpenTerm $ map (typeTranslate' ctx) (permSpecOfPermSet ps)
