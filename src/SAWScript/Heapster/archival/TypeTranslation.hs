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
  OpenTermCtxt,
  TypeTranslate(..),
  TypeTranslate'(..),
  TypeTranslate''(..),
  testTypeTranslation,
  typeTranslateDependentPair,
  typeTranslatePermSetSpec,
  ) where

import           Data.Functor.Const

import           Data.Parameterized.Context
import           Data.Parameterized.TraversableFC
import           Lang.Crucible.Types
import           SAWScript.CrucibleLLVM
import           SAWScript.Heapster.Permissions
import           SAWScript.Heapster.ValueTranslation
import           SAWScript.TopLevel
import           Verifier.SAW.OpenTerm
import           Verifier.SAW.Term.Functor

-- | The @TypeTranslate@ family of type classes captures translations from
-- permission types to SAW types.  The idea is to translate imperative
-- structures into a functional version of their shape.

type OpenTermCtxt ctx = Assignment (Const OpenTerm) ctx

class TypeTranslate (f :: Ctx k -> k' -> *) where
  typeTranslate :: OpenTermCtxt ctx -> f ctx a -> OpenTerm

class TypeTranslate' (f :: Ctx k -> *) where
  typeTranslate' :: OpenTermCtxt ctx -> f ctx -> OpenTerm

class TypeTranslate'' (d :: *) where
  typeTranslate'' :: d -> OpenTerm

instance TypeTranslate'' (TypeRepr a) where
  typeTranslate'' (AnyRepr)                = error "TypeTranslate: Any"
  typeTranslate'' (UnitRepr)               = unitTypeOpenTerm
  typeTranslate'' (BoolRepr)               = dataTypeOpenTerm "Prelude.Bool" []
  typeTranslate'' (NatRepr)                = dataTypeOpenTerm "Prelude.Nat" []
  typeTranslate'' (IntegerRepr)            = error "TypeTranslate: IntegerRepr"
  typeTranslate'' (RealValRepr)            = error "TypeTranslate: RealValRepr"
  typeTranslate'' (ComplexRealRepr)        = error "TypeTranslate: ComplexRealRepr"
  typeTranslate'' (BVRepr w)               = applyOpenTerm (globalOpenTerm "Prelude.bitvector") (valueTranslate'' w)
  typeTranslate'' (LLVMPointerRepr _)      = unitTypeOpenTerm
  typeTranslate'' (IntrinsicRepr _ _)      = error "TypeTranslate: IntrinsicRepr (other than LLVMPointerRepr)"
  typeTranslate'' (RecursiveRepr _ _)      = error "TypeTranslate: RecursiveRepr"
  typeTranslate'' (FloatRepr _)            = dataTypeOpenTerm "Prelude.Float" []
  typeTranslate'' (IEEEFloatRepr _)        = error "TypeTranslate: IEEEFloatRepr"
  typeTranslate'' (CharRepr)               = error "TypeTranslate: CharRepr"
  typeTranslate'' (StringRepr)             = dataTypeOpenTerm "Prelude.String" []
  typeTranslate'' (FunctionHandleRepr _ _) = error "TypeTranslate: FunctionHandleRepr"
  typeTranslate'' (MaybeRepr tp)           = applyOpenTerm (globalOpenTerm "Prelude.Maybe") (typeTranslate'' tp)
  typeTranslate'' (VectorRepr _)           = error "TypeTranslate: VectorRepr (can't map to Vec without size)"
  typeTranslate'' (StructRepr _)           = error "TypeTranslate: StructRepr"
  typeTranslate'' (VariantRepr _)          = error "TypeTranslate: VariantRepr"
  typeTranslate'' (ReferenceRepr _)        = error "TypeTranslate: ReferenceRepr"
  typeTranslate'' (WordMapRepr _ _)        = error "TypeTranslate: WordMapRepr"
  typeTranslate'' (StringMapRepr _)        = error "TypeTranslate: StringMapRepr"
  typeTranslate'' (SymbolicArrayRepr _ _)  = error "TypeTranslate: SymbolicArrayRepr"
  typeTranslate'' (SymbolicStructRepr _)   = error "TypeTranslate: SymbolicStructRepr"

instance TypeTranslate'' (CtxRepr ctx) where
  typeTranslate'' = tupleTypeOpenTerm . toListFC typeTranslate''

typeTranslateDependentPair ::
  OpenTermCtxt ctx ->
  TypeRepr tp ->
  ValuePerm (ctx ::> tp) a ->
  (OpenTerm, OpenTerm)
typeTranslateDependentPair ctx tp p =
  let typFst = typeTranslate'' tp in
  let typSnd = lambdaOpenTerm "fst" typFst (\ fstVar -> typeTranslate (extend ctx (Const fstVar)) p) in
  (typFst, typSnd)

instance TypeTranslate ValuePerm where
  typeTranslate ctx = \case

    ValPerm_True           -> flatOpenTerm UnitType

    ValPerm_Eq _           -> flatOpenTerm UnitType

    ValPerm_Or p1 p2       ->
      let t1 = typeTranslate ctx p1 in
      let t2 = typeTranslate ctx p2 in
      dataTypeOpenTerm "Prelude.Either" [t1, t2]

    ValPerm_Exists t p     ->
      let (typFst, typSnd) = typeTranslateDependentPair ctx t p in
      dataTypeOpenTerm "Prelude.Sigma" [typFst, typSnd]

    ValPerm_Mu _           -> error "TODO: TypeTranslate ValPerm_Mu"

    ValPerm_Var _index     -> error "TODO: TypeTranslate ValPerm_Var"

    ValPerm_Nat_Neq0       -> error "TODO: TypeTranslate ValPerm_Nat_Neq0"

    ValPerm_LLVMPtr _ ps _ ->
      tupleTypeOpenTerm (typeTranslate ctx <$> ps)

instance TypeTranslate LLVMShapePerm where
  typeTranslate ctx = \case

    LLVMFieldShapePerm (LLVMFieldPerm {..}) -> typeTranslate ctx llvmFieldPerm

    LLVMArrayShapePerm (LLVMArrayPerm {..}) ->
      let len = valueTranslate ctx llvmArrayLen in
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

typeTranslatePermSetSpec :: OpenTermCtxt ctx -> PermSetSpec EmptyCtx ctx -> OpenTerm
typeTranslatePermSetSpec ctx = tupleTypeOpenTerm . map (typeTranslate' ctx)
