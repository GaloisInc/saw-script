{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Turns 'SetupValue's back into 'MIRVal's.
module SAWCentral.Crucible.MIR.ResolveSetupValue
  ( MIRVal(..)
  , ppMIRVal
  , resolveSetupVal
  , typeOfSetupValue
  , lookupAllocIndex
  , toMIRType
  , resolveTypedTerm
  , resolveBoolTerm
  , resolveSAWPred
  , indexSeqTerm
  , indexMirVector
  , indexMirArray
  , usizeBvLit
  , equalValsPred
  , checkCompatibleTys
  , readMaybeType
  , doAlloc
  , doPointsTo
  , mirAdtToTy
  , findDefId
  , findDefIdEither
    -- * Slices
  , sliceElemTy
  , sliceRefTyToSliceInfo
    -- * Static items
  , findStatic
  , findStaticInitializer
  , findStaticVar
  , staticRefMux
    -- * Enum discriminants
  , getEnumVariantDiscr
  , testDiscriminantIsBV
  , variantIntIndex
    -- * Casts
  , containsCast
    -- * Types of errors
  , MIRTypeOfError(..)
  ) where

import           Control.Lens
import           Control.Monad (guard, unless, forM, foldM, zipWithM, zipWithM_)
import qualified Control.Monad.Catch as X
import           Control.Monad.IO.Class (MonadIO(..))
import           Control.Monad.Trans.Maybe (MaybeT(..))
import qualified Data.BitVector.Sized as BV
import qualified Data.Foldable as F
import qualified Data.Functor.Product as Functor
import           Data.Kind (Type)
import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.List.Extra as List (firstJust)
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some (Some(..))
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Parameterized.TraversableFC.WithIndex as FCI
import qualified Data.Text as Text
import           Data.Text (Text)
import qualified Data.Vector as V
import           Data.Void (absurd)
import           Numeric.Natural (Natural)
import qualified Prettyprinter as PP

import qualified Cryptol.Eval.Type as Cryptol (TValue(..), tValTy, evalValType)
import qualified Cryptol.TypeCheck.AST as Cryptol (Type, Schema(..))
import qualified Cryptol.Utils.PP as Cryptol (pp)
import Lang.Crucible.Simulator
  ( GlobalVar(..), RegValue, RegValue'(..), SymGlobalState
  , VariantBranch(..), injectVariant
  )
import Lang.Crucible.Simulator.RegMap (muxRegForType)
import Lang.Crucible.Types (TypeRepr(..))
import qualified Mir.DefId as Mir
import qualified Mir.FancyMuxTree as Mir
import qualified Mir.Generator as Mir
import qualified Mir.Intrinsics as Mir
import Mir.Intrinsics (MIR)
import qualified Mir.Mir as Mir
import qualified Mir.TransTy as Mir

import qualified What4.BaseTypes as W4
import qualified What4.Interface as W4
import qualified What4.Partial as W4

import CryptolSAWCore.Cryptol (importType, emptyEnv)
import SAWCore.SharedTerm
import SAWCoreWhat4.ReturnTrip
import CryptolSAWCore.TypedTerm

import SAWCentral.Crucible.Common
import qualified SAWCentral.Crucible.Common.MethodSpec as MS
import SAWCentral.Crucible.Common.MethodSpec (AllocIndex(..))
import SAWCentral.Crucible.Common.ResolveSetupValue (resolveBoolTerm, resolveBitvectorTerm)
import SAWCentral.Crucible.MIR.Setup.Value(mccUninterp)
import SAWCentral.Crucible.MIR.MethodSpecIR
import SAWCentral.Crucible.MIR.TypeShape
import SAWCentral.Panic

-- | A pair of a simulation-time MIR value ('RegValue') and its corresponding
-- type ('TypeShape'), where the @tp@ type parameter is closed over
-- existentially. SAW's MIR backend passes around 'MIRVal's at simulation time.
data MIRVal where
  MIRVal :: TypeShape tp -> RegValue Sym tp -> MIRVal

-- | Pretty-print a 'MIRVal'.
ppMIRVal ::
  forall ann.
  Sym ->
  MIRVal ->
  PP.Doc ann
ppMIRVal sym (MIRVal shp val) =
  case shp of
    UnitShape _ ->
      PP.pretty val
    PrimShape _ _ ->
      W4.printSymExpr val
    TupleShape _ elems -> prettyAggregate elems val
    ArrayShape _ _ elemSz shp' len -> prettyAggregateArray elemSz shp' len val
    StructShape _ _ fldShp ->
      PP.braces $ prettyAdtOrTuple fldShp val
    EnumShape _ _ variantShps _ _
      |  Ctx.Empty Ctx.:> RV _ Ctx.:> RV variants <- val
      -> case firstConcreteVariant variantShps variants of
           Just (Some (Functor.Pair fldShps fldVals)) ->
             PP.braces $ prettyAdtOrTuple fldShps fldVals
           Nothing ->
             "<symbolic enum>"
    TransparentShape _ shp' ->
      ppMIRVal sym $ MIRVal shp' val
    RefShape _ _ _ _  ->
      "<reference>"
    SliceShape _ _ _ _ ->
      "<slice>"
    FnPtrShape _ _ _ ->
      PP.viaShow val
  where
    commaList :: [PP.Doc ann] -> PP.Doc ann
    commaList []     = PP.emptyDoc
    commaList (x:xs) = x PP.<> PP.hcat (map (\y -> PP.comma PP.<+> y) xs)

    -- Return Just the first VariantBranch whose predicate is concretely equal
    -- to True. If none of the VariantBranches satisfy this property, then
    -- return Nothing.
    firstConcreteVariant ::
      Ctx.Assignment VariantShape ctx ->
      Ctx.Assignment (VariantBranch Sym) ctx ->
      Maybe (Some (Functor.Product
        (Ctx.Assignment FieldShape)
        (Ctx.Assignment (RegValue' Sym))))
    firstConcreteVariant variantShapes variantBranches =
      List.firstJust
        (\(Some (Functor.Pair (VariantShape fldShps) (VB branch))) ->
          case branch of
            W4.PE fldPred fldVals
              |  W4.asConstantPred fldPred == Just True
              -> Just $ Some $ Functor.Pair fldShps fldVals
              |  otherwise
              -> Nothing
            W4.Unassigned ->
              Nothing) $
      FC.toListFC Some $
      Ctx.zipWith Functor.Pair variantShapes variantBranches

    prettyAdtOrTuple ::
      forall ctx.
      Ctx.Assignment FieldShape ctx ->
      Ctx.Assignment (RegValue' Sym) ctx ->
      PP.Doc ann
    prettyAdtOrTuple fldShp fldVals =
      commaList $
      map (\(Some (Functor.Pair shp' (RV v))) -> prettyField shp' v) $
      FC.toListFC Some $
      Ctx.zipWith Functor.Pair fldShp fldVals

    prettyField ::
      forall tp.
      FieldShape tp ->
      RegValue Sym tp ->
      PP.Doc ann
    prettyField fldShp val' =
      case fldShp of
        OptField shp' ->
          ppMIRVal sym $ MIRVal shp' $
          readMaybeType sym "field" (shapeType shp') val'
        ReqField shp' ->
          ppMIRVal sym $ MIRVal shp' val'

    prettyAggregate ::
      [AgElemShape] ->
      Mir.MirAggregate Sym ->
      PP.Doc ann
    prettyAggregate elems (Mir.MirAggregate _sz m) =
      PP.braces $ commaList (map (prettyAgElem m) elems)

    prettyAggregateArray ::
      Word ->
      TypeShape tp ->
      Word ->
      Mir.MirAggregate Sym ->
      PP.Doc ann
    prettyAggregateArray elemSz elemShp len (Mir.MirAggregate _sz m) =
      let elems = arrayAgElemShapes elemSz elemShp len in
      PP.brackets $ commaList (map (prettyAgElem m) elems)

    prettyAgElem ::
      IntMap (Mir.MirAggregateEntry Sym) ->
      AgElemShape ->
      PP.Doc ann
    prettyAgElem m e@(AgElemShape off _sz _shp') =
      let valDoc = prettyAgElemValue m e in
      PP.viaShow off PP.<+> "->" PP.<+> valDoc

    prettyAgElemValue ::
      IntMap (Mir.MirAggregateEntry Sym) ->
      AgElemShape ->
      PP.Doc ann
    prettyAgElemValue m (AgElemShape off _sz shp') =
      case IntMap.lookup (fromIntegral off) m of
        Just (Mir.MirAggregateEntry _sz tpr rv)
          | Just Refl <- W4.testEquality tpr (shapeType shp') ->
              ppMIRVal sym $ MIRVal shp' $
              readMaybeType sym "elem" tpr rv
          | otherwise -> "<type mismatch>"
        Nothing -> "<unset>"


-- | Wrapper around `buildMirAggregate` for the case where the additional
-- values are `MIRVal`s.  This automatically checks that the `MIRVal`'s
-- `TypeShape` matches the shape of the `Mir.MirAggregateEntry` and just passes
-- the `MIRVal`'s inner `RegValue` to the callback.
buildMirAggregateWithVal ::
  (Monad m, MonadFail m) =>
  Sym ->
  [AgElemShape] ->
  [MIRVal] ->
  (forall tp. Word -> Word -> TypeShape tp -> RegValue Sym tp -> m (RegValue Sym tp)) ->
  m (Mir.MirAggregate Sym)
buildMirAggregateWithVal sym elems vals f =
  buildMirAggregate sym elems vals $
    \off sz shp (MIRVal shp' rv) ->
      case W4.testEquality shp shp' of
        Just Refl -> f off sz shp rv
        Nothing -> fail $ "buildMirAggregateWithVal: type mismatch at offset "
          ++ show off ++ ": expected " ++ show shp ++ ", but the MIRVal contained " ++ show shp'

buildMirAggregateArrayWithVal ::
  (Monad m, MonadFail m) =>
  Sym ->
  -- | Size of array element type
  Word ->
  -- | `TypeShape` of array element type
  TypeShape tp ->
  -- | Array length
  Word ->
  [MIRVal] ->
  (Word -> RegValue Sym tp -> m (RegValue Sym tp)) ->
  m (Mir.MirAggregate Sym)
buildMirAggregateArrayWithVal sym elemSz elemShp len vals f =
  buildMirAggregateArray sym elemSz elemShp len vals $
    \off (MIRVal shp rv) ->
      case W4.testEquality elemShp shp of
        Just Refl -> f off rv
        Nothing -> fail $ "buildMirAggregateArrayWithVal: type mismatch at offset "
          ++ show off ++ ": expected " ++ show elemShp ++ ", but the MIRVal contained " ++ show shp


type SetupValue = MS.SetupValue MIR

data MIRTypeOfError
  = MIRPolymorphicType Cryptol.Schema
  | MIRNonRepresentableType Cryptol.Type ToMIRTypeErr
  | MIRInvalidTypedTerm TypedTermType
  | MIRInvalidIdentifier String
  | MIRStaticNotFound Mir.DefId
  | MIRSliceNonReference Mir.Ty
  | MIRSliceNonArrayReference Mir.Ty
  | MIRSliceWrongTy Mir.Ty
  | MIRStrSliceNonU8Array Mir.Ty
  | MIRMuxNonBoolCondition Mir.Ty
  | MIRMuxDifferentBranchTypes Mir.Ty Mir.Ty
  | MIRCastNonRawPtr Mir.Ty
  | MIRIndexOutOfBounds
      Mir.Ty -- ^ sequence type
      Int    -- ^ sequence length
      Int    -- ^ attempted index
  | MIRIndexWrongTy MirIndexingMode Mir.Ty

instance Show MIRTypeOfError where
  show (MIRPolymorphicType s) =
    unlines
    [ "Expected monomorphic term"
    , "instead got:"
    , show (Cryptol.pp s)
    ]
  show (MIRNonRepresentableType ty err) =
    unlines
    [ "Type not representable in MIR:"
    , show (Cryptol.pp ty)
    , toMIRTypeErrToString err
    ]
  show (MIRInvalidTypedTerm tp) =
    unlines
    [ "Expected typed term with Cryptol-representable type, but got"
    , show (ppTypedTermType tp)
    ]
  show (MIRInvalidIdentifier errMsg) =
    errMsg
  show (MIRStaticNotFound did) =
    staticNotFoundErr did
  show (MIRSliceNonReference ty) =
    unlines
    [ "Expected a reference, but got"
    , show (PP.pretty ty)
    ]
  show (MIRSliceNonArrayReference ty) =
    unlines
    [ "Expected a reference to an array, but got"
    , show (PP.pretty ty)
    ]
  show (MIRSliceWrongTy ty) =
    unlines
    [ "Expected a slice type, but got"
    , show (PP.pretty ty)
    ]
  show (MIRStrSliceNonU8Array ty) =
    unlines
    [ "Expected a value of type &[u8; <length>], but got"
    , show (PP.pretty ty)
    ]
  show (MIRMuxNonBoolCondition ty) =
    unlines
    [ "Expected a bool-typed condition in a mux, but got"
    , show (PP.pretty ty)
    ]
  show (MIRMuxDifferentBranchTypes tTy fTy) =
    unlines
    [ "Mismatch in mux branch types:"
    , "True  branch type: " ++ show (PP.pretty tTy)
    , "False branch type: " ++ show (PP.pretty fTy)
    ]
  show (MIRCastNonRawPtr ty) =
    unlines
    [ "Casting only works on raw pointers"
    , "Expected a raw pointer (*const T or *mut T), but got"
    , show (PP.pretty ty)
    ]
  show (MIRIndexOutOfBounds xsTy len i) =
    unlines
    [ "Index out of bounds:"
    , "Indexing into: " ++ show (PP.pretty xsTy)
    , "with length:   " ++ show len
    , "at index:      " ++ show i
    ]
  show (MIRIndexWrongTy ixMode ty) =
    unlines
    [ "Expected " ++ expected ++ ", but got"
    , show (PP.pretty ty)
    ]
    where
      expected =
        case ixMode of
          MirIndexIntoVal -> "an array"
          MirIndexIntoRef -> "a reference (or raw pointer) to an array"
          MirIndexOffsetRef -> "a reference or raw pointer"

staticNotFoundErr :: Mir.DefId -> String
staticNotFoundErr did =
  unlines
  [ "Could not find static named:"
  , show did
  ]

instance X.Exception MIRTypeOfError

typeOfSetupValue ::
  forall m.
  X.MonadThrow m =>
  MIRCrucibleContext ->
  Map AllocIndex (Some MirAllocSpec) ->
  Map AllocIndex Text ->
  SetupValue ->
  m Mir.Ty
typeOfSetupValue mcc env nameEnv val =
  case val of
    MS.SetupVar i ->
      case Map.lookup i env of
        Nothing ->
           panic "MIRSetup (in typeOfSetupValue)" [
               "Unresolved prestate variable: " <> Text.pack (show i)
           ]
        Just (Some alloc) ->
          pure $ ptrKindToTy (alloc^.maPtrKind) (alloc^.maMirType) (alloc^.maMutbl)
    MS.SetupTerm tt ->
      typeOfTypedTerm tt
    MS.SetupArray elemTy vs ->
      pure $ Mir.TyArray elemTy (length vs)
    MS.SetupStruct adt _ ->
      pure $ mirAdtToTy adt
    MS.SetupEnum enum_ ->
      case enum_ of
        MirSetupEnumVariant adt _ _ _ ->
          pure $ mirAdtToTy adt
        MirSetupEnumSymbolic adt _ _ ->
          pure $ mirAdtToTy adt
    MS.SetupTuple () vals -> do
      tys <- traverse (typeOfSetupValue mcc env nameEnv) vals
      pure $ Mir.TyTuple tys
    MS.SetupGlobal () name ->
      staticTyRef <$> findStatic cs name
    MS.SetupGlobalInitializer () name -> do
      static <- findStatic cs name
      pure $ static ^. Mir.sTy
    MS.SetupSlice slice ->
      case slice of
        MirSetupSliceRaw{} ->
          panic "MIRSetup (in typeOfSetupValue)" [
              "MirSetupSliceRaw not yet implemented"
          ]
        MirSetupSlice sliceInfo arrRef ->
          typeOfSliceFromArrayRef sliceInfo arrRef
        MirSetupSliceRange sliceInfo arrRef _ _ ->
          typeOfSliceFromArrayRef sliceInfo arrRef
    MS.SetupMux () c t f -> do
      cTy <- typeOfTypedTerm c
      unless (cTy == Mir.TyBool) $
        X.throwM $ MIRMuxNonBoolCondition cTy
      tTy <- typeOfSetupValue mcc env nameEnv t
      fTy <- typeOfSetupValue mcc env nameEnv f
      unless (checkCompatibleTys tTy fTy) $
        X.throwM $ MIRMuxDifferentBranchTypes tTy fTy
      pure tTy
    MS.SetupCast newPointeeTy oldPtr -> do
      -- Make sure the cast is valid
      oldPtrTy <- typeOfSetupValue mcc env nameEnv oldPtr
      case oldPtrTy of
        Mir.TyRawPtr _ mutbl ->
          pure $ Mir.TyRawPtr newPointeeTy mutbl
        _ -> X.throwM $ MIRCastNonRawPtr oldPtrTy

    MS.SetupElem ixMode xs i -> do
      xsTy <- typeOfSetupValue mcc env nameEnv xs
      let boundsCheck len res
            | i >= 0 && i < len = pure res
            | otherwise = X.throwM $ MIRIndexOutOfBounds xsTy len i
          throwWrongTy = X.throwM $ MIRIndexWrongTy ixMode xsTy
      case ixMode of
        MirIndexIntoVal ->
          case xsTy of
            Mir.TyArray elemTy len -> boundsCheck len elemTy
            _ -> throwWrongTy
        MirIndexIntoRef ->
          case tyToShape col xsTy of
            Some (RefShape ptrTy (Mir.TyArray elemTy len) mutbl _) ->
              boundsCheck len $ ptrKindToTy (tyToPtrKind ptrTy) elemTy mutbl
            _ -> throwWrongTy
        MirIndexOffsetRef ->
          panic "MIRSetup (in typeOfSetupValue)"
            ["MirIndexOffsetRef not yet implemented"]
    MS.SetupField _ _ _ ->
      panic "MIRSetup (in typeOfSetupValue)" ["fields not yet implemented"]

    MS.SetupNull empty                -> absurd empty
    MS.SetupUnion empty _ _           -> absurd empty
  where
    cs = mcc ^. mccRustModule . Mir.rmCS
    col = cs ^. Mir.collection

    typeOfSliceFromArrayRef :: MirSliceInfo -> SetupValue -> m Mir.Ty
    typeOfSliceFromArrayRef sliceInfo arrRef = do
      arrRefTy <- typeOfSetupValue mcc env nameEnv arrRef
      case arrRefTy of
        Mir.TyRef arrTy mut -> do
          (sliceTy, _elemTy, _len) <- arrayToSliceTys sliceInfo mut arrTy
          pure $ Mir.TyRef sliceTy mut
        _ ->
          X.throwM $ MIRSliceNonReference arrRefTy

    typeOfTypedTerm :: TypedTerm -> m Mir.Ty
    typeOfTypedTerm tt =
      case ttType tt of
        TypedTermSchema (Cryptol.Forall [] [] ty) ->
          case toMIRType (Cryptol.evalValType mempty ty) of
            Left err -> X.throwM (MIRNonRepresentableType ty err)
            Right mirTy -> return mirTy
        TypedTermSchema s -> X.throwM (MIRPolymorphicType s)
        tp -> X.throwM (MIRInvalidTypedTerm tp)

lookupAllocIndex :: Map AllocIndex a -> AllocIndex -> a
lookupAllocIndex env i =
  case Map.lookup i env of
    Just x -> x
    Nothing ->
        panic "MIRSetup (in lookupAllocIndex)" [
            "Unresolved prestate variable: " <> Text.pack (show i)
        ]

-- | Translate a SetupValue into a Crucible MIR value, resolving
-- references
resolveSetupVal ::
  MIRCrucibleContext ->
  Map AllocIndex (Some (MirPointer Sym)) ->
  Map AllocIndex (Some MirAllocSpec) ->
  Map AllocIndex Text ->
  SetupValue ->
  IO MIRVal
resolveSetupVal mcc env tyenv nameEnv val =
  mccWithBackend mcc $ \bak ->
  let sym = backendGetSym bak in
  case val of
    MS.SetupVar i -> do
      Some ptr <- pure $ lookupAllocIndex env i
      let pointeeType = ptr ^. mpMirType
      pure $ MIRVal (RefShape
                        (ptrKindToTy (ptr ^. mpKind) pointeeType (ptr ^. mpMutbl))
                        pointeeType
                        (ptr ^. mpMutbl)
                        (ptr ^. mpType))
                    (ptr ^. mpRef)
    MS.SetupTerm tm -> resolveTypedTerm mcc tm
    MS.SetupNull empty                -> absurd empty
    MS.SetupStruct adt flds ->
      case adt of
        _ | adt ^. Mir.adtReprTransparent,
            Just i <- Mir.findReprTransparentField col adt,
            Just fld <- flds ^? ix i ->
          resolveTransparentSetupVal adt fld
        Mir.Adt nm Mir.Struct variants _ _ _ _ -> do
          -- First, retrieve the struct variant.
          variant <-
            case variants of
              [variant] ->
                pure variant
              _ ->
                panic "resolveSetupVal" [
                    "Encountered struct Adt with " <>
                        Text.pack (show (length variants)) <>
                        " variants: ",
                    "   " <> Text.pack (show nm)
                ]

          -- Next, resolve the field values and check that they have the
          -- expected types.
          flds' <- traverse (resolveSetupVal mcc env tyenv nameEnv) flds
          let expectedFlds = variant ^. Mir.vfields
          let actualFldTys = map (\(MIRVal shp _) -> shapeMirTy shp) flds'
          checkFields nm "Struct" "struct fields" expectedFlds actualFldTys

          -- Finally, construct a MIRVal of the appropriate shape.
          Some (Functor.Pair fldShpAssn valAssn) <-
            pure $ variantFieldsToAssns sym flds'
          let structShp = StructShape (mirAdtToTy adt) actualFldTys fldShpAssn
          pure $ MIRVal structShp valAssn
        Mir.Adt nm (Mir.Enum _) _ _ _ _ _ ->
          panic "resolveSetupVal" [
              "Expected struct type, received enum: " <> Text.pack (show nm)
          ]
        Mir.Adt nm Mir.Union _ _ _ _ _ ->
          panic "resolveSetupVal" [
              "Expected struct type, received union: " <> Text.pack (show nm)
          ]
    MS.SetupEnum enum_ ->
      case enum_ of
        MirSetupEnumVariant adt variant variantIdxInt flds ->
          case adt of
            _ | adt ^. Mir.adtReprTransparent,
                Just i <- Mir.findReprTransparentField col adt,
                Just fld <- flds ^? ix i -> do
              resolveTransparentSetupVal adt fld
            Mir.Adt nm (Mir.Enum discrTp) variants _ _ _ _ -> do
              -- Resolve the field values and check that they have the expected
              -- types.
              flds' <- traverse (resolveSetupVal mcc env tyenv nameEnv) flds
              let expectedFlds = variant ^. Mir.vfields
              let actualFldTys = map (\(MIRVal shp _) -> shapeMirTy shp) flds'
              checkFields
                nm
                "Enum"
                ("fields in enum variant " ++ show (variant ^. Mir.vname))
                expectedFlds
                actualFldTys

              -- Ensure that the discriminant has an integral type and build
              -- a symbolic bitvector from it.
              Some discrTpr <- case Mir.tyToRepr col discrTp of
                Left err -> panic "resolveSetupVal" ["Unsupported type", Text.pack err]
                Right x -> return x
              let discrShp = tyToShapeEq col discrTp discrTpr
              IsBVShape _ discrW <- pure $ testDiscriminantIsBV discrShp
              let discr = getEnumVariantDiscr variant
              discrVal <- W4.bvLit sym discrW $ BV.mkBV discrW discr

              -- Construct an EnumShape and RustEnumRepr. This requires
              -- processing /all/ variants, not just the particular variant that
              -- we are building.
              SomeEnumShape expectedVariantShps enumShp <- pure $
                someEnumShape adt discrTp discrShp variants
              let variantTprs =
                    FC.fmapFC variantShapeType expectedVariantShps

              -- Construct the VariantShape of the particular variant that we
              -- are building.
              Some variantIdx <- pure $
                variantIntIndex nm variantIdxInt $
                Ctx.size expectedVariantShps
              VariantShape expectedFldAssn <-
                pure $ expectedVariantShps Ctx.! variantIdx

              -- Check that the actual field values match the expected types.
              Some (Functor.Pair actualFldAssn actualValAssn) <-
                pure $ variantFieldsToAssns sym flds'
              Refl <-
                case W4.testEquality expectedFldAssn actualFldAssn of
                  Just r -> pure r
                  Nothing ->
                    panic "resolveSetupVal" [
                        "Enum field shape mismatch",
                        "Expected: " <> Text.pack (show expectedFldAssn),
                        "Actual: " <> Text.pack (show actualFldAssn)
                    ]

              -- Finally, construct a MIRVal.
              let enumVal =
                    Ctx.empty
                      Ctx.:> RV discrVal
                      Ctx.:> RV (injectVariant sym variantTprs variantIdx actualValAssn)
              pure $ MIRVal enumShp enumVal
            Mir.Adt nm Mir.Struct _ _ _ _ _ ->
              panic "resolveSetupVal" [
                  "Expected enum type, received struct: " <> Text.pack (show nm)
              ]
            Mir.Adt nm Mir.Union _ _ _ _ _ ->
              panic "resolveSetupVal" [
                  "Expected enum type, received union: " <> Text.pack (show nm)
              ]
        -- See Note [Symbolic enums] in SAWCentral.Crucible.MIR.Setup.Value for
        -- more information on the approach used to resolve symbolic enum
        -- values.
        MirSetupEnumSymbolic adt discr variantFlds ->
          case adt of
            _ | adt ^. Mir.adtReprTransparent ->
              -- `repr(transparent)` enum values use MirSetupEnumVariant rather
              -- than MirSetupEnumSymbolic. See the Haddocks for
              -- MirSetupEnumSymbolic for an explanation.
              panic "resolveSetupVal" [
                  "Symbolic enum of type " <> Text.pack (show (adt ^. Mir.adtname)),
                  "that uses MirSetupEnumSymbolic rather than MirSetupEnumVariant"
              ]
            Mir.Adt nm (Mir.Enum discrTp) variants _ _ _ _ -> do
              -- Resolve the discriminant value and ensure that it has an
              -- integral type.
              MIRVal discrShp discrVal <- resolveSetupVal mcc env tyenv nameEnv discr
              IsBVShape _ discrW <- pure $ testDiscriminantIsBV discrShp

              -- Resolve the field values in each possible variant and check
              -- that they have the expected types.
              variantFlds' <-
                zipWithM
                  (\variant flds -> do
                    let variantDiscr = getEnumVariantDiscr variant
                    variantDiscrBV <- W4.bvLit sym discrW $ BV.mkBV discrW variantDiscr
                    branch <- W4.bvEq sym variantDiscrBV discrVal
                    flds' <- traverse (resolveSetupVal mcc env tyenv nameEnv) flds
                    let expectedFlds = variant ^. Mir.vfields
                    let actualFldTys = map (\(MIRVal shp _) -> shapeMirTy shp) flds'
                    checkFields
                      nm
                      "Enum"
                      ("fields in enum variant " ++ show (variant ^. Mir.vname))
                      expectedFlds
                      actualFldTys
                    Some (Functor.Pair fldShpAssn valAssn) <-
                      pure $ variantFieldsToAssns sym flds'
                    pure $ Some
                         $ Functor.Pair
                             (VariantShape fldShpAssn)
                             (VB (W4.PE branch valAssn)))
                  variants
                  variantFlds
              Some variantBranchAssn <- pure $ Ctx.fromList variantFlds'
              let (actualVariantShps, branchAssn) =
                    Ctx.unzip variantBranchAssn

              -- Construct an EnumShape.
              SomeEnumShape expectedVariantShps enumShp <- pure $
                someEnumShape adt discrTp discrShp variants

              -- Check that the actual variant types match the expected types.
              Refl <-
                case W4.testEquality expectedVariantShps actualVariantShps of
                  Just r -> pure r
                  Nothing ->
                    panic "resolveSetupVal" [
                        "Enum variant shape mismatch",
                        "Expected: " <> Text.pack (show expectedVariantShps),
                        "Actual: " <> Text.pack (show actualVariantShps)
                    ]

              -- Finally, construct a MIRVal.
              let enumVal =
                    Ctx.empty
                      Ctx.:> RV discrVal
                      Ctx.:> RV branchAssn
              pure $ MIRVal enumShp enumVal
            Mir.Adt nm Mir.Struct _ _ _ _ _ ->
              panic "resolveSetupVal" [
                  "Expected enum type, received struct: " <> Text.pack (show nm)
              ]
            Mir.Adt nm Mir.Union _ _ _ _ _ ->
              panic "resolveSetupVal" [
                  "Expected enum type, received union: " <> Text.pack (show nm)
              ]
    MS.SetupTuple () [] -> pure $ MIRVal (UnitShape (Mir.TyTuple [])) ()
    MS.SetupTuple () flds -> do
      flds' <- traverse (resolveSetupVal mcc env tyenv nameEnv) flds
      let fldMirTys = map (\(MIRVal shp _) -> shapeMirTy shp) flds'
      -- TODO: get proper tuple layout
      let elems = [AgElemShape i 1 shp | (i, MIRVal shp _) <- zip [0..] flds']
      ag <- buildMirAggregateWithVal sym elems flds' $ \_off _sz _shp rv -> return rv
      let tupleShp = TupleShape (Mir.TyTuple fldMirTys) elems
      pure $ MIRVal tupleShp ag
    MS.SetupSlice slice ->
      case slice of
        MirSetupSliceRaw{} ->
          panic "resolveSetupVal" ["MirSetupSliceRaw not yet implemented"]
        MirSetupSlice sliceInfo arrRef -> do
          SetupSliceFromArrayRef sliceShp refVal len <-
            resolveSetupSliceFromArrayRef bak sliceInfo arrRef
          lenVal <- usizeBvLit sym len
          pure $ MIRVal sliceShp (Ctx.Empty Ctx.:> RV refVal Ctx.:> RV lenVal)
        MirSetupSliceRange sliceInfo arrRef start end -> do
          unless (start <= end) $
            fail $ "slice index starts at " ++ show start
                ++ " but ends at " ++ show end
          SetupSliceFromArrayRef sliceShp refVal0 len <-
            resolveSetupSliceFromArrayRef bak sliceInfo arrRef
          unless (end <= len) $
            fail $ "range end index " ++ show end
                ++ " out of range for slice of length " ++ show len
          startBV <- usizeBvLit sym start
          refVal1 <- Mir.mirRef_offsetIO bak iTypes refVal0 startBV
          lenVal <- usizeBvLit sym $ end - start
          pure $ MIRVal sliceShp (Ctx.Empty Ctx.:> RV refVal1 Ctx.:> RV lenVal)
    MS.SetupArray elemTy vs -> do
      vals <- mapM (resolveSetupVal mcc env tyenv nameEnv) vs

      Some (shp :: TypeShape tp) <-
        pure $ tyToShape col elemTy

      let elemSz = 1      -- TODO: hardcoded size=1
      let len = length vals

      ag <- buildMirAggregateArrayWithVal sym elemSz shp (fromIntegral len) vals $
        \_off rv -> return rv
      let arrShp = ArrayShape (Mir.TyArray elemTy len) elemTy elemSz shp (fromIntegral len)
      return $ MIRVal arrShp ag
    MS.SetupElem ixMode xs i -> do
      MIRVal xsShp xsVal <- resolveSetupVal mcc env tyenv nameEnv xs
      case ixMode of
        MirIndexIntoVal
          | ArrayShape arrTy@(Mir.TyArray _ _) _ elemSz elemShp len <- xsShp -> do
            if i >= 0 && i < fromIntegral len
              then do
                res <- runMaybeT $ indexMirArray sym i elemSz elemShp xsVal
                case res of
                  Just mv -> pure mv
                  -- FIXME: use a different error kind here (this is a type
                  -- or size mismatch error; bounds are checked elsewhere)
                  Nothing -> X.throwM $ MIRIndexOutOfBounds arrTy (fromIntegral len) i
              else
                X.throwM $ MIRIndexOutOfBounds arrTy (fromIntegral len) i
        MirIndexIntoRef
          | RefShape ptrTy
                     (Mir.TyArray elemTy len)
                     mutbl
                     Mir.MirAggregateRepr
              <- xsShp ->
            if i >= 0 && i < len
              then do
                let elemPtrTy = ptrKindToTy (tyToPtrKind ptrTy) elemTy mutbl
                Some elemTpr <- case Mir.tyToRepr col elemTy of
                  Left err -> panic "resolveSetupValue" ["Unsupported type", Text.pack err]
                  Right x -> return x
                i_sym <- usizeBvLit sym i
                MIRVal (RefShape elemPtrTy elemTy mutbl elemTpr) <$>
                  Mir.subindexMirRefIO bak iTypes elemTpr xsVal i_sym
              else
                X.throwM $ MIRIndexOutOfBounds ptrTy len i
        MirIndexOffsetRef ->
          panic "resolveSetupValue" ["MirIndexOffsetRef not yet implemented"]
        _ ->
          X.throwM $ MIRIndexWrongTy ixMode (shapeMirTy xsShp)
    MS.SetupField _ _ _               -> panic "resolveSetupValue" ["fields not yet implemented"]
    MS.SetupCast newPointeeTy oldPtrSetupVal -> do
      MIRVal oldShp ref <- resolveSetupVal mcc env tyenv nameEnv oldPtrSetupVal
      case oldShp of
        RefShape (Mir.TyRawPtr _ _) _ mutbl _ -> do
          let newPtrTy = Mir.TyRawPtr newPointeeTy mutbl
          Some newPointeeTpr <- case Mir.tyToRepr col newPointeeTy of
            Left err -> panic "resolveSetupValue" ["Unsupported type", Text.pack err]
            Right x -> return x
          -- Due to the cast, here the type in the RefShape does not necessarily
          -- match the actual type that the ref is pointing to!
          --
          -- See Note [Raw pointer casts] in SAWCentral.Crucible.MIR.Setup.Value
          -- for more info.
          pure $ MIRVal (RefShape newPtrTy newPointeeTy mutbl newPointeeTpr) ref
        _ ->
          X.throwM $ MIRCastNonRawPtr $ shapeMirTy oldShp
    MS.SetupUnion empty _ _           -> absurd empty
    MS.SetupGlobal () name -> do
      static <- findStatic cs name
      Mir.StaticVar gv <- findStaticVar cs (static ^. Mir.sName)
      let sMut = staticMutability static
          sTy  = static ^. Mir.sTy
      pure $ MIRVal (RefShape (staticTyRef static) sTy sMut (globalType gv))
           $ staticRefMux sym gv
    MS.SetupGlobalInitializer () name -> do
      static <- findStatic cs name
      findStaticInitializer mcc static
    MS.SetupMux () c t f -> do
      MIRVal cShp cVal <- resolveTypedTerm mcc c
      let cTy = shapeMirTy cShp
      let cTpr = shapeType cShp
      Refl <-
        case W4.testEquality cTpr BoolRepr of
          Just r -> pure r
          Nothing -> X.throwM $ MIRMuxNonBoolCondition cTy

      MIRVal tShp tVal <- resolveSetupVal mcc env tyenv nameEnv t
      let tTy = shapeMirTy tShp
      let tTpr = shapeType tShp
      MIRVal fShp fVal <- resolveSetupVal mcc env tyenv nameEnv f
      let fTy = shapeMirTy fShp
      let fTpr = shapeType fShp
      Refl <-
        case W4.testEquality tTpr fTpr of
          Just r -> pure r
          Nothing -> X.throwM $ MIRMuxDifferentBranchTypes tTy fTy

      let muxShp = tShp
      let muxTpr = tTpr
      muxVal <- muxRegForType sym iTypes muxTpr cVal tVal fVal
      pure $ MIRVal muxShp muxVal
  where
    cs  = mcc ^. mccRustModule . Mir.rmCS
    col = cs ^. Mir.collection
    iTypes = mcc ^. mccIntrinsicTypes

    -- Perform a light amount of typechecking on the fields in a struct or enum
    -- variant. This ensures that the variant receives the expected number of
    -- types and that the types of each field match.
    checkFields ::
      Mir.DefId {- The struct or enum name. (Only used for error messages.) -} ->
      String {- "Struct" or "Enum". (Only used for error messages.) -} ->
      String {- What type of fields are we checking?
                (Only used for error messages.) -} ->
      [Mir.Field] {- The expected fields. -} ->
      [Mir.Ty] {- The actual field types. -} ->
      IO ()
    checkFields adtNm what fieldDiscr expectedFlds actualFldTys = do
      let expectedFldsNum = length expectedFlds
      let actualFldsNum = length actualFldTys
      unless (expectedFldsNum == actualFldsNum) $
        fail $ unlines
          [ "Mismatch in number of " ++ fieldDiscr
          , what ++ " name: " ++ show adtNm
          , "Expected number of fields: " ++ show expectedFldsNum
          , "Actual number of fields:   " ++ show actualFldsNum
          ]
      zipWithM_
        (\expectedFld actualFldTy ->
          let expectedFldTy = expectedFld ^. Mir.fty in
          let expectedFldName = expectedFld ^. Mir.fName in
          unless (checkCompatibleTys expectedFldTy actualFldTy) $
            fail $ unlines
              [ what ++ " field type mismatch"
              , "Field name: " ++ show expectedFldName
              , "Expected type: " ++ show (PP.pretty expectedFldTy)
              , "Given type:    " ++ show (PP.pretty actualFldTy)
              ])
        expectedFlds
        actualFldTys

    -- Construct the shape for an enum, returning it as a 'SomeEnumShape' value.
    someEnumShape ::
      Mir.Adt {- The enum type -} ->
      Mir.Ty {- The discriminant's MIR type -} ->
      TypeShape discrTp {- The discriminant's TypeShape -} ->
      [Mir.Variant] {- The enum's variants -} ->
      SomeEnumShape discrTp
    someEnumShape adt discrTp discrShp variants
      | let variantTys =
              map (\v -> v ^.. Mir.vfields . each . Mir.fty) variants
      , Some variantShps <-
          Ctx.fromList $
          map (\fldTys ->
                case Ctx.fromList $
                     map
                       (\ty ->
                         case tyToShape col ty of
                           Some shp ->
                             if Mir.canInitialize col ty
                             then Some $ ReqField shp
                             else Some $ OptField shp)
                       fldTys of
                  Some fldAssn -> Some $ VariantShape fldAssn)
              variantTys
      , let enumShp =
              EnumShape
                (mirAdtToTy adt) variantTys
                variantShps discrTp discrShp
      = SomeEnumShape variantShps enumShp

    -- Resolve parts of a slice that are shared in common between
    -- 'MirSetupSlice' and 'MirSetupSliceRange'.
    resolveSetupSliceFromArrayRef ::
      OnlineSolver solver =>
      Backend solver ->
      MirSliceInfo ->
      SetupValue ->
      IO SetupSliceFromArrayRef
    resolveSetupSliceFromArrayRef bak sliceInfo arrRef = do
      let sym = backendGetSym bak
      MIRVal arrRefShp arrRefVal <- resolveSetupVal mcc env tyenv nameEnv arrRef
      case arrRefShp of
        RefShape _ arrTy mut Mir.MirAggregateRepr -> do
          (sliceTy, elemTy, len) <- arrayToSliceTys sliceInfo mut arrTy
          Some elemTpr <- case Mir.tyToRepr col elemTy of
            Left err -> panic "resolveSetupSliceFromArrayRef" ["Unsupported type", Text.pack err]
            Right x -> return x
          zeroBV <- usizeBvLit sym 0
          refVal <- Mir.subindexMirRefIO bak iTypes elemTpr arrRefVal zeroBV
          let sliceShp = SliceShape (Mir.TyRef sliceTy mut) elemTy mut elemTpr
          pure $ SetupSliceFromArrayRef sliceShp refVal len
        _ -> X.throwM $ MIRSliceNonReference $ shapeMirTy arrRefShp

    -- Resolve a transparent struct or enum value.
    resolveTransparentSetupVal :: Mir.Adt -> SetupValue -> IO MIRVal
    resolveTransparentSetupVal adt fld = do
      MIRVal shp fld' <- resolveSetupVal mcc env tyenv nameEnv fld
      pure $ MIRVal (TransparentShape (mirAdtToTy adt) shp) fld'

    -- Given the list of fields in a struct or enum variant, construct two
    -- Assignments, where the first Assignment consists of each field's type,
    -- and the second assignment consists of each field's value.
    variantFieldsToAssns ::
      Sym ->
      [MIRVal] ->
      Some (Functor.Product
             (Ctx.Assignment FieldShape)
             (Ctx.Assignment (RegValue' Sym)))
    variantFieldsToAssns sym flds
      | Some fldValAssn <- someFldValAssn
      , (fldAssn, valAssn) <- Ctx.unzip fldValAssn
      = Some $ Functor.Pair fldAssn valAssn
      where
        someFldValAssn ::
          Some (Ctx.Assignment (Functor.Product FieldShape (RegValue' Sym)))
        someFldValAssn =
          Ctx.fromList $
          map (\(MIRVal shp v) ->
                if Mir.canInitialize col (shapeMirTy shp)
                then Some $ Functor.Pair (ReqField shp) (RV v)
                else Some $ Functor.Pair (OptField shp) (RV (W4.justPartExpr sym v)))
              flds

-- | An intermediate data structure that is only used by
-- 'someEnumShape'. This existentially closes over the @variantsCtx@ type
-- parameter.
data SomeEnumShape discrTp where
  SomeEnumShape ::
    Ctx.Assignment VariantShape variantsCtx ->
    TypeShape (Mir.RustEnumType discrTp variantsCtx) ->
    SomeEnumShape discrTp

-- | An intermediate data structure that is only used by
-- 'resolveSetupSliceFromArrayRef'.
data SetupSliceFromArrayRef where
  SetupSliceFromArrayRef ::
    TypeShape Mir.MirSlice {- ^ The overall shape of the slice -} ->
    Mir.MirReferenceMux Sym {- ^ The reference to the array -} ->
    Int {- ^ The array length -} ->
    SetupSliceFromArrayRef

resolveTypedTerm ::
  MIRCrucibleContext ->
  TypedTerm       ->
  IO MIRVal
resolveTypedTerm mcc tm =
  case ttType tm of
    TypedTermSchema (Cryptol.Forall [] [] ty) ->
      resolveSAWTerm mcc (Cryptol.evalValType mempty ty) (ttTerm tm)
    tp -> fail $ unlines
            [ "resolveTypedTerm: expected monomorphic term"
            , "but got a term of type"
            , show (ppTypedTermType tp)
            ]

resolveSAWPred ::
  MIRCrucibleContext ->
  Term ->
  IO (W4.Pred Sym)
resolveSAWPred cc = resolveBoolTerm (cc ^. mccSym) (cc ^. mccUninterp)

resolveSAWTerm ::
  MIRCrucibleContext ->
  Cryptol.TValue ->
  Term ->
  IO MIRVal
resolveSAWTerm mcc tp tm =
  case tp of
    Cryptol.TVBit ->
      do b <- resolveBoolTerm sym (mcc ^. mccUninterp) tm
         pure $ MIRVal (PrimShape Mir.TyBool W4.BaseBoolRepr) b
    Cryptol.TVInteger ->
      fail "resolveSAWTerm: unimplemented type Integer (FIXME)"
    Cryptol.TVIntMod _ ->
      fail "resolveSAWTerm: unimplemented type Z n (FIXME)"
    Cryptol.TVFloat{} ->
      fail "resolveSAWTerm: unimplemented type Float e p (FIXME)"
    Cryptol.TVArray{} ->
      fail "resolveSAWTerm: unimplemented type Array a b (FIXME)"
    Cryptol.TVRational ->
      fail "resolveSAWTerm: unimplemented type Rational (FIXME)"
    Cryptol.TVSeq sz Cryptol.TVBit ->
      case sz of
        8   -> bv_term Mir.B8   $ W4.knownNat @8
        16  -> bv_term Mir.B16  $ W4.knownNat @16
        32  -> bv_term Mir.B32  $ W4.knownNat @32
        64  -> bv_term Mir.B64  $ W4.knownNat @64
        128 -> bv_term Mir.B128 $ W4.knownNat @128
        _   -> fail ("Invalid bitvector width: " ++ show sz)
      where
        bv_term :: forall w. 1 W4.<= w
                => Mir.BaseSize -> W4.NatRepr w -> IO MIRVal
        bv_term b n =
         MIRVal (PrimShape (Mir.TyUint b) (W4.BaseBVRepr n)) <$>
         resolveBitvectorTerm sym (mcc ^. mccUninterp) n tm
    Cryptol.TVSeq sz tp' -> do
      doIndex <- indexSeqTerm sym (sz, tp') tm
      case toMIRType tp' of
        Left e -> fail ("In resolveSAWTerm: " ++ toMIRTypeErrToString e)
        Right mirTy -> do
          Some (shp :: TypeShape tp) <- pure $ tyToShape col mirTy

          let szInt = fromInteger sz :: Int
          let szWord = fromInteger sz :: Word

          let elemSz = 1      -- TODO: hardcoded size=1
          vals <- forM [0 .. szInt - 1] $ \i -> do
            tm' <- doIndex i
            resolveSAWTerm mcc tp' tm'
          ag <- buildMirAggregateArrayWithVal sym elemSz shp szWord vals $
            \_ rv -> return rv
          let arrShp = ArrayShape (Mir.TyArray mirTy szInt) mirTy elemSz shp szWord
          pure $ MIRVal arrShp ag
    Cryptol.TVStream _tp' ->
      fail "resolveSAWTerm: unsupported infinite stream type"
    Cryptol.TVTuple [] -> pure $ MIRVal (UnitShape (Mir.TyTuple [])) ()
    Cryptol.TVTuple tps -> do
      st <- sawCoreState sym
      let sc = saw_ctx st
      tms <- traverse (\i -> scTupleSelector sc tm i (length tps)) [1 .. length tps]
      vals <- zipWithM (resolveSAWTerm mcc) tps tms
      let mirTys = map (\(MIRVal shp _) -> shapeMirTy shp) vals
      -- TODO: get proper tuple layout
      let elems = [AgElemShape i 1 shp | (i, MIRVal shp _) <- zip [0..] vals]
      ag <- buildMirAggregateWithVal sym elems vals $ \_off _sz _shp rv -> return rv
      let tupleShp = TupleShape (Mir.TyTuple mirTys) elems
      pure $ MIRVal tupleShp ag
    Cryptol.TVRec _flds ->
      fail "resolveSAWTerm: unsupported record type"
    Cryptol.TVFun _ _ ->
      fail "resolveSAWTerm: unsupported function type"
    Cryptol.TVNominal {} ->
      fail "resolveSAWTerm: unsupported nominal type"
  where
    sym = mcc ^. mccSym
    col = mcc ^. mccRustModule ^. Mir.rmCS ^. Mir.collection

data ToMIRTypeErr = NotYetSupported String | Impossible String

toMIRTypeErrToString :: ToMIRTypeErr -> String
toMIRTypeErrToString =
  \case
    NotYetSupported ty ->
      unwords [ "SAW doesn't yet support translating Cryptol's"
              , ty
              , "type(s) into crucible-mir's type system."
              ]
    Impossible ty ->
      unwords [ "User error: It's impossible to store Cryptol"
              , ty
              , "values in crucible-mir's memory model."
              ]

toMIRType ::
  Cryptol.TValue ->
  Either ToMIRTypeErr Mir.Ty
toMIRType tp =
  case tp of
    Cryptol.TVBit -> Right Mir.TyBool
    Cryptol.TVInteger -> Left (NotYetSupported "integer")
    Cryptol.TVIntMod _ -> Left (Impossible "integer (mod n)")
    Cryptol.TVFloat{} -> Left (NotYetSupported "float e p")
    Cryptol.TVArray{} -> Left (NotYetSupported "array a b")
    Cryptol.TVRational -> Left (NotYetSupported "rational")
    Cryptol.TVSeq n Cryptol.TVBit ->
      case n of
        8   -> Right $ Mir.TyUint Mir.B8
        16  -> Right $ Mir.TyUint Mir.B16
        32  -> Right $ Mir.TyUint Mir.B32
        64  -> Right $ Mir.TyUint Mir.B64
        128 -> Right $ Mir.TyUint Mir.B128
        _   -> Left (Impossible ("unsupported bitvector size: " ++ show n))
    Cryptol.TVSeq n t -> do
      t' <- toMIRType t
      let n' = fromIntegral n
      Right $ Mir.TyArray t' n'
    Cryptol.TVStream _tp' -> Left (Impossible "stream")
    Cryptol.TVTuple tps -> do
      tps' <- traverse toMIRType tps
      Right $ Mir.TyTuple tps'
    Cryptol.TVRec _flds -> Left (NotYetSupported "record")
    Cryptol.TVFun _ _ -> Left (Impossible "function")
    Cryptol.TVNominal {} -> Left (Impossible "nominal")

-- | Index into a 'Term' which has a Cryptol sequence type. Curried so that we
-- can save some work if we want to index multiple times into the same term.
indexSeqTerm ::
  Sym ->
  (Integer, Cryptol.TValue)
    {- ^ length and Cryptol element type of the sequence -} ->
  Term {- ^ term to index into -} ->
  IO (Int -> IO Term) -- ^ the indexing function
indexSeqTerm sym (sz, elemTp) tm = do
  st <- sawCoreState sym
  let sc = saw_ctx st
  sz_tm <- scNat sc (fromInteger sz)
  elemTp_tm <- importType sc emptyEnv (Cryptol.tValTy elemTp)
  pure $ \i -> do
    i_tm <- scNat sc (fromIntegral i)
    scAt sc sz_tm elemTp_tm tm i_tm

-- | Index into a 'MIRVal' with an 'ArrayShape' 'TypeShape'. Returns 'Nothing'
-- if the index is out of bounds.
indexMirVector ::
  MonadIO m =>
  Sym ->
  Int {- ^ the index -} ->
  TypeShape elemTp {- ^ 'TypeShape' of the array elements -} ->
  Mir.MirVector Sym elemTp {- ^ 'RegValue' of the 'MIRVal' -} ->
  MaybeT m MIRVal
indexMirVector sym i elemShp vec =
  MIRVal elemShp <$>
    case vec of
      Mir.MirVector_Vector vs ->
        MaybeT $ pure $ vs V.!? i
      Mir.MirVector_PartialVector vs ->
        MaybeT $ pure $
          readMaybeType sym "vector element" (shapeType elemShp) <$> vs V.!? i
      Mir.MirVector_Array array -> liftIO $ do
        i_sym <- usizeBvLit sym i
        W4.arrayLookup sym array (Ctx.Empty Ctx.:> i_sym)

-- | Index into a 'MIRVal' with an 'ArrayShape' 'TypeShape'. Returns 'Nothing'
-- if the index is out of bounds.
indexMirArray ::
  Monad m =>
  Sym ->
  Int {- ^ the index -} ->
  Word {- ^ element size in bytes -} ->
  TypeShape elemTp {- ^ 'TypeShape' of the array elements -} ->
  Mir.MirAggregate Sym {- ^ 'RegValue' of the 'MIRVal' -} ->
  MaybeT m MIRVal
indexMirArray sym i elemSz elemShp (Mir.MirAggregate _totalSize m) = MaybeT $ pure $ do
  let off = fromIntegral i * elemSz
  Mir.MirAggregateEntry sz' tpr' rvPart <- IntMap.lookup (fromIntegral off) m
  Refl <- W4.testEquality (shapeType elemShp) tpr'
  guard (elemSz == sz')
  rv <- readPartExprMaybe sym rvPart
  return $ MIRVal elemShp rv

-- | Create a symbolic @usize@ from an 'Int'.
usizeBvLit :: W4.IsSymExprBuilder sym => sym -> Int -> IO (W4.SymBV sym Mir.SizeBits)
usizeBvLit sym = W4.bvLit sym W4.knownNat . BV.mkBV W4.knownNat . toInteger

-- | Check if two 'MIRVal's are equal.
equalValsPred ::
  MIRCrucibleContext ->
  MIRVal ->
  MIRVal ->
  IO (W4.Pred Sym)
equalValsPred cc mv1 mv2 =
  case (mv1, mv2) of
    (MIRVal shp1 v1, MIRVal shp2 v2) -> do
      mbEq <- runMaybeT $ do
        guard $ checkCompatibleTys (shapeMirTy shp1) (shapeMirTy shp2)
        Refl <- testEquality shp1 shp2
        goTy shp1 v1 v2
      pure $ fromMaybe (W4.falsePred sym) mbEq
  where
    sym = cc^.mccSym

    testEquality :: forall k (f :: k -> Type) (a :: k) (b :: k)
                  . W4.TestEquality f
                 => f a -> f b -> MaybeT IO (a :~: b)
    testEquality v1 v2 = MaybeT $ pure $ W4.testEquality v1 v2

    goTy :: TypeShape tp
         -> RegValue Sym tp
         -> RegValue Sym tp
         -> MaybeT IO (W4.Pred Sym)
    goTy (UnitShape _) () () =
      pure $ W4.truePred sym
    goTy (PrimShape _ _) v1 v2 =
      liftIO $ W4.isEq sym v1 v2
    goTy (TupleShape _ elems) ag1 ag2 =
      goAg elems ag1 ag2
    goTy (ArrayShape _ _ elemSz shp len) ag1 ag2 =
      let elems = arrayAgElemShapes elemSz shp len in
      goAg elems ag1 ag2
    goTy (StructShape _ _ fldShp) fldAssn1 fldAssn2 =
      goFldAssn fldShp fldAssn1 fldAssn2
    goTy (EnumShape _ _ variantShp _ discrShp)
         (Ctx.Empty Ctx.:> RV discr1 Ctx.:> RV variant1)
         (Ctx.Empty Ctx.:> RV discr2 Ctx.:> RV variant2) = do
      discrPred <- goTy discrShp discr1 discr2
      variantPred <- goVariantAssn variantShp variant1 variant2
      liftIO $ W4.andPred sym discrPred variantPred
    goTy (TransparentShape _ shp) v1 v2 =
      goTy shp v1 v2
    goTy (RefShape _ _ _ _) ref1 ref2 =
      mccWithBackend cc $ \bak ->
        liftIO $ Mir.mirRef_eqIO bak ref1 ref2
    goTy (SliceShape _ ty mut tpr)
         (Ctx.Empty Ctx.:> RV ref1 Ctx.:> RV len1)
         (Ctx.Empty Ctx.:> RV ref2 Ctx.:> RV len2) = do
      let (refShp, lenShp) = sliceShapeParts ty mut tpr
      refPred <- goTy refShp ref1 ref2
      lenPred <- goTy lenShp len1 len2
      liftIO $ W4.andPred sym refPred lenPred
    goTy (FnPtrShape _ _ _) _fh1 _fh2 =
      error "Function pointers not currently supported in overrides"

    goFldAssn :: Ctx.Assignment FieldShape ctx
              -> Ctx.Assignment (RegValue' Sym) ctx
              -> Ctx.Assignment (RegValue' Sym) ctx
              -> MaybeT IO (W4.Pred Sym)
    goFldAssn fldShp fldAssn1 fldAssn2 =
      FCI.ifoldrMFC
        (\idx (Functor.Pair (RV fld1) (RV fld2)) z -> do
          let shp = fldShp Ctx.! idx
          eq <- goFld shp fld1 fld2
          liftIO $ W4.andPred sym eq z)
        (W4.truePred sym)
        (Ctx.zipWith Functor.Pair fldAssn1 fldAssn2)

    goAg :: [AgElemShape]
         -> Mir.MirAggregate Sym
         -> Mir.MirAggregate Sym
         -> MaybeT IO (W4.Pred Sym)
    goAg elems ag1 ag2 = do
      eqs <- zipMirAggregates sym elems ag1 ag2 $
        \_off _sz shp rv1 rv2 -> goTy shp rv1 rv2
      liftIO $ F.foldrM (W4.andPred sym) (W4.truePred sym) eqs

    goVariantAssn :: Ctx.Assignment VariantShape ctx
                  -> Ctx.Assignment (VariantBranch Sym) ctx
                  -> Ctx.Assignment (VariantBranch Sym) ctx
                  -> MaybeT IO (W4.Pred Sym)
    goVariantAssn variantShp vbAssn1 vbAssn2 =
      FCI.ifoldrMFC
        (\idx (Functor.Pair (VB var1) (VB var2)) z -> do
          VariantShape fldShp <- pure $ variantShp Ctx.! idx
          varPred <- goVariantFlds fldShp var1 var2
          liftIO $ W4.andPred sym varPred z)
        (W4.truePred sym)
        (Ctx.zipWith Functor.Pair vbAssn1 vbAssn2)

    goVariantFlds :: Ctx.Assignment FieldShape ctx
                  -> W4.PartExpr (W4.Pred Sym) (Ctx.Assignment (RegValue' Sym) ctx)
                  -> W4.PartExpr (W4.Pred Sym) (Ctx.Assignment (RegValue' Sym) ctx)
                  -> MaybeT IO (W4.Pred Sym)
    goVariantFlds fldShp (W4.PE p1 fldAssn1) (W4.PE p2 fldAssn2) = do
      pPred <- liftIO $ W4.eqPred sym p1 p2
      fldPred <- goFldAssn fldShp fldAssn1 fldAssn2
      liftIO $ W4.andPred sym pPred fldPred
    goVariantFlds _ W4.Unassigned W4.Unassigned =
      pure $ W4.truePred sym
    goVariantFlds _ (W4.PE{}) W4.Unassigned =
      pure $ W4.falsePred sym
    goVariantFlds _ W4.Unassigned (W4.PE{}) =
      pure $ W4.falsePred sym

    goFld :: FieldShape tp
          -> RegValue Sym tp
          -> RegValue Sym tp
          -> MaybeT IO (W4.Pred Sym)
    goFld shp v1 v2 =
      case shp of
        ReqField shp' ->
          goTy shp' v1 v2
        OptField shp' -> do
          let readField v = readMaybeType sym "field" (shapeType shp') v
          let v1' = readField v1
          let v2' = readField v2
          goTy shp' v1' v2'

-- | Take an array 'Mir.Ty' (arising from a reference type) and return three
-- things:
--
-- 1. The 'Mir.Ty' of the corresponding slice. When the 'MirSliceInfo' argument
--    is 'MirArraySlice', then 'Mir.TySlice' will be returned. When the
--    'MirSliceInfo' argument is a 'MirStrSlice', then 'Mir.TyStr' will be
--    returned.
--
-- 2. The 'Mir.Ty' of the \"element type\" of the slice. When the 'MirSliceInfo'
--    argument is 'MirArraySlice', then the element type of the array will be
--    returned. When the 'MirSliceInfo' argument is a 'MirStrSlice', then @u8@
--    will be returned.
--
-- 3. The length of the array.
--
-- This function will throw an exception if the supplied 'Mir.Ty' is not an
-- array type.
arrayToSliceTys ::
  X.MonadThrow m =>
  MirSliceInfo ->
  Mir.Mutability ->
  Mir.Ty ->
  m (Mir.Ty, Mir.Ty, Int)
arrayToSliceTys sliceInfo mut arrTy@(Mir.TyArray ty len) =
  case sliceInfo of
    MirArraySlice ->
      pure (Mir.TySlice ty, ty, len)
    MirStrSlice
      |  checkCompatibleTys ty u8
      -> pure (Mir.TyStr, u8, len)
      |  otherwise
      -> X.throwM $ MIRStrSliceNonU8Array $ Mir.TyRef arrTy mut
  where
    u8 = Mir.TyUint Mir.B8
arrayToSliceTys _sliceInfo mut arrTy =
  X.throwM $ MIRSliceNonArrayReference $ Mir.TyRef arrTy mut

-- | Retrieve the \"element type\" of a slice type. If the supplied type is an
-- array slice type (e.g., @[u32]@), return the underlying type (e.g., @u32@).
-- If the supplied type is a @str@ slice, return @u8@. For all other types,
-- throw an exception.
sliceElemTy ::
  X.MonadThrow m =>
  Mir.Ty ->
  m Mir.Ty
sliceElemTy (Mir.TySlice ty) =
  pure ty
sliceElemTy Mir.TyStr =
  pure $ Mir.TyUint Mir.B8
sliceElemTy ty =
  X.throwM $ MIRSliceWrongTy ty

-- | Take a slice reference type and return the corresponding 'MirSliceInfo'.
-- Throw an exception if the supplied type is not a slice reference type.
sliceRefTyToSliceInfo ::
  X.MonadThrow m =>
  Mir.Ty ->
  m MirSliceInfo
sliceRefTyToSliceInfo (Mir.TyRef sliceTy _) =
  case sliceTy of
    Mir.TySlice _ ->
      pure MirArraySlice
    Mir.TyStr ->
      pure MirStrSlice
    _ ->
      X.throwM $ MIRSliceWrongTy sliceTy
sliceRefTyToSliceInfo ty =
  X.throwM $ MIRSliceNonReference ty

-- | Check if two 'Mir.Ty's are compatible in SAW. This is a slightly coarser
-- notion of equality to reflect the fact that MIR's type system is richer than
-- Cryptol's type system, and some types which would be distinct in MIR are in
-- fact equal when converted to the equivalent Cryptol types. In particular:
--
-- 1. A @u<N>@ type is always compatible with an @i<N>@ type. For instance, @u8@
--    is compatible with @i8@, and @u16@ is compatible with @i16@. Note that the
--    bit sizes of both types must be the same. For instance, @u8@ is /not/
--    compatible with @i16@.
--
-- 2. The @usize@/@isize@ types are always compatible with @u<N>@/@i<N>@, where
--    @N@ is the number of bits corresponding to the 'Mir.SizeBits' type in
--    "Mir.Intrinsics". (This is a bit unsavory, as the actual size of
--    @usize@/@isize@ is platform-dependent, but this is the current approach.)
--
-- 3. Compatibility applies recursively. For instance, @[ty_1; N]@ is compatible
--    with @[ty_2; N]@ iff @ty_1@ and @ty_2@ are compatibile. Similarly, a tuple
--    typle @(ty_1_a, ..., ty_n_a)@ is compatible with @(ty_1_b, ..., ty_n_b)@
--    iff @ty_1_a@ is compatible with @ty_1_b@, ..., and @ty_n_a@ is compatible
--    with @ty_n_b@.
--
-- See also @checkRegisterCompatibility@ in "SAWCentral.Crucible.LLVM.Builtins"
-- and @registerCompatible@ in "SAWCentral.Crucible.JVM.Builtins", which fill a
-- similar niche in the LLVM and JVM backends, respectively.
checkCompatibleTys :: Mir.Ty -> Mir.Ty -> Bool
checkCompatibleTys ty1 ty2 = tyView ty1 == tyView ty2

-- | Like 'Mir.Ty', but where:
--
-- * The 'TyInt' and 'TyUint' constructors have been collapsed into a single
--   'TyViewInt' constructor.
--
-- * 'TyViewInt' uses 'BaseSizeView' instead of 'Mir.BaseSize'.
--
-- * Recursive occurrences of 'Mir.Ty' use 'TyView' instead. This also applies
--   to fields of type 'SubstsView' and 'FnSigView', which also replace 'Mir.Ty'
--   with 'TyView' in their definitions.
--
-- This provides a coarser notion of equality than what the 'Eq' instance for
-- 'Mir.Ty' provides, which distinguishes the two sorts of integer types.
--
-- This is an internal data type that is used to power the 'checkCompatibleTys'
-- function. Refer to the Haddocks for that function for more information on why
-- this is needed.
data TyView
  = TyViewBool
  | TyViewChar
    -- | The sole integer type. Both 'TyInt' and 'TyUint' are mapped to
    -- 'TyViewInt', and 'BaseSizeView' is used instead of 'Mir.BaseSize'.
  | TyViewInt !BaseSizeView
  | TyViewTuple ![TyView]
  | TyViewSlice !TyView
  | TyViewArray !TyView !Int
  | TyViewRef !TyView !Mir.Mutability
  | TyViewAdt !Mir.DefId !Mir.DefId !SubstsView
  | TyViewFnDef !Mir.DefId
  | TyViewClosure [TyView]
  | TyViewStr
  | TyViewFnPtr !FnSigView
  | TyViewDynamic !Mir.TraitName
  | TyViewRawPtr !TyView !Mir.Mutability
  | TyViewFloat !Mir.FloatKind
  | TyViewDowncast !TyView !Integer
  | TyViewNever
  | TyViewForeign
  | TyViewLifetime
  | TyViewConst
  | TyViewErased
  | TyViewInterned Mir.TyName
  deriving Eq

-- | Like 'Mir.BaseSize', but without a special case for @usize@/@isize@.
-- Instead, these are mapped to their actual size, which is determined by the
-- number of bits in the 'Mir.SizeBits' type in "Mir.Intrinsics". (This is a bit
-- unsavory, as the actual size of @usize@/@isize@ is platform-dependent, but
-- this is the current approach.)
data BaseSizeView
  = B8View
  | B16View
  | B32View
  | B64View
  | B128View
  deriving Eq

-- | Like 'Mir.Substs', but using 'TyView's instead of 'Mir.Ty'.
--
-- This is an internal data type that is used to power the 'checkCompatibleTys'
-- function. Refer to the Haddocks for that function for more information on why
-- this is needed.
newtype SubstsView = SubstsView [TyView]
  deriving Eq

-- | Like 'Mir.FnSig', but using 'TyView's instead of 'Mir.Ty'.
--
-- This is an internal data type that is used to power the 'checkCompatibleTys'
-- function. Refer to the Haddocks for that function for more information on why
-- this is needed.
data FnSigView = FnSigView {
    _fsvarg_tys    :: ![TyView]
  , _fsvreturn_ty  :: !TyView
  , _fsvabi        :: Mir.Abi
  }
  deriving Eq

-- | Convert a 'Mir.Ty' value to a 'TyView' value.
tyView :: Mir.Ty -> TyView
-- The two most important cases. Both sorts of integers are mapped to TyViewInt.
tyView (Mir.TyInt  bs) = TyViewInt (baseSizeView bs)
tyView (Mir.TyUint bs) = TyViewInt (baseSizeView bs)
-- All other cases are straightforward.
tyView Mir.TyBool = TyViewBool
tyView Mir.TyChar = TyViewChar
tyView (Mir.TyTuple tys) = TyViewTuple (map tyView tys)
tyView (Mir.TySlice ty) = TyViewSlice (tyView ty)
tyView (Mir.TyArray ty n) = TyViewArray (tyView ty) n
tyView (Mir.TyRef ty mut) = TyViewRef (tyView ty) mut
tyView (Mir.TyAdt monoDid origDid substs) =
  TyViewAdt monoDid origDid (substsView substs)
tyView (Mir.TyFnDef did) = TyViewFnDef did
tyView (Mir.TyClosure tys) = TyViewClosure (map tyView tys)
tyView Mir.TyStr = TyViewStr
tyView (Mir.TyFnPtr sig) = TyViewFnPtr (fnSigView sig)
tyView (Mir.TyDynamic trait) = TyViewDynamic trait
tyView (Mir.TyRawPtr ty mut) = TyViewRawPtr (tyView ty) mut
tyView (Mir.TyFloat fk) = TyViewFloat fk
tyView (Mir.TyDowncast ty n) = TyViewDowncast (tyView ty) n
tyView Mir.TyNever = TyViewNever
tyView Mir.TyForeign = TyViewForeign
tyView Mir.TyLifetime = TyViewLifetime
tyView Mir.TyConst = TyViewConst
tyView Mir.TyErased = TyViewErased
tyView (Mir.TyInterned nm) = TyViewInterned nm

-- | Convert a 'Mir.BaseSize' value to a 'BaseSizeView' value.
baseSizeView :: Mir.BaseSize -> BaseSizeView
baseSizeView Mir.B8    = B8View
baseSizeView Mir.B16   = B16View
baseSizeView Mir.B32   = B32View
baseSizeView Mir.B64   = B64View
baseSizeView Mir.B128  = B128View
baseSizeView Mir.USize =
  case Map.lookup (W4.natValue sizeBitsRepr) bitSizesMap of
    Just bsv -> bsv
    Nothing ->
      error $ "Mir.Intrinsics.BaseSize bit size not supported: " ++ show sizeBitsRepr
  where
    sizeBitsRepr = W4.knownNat @Mir.SizeBits

    bitSizesMap :: Map Natural BaseSizeView
    bitSizesMap = Map.fromList
      [ (W4.natValue (W4.knownNat @8),   B8View)
      , (W4.natValue (W4.knownNat @16),  B16View)
      , (W4.natValue (W4.knownNat @32),  B32View)
      , (W4.natValue (W4.knownNat @64),  B64View)
      , (W4.natValue (W4.knownNat @128), B128View)
      ]

-- | Convert a 'Mir.Substs' value to a 'SubstsView' value.
substsView :: Mir.Substs -> SubstsView
substsView (Mir.Substs tys) = SubstsView (map tyView tys)

-- | Convert a 'Mir.FnSig' value to a 'FnSigView' value.
fnSigView :: Mir.FnSig -> FnSigView
fnSigView (Mir.FnSig argTys retTy abi) =
  FnSigView (map tyView argTys) (tyView retTy) abi

-- | Allocate memory for each 'mir_alloc', 'mir_alloc_mut',
-- 'mir_alloc_raw_ptr_const', or 'mir_alloc_raw_ptr_mut'.
doAlloc ::
     MIRCrucibleContext
  -> SymGlobalState Sym
  -> Some MirAllocSpec
  -> IO (Some (MirPointer Sym), SymGlobalState Sym)
doAlloc cc globals (Some ma) =
  mccWithBackend cc $ \bak ->
  do let col = cc ^. mccRustModule ^. Mir.rmCS ^. Mir.collection
     let halloc = cc^.mccHandleAllocator
     let sym = backendGetSym bak
     let iTypes = cc^.mccIntrinsicTypes
     Some tpr <- case Mir.tyToRepr col (ma^.maMirType) of
       Left err -> panic "doAlloc" ["Unsupported type", Text.pack err]
       Right x -> return x

     -- Create an uninitialized `MirAggregate` of the allocation's
     -- length and return a pointer to its first element.
     -- See Note [Allocating multiple MIR values] for more details.
     ref <- Mir.newMirRefIO sym halloc Mir.MirAggregateRepr

     len_sym <- usizeBvLit sym (ma^.maLen)
     -- TODO: hardcoded size=1 (implied in conversion of `len_sym` to `sz_sym`
     let sz_sym = len_sym
     ag <- Mir.mirAggregate_uninitIO bak sz_sym
     globals' <- Mir.writeMirRefIO bak globals iTypes Mir.MirAggregateRepr ref ag

     zero <- W4.bvLit sym W4.knownRepr $ BV.mkBV W4.knownRepr 0
     ptr <- Mir.subindexMirRefIO bak iTypes tpr ref zero
     let mirPtr = Some MirPointer
           { _mpType = tpr
           , _mpKind = ma^.maPtrKind
           , _mpMutbl = ma^.maMutbl
           , _mpMirType = ma^.maMirType
           , _mpRef = ptr
           }

     pure (mirPtr, globals')

{-
Note [Allocating multiple MIR values]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
MIR allocations have a type and a length. The length is the number of values of
that type to allocate contiguously. The `newMirRef` family of functions in
crucible-mir allocates and returns a reference to the space for a *single* value
of the given type. So when we need to potentially allocate multiple values, we
instead call `newMirRef` to allocate a single `MirAggregate`, which itself contains
space for many elements. All elements of the aggregate start out as uninitialized
because the memory is uninitialized. Then we get the reference to the first
element, and return that. This is the same way that crucible's custom allocator
works, in Mir.TransCustom.allocate.
-}

doPointsTo ::
     MS.CrucibleMethodSpecIR MIR
  -> MIRCrucibleContext
  -> Map MS.AllocIndex (Some (MirPointer Sym))
  -> SymGlobalState Sym
  -> MirPointsTo
  -> IO (SymGlobalState Sym)
doPointsTo mspec cc env globals (MirPointsTo _ reference target) =
  mccWithBackend cc $ \bak -> do
    let sym = backendGetSym bak
    MIRVal referenceShp referenceVal <-
      resolveSetupVal cc env tyenv nameEnv reference
    -- By the time we reach here, we have already checked (in mir_points_to)
    -- that we are in fact dealing with a reference value, so the call to
    -- `testRefShape` below should always succeed.
    IsRefShape _ _ _ (referenceInnerTy :: TypeRepr referenceInnerTp) <-
      case testRefShape referenceShp of
        Just irs -> pure irs
        Nothing ->
          panic "doPointsTo" [
              "Unexpected non-reference type: ",
              "   " <> Text.pack (show $ PP.pretty $ shapeMirTy referenceShp)
          ]
    -- By the time we reach here, we have already checked (in mir_points_to)
    -- that the type of the reference is compatible with the right-hand side
    -- value, so the equality check below should never fail.
    let testReferentShp ::
          TypeShape referentTp ->
          IO (referenceInnerTp :~: referentTp)
        testReferentShp referentShp =
          case W4.testEquality referenceInnerTy (shapeType referentShp) of
            Just r -> pure r
            Nothing ->
              panic "doPointsTo" [
                  "Unexpected type mismatch between reference and referent",
                  "Reference type: " <> Text.pack (show referenceInnerTy),
                  "Referent type:  " <> Text.pack (show (shapeType referentShp))
              ]
    case target of
      CrucibleMirCompPointsToTarget {} ->
        panic "doPointsTo"
          [ "CrucibleMirCompPointsToTarget not implemented in SAW"
          ]
      MirPointsToSingleTarget referent -> do
        MIRVal referentShp referentVal <-
          resolveSetupVal cc env tyenv nameEnv referent
        Refl <- testReferentShp referentShp
        Mir.writeMirRefIO bak globals iTypes referenceInnerTy
          referenceVal referentVal
      MirPointsToMultiTarget referentArray -> do
        MIRVal referentArrShp referentArrVal <-
          resolveSetupVal cc env tyenv nameEnv referentArray
        case referentArrShp of
          -- mir_points_to_multi should check that the RHS type is TyArray, so
          -- this case should always match.
          ArrayShape _ _ _ referentElemShp _ -> do
            Refl <- testReferentShp referentElemShp
            let write globals' i referentVal = do
                  i_sym <- usizeBvLit sym i
                  referenceVal' <- Mir.mirRef_offsetIO bak iTypes referenceVal i_sym
                  Mir.writeMirRefIO bak globals' iTypes referenceInnerTy
                    referenceVal' referentVal
            let writeEntry globals' (off, Mir.MirAggregateEntry _sz tpr rvPart) = do
                  Refl <- case W4.testEquality tpr (shapeType referentElemShp) of
                    Just r -> pure r
                    Nothing ->
                      panic "doPointsTo" [
                          "Unexpected type mismatch between referent outer and entry types",
                          "Outer type: " <> Text.pack (show (shapeType referentElemShp)),
                          "Entry type: " <> Text.pack (show tpr),
                          "At offset " <> Text.pack (show off)
                      ]
                  let rv = readMaybeType sym "array element" tpr rvPart
                  -- TODO: hardcoded size=1 (implied in conversion of `off` to `i`)
                  write globals' (fromIntegral off) rv
            foldM writeEntry globals (Mir.mirAggregate_entries sym referentArrVal)
          _ -> panic "doPointsTo"
            [ "Unexpected non-array shape resolved from MirPointsToMultiTarget:"
            , Text.pack (show referentArrShp)
            ]
  where
    iTypes = cc ^. mccIntrinsicTypes
    tyenv = MS.csAllocations mspec
    nameEnv = mspec ^. MS.csPreState . MS.csVarTypeNames

-- | Construct an 'Mir.TyAdt' from an 'Mir.Adt'.
mirAdtToTy :: Mir.Adt -> Mir.Ty
mirAdtToTy adt =
  Mir.TyAdt (adt ^. Mir.adtname) (adt ^. Mir.adtOrigDefId) (adt ^. Mir.adtOrigSubsts)

-- | Like 'findDefIdEither', but any errors are thrown with 'fail'.
findDefId :: MonadFail m => Mir.CollectionState -> Text -> m Mir.DefId
findDefId cs defName =
  either fail pure $ findDefIdEither cs defName

-- | Given a definition name @defName@, attempt to look up its corresponding
-- 'Mir.DefId'. If successful, return it with 'Right'. Currently, the following
-- types of definition names are permitted:
--
-- * @<crate_name>/<disambiguator>::<def_name>: A fully disambiguated name.
--
-- * @<crate_name>::<def_name>: A name without a disambiguator. In this
--   case, SAW will attempt to look up a disambiguator from the
--   'Mir.crateHashesMap'. If none can be found, or if there are multiple
--   disambiguators for the given @<crate_name>@, then this will return an error
--   message with 'Left'.
--
-- This also consults the 'Mir.langItems' so that if a user looks up the
-- original 'DefId' for a lang item (e.g., @core::option::Option@), then this
-- function will return the @$lang@-based 'DefId' instead (e.g.,
-- @$lang::Option@), as the latter 'DefId' is what will be used throughout the
-- rest of the MIR code.
findDefIdEither :: Mir.CollectionState -> Text -> Either String Mir.DefId
findDefIdEither cs defName = do
    (crate, path) <-
      case edid of
        crate:path -> pure (crate, path)
        [] -> Left $ unlines
                [ "The definition `" ++ defNameStr ++ "` lacks a crate."
                , "Consider providing one, e.g., `<crate_name>::" ++ defNameStr ++ "`."
                ]
    let crateStr = Text.unpack crate
    origDefId <-
      case Text.splitOn "/" crate of
        [crateNoDisambig, disambig] ->
          Right $ Mir.textId $ Text.intercalate "::"
                $ (crateNoDisambig <> "/" <> disambig) : path
        [_] ->
          case Map.lookup crate crateDisambigs of
              Just allDisambigs@(disambig :| otherDisambigs)
                |  F.null otherDisambigs
                -> Right $ Mir.textId $ Text.intercalate "::"
                         $ (crate <> "/" <> disambig) : path
                |  otherwise
                -> Left $ unlines $
                     [ "ambiguous crate " ++ crateStr
                     , "crate disambiguators:"
                     ] ++ F.toList (Text.unpack <$> allDisambigs)
              Nothing -> Left $ "unknown crate " ++ crateStr
        _ -> Left $ "Malformed crate name: " ++ show crateStr
    Right $ Map.findWithDefault origDefId origDefId langItemDefIds
  where
    crateDisambigs = cs ^. Mir.crateHashesMap
    langItemDefIds = cs ^. Mir.collection . Mir.langItems

    defNameStr = Text.unpack defName
    edid = Text.splitOn "::" defName

-- | Consult the given 'Mir.CollectionState' to find a 'Mir.Static' with the
-- given 'String' as an identifier. If such a 'Mir.Static' cannot be found, this
-- will raise an error.
findStatic :: X.MonadThrow m => Mir.CollectionState -> Text -> m Mir.Static
findStatic cs name = do
  did <- case findDefIdEither cs name of
    Left err -> X.throwM $ MIRInvalidIdentifier err
    Right did -> pure did
  case Map.lookup did (cs ^. Mir.collection . Mir.statics) of
    Nothing -> X.throwM $ MIRStaticNotFound did
    Just static -> pure static

-- | Consult the given 'MIRCrucibleContext' to find the 'MIRVal' used to
-- initialize a 'Mir.Static' value. If such a 'MIRVal' cannot be found, this
-- will raise an error.
findStaticInitializer ::
  X.MonadThrow m =>
  MIRCrucibleContext ->
  Mir.Static ->
  m MIRVal
findStaticInitializer mcc static = do
  Mir.StaticVar gv <- findStaticVar cs staticDefId
  let staticShp = tyToShapeEq col (static ^. Mir.sTy) (globalType gv)
  case MapF.lookup gv (mcc^.mccStaticInitializerMap) of
    Just (RV staticInitVal) ->
      pure $ MIRVal staticShp staticInitVal
    Nothing ->
      X.throwM $ MIRStaticNotFound staticDefId
  where
    staticDefId = static ^. Mir.sName
    cs  = mcc ^. mccRustModule . Mir.rmCS
    col = cs ^. Mir.collection

-- | Consult the given 'Mir.CollectionState' to find a 'Mir.StaticVar' with the
-- given 'Mir.DefId'. If such a 'Mir.StaticVar' cannot be found, this will raise
-- an error.
findStaticVar ::
  X.MonadThrow m =>
  Mir.CollectionState ->
  Mir.DefId ->
  m Mir.StaticVar
findStaticVar cs staticDefId =
  case Map.lookup staticDefId (cs ^. Mir.staticMap) of
    Nothing -> X.throwM $ MIRStaticNotFound staticDefId
    Just sv -> pure sv

-- | Compute the 'Mir.Mutability' of a 'Mir.Static' value.
staticMutability :: Mir.Static -> Mir.Mutability
staticMutability static
  | static ^. Mir.sMutable = Mir.Mut
  | otherwise              = Mir.Immut

-- | Compute a 'Mir.MirReferenceMux' pointing to a static value's 'GlobalVar'.
staticRefMux ::
  W4.IsSymExprBuilder sym =>
  sym ->
  GlobalVar tp ->
  Mir.MirReferenceMux sym
staticRefMux sym gv =
  Mir.MirReferenceMux $
  Mir.toFancyMuxTree sym $
  Mir.MirReference (globalType gv) (Mir.GlobalVar_RefRoot gv) Mir.Empty_RefPath

-- | Compute the 'Mir.Ty' of a reference to a 'Mir.Static' value.
staticTyRef :: Mir.Static -> Mir.Ty
staticTyRef static =
  Mir.TyRef
    (static ^. Mir.sTy)
    (staticMutability static)

-- | Retrieve the discriminant corresponding to an enum variant. This function
-- will panic if the variant does not contain a discriminant.
getEnumVariantDiscr :: Mir.Variant -> Integer
getEnumVariantDiscr variant =
  case variant ^. Mir.discrval of
    Just discr ->
      discr
    Nothing ->
      panic "getEnumVariantDiscr" [
          "discrval not set for variant: " <> Text.pack (show (variant ^. Mir.vname))
      ]

-- | An enum's discriminant should have an integral type such as @isize@ or
-- @i8@, which this function checks. If this is not the case, this function will
-- panic.
testDiscriminantIsBV :: TypeShape shp -> IsBVShape shp
testDiscriminantIsBV discrShp =
  case testBVShape discrShp of
    Just ibvs -> ibvs
    Nothing ->
      panic "testDiscriminantIsBV" [
          "Unexpected non-integral discriminant type:",
          "   " <> Text.pack (show $ PP.pretty $ shapeMirTy discrShp)
      ]

-- | Compute the index of a variant as an 'Ctx.Index'. If the index is out of
-- range, this function will panic.
variantIntIndex ::
  Mir.DefId {-^ The enum identifier. (Only used for error messages.) -} ->
  Int {-^ The index of the variant as an 'Int'. -} ->
  Ctx.Size ctx {-^ The number of variants as a 'Ctx.Size'. -} ->
  Some (Ctx.Index ctx)
variantIntIndex adtNm variantIdx variantsSize =
  case Ctx.intIndex variantIdx variantsSize of
    Just someIdx ->
      someIdx
    Nothing ->
      panic "variantIntIndex" [
          "Enum variant index out of range",
          "Enum: " <> Text.pack (show adtNm),
          "Index: " <> Text.pack (show variantIdx),
          "Number of variants: " <> Text.pack (show variantsSize)
      ]

-- | Check if there is a 'SetupCast' somewhere in a 'SetupValue'.
containsCast :: SetupValue -> Bool
containsCast (MS.SetupVar _) = False
containsCast (MS.SetupTerm _) = False
containsCast (MS.SetupNull empty) = absurd empty
containsCast (MS.SetupStruct _ vs) = any containsCast vs
containsCast (MS.SetupArray _ vs) = any containsCast vs
containsCast (MS.SetupElem _ v _) = containsCast v
containsCast (MS.SetupField () v _) = containsCast v
containsCast (MS.SetupCast _ _) = True
containsCast (MS.SetupUnion empty _ _) = absurd empty
containsCast (MS.SetupTuple () vs) = any containsCast vs
containsCast (MS.SetupSlice slice) =
  case slice of
    MirSetupSliceRaw ptr _ -> containsCast ptr
    MirSetupSlice _ ref -> containsCast ref
    MirSetupSliceRange _ ref _ _ -> containsCast ref
containsCast (MS.SetupEnum enum_) =
  case enum_ of
    MirSetupEnumVariant _ _ _ vs -> any containsCast vs
    MirSetupEnumSymbolic _ disc vss ->
      containsCast disc || any (any containsCast) vss
containsCast (MS.SetupGlobal () _) = False
containsCast (MS.SetupGlobalInitializer () _) = False
containsCast (MS.SetupMux () _ vt vf) = containsCast vt || containsCast vf
