{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | The 'TypeShape' data type and related utilities.
module SAWCentral.Crucible.MIR.TypeShape
  ( TypeShape(..)
  , FieldShape(..)
  , VariantShape(..)
  , tyToShape
  , tyToShapeEq
  , shapeType
  , fieldShapeType
  , variantShapeType
  , shapeMirTy
  , fieldShapeMirTy
  , shapeToTerm
  , IsBVShape(..)
  , testBVShape
  , IsRefShape(..)
  , testRefShape
  , sliceShapeParts
  ) where

import Control.Lens ((^.), (^..), each)
import Control.Monad.IO.Class (MonadIO(..))
import Data.Functor.Const (Const(..))
import qualified Data.Map as Map
import Data.Parameterized.Classes (ShowF)
import Data.Parameterized.Context (pattern Empty, pattern (:>), Assignment)
import Data.Parameterized.Some
import Data.Parameterized.TH.GADT
import Data.Parameterized.TraversableFC
import GHC.Stack (HasCallStack)
import qualified Prettyprinter as PP

import Lang.Crucible.Types

import Mir.Intrinsics
import qualified Mir.Mir as M
import Mir.TransTy ( tyListToCtx, tyToRepr, tyToReprCont, canInitialize
                   , isUnsized, reprTransparentFieldTy )

import qualified SAWCore.SharedTerm as SAW

-- | TypeShape is used to classify MIR `Ty`s and their corresponding
-- CrucibleTypes into a few common cases.  We don't use `Ty` directly because
-- there are some `Ty`s that have identical structure (such as TyRef vs.
-- TyRawPtr) or similar enough structure that we'd rather write only one case
-- (such as `u8` vs `i8` vs `i32`, all primitives/BaseTypes).  And we don't use
-- TypeRepr directly because it's lacking information in some cases.
--
-- In each constructor, the first `M.Ty` is the overall MIR type (e.g., for
-- ArrayShape, this is the TyArray type).  The overall `TypeRepr tp` isn't
-- stored directly, but can be computed with `shapeType`.
data TypeShape (tp :: CrucibleType) where
    UnitShape :: M.Ty -> TypeShape UnitType
    PrimShape :: M.Ty -> BaseTypeRepr btp -> TypeShape (BaseToType btp)
    TupleShape :: M.Ty -> [M.Ty] -> Assignment FieldShape ctx -> TypeShape (StructType ctx)
    ArrayShape :: M.Ty -> M.Ty -> TypeShape tp -> TypeShape (MirVectorType tp)
    StructShape :: M.Ty -> [M.Ty] -> Assignment FieldShape ctx -> TypeShape (StructType ctx)
    TransparentShape :: M.Ty -> TypeShape tp -> TypeShape tp
    -- | Note that RefShape contains only a TypeRepr for the pointee type, not
    -- a TypeShape.  None of our operations need to recurse inside pointers,
    -- and also this saves us from some infinite recursion.
    RefShape :: M.Ty
             -- ^ The reference type
             -> M.Ty
             -- ^ The pointee type
             -> M.Mutability
             -- ^ Is the reference mutable or immutable?
             -> TypeRepr tp
             -- ^ The Crucible representation of the pointee type
             -> TypeShape MirReferenceType
    -- | A shape for a slice reference of type @&[T]@ or @&str@, which is
    -- represented in @crucible-mir@ as a 'MirSlice', i.e., a 'StructType'
    -- where:
    --
    -- * The first type in the struct is a reference to the element type.
    --   If the slice reference has type @&[T]@, then the element type is @T@.
    --   If the slice reference has type @&str@, then the element type is @u8@.
    --
    -- * The second type in the struct is the length of the slice.
    --
    -- The @crucible-mir@ representations for tuples and slices are almost, but
    -- not quite, the same, as tuples can wrap their fields in 'MaybeType's (see
    -- 'FieldShape') but slices never do this. Nevertheless, many places in the
    -- code effectively treat tuples and slices identically (modulo 'MaybeType's).
    --
    -- To make it easier to recurse on the 'TypeShape's for the slice's
    -- reference and length types, we provide the 'sliceShapeParts' function.
    SliceShape :: M.Ty
               -- ^ The type of the slice reference (either @&[T]@ or @&str@).
               -> M.Ty
               -- ^ The element type (either @T@ or @u8@).
               -> M.Mutability
               -- ^ Is the reference mutable or immutable?
               -> TypeRepr tp
               -- ^ The Crucible representation of the element type.
               -> TypeShape MirSlice
    -- | A shape for an enum type.
    EnumShape :: M.Ty
              -- ^ The overall enum type.
              -> [[M.Ty]]
              -- ^ The field types in each of the enum's variants.
              -> Assignment VariantShape variantsCtx
              -- ^ The shapes of the enum type's variants.
              -> M.Ty
              -- ^ The discriminant type.
              -> TypeShape discrTp
              -- ^ The shape of the discriminant type.
              -> TypeShape (RustEnumType discrTp variantsCtx)
    -- | Note that 'FnPtrShape' contains only 'TypeRepr's for the argument and
    -- result types, not 'TypeShape's, as none of our operations need to recurse
    -- inside them.
    FnPtrShape :: M.Ty -> CtxRepr args -> TypeRepr ret
               -> TypeShape (FunctionHandleType args ret)

-- TODO: Improve?
instance PP.Pretty (TypeShape tp) where
  pretty = PP.viaShow

deriving instance Show (TypeShape tp)
instance ShowF TypeShape

-- | The TypeShape of a struct field, which might have a MaybeType wrapper to
-- allow for partial initialization.
data FieldShape (tp :: CrucibleType) where
    OptField :: TypeShape tp -> FieldShape (MaybeType tp)
    ReqField :: TypeShape tp -> FieldShape tp

-- TODO: Improve?
instance PP.Pretty (FieldShape tp) where
  pretty = PP.viaShow

deriving instance Show (FieldShape tp)
instance ShowF FieldShape

-- | The 'TypeShape' of an enum variant, which consists of some number of field
-- types.
--
-- This is indexed by a 'StructType', but that is simply an artifact of the
-- particular way that @crucible-mir@ encodes enum types. Despite the use of
-- 'StructType' as a type index, we only use 'VariantShape' for enums, not
-- structs.
data VariantShape (tp :: CrucibleType) where
    VariantShape :: Assignment FieldShape ctx
                 -- ^ The shapes of the variant's field types.
                 -> VariantShape (StructType ctx)

-- TODO: Improve?
instance PP.Pretty (VariantShape tp) where
  pretty = PP.viaShow

deriving instance Show (VariantShape tp)
instance ShowF VariantShape

-- | Return the `TypeShape` of `ty`.
--
-- It is guaranteed that the `tp :: CrucibleType` index of the resulting
-- `TypeShape` matches that returned by `tyToRepr`.
tyToShape :: M.Collection -> M.Ty -> Some TypeShape
tyToShape col = go
  where
    go :: M.Ty -> Some TypeShape
    go ty = case ty of
        M.TyBool -> goPrim ty
        M.TyChar -> goPrim ty
        M.TyInt _ -> goPrim ty
        M.TyUint _ -> goPrim ty
        M.TyTuple [] -> goUnit ty
        M.TyTuple tys -> goTuple ty tys
        M.TyClosure tys -> goTuple ty tys
        M.TyFnDef _ -> goUnit ty
        M.TyArray ty' _ | Some shp <- go ty' -> Some $ ArrayShape ty ty' shp
        M.TyAdt nm _ _ -> case Map.lookup nm (col ^. M.adts) of
            Just adt | Just ty' <- reprTransparentFieldTy col adt ->
                mapSome (TransparentShape ty) $ go ty'
            Just (M.Adt _ kind vs _ _ _ _) ->
              case kind of
                M.Struct
                  |  [v] <- vs
                  -> goStruct ty (variantFieldTys v)
                  |  otherwise
                  -> error $ "tyToShape: Unexpected struct with multiple variants: "
                          ++ show (PP.pretty vs)
                M.Enum discrTy -> goEnum ty discrTy vs
                M.Union -> error "tyToShape: Union types NYI"
            Nothing -> error $ "tyToShape: bad adt: " ++ show ty
        M.TyRef ty' mutbl -> goRef ty ty' mutbl
        M.TyRawPtr ty' mutbl -> goRef ty ty' mutbl
        M.TyFnPtr sig -> goFnPtr ty sig
        _ -> error $ "tyToShape: " ++ show ty ++ " NYI"

    goPrim :: M.Ty -> Some TypeShape
    goPrim ty | Some tpr <- tyToRepr col ty, AsBaseType btpr <- asBaseType tpr =
        Some $ PrimShape ty btpr
    goPrim ty | Some tpr <- tyToRepr col ty =
        error $ "tyToShape: type " ++ show ty ++ " produced non-primitive type " ++ show tpr

    goUnit :: M.Ty -> Some TypeShape
    goUnit ty = Some $ UnitShape ty

    goTuple :: M.Ty -> [M.Ty] -> Some TypeShape
    goTuple ty tys | Some flds <- loop tys Empty = Some $ TupleShape ty tys flds
      where
        loop :: forall ctx. [M.Ty] -> Assignment FieldShape ctx -> Some (Assignment FieldShape)
        loop [] flds = Some flds
        loop (ty':tys') flds | Some fld <- go ty' = loop tys' (flds :> OptField fld)

    goStruct :: M.Ty -> [M.Ty] -> Some TypeShape
    goStruct ty tys | Some flds <- goFields tys = Some $ StructShape ty tys flds

    -- The first Ty is the overall enum type, and the second Ty is the
    -- discriminant type.
    goEnum :: M.Ty -> M.Ty -> [M.Variant] -> Some TypeShape
    goEnum ty discrTy vs
        | Some discrShp <- go discrTy
        , Some variants <- loop vs Empty
        = Some $ EnumShape ty variantTys variants discrTy discrShp
      where
        variantTys = map variantFieldTys vs

        loop ::
          forall ctx.
          [M.Variant] ->
          Assignment VariantShape ctx ->
          Some (Assignment VariantShape)
        loop [] variants = Some variants
        loop (v':vs') variants
          | Some variant <- goVariant v'
          = loop vs' (variants :> variant)

    -- Process a single Variant in an enum type.
    goVariant :: M.Variant -> Some VariantShape
    goVariant v
        | Some flds <- goFields tys
        = Some $ VariantShape flds
      where
        tys = variantFieldTys v

    goFields :: [M.Ty] -> Some (Assignment FieldShape)
    goFields tys = loop tys Empty
      where
        loop :: forall ctx. [M.Ty] -> Assignment FieldShape ctx -> Some (Assignment FieldShape)
        loop [] flds = Some flds
        loop (ty':tys') flds | Some fld <- goField ty' = loop tys' (flds :> fld)

    goField :: M.Ty -> Some FieldShape
    goField ty | Some shp <- go ty = case canInitialize col ty of
        True -> Some $ ReqField shp
        False -> Some $ OptField shp

    goRef :: M.Ty -> M.Ty -> M.Mutability -> Some TypeShape
    goRef ty ty' mutbl
      | M.TySlice slicedTy <- ty'
      , Some tpr <- tyToRepr col slicedTy
      = Some $ SliceShape ty slicedTy mutbl tpr
      | M.TyStr <- ty'
      = Some $ SliceShape ty (M.TyUint M.B8) mutbl (BVRepr (knownNat @8))
    goRef ty ty' _ | isUnsized ty' = error $
        "tyToShape: fat pointer " ++ show ty ++ " NYI"
    goRef ty ty' mutbl | Some tpr <- tyToRepr col ty' = Some $ RefShape ty ty' mutbl tpr

    goFnPtr :: M.Ty -> M.FnSig -> Some TypeShape
    goFnPtr ty (M.FnSig args ret _abi _spread) =
        tyListToCtx col args $ \argsr  ->
        tyToReprCont col ret $ \retr ->
           Some (FnPtrShape ty argsr retr)

    -- Retrieve the field types in a variant. This used for both struct and enum
    -- variants.
    variantFieldTys :: M.Variant -> [M.Ty]
    variantFieldTys v = v ^.. M.vfields . each . M.fty

-- | Given a `Ty` and the result of `tyToRepr ty`, produce a `TypeShape` with
-- the same index `tp`.  Raises an `error` if the `TypeRepr` doesn't match
-- `tyToRepr ty`.
tyToShapeEq :: HasCallStack => M.Collection -> M.Ty -> TypeRepr tp -> TypeShape tp
tyToShapeEq col ty tpr | Some shp <- tyToShape col ty =
    case testEquality (shapeType shp) tpr of
        Just Refl -> shp
        Nothing -> error $ "tyToShapeEq: type " ++ show ty ++
            " does not have representation " ++ show tpr ++
            " (got " ++ show (shapeType shp) ++ " instead)"

shapeType :: TypeShape tp -> TypeRepr tp
shapeType = go
  where
    go :: forall tp. TypeShape tp -> TypeRepr tp
    go (UnitShape _) = UnitRepr
    go (PrimShape _ btpr) = baseToType btpr
    go (TupleShape _ _ flds) = StructRepr $ fmapFC fieldShapeType flds
    go (ArrayShape _ _ shp) = MirVectorRepr $ shapeType shp
    go (StructShape _ _ flds) = StructRepr $ fmapFC fieldShapeType flds
    go (EnumShape _ _ variantTys _ discrShp) =
      RustEnumRepr (shapeType discrShp) (fmapFC variantShapeType variantTys)
    go (TransparentShape _ shp) = go shp
    go (RefShape _ _ _ _) = MirReferenceRepr
    go (SliceShape _ _ _ _) = MirSliceRepr
    go (FnPtrShape _ args ret) = FunctionHandleRepr args ret

fieldShapeType :: FieldShape tp -> TypeRepr tp
fieldShapeType (ReqField shp) = shapeType shp
fieldShapeType (OptField shp) = MaybeRepr $ shapeType shp

variantShapeType :: VariantShape tp -> TypeRepr tp
variantShapeType (VariantShape flds) =
  StructRepr $ fmapFC fieldShapeType flds

shapeMirTy :: TypeShape tp -> M.Ty
shapeMirTy (UnitShape ty) = ty
shapeMirTy (PrimShape ty _) = ty
shapeMirTy (TupleShape ty _ _) = ty
shapeMirTy (ArrayShape ty _ _) = ty
shapeMirTy (StructShape ty _ _) = ty
shapeMirTy (EnumShape ty _ _ _ _) = ty
shapeMirTy (TransparentShape ty _) = ty
shapeMirTy (RefShape ty _ _ _) = ty
shapeMirTy (SliceShape ty _ _ _) = ty
shapeMirTy (FnPtrShape ty _ _) = ty

fieldShapeMirTy :: FieldShape tp -> M.Ty
fieldShapeMirTy (ReqField shp) = shapeMirTy shp
fieldShapeMirTy (OptField shp) = shapeMirTy shp

shapeToTerm :: forall tp m.
    (MonadIO m, MonadFail m) =>
    SAW.SharedContext ->
    TypeShape tp ->
    m SAW.Term
shapeToTerm sc = go
  where
    go :: forall tp'. TypeShape tp' -> m SAW.Term
    go (UnitShape _) = liftIO $ SAW.scUnitType sc
    go (PrimShape _ BaseBoolRepr) = liftIO $ SAW.scBoolType sc
    go (PrimShape _ (BaseBVRepr w)) = liftIO $ SAW.scBitvector sc (natValue w)
    go (TupleShape _ _ flds) = do
        tys <- toListFC getConst <$> traverseFC (\x -> Const <$> goField x) flds
        liftIO $ SAW.scTupleType sc tys
    go (ArrayShape (M.TyArray _ n) _ shp) = do
        ty <- go shp
        n' <- liftIO $ SAW.scNat sc (fromIntegral n)
        liftIO $ SAW.scVecType sc n' ty
    go shp = fail $ "shapeToTerm: unsupported type " ++ show (shapeType shp)

    goField :: forall tp'. FieldShape tp' -> m SAW.Term
    goField (OptField shp) = go shp
    goField (ReqField shp) = go shp

-- | A witness that a 'TypeShape' is equal to a 'PrimShape' that characterizes
-- a bitvector.
data IsBVShape (tp :: CrucibleType) where
  IsBVShape :: (1 <= w)
            => M.Ty
            -> NatRepr w
            -> IsBVShape (BVType w)

-- | Check that a 'TypeShape' is equal to a 'PrimShape' that characterizes a
-- bitvector. If so, return 'Just' a witness of that equality. Otherwise, return
-- 'Nothing'.
testBVShape :: TypeShape tp -> Maybe (IsBVShape tp)
testBVShape shp =
  case shp of
    PrimShape ty (BaseBVRepr w)
      -> Just $ IsBVShape ty w
    _ -> Nothing

-- | A witness that a 'TypeShape' is equal to a 'RefShape'.
data IsRefShape (tp :: CrucibleType) where
  IsRefShape :: M.Ty
             -- ^ The reference type
             -> M.Ty
             -- ^ The pointee type
             -> M.Mutability
             -- ^ Is the reference mutable or immutable?
             -> TypeRepr tp
             -- ^ The Crucible representation of the pointee type
             -> IsRefShape MirReferenceType

-- | Check that a 'TypeShape' is equal to a 'RefShape'. If so, return 'Just' a
-- witness of that equality. Otherwise, return 'Nothing'.
testRefShape :: TypeShape tp -> Maybe (IsRefShape tp)
testRefShape shp =
  case shp of
    RefShape ty ty' mut shp'
      -> Just $ IsRefShape ty ty' mut shp'
    _ -> Nothing

-- | Construct the 'TypeShape's for a slice's reference and length types.
sliceShapeParts ::
    M.Ty ->
    M.Mutability ->
    TypeRepr tp ->
    (TypeShape MirReferenceType, TypeShape UsizeType)
sliceShapeParts referentTy refMutbl referentTpr =
    ( RefShape refTy referentTy refMutbl referentTpr
    , PrimShape usizeTy BaseUsizeRepr
    )
  where
    -- We use a ref (of the same mutability as `ty`) when possible, to
    -- avoid unnecessary clobbering.
    refTy = M.TyRef referentTy refMutbl
    usizeTy = M.TyUint M.USize

$(pure [])

instance TestEquality TypeShape where
  testEquality =
    $(structuralTypeEquality
        [t|TypeShape|]
        [ (TypeApp (ConType [t|TypeShape|]) AnyType, [|testEquality|])
        , (TypeApp (ConType [t|BaseTypeRepr|]) AnyType, [|testEquality|])
        , (TypeApp (TypeApp (ConType [t|Assignment|]) AnyType) AnyType, [|testEquality|])
        , (TypeApp (ConType [t|TypeRepr|]) AnyType, [|testEquality|])
        , (TypeApp (ConType [t|CtxRepr|]) AnyType, [|testEquality|])
        ])

instance TestEquality VariantShape where
  testEquality =
    $(structuralTypeEquality
        [t|VariantShape|]
        [ (TypeApp (TypeApp (ConType [t|Assignment|]) AnyType) AnyType, [|testEquality|])
        ])

instance TestEquality FieldShape where
  testEquality =
    $(structuralTypeEquality
        [t|FieldShape|]
        [ (TypeApp (ConType [t|TypeShape|]) AnyType, [|testEquality|])
        ])
