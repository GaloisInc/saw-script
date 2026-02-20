{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
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
  , AgElemShape(..)
  , CryTermAdaptor(..)
  , isCryNoAdapt
  , adaptTuple
  , adaptArray
  , tyToShape
  , tyToShapeEq
  , shapeType
  , fieldShapeType
  , variantShapeType
  , shapeMirTy
  , fieldShapeMirTy
  , shapeToTerm
  , shapeToTerm'
  , IsBVShape(..)
  , testBVShape
  , IsRefShape(..)
  , testRefShape
  , sliceShapeParts
  -- `MirAggregate` / `AgElemShape` helpers
  , buildMirAggregate
  , traverseMirAggregate
  , accessMirAggregate
  , accessMirAggregate'
  , zipMirAggregates
  , arrayAgElemShapes
  , buildMirAggregateArray
  , generateMirAggregateArray
  , traverseMirAggregateArray
  , accessMirAggregateArray
  , accessMirAggregateArray'
  -- Misc helpers
  , checkCompatibleTys
  , readMaybeType
  , readPartExprMaybe
  ) where

import Control.Lens ((^.), (^..), each)
import Control.Monad (when, forM, zipWithM)
import Control.Monad.IO.Class (MonadIO(..))
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (isJust)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Parameterized.Classes (ShowF)
import Data.Parameterized.Context (pattern Empty, pattern (:>), Assignment)
import Data.Parameterized.Some
import Data.Parameterized.TH.GADT
import Data.Parameterized.TraversableFC
import GHC.Stack (HasCallStack)
import Numeric.Natural (Natural)
import qualified Prettyprinter as PP

import qualified What4.Interface as W4
import qualified What4.Partial as W4

import Lang.Crucible.Backend (IsSymInterface)
import Lang.Crucible.Simulator.RegValue (RegValue)
import Lang.Crucible.Types

import qualified Mir.DefId as M
import Mir.Intrinsics
import qualified Mir.Mir as M
import Mir.TransTy ( tyListToCtx, tyToRepr, tyToReprCont, canInitialize
                   , isUnsized, reprTransparentFieldTy )

import SAWCentral.Panic (panic)
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
    PrimShape :: M.Ty -> BaseTypeRepr btp -> TypeShape (BaseToType btp)
    -- | A shape for tuples, as well as for tuple-like types (e.g.,
    -- 'M.TyFnDef', which is treated like an empty tuple).
    TupleShape :: M.Ty -> [AgElemShape] -> TypeShape MirAggregateType
    ArrayShape :: M.Ty
               -- ^ The array type
               -> M.Ty
               -- ^ The array element type
               -> Word
               -- ^ Size of the array element type, in bytes
               -> TypeShape tp
               -- ^ `TypeShape` of the array element type
               -> Word
               -- ^ Length of the array
               -> TypeShape MirAggregateType
    StructShape :: M.Ty -> [M.Ty] -> Assignment FieldShape ctx -> TypeShape (StructType ctx)
    TransparentShape :: M.Ty -> TypeShape tp -> TypeShape tp
    -- | Note that RefShape contains only a TypeRepr for the pointee type, not
    -- a TypeShape.  None of our operations need to recurse inside pointers,
    -- and also this saves us from some infinite recursion.
    --
    -- If there are raw pointer casts involved, the pointee type, the pointee
    -- type contained in the reference type, and the pointee 'TypeRepr' might
    -- not reflect the actual pointee type of any Crucible reference that is
    -- paired with this 'TypeShape'. See @Note [Raw pointer casts]@ in
    -- "SAWCentral.Crucible.MIR.Setup.Value" for more info.
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

data AgElemShape where
    AgElemShape :: Word -> Word -> TypeShape tp -> AgElemShape

-- TODO: Improve?
instance PP.Pretty AgElemShape where
  pretty = PP.viaShow

deriving instance Show AgElemShape


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
        M.TyTuple tys -> goTuple ty tys
        M.TyClosure tys -> goTuple ty tys
        M.TyFnDef _ -> goTuple ty []
        M.TyArray ty' len | Some shp <- go ty' ->
          let elemSz = 1 in   -- TODO: hardcoded size=1
          Some $ ArrayShape ty ty' elemSz shp (fromIntegral len)
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
    goPrim ty =
      case tyToRepr col ty of
        Left err -> error ("goPrim: type " ++ show ty ++ " not supported: " ++ err)
        Right (Some tpr)
          | AsBaseType btpr <- asBaseType tpr -> Some (PrimShape ty btpr)
          | otherwise -> error ("goPrim: type " ++ show ty ++ " produced non-primitive type " ++ show tpr)

    goTuple :: M.Ty -> [M.Ty] -> Some TypeShape
    goTuple ty tys = Some $ TupleShape ty (zipWith mkElem [0..] tys)
      where
        mkElem i ty' | Some shp <- go ty' = AgElemShape i 1 shp

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
      | M.TySlice slicedTy <- ty' =
        case tyToRepr col slicedTy of
          Left err -> error ("goRef: " ++ err)
          Right (Some tpr) -> Some (SliceShape ty slicedTy mutbl tpr)
      | M.TyStr <- ty'
      = Some $ SliceShape ty (M.TyUint M.B8) mutbl (BVRepr (knownNat @8))
    goRef ty ty' _ | isUnsized ty' = error $
        "tyToShape: fat pointer " ++ show ty ++ " NYI"
    goRef ty ty' mutbl =
      case tyToRepr col ty' of
        Left err -> error ("goRef: " ++ err)
        Right (Some tpr) -> Some (RefShape ty ty' mutbl tpr)

    goFnPtr :: M.Ty -> M.FnSig -> Some TypeShape
    goFnPtr ty (M.FnSig args ret _abi) =
        case tyListToCtx col args $ \argsr  ->
             tyToReprCont col ret $ \retr ->
             Right (Some (FnPtrShape ty argsr retr)) of
          Left err -> error ("goFnPtr: " ++ err)
          Right x -> x

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
    go (PrimShape _ btpr) = baseToType btpr
    go (TupleShape _ _) = MirAggregateRepr
    go (ArrayShape _ _ _ _ _) = MirAggregateRepr
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
shapeMirTy (PrimShape ty _) = ty
shapeMirTy (TupleShape ty _) = ty
shapeMirTy (ArrayShape ty _ _ _ _) = ty
shapeMirTy (StructShape ty _ _) = ty
shapeMirTy (EnumShape ty _ _ _ _) = ty
shapeMirTy (TransparentShape ty _) = ty
shapeMirTy (RefShape ty _ _ _) = ty
shapeMirTy (SliceShape ty _ _ _) = ty
shapeMirTy (FnPtrShape ty _ _) = ty

fieldShapeMirTy :: FieldShape tp -> M.Ty
fieldShapeMirTy (ReqField shp) = shapeMirTy shp
fieldShapeMirTy (OptField shp) = shapeMirTy shp

-- | This is to accomodate multiple Rust types mapping to the same Cryptol
-- type.  For example, if a Cryptol function expects [3][8], we could map
-- it to a Rust function that either expects `[u8;3]`, or `&[u8]` with a
-- dynamic check that it has 3 elements.  The type parameter `a` is for the
-- the lengths of the slices---it will be either Cryptol's `Type` during
-- type checking, or `Integer`, once we instantiate a schema at a concrete
-- type.
data CryTermAdaptor a =
    NoAdapt                               -- ^ Use default translation
  | AdaptTuple [CryTermAdaptor a]         -- ^ Adapt a tuple
  | AdaptArray (CryTermAdaptor a)         -- ^ Adapt an array
  | AdaptDerefSlice M.Collection a (CryTermAdaptor a)
    -- ^ A reference to a slice.
    -- We also store the 'M.Collection' here so that we can convert the
    -- element type's 'TypeRepr' to a 'TypeShape' when we need to (see,
    -- for instance, the implementation of `shapeToTerm'`).
  | AdaptDerefRef M.Collection (CryTermAdaptor a) -- ^ Transparently adapt a reference
    deriving (Functor, Foldable, Traversable)

isCryNoAdapt :: CryTermAdaptor a -> Bool
isCryNoAdapt ada =
  case ada of
    NoAdapt -> True
    _       -> False

adaptTuple :: [CryTermAdaptor a] -> CryTermAdaptor a
adaptTuple as
  | all isCryNoAdapt as = NoAdapt
  | otherwise = AdaptTuple as

adaptArray :: CryTermAdaptor a -> CryTermAdaptor a
adaptArray a
  | isCryNoAdapt a = NoAdapt
  | otherwise = AdaptArray a

shapeToTerm :: forall tp m.
    (MonadIO m, MonadFail m) =>
    SAW.SharedContext ->
    TypeShape tp ->
    m SAW.Term
shapeToTerm sc = shapeToTerm' sc NoAdapt

-- | Convert a type shape to a `Term` representing the type of values we'd
-- get for the type shape.  References to slices are mapped to vectors (the values
-- pointed to by the reference), and the `CryTermAnnot`, if any,
-- contains the information about the length of the vector.
shapeToTerm' :: forall tp m.
    (MonadIO m, MonadFail m) =>
    SAW.SharedContext ->
    CryTermAdaptor Integer ->
    TypeShape tp ->
    m SAW.Term
shapeToTerm' sc = go
  where
    go :: forall tp'. CryTermAdaptor Integer -> TypeShape tp' -> m SAW.Term
    go NoAdapt (PrimShape _ BaseBoolRepr) = liftIO $ SAW.scBoolType sc
    go NoAdapt (PrimShape _ (BaseBVRepr w)) = liftIO $ SAW.scBitvector sc (natValue w)
    go ada (TupleShape _ elems) = do
        subAda <- case ada of
                    NoAdapt -> pure (repeat NoAdapt)
                    AdaptTuple as -> pure as
                    _ -> fail "Expected a tuple Cryptol adaptor"
        tys <- zipWithM goAgElem subAda elems
        liftIO $ SAW.scTupleType sc tys
    go ada (ArrayShape _ _ _ shp len) = do
        sub <- case ada of
                 NoAdapt -> pure NoAdapt
                 AdaptArray a -> pure a
                 _ -> fail "Expected an array Cryptol adaptor"
        ty <- go sub shp
        liftIO (mkVec len ty)
    go (AdaptDerefSlice col n ada) (SliceShape _ elT M.Immut tpr) =
      do et <- go ada (tyToShapeEq col elT tpr)
         liftIO (mkVec n et)
    go (AdaptDerefRef col ada) (RefShape _ elT M.Immut tpr) =
      go ada (tyToShapeEq col elT tpr)
    go _ada shp = fail $ "shapeToTerm: unsupported type " ++ show (shapeType shp)

    mkVec :: Integral a => a -> SAW.Term -> IO SAW.Term
    mkVec n ty =
      do
        n' <- SAW.scNat sc (fromIntegral n)
        SAW.scVecType sc n' ty

    goAgElem :: CryTermAdaptor Integer -> AgElemShape -> m SAW.Term
    goAgElem ada (AgElemShape _ _ shp) = go ada shp


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


-- Helpers for manipulating `MirAggregate` with matching `AgElemShape`s.

agCheckLengthsEq :: Monad m => Text -> [AgElemShape] -> [a] -> m ()
agCheckLengthsEq loc elems xs =
  when (length elems /= length xs) $
    panic loc
      [Text.pack $ "got " ++ show (length elems) ++ " elems, but " ++ show (length xs) ++ " xs"]

agCheckKeysEq :: MonadFail m => String -> [AgElemShape] -> IntMap (MirAggregateEntry sym) -> m ()
agCheckKeysEq loc elems m = do
  let mKeys = IntMap.keysSet m
  let elemsKeys = IntSet.fromList [fromIntegral off | AgElemShape off _ _ <- elems]
  when (mKeys /= elemsKeys) $
    if mKeys `IntSet.isSubsetOf` elemsKeys
      then fail $ loc ++ ": missing or uninitialized fields at offsets "
        ++ show (elemsKeys IntSet.\\ mKeys)
      else fail $ loc ++ ": expected aggregate to have fields at offsets "
        ++ show elemsKeys ++ ", but got fields at offsets " ++ show mKeys

-- | Build a `MirAggregate` with one entry for each provided `AgElemShape`.
-- The callback receives the offset, size, and type of the entry, along with
-- the corresponding value from @xs@ (which must have as many items as there
-- are `AgElemShape`s), and the result of the callback is used as the value for
-- the entry.
buildMirAggregate ::
  (IsSymInterface sym, Monad m, MonadFail m) =>
  sym ->
  [AgElemShape] ->
  [a] ->
  (forall tp. Word -> Word -> TypeShape tp -> a -> m (RegValue sym tp)) ->
  m (MirAggregate sym)
buildMirAggregate sym elems xs f = do
  agCheckLengthsEq "buildMirAggregate" elems xs
  let totalSize = maximum (0 : [off + sz | AgElemShape off sz _ <- elems])
  entries <- forM (zip elems xs) $ \(AgElemShape off sz shp, x) -> do
    rv <- f off sz shp x
    let rvPart = W4.justPartExpr sym rv
    return (fromIntegral off, MirAggregateEntry sz (shapeType shp) rvPart)
  return $ MirAggregate totalSize (IntMap.fromList entries)

-- | Modify the value of each entry in a `MirAggregate`.  The callback gets the
-- offset, size, type, and value of the entry, and its result is stored as the
-- new value in the output.
traverseMirAggregate ::
  forall sym m.
  (IsSymInterface sym, Monad m, MonadFail m, MonadIO m) =>
  sym ->
  [AgElemShape] ->
  MirAggregate sym ->
  (forall tp. Word -> Word -> TypeShape tp -> RegValue sym tp -> m (RegValue sym tp)) ->
  m (MirAggregate sym)
traverseMirAggregate sym elems (MirAggregate totalSize m) f = do
  agCheckKeysEq "traverseMirAggregate" elems m
  m' <-
    -- Hack: we include a special case for when the list of AgElemShapes and
    -- the MirAggregate are both empty, skipping the call to mergeEntries
    -- entirely if this is the case. This is because mergeEntries calls
    -- IntMap.mergeWithKey under the hood, and prior to containers-0.8, the
    -- implementation of IntMap.mergeWithKey had a bug where merging two empty
    -- IntMaps would invoke the third callback argument instead of just
    -- returning an empty map. (See
    -- https://github.com/haskell/containers/issues/979.) Note that
    -- mergeEntries uses the third callback argument to panic, however, and we
    -- definitely don't want to panic if the IntMaps are both empty!
    --
    -- Because SAW still supports GHC versions that bundle versions of
    -- containers that are older than 0.8 (and therefore do not contain a fix
    -- for the issue above), we include this special case as a workaround. Once
    -- SAW drops support for pre-0.8 versions of containers, we can remove this
    -- special case.
    if null elems && IntMap.null m
      then pure IntMap.empty
      else mergeEntries
  return $ MirAggregate totalSize m'
 where
  -- Merge the existing MirAggregate's entries together with the new entries
  -- from the list of AgElemShapes.
  --
  -- Precondition: both the list of AgElemShapes and the MirAggregate are
  -- non-empty (see the comments above near mergeEntries' call site).
  mergeEntries :: m (IntMap (MirAggregateEntry sym))
  mergeEntries = sequence $ IntMap.mergeWithKey
    (\_off' (AgElemShape off _sz' shp) (MirAggregateEntry sz tpr rvPart) -> Just $ do
        Refl <- case testEquality tpr (shapeType shp) of
            Just pf -> return pf
            Nothing -> fail $ "traverseMirAggregate: ill-typed field value at offset "
              ++ show off ++ ": expected " ++ show (shapeType shp) ++ ", but got " ++ show tpr
        let rv = readMaybeType sym "elem" tpr rvPart
        rv' <- f off sz shp rv
        let rvPart' = W4.justPartExpr sym rv'
        return $ MirAggregateEntry sz tpr rvPart')
    (\_ -> panic "traverseMirAggregate" ["mismatched keys in aggregate"])
    (\_ -> panic "traverseMirAggregate" ["mismatched keys in aggregate"])
    (IntMap.fromList [(fromIntegral off, e) | e@(AgElemShape off _ _) <- elems])
    m

-- | Extract values from a `MirAggregate`, one for each entry.  The callback
-- gets the offset, size, type, and value of the entry.  Callback results are
-- returned in a list in the same order as @elems@.
accessMirAggregate ::
  (IsSymInterface sym, Monad m, MonadFail m, MonadIO m) =>
  sym ->
  [AgElemShape] ->
  MirAggregate sym ->
  (forall tp. Word -> Word -> TypeShape tp -> RegValue sym tp -> m b) ->
  m [b]
accessMirAggregate sym elems ag f =
  accessMirAggregate' sym elems [() | _ <- elems] ag $
    \off sz shp val () -> f off sz shp val


-- | Extract values from a `MirAggregate`, one for each entry.  This is like
-- `accessMirAggregate`, but the callback also gets the value from the input
-- list @xs@ that corresponds to the current entry.
accessMirAggregate' ::
  (IsSymInterface sym, Monad m, MonadFail m, MonadIO m) =>
  sym ->
  [AgElemShape] ->
  [a] ->
  MirAggregate sym ->
  (forall tp. Word -> Word -> TypeShape tp -> RegValue sym tp -> a -> m b) ->
  m [b]
accessMirAggregate' sym elems xs (MirAggregate _totalSize m) f = do
  agCheckLengthsEq "accessMirAggregate'" elems xs
  agCheckKeysEq "accessMirAggregate'" elems m
  forM (zip elems xs) $ \(AgElemShape off sz shp, x) -> do
    MirAggregateEntry _sz' tpr rvPart <-
      case IntMap.lookup (fromIntegral off) m of
        Just e -> return e
        -- Should be impossible, since we checked above that the key sets
        -- match.
        Nothing -> panic "accessMirAggregate"
          [Text.pack $ "missing MirAggregateEntry at offset " ++ show off]
    Refl <- case testEquality tpr (shapeType shp) of
      Just pf -> return pf
      Nothing -> fail $ "accessMirAggregate: ill-typed field value at offset "
        ++ show off ++ ": expected " ++ show (shapeType shp) ++ ", but got " ++ show tpr
    let rv = readMaybeType sym "elem" tpr rvPart
    f off sz shp rv x

-- | Zip together two `MirAggregate`s and extract values from them.  The callback
-- gets the offset, size, type, and the value at that offset in each aggregate.
-- Callback results are returned in a list in the same order as @elems@.
zipMirAggregates ::
  (IsSymInterface sym, Monad m, MonadFail m, MonadIO m) =>
  sym ->
  [AgElemShape] ->
  MirAggregate sym ->
  MirAggregate sym ->
  (forall tp. Word -> Word -> TypeShape tp -> RegValue sym tp -> RegValue sym tp -> m b) ->
  m [b]
zipMirAggregates sym elems (MirAggregate _totalSize1 m1) (MirAggregate _totalSize2 m2) f = do
  agCheckKeysEq "zipMirAggregates" elems m1
  agCheckKeysEq "zipMirAggregates" elems m2
  -- We don't require the `totalSize`s of the two aggregates to match.
  -- `buildMirAggregate` sets the `totalSize` to the end of the last field, but
  -- other methods of building aggregates use the actual layout from rustc,
  -- which may have extra padding at the end.
  forM elems $ \(AgElemShape off sz shp) -> do
    MirAggregateEntry _sz1 tpr1 rvPart1 <-
      case IntMap.lookup (fromIntegral off) m1 of
        Just e -> return e
        Nothing -> panic "zipMirAggregates"
          [Text.pack $ "missing MirAggregateEntry at offset " ++ show off
            ++ " (in first input)"]
    MirAggregateEntry _sz2 tpr2 rvPart2 <-
      case IntMap.lookup (fromIntegral off) m2 of
        Just e -> return e
        Nothing -> panic "zipMirAggregates"
          [Text.pack $ "missing MirAggregateEntry at offset " ++ show off
            ++ " (in second input)"]
    Refl <- case testEquality tpr1 (shapeType shp) of
      Just pf -> return pf
      Nothing -> fail $ "zipMirAggregates: ill-typed field value at offset "
        ++ show off ++ ": expected " ++ show (shapeType shp) ++ ", but got " ++ show tpr1
        ++ " (in first aggregate)"
    Refl <- case testEquality tpr2 (shapeType shp) of
      Just pf -> return pf
      Nothing -> fail $ "zipMirAggregates: ill-typed field value at offset "
        ++ show off ++ ": expected " ++ show (shapeType shp) ++ ", but got " ++ show tpr2
        ++ " (in second aggregate)"
    let rv1 = readMaybeType sym "elem" tpr1 rvPart1
    let rv2 = readMaybeType sym "elem" tpr2 rvPart2
    f off sz shp rv1 rv2


-- | Generate a list of `AgElemShape`s corresponding to positions within an
-- array.  The resulting list can then be used with `buildMirAggregate` and
-- similar functions to manipulate array aggregates.
arrayAgElemShapes ::
  -- | Size of array element type
  Word ->
  -- | `TypeShape` of array element type
  TypeShape tp ->
  -- | Array length
  Word ->
  [AgElemShape]
arrayAgElemShapes elemSz elemShp len
  | len == 0 = []
  | otherwise = [AgElemShape (i * elemSz) elemSz elemShp | i <- [0 .. len - 1]]

agArrayCheckLengthsEq :: Monad m => Text -> Word -> [a] -> m ()
agArrayCheckLengthsEq loc len xs =
  when (fromIntegral len /= length xs) $
    panic loc
      [Text.pack $ "got len = " ++ show len ++ ", but " ++ show (length xs) ++ " xs"]

buildMirAggregateArray ::
  (IsSymInterface sym, Monad m, MonadFail m) =>
  sym ->
  -- | Size of array element type
  Word ->
  -- | `TypeShape` of array element type
  TypeShape tp ->
  -- | Array length
  Word ->
  [a] ->
  (Word -> a -> m (RegValue sym tp)) ->
  m (MirAggregate sym)
buildMirAggregateArray sym elemSz elemShp len xs f = do
  agArrayCheckLengthsEq "buildMirAggregateArray" len xs
  let elems = arrayAgElemShapes elemSz elemShp len
  buildMirAggregate sym elems xs $
    \off _sz shp x -> do
      Refl <- case testEquality (shapeType shp) (shapeType elemShp) of
        Just pf -> return pf
        Nothing -> panic "buildMirAggregateArray"
          ["impossible: arrayAgElemShapes always uses the input TypeShape"]
      f off x

generateMirAggregateArray ::
  (IsSymInterface sym, Monad m, MonadFail m) =>
  sym ->
  -- | Size of array element type
  Word ->
  -- | `TypeShape` of array element type
  TypeShape tp ->
  -- | Array length
  Word ->
  (Word -> m (RegValue sym tp)) ->
  m (MirAggregate sym)
generateMirAggregateArray sym elemSz elemShp len f = do
  buildMirAggregateArray sym elemSz elemShp len (init [0 .. len]) $ \_off i -> f i

traverseMirAggregateArray ::
  forall sym m tp.
  (IsSymInterface sym, Monad m, MonadFail m, MonadIO m) =>
  sym ->
  -- | Size of array element type
  Word ->
  -- | `TypeShape` of array element type
  TypeShape tp ->
  -- | Array length
  Word ->
  MirAggregate sym ->
  (Word -> RegValue sym tp -> m (RegValue sym tp)) ->
  m (MirAggregate sym)
traverseMirAggregateArray sym elemSz elemShp len ag f = do
  let elems = arrayAgElemShapes elemSz elemShp len
  traverseMirAggregate sym elems ag $
    \off _sz shp rv -> do
      Refl <- case testEquality (shapeType shp) (shapeType elemShp) of
        Just pf -> return pf
        Nothing -> panic "traverseMirAggregateArray"
          ["impossible: arrayAgElemShapes always uses the input TypeShape"]
      f off rv

accessMirAggregateArray ::
  (IsSymInterface sym, Monad m, MonadFail m, MonadIO m) =>
  sym ->
  -- | Size of array element type
  Word ->
  -- | `TypeShape` of array element type
  TypeShape tp ->
  -- | Array length
  Word ->
  MirAggregate sym ->
  (Word -> RegValue sym tp -> m b) ->
  m [b]
accessMirAggregateArray sym elemSz elemShp len ag f = do
  let xs = replicate (fromIntegral len) ()
  accessMirAggregateArray' sym elemSz elemShp len xs ag $
    \off val () -> f off val

accessMirAggregateArray' ::
  (IsSymInterface sym, Monad m, MonadFail m, MonadIO m) =>
  sym ->
  -- | Size of array element type
  Word ->
  -- | `TypeShape` of array element type
  TypeShape tp ->
  -- | Array length
  Word ->
  [a] ->
  MirAggregate sym ->
  (Word -> RegValue sym tp -> a -> m b) ->
  m [b]
accessMirAggregateArray' sym elemSz elemShp len xs ag f = do
  agArrayCheckLengthsEq "accessMirAggregateArray'" len xs
  let elems = arrayAgElemShapes elemSz elemShp (fromIntegral $ length xs)
  accessMirAggregate' sym elems xs ag $
    \off _sz shp rv x -> do
      Refl <- case testEquality (shapeType shp) (shapeType elemShp) of
        Just pf -> return pf
        Nothing -> panic "accessMirAggregateArray'"
          ["impossible: arrayAgElemShapes always uses the input TypeShape"]
      f off rv x


-- Misc helpers

-- | Read the value out of a 'MaybeType' expression that is assumed to be
-- assigned to a value. If this assumption does not hold (i.e., if the value is
-- unassigned), then this function will raise an error.
readMaybeType ::
  IsSymInterface sym =>
  sym ->
  String ->
  TypeRepr tp ->
  RegValue sym (MaybeType tp) ->
  RegValue sym tp
readMaybeType sym desc tpr rv =
  case readPartExprMaybe sym rv of
    Just x -> x
    Nothing -> error $ "readMaybeType: accessed possibly-uninitialized " ++ desc ++
        " of type " ++ show tpr

readPartExprMaybe ::
  IsSymInterface sym =>
  sym ->
  W4.PartExpr (W4.Pred sym) a ->
  Maybe a
readPartExprMaybe _sym W4.Unassigned = Nothing
readPartExprMaybe _sym (W4.PE p v)
  | Just True <- W4.asConstantPred p = Just v
  | otherwise = Nothing


$(pure [])

-- | Check if two 'M.Ty's are compatible in SAW. This is a slightly coarser
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
--    @N@ is the number of bits corresponding to the 'SizeBits' type in
--    "M.Intrinsics". (This is a bit unsavory, as the actual size of
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
checkCompatibleTys :: M.Ty -> M.Ty -> Bool
checkCompatibleTys ty1 ty2 = tyView ty1 == tyView ty2

-- | Like 'M.Ty', but where:
--
-- * The 'TyInt' and 'TyUint' constructors have been collapsed into a single
--   'TyViewInt' constructor.
--
-- * 'TyViewInt' uses 'BaseSizeView' instead of 'M.BaseSize'.
--
-- * Recursive occurrences of 'M.Ty' use 'TyView' instead. This also applies
--   to fields of type 'SubstsView' and 'FnSigView', which also replace 'M.Ty'
--   with 'TyView' in their definitions.
--
-- This provides a coarser notion of equality than what the 'Eq' instance for
-- 'M.Ty' provides, which distinguishes the two sorts of integer types.
--
-- This is an internal data type that is used to power the 'checkCompatibleTys'
-- function. Refer to the Haddocks for that function for more information on why
-- this is needed.
data TyView
  = TyViewBool
  | TyViewChar
    -- | The sole integer type. Both 'TyInt' and 'TyUint' are mapped to
    -- 'TyViewInt', and 'BaseSizeView' is used instead of 'M.BaseSize'.
  | TyViewInt !BaseSizeView
  | TyViewTuple ![TyView]
  | TyViewSlice !TyView
  | TyViewArray !TyView !Int
  | TyViewRef !TyView !M.Mutability
  | TyViewAdt !M.DefId !M.DefId !SubstsView
  | TyViewFnDef !M.DefId
  | TyViewClosure [TyView]
  | TyViewStr
  | TyViewFnPtr !FnSigView
  | TyViewDynamic !M.TraitName
  | TyViewRawPtr !TyView !M.Mutability
  | TyViewFloat !M.FloatKind
  | TyViewDowncast !TyView !Integer
  | TyViewNever
  | TyViewForeign
  | TyViewLifetime
  | TyViewConst !M.ConstVal
  | TyViewCoroutine !CoroutineArgsView
  | TyViewCoroutineClosure [TyView]
  | TyViewErased
  | TyViewInterned M.TyName
  deriving Eq

-- | Like 'M.BaseSize', but without a special case for @usize@/@isize@.
-- Instead, these are mapped to their actual size, which is determined by the
-- number of bits in the 'SizeBits' type in "M.Intrinsics". (This is a bit
-- unsavory, as the actual size of @usize@/@isize@ is platform-dependent, but
-- this is the current approach.)
data BaseSizeView
  = B8View
  | B16View
  | B32View
  | B64View
  | B128View
  deriving Eq

-- | Like 'M.Substs', but using 'TyView's instead of 'M.Ty'.
--
-- This is an internal data type that is used to power the 'checkCompatibleTys'
-- function. Refer to the Haddocks for that function for more information on why
-- this is needed.
newtype SubstsView = SubstsView [TyView]
  deriving Eq

-- | Like 'M.FnSig', but using 'TyView's instead of 'M.Ty'.
--
-- This is an internal data type that is used to power the 'checkCompatibleTys'
-- function. Refer to the Haddocks for that function for more information on why
-- this is needed.
data FnSigView = FnSigView {
    _fsvarg_tys    :: ![TyView]
  , _fsvreturn_ty  :: !TyView
  , _fsvabi        :: M.Abi
  }
  deriving Eq

-- | Like 'M.CoroutineArgs', but using 'TyView's instead of 'M.Ty'.
--
-- This is an internal data type that is used to power the 'checkCompatibleTys'
-- function. Refer to the Haddocks for that function for more information on why
-- this is needed.
data CoroutineArgsView = CoroutineArgsView
  { _cavDiscrTy :: !TyView
  , _cavUpvarTys :: ![TyView]
  , _cavSavedTys :: ![TyView]
  , _cavFieldMap :: !(Map (Int, Int) Int)
  } deriving Eq

-- | Convert a 'M.Ty' value to a 'TyView' value.
tyView :: M.Ty -> TyView
-- The two most important cases. Both sorts of integers are mapped to TyViewInt.
tyView (M.TyInt  bs) = TyViewInt (baseSizeView bs)
tyView (M.TyUint bs) = TyViewInt (baseSizeView bs)
-- All other cases are straightforward.
tyView M.TyBool = TyViewBool
tyView M.TyChar = TyViewChar
tyView (M.TyTuple tys) = TyViewTuple (map tyView tys)
tyView (M.TySlice ty) = TyViewSlice (tyView ty)
tyView (M.TyArray ty n) = TyViewArray (tyView ty) n
tyView (M.TyRef ty mut) = TyViewRef (tyView ty) mut
tyView (M.TyAdt monoDid origDid substs) =
  TyViewAdt monoDid origDid (substsView substs)
tyView (M.TyFnDef did) = TyViewFnDef did
tyView (M.TyClosure tys) = TyViewClosure (map tyView tys)
tyView M.TyStr = TyViewStr
tyView (M.TyFnPtr sig) = TyViewFnPtr (fnSigView sig)
tyView (M.TyDynamic trait) = TyViewDynamic trait
tyView (M.TyRawPtr ty mut) = TyViewRawPtr (tyView ty) mut
tyView (M.TyFloat fk) = TyViewFloat fk
tyView (M.TyDowncast ty n) = TyViewDowncast (tyView ty) n
tyView M.TyNever = TyViewNever
tyView M.TyForeign = TyViewForeign
tyView M.TyLifetime = TyViewLifetime
tyView (M.TyConst c) = TyViewConst c
tyView (M.TyCoroutine ca) = TyViewCoroutine (coroutineArgsView ca)
tyView (M.TyCoroutineClosure tys) = TyViewCoroutineClosure (map tyView tys)
tyView M.TyErased = TyViewErased
tyView (M.TyInterned nm) = TyViewInterned nm

-- | Convert a 'M.BaseSize' value to a 'BaseSizeView' value.
baseSizeView :: M.BaseSize -> BaseSizeView
baseSizeView M.B8    = B8View
baseSizeView M.B16   = B16View
baseSizeView M.B32   = B32View
baseSizeView M.B64   = B64View
baseSizeView M.B128  = B128View
baseSizeView M.USize =
  case Map.lookup (W4.natValue sizeBitsRepr) bitSizesMap of
    Just bsv -> bsv
    Nothing ->
      error $ "M.Intrinsics.BaseSize bit size not supported: " ++ show sizeBitsRepr
  where
    sizeBitsRepr = W4.knownNat @SizeBits

    bitSizesMap :: Map Natural BaseSizeView
    bitSizesMap = Map.fromList
      [ (W4.natValue (W4.knownNat @8),   B8View)
      , (W4.natValue (W4.knownNat @16),  B16View)
      , (W4.natValue (W4.knownNat @32),  B32View)
      , (W4.natValue (W4.knownNat @64),  B64View)
      , (W4.natValue (W4.knownNat @128), B128View)
      ]

-- | Convert a 'M.Substs' value to a 'SubstsView' value.
substsView :: M.Substs -> SubstsView
substsView (M.Substs tys) = SubstsView (map tyView tys)

-- | Convert a 'M.FnSig' value to a 'FnSigView' value.
fnSigView :: M.FnSig -> FnSigView
fnSigView (M.FnSig argTys retTy abi) =
  FnSigView (map tyView argTys) (tyView retTy) abi

-- | Convert a 'M.CoroutineArgs' value to a 'CoroutineArgsView' value.
coroutineArgsView :: M.CoroutineArgs -> CoroutineArgsView
coroutineArgsView (M.CoroutineArgs discrTy upvarTys savedTys fieldMap) =
  CoroutineArgsView
    (tyView discrTy)
    (map tyView upvarTys)
    (map tyView savedTys)
    fieldMap

instance TestEquality TypeShape where
  testEquality =
    $(structuralTypeEquality
        [t|TypeShape|]
        [ (TypeApp (ConType [t|TypeShape|]) AnyType, [|testEquality|])
        , (TypeApp (ConType [t|BaseTypeRepr|]) AnyType, [|testEquality|])
        , (TypeApp (TypeApp (ConType [t|Assignment|]) AnyType) AnyType, [|testEquality|])
        , (TypeApp (ConType [t|TypeRepr|]) AnyType, [|testEquality|])
        , (TypeApp (ConType [t|CtxRepr|]) AnyType, [|testEquality|])
          -- See #1976 for why we use checkCompatibleTys to compare MIR types
          -- instead of (==).
        , (ConType [t|M.Ty|], [| \x y -> if checkCompatibleTys x y then Just Refl else Nothing |])
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

instance Eq AgElemShape where
    AgElemShape off1 sz1 shp1 == AgElemShape off2 sz2 shp2 =
        off1 == off2
            && sz1 == sz2
            && isJust (testEquality shp1 shp2)
