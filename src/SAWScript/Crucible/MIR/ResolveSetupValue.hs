{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Turns 'SetupValue's back into 'MIRVal's.
module SAWScript.Crucible.MIR.ResolveSetupValue
  ( MIRVal(..)
  , ppMIRVal
  , resolveSetupVal
  , typeOfSetupValue
  , lookupAllocIndex
  , toMIRType
  , resolveTypedTerm
  , resolveBoolTerm
  , resolveSAWPred
  , equalRefsPred
  , equalValsPred
  , checkCompatibleTys
  , readMaybeType
  , doAlloc
  , doPointsTo
  , firstPointsToReferent
  , mirAdtToTy
  , findDefId
  , findDefIdEither
    -- * Static items
  , findStatic
  , findStaticInitializer
  , findStaticVar
  , staticRefMux
    -- * Enum discriminants
  , getEnumVariantDiscr
  , testDiscriminantIsBV
  , variantIntIndex
    -- * Types of errors
  , MIRTypeOfError(..)
  ) where

import           Control.Lens
import           Control.Monad (guard, unless, zipWithM, zipWithM_)
import qualified Control.Monad.Catch as X
import           Control.Monad.IO.Class (MonadIO(..))
import           Control.Monad.Trans.Maybe (MaybeT(..))
import qualified Data.BitVector.Sized as BV
import qualified Data.Foldable as F
import qualified Data.Functor.Product as Functor
import           Data.Kind (Type)
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
import           Data.Vector (Vector)
import           Data.Void (absurd)
import           Numeric.Natural (Natural)
import qualified Prettyprinter as PP

import qualified Cryptol.Eval.Type as Cryptol (TValue(..), tValTy, evalValType)
import qualified Cryptol.TypeCheck.AST as Cryptol (Type, Schema(..))
import qualified Cryptol.Utils.PP as Cryptol (pp)
import Lang.Crucible.Backend (IsSymInterface)
import Lang.Crucible.Simulator
  ( AnyValue(..), GlobalVar(..), RegValue, RegValue'(..), SymGlobalState
  , VariantBranch(..), injectVariant
  )
import Lang.Crucible.Types (AnyType, MaybeType, TypeRepr(..))
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

import Verifier.SAW.Cryptol (importType, emptyEnv)
import Verifier.SAW.SharedTerm
import qualified Verifier.SAW.Prim as Prim
import qualified Verifier.SAW.Simulator.Concrete as Concrete
import Verifier.SAW.Simulator.What4.ReturnTrip
import Verifier.SAW.TypedTerm

import SAWScript.Crucible.Common
import qualified SAWScript.Crucible.Common.MethodSpec as MS
import SAWScript.Crucible.Common.MethodSpec (AllocIndex(..))
import SAWScript.Crucible.Common.ResolveSetupValue (resolveBoolTerm)
import SAWScript.Crucible.MIR.MethodSpecIR
import SAWScript.Crucible.MIR.TypeShape
import SAWScript.Panic

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
    TupleShape _ _ fldShp ->
      PP.parens $ prettyAdtOrTuple fldShp val
    ArrayShape _ _ shp' ->
      case val of
        Mir.MirVector_Vector vec ->
          PP.brackets $ commaList $ V.toList $
          fmap (\v -> ppMIRVal sym (MIRVal shp' v)) vec
        Mir.MirVector_PartialVector vec ->
          PP.braces $ commaList $ V.toList $
          fmap (\v -> let v' = readMaybeType sym "vector element" (shapeType shp') v in
                      ppMIRVal sym (MIRVal shp' v')) vec
        Mir.MirVector_Array arr ->
          W4.printSymExpr arr
    StructShape _ _ fldShp
      |  AnyValue (StructRepr fldTpr) fldVals <- val
      ,  Just Refl <- W4.testEquality (FC.fmapFC fieldShapeType fldShp) fldTpr
      -> PP.braces $ prettyAdtOrTuple fldShp fldVals

      | otherwise
      -> error "Malformed MIRVal struct"
    EnumShape _ _ variantShps _ _
      |  AnyValue (Mir.RustEnumRepr _ variantCtx)
                  (Ctx.Empty Ctx.:> RV _ Ctx.:> RV variants) <- val
      ,  Just Refl <- W4.testEquality (FC.fmapFC variantShapeType variantShps) variantCtx
      -> case firstConcreteVariant variantShps variants of
           Just (Some (Functor.Pair fldShps fldVals)) ->
             PP.braces $ prettyAdtOrTuple fldShps fldVals
           Nothing ->
             "<symbolic enum>"

      |  otherwise
      -> error "Malformed MIRVal enum"
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

type SetupValue = MS.SetupValue MIR

data MIRTypeOfError
  = MIRPolymorphicType Cryptol.Schema
  | MIRNonRepresentableType Cryptol.Type ToMIRTypeErr
  | MIRInvalidTypedTerm TypedTermType
  | MIRInvalidIdentifier String
  | MIRStaticNotFound Mir.DefId
  | MIRSliceNonArrayReference Mir.Ty

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
    , show (MS.ppTypedTermType tp)
    ]
  show (MIRInvalidIdentifier errMsg) =
    errMsg
  show (MIRStaticNotFound did) =
    staticNotFoundErr did
  show (MIRSliceNonArrayReference ty) =
    unlines
    [ "Expected a reference to an array, but got"
    , show (PP.pretty ty)
    ]

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
        Nothing -> panic "MIRSetup" ["typeOfSetupValue", "Unresolved prestate variable:" ++ show i]
        Just (Some alloc) ->
          return $ Mir.TyRef (alloc^.maMirType) (alloc^.maMutbl)
    MS.SetupTerm tt ->
      case ttType tt of
        TypedTermSchema (Cryptol.Forall [] [] ty) ->
          case toMIRType (Cryptol.evalValType mempty ty) of
            Left err -> X.throwM (MIRNonRepresentableType ty err)
            Right mirTy -> return mirTy
        TypedTermSchema s -> X.throwM (MIRPolymorphicType s)
        tp -> X.throwM (MIRInvalidTypedTerm tp)
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
          panic "typeOfSetupValue" ["MirSetupSliceRaw not yet implemented"]
        MirSetupSlice arr ->
          typeOfSliceFromArray arr
        MirSetupSliceRange arr _ _ ->
          typeOfSliceFromArray arr

    MS.SetupNull empty                -> absurd empty
    MS.SetupElem _ _ _                -> panic "typeOfSetupValue" ["elems not yet implemented"]
    MS.SetupField _ _ _               -> panic "typeOfSetupValue" ["fields not yet implemented"]
    MS.SetupCast empty _              -> absurd empty
    MS.SetupUnion empty _ _           -> absurd empty
  where
    cs = mcc ^. mccRustModule . Mir.rmCS

    typeOfSliceFromArray :: SetupValue -> m Mir.Ty
    typeOfSliceFromArray arr = do
      arrTy <- typeOfSetupValue mcc env nameEnv arr
      case arrTy of
        Mir.TyRef (Mir.TyArray ty _) mut ->
          pure $ Mir.TyRef (Mir.TySlice ty) mut
        _ ->
          X.throwM $ MIRSliceNonArrayReference arrTy

lookupAllocIndex :: Map AllocIndex a -> AllocIndex -> a
lookupAllocIndex env i =
  case Map.lookup i env of
    Nothing -> panic "MIRSetup" ["Unresolved prestate variable:" ++ show i]
    Just x -> x

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
                        (Mir.TyRef pointeeType (ptr ^. mpMutbl))
                        pointeeType
                        (ptr ^. mpMutbl)
                        (ptr ^. mpType))
                    (ptr ^. mpRef)
    MS.SetupTerm tm -> resolveTypedTerm mcc tm
    MS.SetupNull empty                -> absurd empty
    MS.SetupStruct adt flds ->
      case adt of
        _ | adt ^. Mir.adtReprTransparent,
            [fld] <- flds ->
          resolveTransparentSetupVal adt fld
        Mir.Adt nm Mir.Struct variants _ _ _ _ -> do
          -- First, retrieve the struct variant.
          variant <-
            case variants of
              [variant] ->
                pure variant
              _ ->
                panic "resolveSetupVal"
                      [ "Encountered struct Adt with " ++
                        show (length variants) ++
                        " variants:"
                      , show nm
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
          let structTpr = StructRepr (FC.fmapFC fieldShapeType fldShpAssn)
          pure $ MIRVal structShp (AnyValue structTpr valAssn)
        Mir.Adt nm (Mir.Enum _) _ _ _ _ _ ->
          panic "resolveSetupVal"
                [ "Expected struct type, received enum:"
                , show nm
                ]
        Mir.Adt nm Mir.Union _ _ _ _ _ ->
          panic "resolveSetupVal"
                [ "Expected struct type, received union:"
                , show nm
                ]
    MS.SetupEnum enum_ ->
      case enum_ of
        MirSetupEnumVariant adt variant variantIdxInt flds ->
          case adt of
            _ | adt ^. Mir.adtReprTransparent,
                [fld] <- flds -> do
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
              Some discrTpr <- pure $ Mir.tyToRepr col discrTp
              let discrShp = tyToShapeEq col discrTp discrTpr
              IsBVShape _ discrW <- pure $ testDiscriminantIsBV discrShp
              let discr = getEnumVariantDiscr variant
              discrVal <- W4.bvLit sym discrW $ BV.mkBV discrW discr

              -- Construct an EnumShape and RustEnumRepr. This requires
              -- processing /all/ variants, not just the particular variant that
              -- we are building.
              (enumShp, Some expectedVariantShps) <- pure $
                enumShapes adt discrTp discrShp variants
              let variantTprs =
                    FC.fmapFC variantShapeType expectedVariantShps
              let enumTpr = Mir.RustEnumRepr
                              discrTpr
                              variantTprs

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
                    panic "resolveSetupVal"
                          [ "Enum field shape mismatch"
                          , "Expected: " ++ show expectedFldAssn
                          , "Actual: " ++ show actualFldAssn
                          ]

              -- Finally, construct a MIRVal.
              let enumVal =
                    Ctx.empty
                      Ctx.:> RV discrVal
                      Ctx.:> RV (injectVariant sym variantTprs variantIdx actualValAssn)
              pure $ MIRVal enumShp $ AnyValue enumTpr enumVal
            Mir.Adt nm Mir.Struct _ _ _ _ _ ->
              panic "resolveSetupVal"
                    [ "Expected enum type, received struct:"
                    , show nm
                    ]
            Mir.Adt nm Mir.Union _ _ _ _ _ ->
              panic "resolveSetupVal"
                    [ "Expected enum type, received union:"
                    , show nm
                    ]
        -- See Note [Symbolic enums] in SAWScript.Crucible.MIR.Setup.Value for
        -- more information on the approach used to resolve symbolic enum
        -- values.
        MirSetupEnumSymbolic adt discr variantFlds ->
          case adt of
            _ | adt ^. Mir.adtReprTransparent ->
              -- `repr(transparent)` enum values use MirSetupEnumVariant rather
              -- than MirSetupEnumSymbolic. See the Haddocks for
              -- MirSetupEnumSymbolic for an explanation.
              panic "resolveSetupVal"
                    [ "Symbolic enum of type " ++ show (adt ^. Mir.adtname)
                    , "that uses MirSetupEnumSymbolic rather than MirSetupEnumVarianr"
                    ]
            Mir.Adt nm (Mir.Enum discrTp) variants _ _ _ _ -> do
              -- Resolve the discriminant value and ensure that it has an
              -- integral type.
              MIRVal discrShp discrVal <- resolveSetupVal mcc env tyenv nameEnv discr
              IsBVShape _ discrW <- pure $ testDiscriminantIsBV discrShp
              let discrTpr = shapeType discrShp

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

              -- Construct an EnumShape and RustEnumRepr.
              (enumShp, Some expectedVariantShps) <- pure $
                enumShapes adt discrTp discrShp variants
              let variantTprs =
                    FC.fmapFC variantShapeType expectedVariantShps
              let enumTpr = Mir.RustEnumRepr
                              discrTpr
                              variantTprs

              -- Check that the actual variant types match the expected types.
              Refl <-
                case W4.testEquality expectedVariantShps actualVariantShps of
                  Just r -> pure r
                  Nothing ->
                    panic "resolveSetupVal"
                          [ "Enum variant shape mismatch"
                          , "Expected: " ++ show expectedVariantShps
                          , "Actual: " ++ show actualVariantShps
                          ]

              -- Finally, construct a MIRVal.
              let enumVal =
                    Ctx.empty
                      Ctx.:> RV discrVal
                      Ctx.:> RV branchAssn
              pure $ MIRVal enumShp $ AnyValue enumTpr enumVal
            Mir.Adt nm Mir.Struct _ _ _ _ _ ->
              panic "resolveSetupVal"
                    [ "Expected enum type, received struct:"
                    , show nm
                    ]
            Mir.Adt nm Mir.Union _ _ _ _ _ ->
              panic "resolveSetupVal"
                    [ "Expected enum type, received union:"
                    , show nm
                    ]
    MS.SetupTuple () flds -> do
      flds' <- traverse (resolveSetupVal mcc env tyenv nameEnv) flds
      let fldMirTys = map (\(MIRVal shp _) -> shapeMirTy shp) flds'
      Some fldAssn <-
        pure $ Ctx.fromList $
        map (\(MIRVal shp v) ->
              Some $ Functor.Pair (OptField shp) (RV (W4.justPartExpr sym v)))
            flds'
      let (fldShpAssn, valAssn) = Ctx.unzip fldAssn
      let tupleShp = TupleShape (Mir.TyTuple fldMirTys) fldMirTys fldShpAssn
      pure $ MIRVal tupleShp valAssn
    MS.SetupSlice slice ->
      case slice of
        MirSetupSliceRaw{} ->
          panic "resolveSetupVal" ["MirSetupSliceRaw not yet implemented"]
        MirSetupSlice arrRef -> do
          SetupSliceFromArray _elemTpr sliceShp refVal len <-
            resolveSetupSliceFromArray bak arrRef
          lenVal <- usizeBvLit sym len
          pure $ MIRVal sliceShp (Ctx.Empty Ctx.:> RV refVal Ctx.:> RV lenVal)
        MirSetupSliceRange arrRef start end -> do
          unless (start <= end) $
            fail $ "slice index starts at " ++ show start
                ++ " but ends at " ++ show end
          SetupSliceFromArray elemTpr sliceShp refVal0 len <-
            resolveSetupSliceFromArray bak arrRef
          unless (end <= len) $
            fail $ "range end index " ++ show end
                ++ " out of range for slice of length " ++ show len
          startBV <- usizeBvLit sym start
          refVal1 <- Mir.mirRef_offsetIO bak iTypes elemTpr refVal0 startBV
          lenVal <- usizeBvLit sym $ end - start
          pure $ MIRVal sliceShp (Ctx.Empty Ctx.:> RV refVal1 Ctx.:> RV lenVal)
    MS.SetupArray elemTy vs -> do
      vals <- V.mapM (resolveSetupVal mcc env tyenv nameEnv) (V.fromList vs)

      Some (shp :: TypeShape tp) <-
        pure $ tyToShape col elemTy

      let vals' :: Vector (RegValue Sym tp)
          vals' = V.map (\(MIRVal shp' val') ->
                          case W4.testEquality shp shp' of
                            Just Refl -> val'
                            Nothing -> error $ unlines
                              [ "resolveSetupVal: internal error"
                              , show shp
                              , show shp'
                              ])
                        vals
      return $ MIRVal (ArrayShape (Mir.TyArray elemTy (V.length vals)) elemTy shp)
                      (Mir.MirVector_Vector vals')
    MS.SetupElem _ _ _                -> panic "resolveSetupValue" ["elems not yet implemented"]
    MS.SetupField _ _ _               -> panic "resolveSetupValue" ["fields not yet implemented"]
    MS.SetupCast empty _              -> absurd empty
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
  where
    cs  = mcc ^. mccRustModule . Mir.rmCS
    col = cs ^. Mir.collection
    iTypes = mcc ^. mccIntrinsicTypes

    usizeBvLit :: Sym -> Int -> IO (W4.SymBV Sym Mir.SizeBits)
    usizeBvLit sym = W4.bvLit sym W4.knownNat . BV.mkBV W4.knownNat . toInteger

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

    -- Construct the 'TypeShape' for an enum, along with the 'VariantShape's for
    -- the enum's variants.
    enumShapes ::
      Mir.Adt {- The enum type -} ->
      Mir.Ty {- The discriminant's MIR type -} ->
      TypeShape discrShp {- The discriminant's TypeShape -} ->
      [Mir.Variant] {- The enum's variants -} ->
      (TypeShape AnyType, Some (Ctx.Assignment VariantShape))
    enumShapes adt discrTp discrShp variants
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
      = (enumShp, Some variantShps)

    -- Resolve parts of a slice that are shared in common between
    -- 'MirSetupSlice' and 'MirSetupSliceRange'.
    resolveSetupSliceFromArray ::
      OnlineSolver solver =>
      Backend solver ->
      SetupValue ->
      IO SetupSliceFromArray
    resolveSetupSliceFromArray bak arrRef = do
      let sym = backendGetSym bak
      MIRVal arrRefShp arrRefVal <- resolveSetupVal mcc env tyenv nameEnv arrRef
      case arrRefShp of
        RefShape _ (Mir.TyArray elemTy len) mut (Mir.MirVectorRepr elemTpr) -> do
          zeroBV <- usizeBvLit sym 0
          refVal <- Mir.subindexMirRefIO bak iTypes elemTpr arrRefVal zeroBV
          let sliceShp = SliceShape (Mir.TySlice elemTy) elemTy mut elemTpr
          pure $ SetupSliceFromArray elemTpr sliceShp refVal len
        _ -> X.throwM $ MIRSliceNonArrayReference $ shapeMirTy arrRefShp

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
-- 'resolveSetupSliceFromArray'.
data SetupSliceFromArray where
  SetupSliceFromArray ::
    TypeRepr tp {- ^ The array's element type -} ->
    TypeShape (Mir.MirSlice tp) {- ^ The overall shape of the slice -} ->
    Mir.MirReferenceMux Sym tp {- ^ The reference to the array -} ->
    Int {- ^ The array length -} ->
    SetupSliceFromArray

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
            , show (MS.ppTypedTermType tp)
            ]

resolveSAWPred ::
  MIRCrucibleContext ->
  Term ->
  IO (W4.Pred Sym)
resolveSAWPred cc tm =
  do let sym = cc^.mccSym
     st <- sawCoreState sym
     bindSAWTerm sym st W4.BaseBoolRepr tm

resolveSAWTerm ::
  MIRCrucibleContext ->
  Cryptol.TValue ->
  Term ->
  IO MIRVal
resolveSAWTerm mcc tp tm =
  case tp of
    Cryptol.TVBit ->
      do b <- resolveBoolTerm sym tm
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
         resolveBitvectorTerm sym n tm
    Cryptol.TVSeq sz tp' -> do
      st <- sawCoreState sym
      let sc = saw_ctx st
      sz_tm <- scNat sc (fromIntegral sz)
      tp_tm <- importType sc emptyEnv (Cryptol.tValTy tp')
      case toMIRType tp' of
        Left e -> fail ("In resolveSAWTerm: " ++ toMIRTypeErrToString e)
        Right mirTy -> do
          Some (shp :: TypeShape tp) <- pure $ tyToShape col mirTy

          let sz' = fromInteger sz

              f :: Int -> IO (RegValue Sym tp)
              f i = do
                i_tm <- scNat sc (fromIntegral i)
                tm' <- scAt sc sz_tm tp_tm tm i_tm
                MIRVal shp' val <- resolveSAWTerm mcc tp' tm'
                Refl <- case W4.testEquality shp shp' of
                          Just r -> pure r
                          Nothing -> fail $ unlines
                            [ "resolveSAWTerm: internal error"
                            , show shp
                            , show shp'
                            ]
                pure val

          vals <- V.generateM sz' f
          pure $ MIRVal (ArrayShape (Mir.TyArray mirTy sz') mirTy shp)
               $ Mir.MirVector_Vector vals
    Cryptol.TVStream _tp' ->
      fail "resolveSAWTerm: unsupported infinite stream type"
    Cryptol.TVTuple tps -> do
      st <- sawCoreState sym
      let sc = saw_ctx st
      tms <- traverse (\i -> scTupleSelector sc tm i (length tps)) [1 .. length tps]
      vals <- zipWithM (resolveSAWTerm mcc) tps tms
      if null vals
        then pure $ MIRVal (UnitShape (Mir.TyTuple [])) ()
        else do
          let mirTys = map (\(MIRVal shp _) -> shapeMirTy shp) vals
          let mirTupleTy = Mir.TyTuple mirTys
          Some fldAssn <-
            pure $ Ctx.fromList $
            map (\(MIRVal shp val) ->
                  Some $ Functor.Pair (OptField shp) (RV (W4.justPartExpr sym val)))
                vals
          let (fldShpAssn, valAssn) = Ctx.unzip fldAssn
          pure $ MIRVal (TupleShape mirTupleTy mirTys fldShpAssn) valAssn
    Cryptol.TVRec _flds ->
      fail "resolveSAWTerm: unsupported record type"
    Cryptol.TVFun _ _ ->
      fail "resolveSAWTerm: unsupported function type"
    Cryptol.TVAbstract _ _ ->
      fail "resolveSAWTerm: unsupported abstract type"
    Cryptol.TVNewtype{} ->
      fail "resolveSAWTerm: unsupported newtype"
  where
    sym = mcc ^. mccSym
    col = mcc ^. mccRustModule ^. Mir.rmCS ^. Mir.collection

resolveBitvectorTerm ::
  forall w.
  (1 W4.<= w) =>
  Sym ->
  W4.NatRepr w ->
  Term ->
  IO (W4.SymBV Sym w)
resolveBitvectorTerm sym w tm =
  do st <- sawCoreState sym
     let sc = saw_ctx st
     mx <- case getAllExts tm of
             -- concretely evaluate if it is a closed term
             [] ->
               do modmap <- scGetModuleMap sc
                  let v = Concrete.evalSharedTerm modmap mempty mempty tm
                  pure (Just (Prim.unsigned (Concrete.toWord v)))
             _ -> return Nothing
     case mx of
       Just x  -> W4.bvLit sym w (BV.mkBV w x)
       Nothing -> bindSAWTerm sym st (W4.BaseBVRepr w) tm

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
    Cryptol.TVAbstract _ _ -> Left (Impossible "abstract")
    Cryptol.TVNewtype{} -> Left (Impossible "newtype")

-- | Check if two MIR references are equal.
equalRefsPred ::
  MIRCrucibleContext ->
  MirPointer Sym tp1 ->
  MirPointer Sym tp2 ->
  IO (W4.Pred Sym)
equalRefsPred cc mp1 mp2 =
  mccWithBackend cc $ \bak ->
  let sym = backendGetSym bak in
  case W4.testEquality (mp1^.mpType) (mp2^.mpType) of
    Nothing -> pure $ W4.falsePred sym
    Just Refl -> Mir.mirRef_eqIO bak (mp1^.mpRef) (mp2^.mpRef)

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
    goTy (TupleShape _ _ fldShp) fldAssn1 fldAssn2 =
      goFldAssn fldShp fldAssn1 fldAssn2
    goTy (ArrayShape _ _ shp) vec1 vec2 =
      goVec shp vec1 vec2
    goTy (StructShape _ _ fldShp) any1 any2 =
      case (any1, any2) of
        (AnyValue (StructRepr fldCtx1) fldAssn1,
         AnyValue (StructRepr fldCtx2) fldAssn2) -> do
          Refl <- testEquality fldCtx1 fldCtx2
          Refl <- testEquality (FC.fmapFC fieldShapeType fldShp) fldCtx1
          goFldAssn fldShp fldAssn1 fldAssn2
        (_, _) ->
          pure $ W4.falsePred sym
    goTy (EnumShape _ _ variantShp _ discrShp) any1 any2 =
      case (any1, any2) of
        (AnyValue (Mir.RustEnumRepr discrTpr1 variantCtx1)
                  (Ctx.Empty Ctx.:> RV discr1 Ctx.:> RV variant1),
         AnyValue (Mir.RustEnumRepr discrTpr2 variantCtx2)
                  (Ctx.Empty Ctx.:> RV discr2 Ctx.:> RV variant2)) -> do
           Refl <- testEquality discrTpr1 discrTpr2
           Refl <- testEquality (shapeType discrShp) discrTpr1
           Refl <- testEquality variantCtx1 variantCtx2
           Refl <- testEquality (FC.fmapFC variantShapeType variantShp) variantCtx1
           discrPred <- goTy discrShp discr1 discr2
           variantPred <- goVariantAssn variantShp variant1 variant2
           liftIO $ W4.andPred sym discrPred variantPred
        (_, _) ->
          pure $ W4.falsePred sym
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

    goVec :: TypeShape tp
          -> Mir.MirVector Sym tp
          -> Mir.MirVector Sym tp
          -> MaybeT IO (W4.Pred Sym)
    goVec shp (Mir.MirVector_Vector vec1)
              (Mir.MirVector_Vector vec2) = do
      eqs <- V.zipWithM (goTy shp) vec1 vec2
      liftIO $ F.foldrM (W4.andPred sym) (W4.truePred sym) eqs
    goVec shp (Mir.MirVector_PartialVector vec1)
              (Mir.MirVector_PartialVector vec2) = do
      eqs <- V.zipWithM
               (\v1 v2 -> do
                 let readElem v = readMaybeType sym "vector element" (shapeType shp) v
                 let v1' = readElem v1
                 let v2' = readElem v2
                 goTy shp v1' v2')
               vec1
               vec2
      liftIO $ F.foldrM (W4.andPred sym) (W4.truePred sym) eqs
    goVec _shp (Mir.MirVector_Array vec1) (Mir.MirVector_Array vec2) =
      liftIO $ W4.arrayEq sym vec1 vec2
    goVec _shp _vec1 _vec2 =
      pure $ W4.falsePred sym

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
-- See also @checkRegisterCompatibility@ in "SAWScript.Crucible.LLVM.Builtins"
-- and @registerCompatible@ in "SAWScript.Crucible.JVM.Builtins", which fill a
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
  , _fsvspreadarg  :: Maybe Int
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
fnSigView (Mir.FnSig argTys retTy abi spreadarg) =
  FnSigView (map tyView argTys) (tyView retTy) abi spreadarg

-- | Read the value out of a 'MaybeType' expression that is assumed to be
-- assigned to a value. If this assumption does not hold (i.e., if the value is
-- unassigned), then this function will raise an error.
readMaybeType ::
     IsSymInterface sym
  => sym
  -> String
  -> TypeRepr tp
  -> RegValue sym (MaybeType tp)
  -> RegValue sym tp
readMaybeType sym desc tpr rv =
  case readPartExprMaybe sym rv of
    Just x -> x
    Nothing -> error $ "readMaybeType: accessed possibly-uninitialized " ++ desc ++
        " of type " ++ show tpr

readPartExprMaybe ::
     IsSymInterface sym
  => sym
  -> W4.PartExpr (W4.Pred sym) a
  -> Maybe a
readPartExprMaybe _sym W4.Unassigned = Nothing
readPartExprMaybe _sym (W4.PE p v)
  | Just True <- W4.asConstantPred p = Just v
  | otherwise = Nothing

-- | Allocate memory for each 'mir_alloc' or 'mir_alloc_mut'.
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
     Some tpr <- pure $ Mir.tyToRepr col (ma^.maMirType)

     -- Create an uninitialized `MirVector_PartialVector` of length 1 and
     -- return a pointer to its element.
     ref <- Mir.newMirRefIO sym halloc (Mir.MirVectorRepr tpr)

     one <- W4.bvLit sym W4.knownRepr $ BV.mkBV W4.knownRepr 1
     vec <- Mir.mirVector_uninitIO bak one
     globals' <- Mir.writeMirRefIO bak globals iTypes ref vec

     zero <- W4.bvLit sym W4.knownRepr $ BV.mkBV W4.knownRepr 0
     ptr <- Mir.subindexMirRefIO bak iTypes tpr ref zero
     let mirPtr = Some MirPointer
           { _mpType = tpr
           , _mpMutbl = ma^.maMutbl
           , _mpMirType = ma^.maMirType
           , _mpRef = ptr
           }

     pure (mirPtr, globals')

doPointsTo ::
     MS.CrucibleMethodSpecIR MIR
  -> MIRCrucibleContext
  -> Map MS.AllocIndex (Some (MirPointer Sym))
  -> SymGlobalState Sym
  -> MirPointsTo
  -> IO (SymGlobalState Sym)
doPointsTo mspec cc env globals (MirPointsTo _ reference referents) =
  mccWithBackend cc $ \bak -> do
    MIRVal referenceShp referenceVal <-
      resolveSetupVal cc env tyenv nameEnv reference
    -- By the time we reach here, we have already checked (in mir_points_to)
    -- that we are in fact dealing with a reference value, so the call to
    -- `testRefShape` below should always succeed.
    IsRefShape _ _ _ referenceInnerTy <-
      case testRefShape referenceShp of
        Just irs -> pure irs
        Nothing ->
          panic "doPointsTo"
                [ "Unexpected non-reference type:"
                , show $ PP.pretty $ shapeMirTy referenceShp
                ]
    referent <- firstPointsToReferent referents
    MIRVal referentShp referentVal <-
      resolveSetupVal cc env tyenv nameEnv referent
    -- By the time we reach here, we have already checked (in mir_points_to)
    -- that the type of the reference is compatible with the right-hand side
    -- value, so the equality check below should never fail.
    Refl <-
      case W4.testEquality referenceInnerTy (shapeType referentShp) of
        Just r -> pure r
        Nothing ->
          panic "doPointsTo"
                [ "Unexpected type mismatch between reference and referent"
                , "Reference type: " ++ show referenceInnerTy
                , "Referent type:  " ++ show (shapeType referentShp)
                ]
    Mir.writeMirRefIO bak globals iTypes referenceVal referentVal
  where
    iTypes = cc ^. mccIntrinsicTypes
    tyenv = MS.csAllocations mspec
    nameEnv = mspec ^. MS.csPreState . MS.csVarTypeNames

-- | @mir_points_to@ always creates a 'MirPointsTo' value with exactly one
-- referent on the right-hand side. As a result, this function should never
-- fail.
firstPointsToReferent ::
  MonadFail m => [MS.SetupValue MIR] -> m (MS.SetupValue MIR)
firstPointsToReferent referents =
  case referents of
    [referent] -> pure referent
    _ -> fail $
      "Unexpected mir_points_to statement with " ++ show (length referents) ++
      " referent(s)"

-- | Construct an 'Mir.TyAdt' from an 'Mir.Adt'.
mirAdtToTy :: Mir.Adt -> Mir.Ty
mirAdtToTy adt =
  Mir.TyAdt (adt ^. Mir.adtname) (adt ^. Mir.adtOrigDefId) (adt ^. Mir.adtOrigSubsts)

-- | Like 'findDefIdEither', but any errors are thrown with 'fail'.
findDefId :: MonadFail m => Map Text (NonEmpty Text) -> Text -> m Mir.DefId
findDefId crateDisambigs fnName =
  either fail pure $ findDefIdEither crateDisambigs fnName

-- | Given a function name @fnName@, attempt to look up its corresponding
-- 'Mir.DefId'. If successful, return it with 'Right'. Currently, the following
-- types of function names are permittd:
--
-- * @<crate_name>/<disambiguator>::<function_name>: A fully disambiguated name.
--
-- * @<crate_name>::<function_name>: A name without a disambiguator. In this
--   case, SAW will attempt to look up a disambiguator from the @crateDisambigs@
--   map. If none can be found, or if there are multiple disambiguators for the
--   given @<crate_name>@, then this will return an error message with 'Left'.
findDefIdEither :: Map Text (NonEmpty Text) -> Text -> Either String Mir.DefId
findDefIdEither crateDisambigs fnName = do
    (crate, path) <-
      case edid of
        crate:path -> pure (crate, path)
        [] -> Left $ unlines
                [ "The function `" ++ fnNameStr ++ "` lacks a crate."
                , "Consider providing one, e.g., `<crate_name>::" ++ fnNameStr ++ "`."
                ]
    let crateStr = Text.unpack crate
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
  where
    fnNameStr = Text.unpack fnName
    edid = Text.splitOn "::" fnName

-- | Consult the given 'Mir.CollectionState' to find a 'Mir.Static' with the
-- given 'String' as an identifier. If such a 'Mir.Static' cannot be found, this
-- will raise an error.
findStatic :: X.MonadThrow m => Mir.CollectionState -> String -> m Mir.Static
findStatic cs name = do
  did <- case findDefIdEither (cs ^. Mir.crateHashesMap) (Text.pack name) of
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
  Mir.MirReferenceMux sym tp
staticRefMux sym gv =
  Mir.MirReferenceMux $
  Mir.toFancyMuxTree sym $
  Mir.MirReference (Mir.GlobalVar_RefRoot gv) Mir.Empty_RefPath

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
      panic "getEnumVariantDiscr"
            [ "discrval not set for variant:"
            , show (variant ^. Mir.vname)
            ]

-- | An enum's discriminant should have an integral type such as @isize@ or
-- @i8@, which this function checks. If this is not the case, this function will
-- panic.
testDiscriminantIsBV :: TypeShape shp -> IsBVShape shp
testDiscriminantIsBV discrShp =
  case testBVShape discrShp of
    Just ibvs -> ibvs
    Nothing ->
      panic "testDiscriminantIsBV"
            [ "Unexpected non-integral discriminant type:"
            , show $ PP.pretty $ shapeMirTy discrShp
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
      panic "variantIntIndex"
            [ "Enum variant index out of range"
            , "Enum: " ++ show adtNm
            , "Index: " ++ show variantIdx
            , "Number of variants: " ++ show variantsSize
            ]
