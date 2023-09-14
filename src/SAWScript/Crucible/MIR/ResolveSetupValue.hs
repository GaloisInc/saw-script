{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Turns 'SetupValue's back into 'MIRVal's.
module SAWScript.Crucible.MIR.ResolveSetupValue
  ( MIRVal(..)
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
  , mirAdtToTy
  , MIRTypeOfError(..)
  ) where

import           Control.Lens
import           Control.Monad (unless, zipWithM, zipWithM_)
import qualified Control.Monad.Catch as X
import qualified Data.BitVector.Sized as BV
import qualified Data.Functor.Product as Functor
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(..))
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Text (Text)
import qualified Data.Vector as V
import           Data.Vector (Vector)
import           Data.Void (absurd)
import           Numeric.Natural (Natural)
import qualified Prettyprinter as PP

import qualified Cryptol.Eval.Type as Cryptol (TValue(..), tValTy, evalValType)
import qualified Cryptol.TypeCheck.AST as Cryptol (Type, Schema(..))
import qualified Cryptol.Utils.PP as Cryptol (pp)
import Lang.Crucible.Simulator (AnyValue(..), RegValue, RegValue'(..))
import Lang.Crucible.Types (TypeRepr(..))
import qualified Mir.DefId as Mir
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

type SetupValue = MS.SetupValue MIR

data MIRTypeOfError
  = MIRPolymorphicType Cryptol.Schema
  | MIRNonRepresentableType Cryptol.Type ToMIRTypeErr
  | MIRInvalidTypedTerm TypedTermType

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

instance X.Exception MIRTypeOfError

typeOfSetupValue ::
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
    MS.SetupTuple () vals -> do
      tys <- traverse (typeOfSetupValue mcc env nameEnv) vals
      pure $ Mir.TyTuple tys

    MS.SetupNull empty                -> absurd empty
    MS.SetupGlobal empty _            -> absurd empty
    MS.SetupElem _ _ _                -> panic "typeOfSetupValue" ["elems not yet implemented"]
    MS.SetupField _ _ _               -> panic "typeOfSetupValue" ["fields not yet implemented"]
    MS.SetupCast empty _              -> absurd empty
    MS.SetupUnion empty _ _           -> absurd empty
    MS.SetupGlobalInitializer empty _ -> absurd empty

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
    MS.SetupGlobal empty _            -> absurd empty
    MS.SetupStruct adt flds ->
      case adt of
        _ | adt ^. Mir.adtReprTransparent,
            [fld] <- flds -> do
          MIRVal shp fld' <- resolveSetupVal mcc env tyenv nameEnv fld
          pure $ MIRVal (TransparentShape (mirAdtToTy adt) shp) fld'
        Mir.Adt nm Mir.Struct [variant] _ _ _ _ -> do
          flds' <- traverse (resolveSetupVal mcc env tyenv nameEnv) flds
          let expectedFlds = variant ^. Mir.vfields
          let expectedFldsNum = length expectedFlds
          let actualFldTys = map (\(MIRVal shp _) -> shapeMirTy shp) flds'
          let actualFldsNum = length actualFldTys
          unless (expectedFldsNum == actualFldsNum) $
            fail $ unlines
              [ "Mismatch in number of struct fields"
              , "Struct name: " ++ show nm
              , "Expected number of fields: " ++ show expectedFldsNum
              , "Actual number of fields:   " ++ show actualFldsNum
              ]
          zipWithM_
            (\expectedFld actualFldTy ->
              let expectedFldTy = expectedFld ^. Mir.fty in
              let expectedFldName = expectedFld ^. Mir.fName in
              unless (checkCompatibleTys expectedFldTy actualFldTy) $
                fail $ unlines
                  [ "Struct field type mismatch"
                  , "Field name: " ++ show expectedFldName
                  , "Expected type: " ++ show (PP.pretty expectedFldTy)
                  , "Given type:    " ++ show (PP.pretty actualFldTy)
                  ])
            expectedFlds
            actualFldTys
          Some fldAssn <-
            pure $ Ctx.fromList $
            map (\(MIRVal shp v) ->
                  if Mir.canInitialize col (shapeMirTy shp)
                  then Some $ Functor.Pair (ReqField shp) (RV v)
                  else Some $ Functor.Pair (OptField shp) (RV (W4.justPartExpr sym v)))
                flds'
          let (fldShpAssn, valAssn) = Ctx.unzip fldAssn
          let structShp = StructShape (mirAdtToTy adt) actualFldTys fldShpAssn
          let structTpr = StructRepr (FC.fmapFC fieldShapeType fldShpAssn)
          pure $ MIRVal structShp (AnyValue structTpr valAssn)
        Mir.Adt _ ak _ _ _ _ _ ->
          panic "resolveSetupVal" ["AdtKind " ++ show ak ++ " not yet implemented"]
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
    MS.SetupGlobalInitializer empty _ -> absurd empty
  where
    sym = mcc ^. mccSym
    col = mcc ^. mccRustModule . Mir.rmCS . Mir.collection

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

equalValsPred ::
  MIRCrucibleContext ->
  MIRVal ->
  MIRVal ->
  IO (W4.Pred Sym)
equalValsPred = panic "equalValsPred" ["not yet implemented"]

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

-- | Construct an 'Mir.TyAdt' from an 'Mir.Adt'.
mirAdtToTy :: Mir.Adt -> Mir.Ty
mirAdtToTy adt =
  Mir.TyAdt (adt ^. Mir.adtname) (adt ^. Mir.adtOrigDefId) (adt ^. Mir.adtOrigSubsts)
