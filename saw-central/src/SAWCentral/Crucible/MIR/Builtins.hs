{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Implementations of Crucible-related SAWScript primitives for MIR.
module SAWCentral.Crucible.MIR.Builtins
  ( -- * Commands
    -- ** Setup
    mir_alloc
  , mir_alloc_mut
  , mir_alloc_raw_ptr_const
  , mir_alloc_raw_ptr_mut
  , mir_alloc_raw_ptr_const_multi
  , mir_alloc_raw_ptr_mut_multi
  , mir_ref_of
  , mir_ref_of_mut
  , mir_assert
  , mir_cast_raw_ptr
  , mir_execute_func
  , mir_equal
  , mir_extract
  , mir_find_adt
  , mir_find_name
  , mir_find_mangled_adt
  , mir_fresh_cryptol_var
  , mir_fresh_expanded_value
  , mir_fresh_var
  , mir_ghost_value
  , mir_load_module
  , mir_points_to
  , mir_points_to_multi
  , mir_postcond
  , mir_precond
  , mir_return
  , mir_unsafe_assume_spec
  , mir_verify
  , mir_unint
    -- ** MIR enums
  , mir_enum_value
    -- ** MIR slices
  , mir_slice_value
  , mir_slice_range_value
  , mir_str_slice_value
  , mir_str_slice_range_value
    -- ** MIR projections
  , mir_elem_value
  , mir_elem_ref
    -- ** MIR muxing
  , mir_mux_values
    -- ** Rust Vecs
  , mir_vec_of
    -- ** MIR types
  , mir_adt
  , mir_array
  , mir_bool
  , mir_char
  , mir_const
  , mir_i8
  , mir_i16
  , mir_i32
  , mir_i64
  , mir_i128
  , mir_isize
  , mir_f32
  , mir_f64
  , mir_lifetime
  , mir_raw_ptr_const
  , mir_raw_ptr_mut
  , mir_ref
  , mir_ref_mut
  , mir_slice
  , mir_str
  , mir_tuple
  , mir_u8
  , mir_u16
  , mir_u32
  , mir_u64
  , mir_u128
  , mir_usize
  , mir_vec
  ) where

import Control.Lens
import Control.Monad (foldM, forM, forM_, mapAndUnzipM, unless, when, zipWithM)
import qualified Control.Monad.Catch as X
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (runReaderT)
import Control.Monad.State (MonadState(..), StateT(..), execStateT, gets)
import Control.Monad.Trans.Class (MonadTrans(..))
import qualified Data.ByteString as BSS
import qualified Data.ByteString.Lazy as BSL
import Data.Char (chr)
import Data.Foldable (for_, toList)
import qualified Data.Foldable.WithIndex as FWI
import qualified Data.IntMap as IntMap
import Data.IORef
import qualified Data.List.Extra as List (find, unsnoc)
import qualified Data.List.NonEmpty as NE
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import Data.Parameterized.NatRepr (intValue, knownNat, maxSigned, natValue)
import Data.Parameterized.Some (Some(..))
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Parameterized.TraversableFC.WithIndex as FCI
import qualified Data.Set as Set
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.String (IsString)
import qualified Data.Text as Text
import Data.Text (Text)
import Data.Time.Clock (diffUTCTime, getCurrentTime)
import Data.Traversable (mapAccumL)
import Data.Type.Equality (TestEquality(..))
import qualified Data.Vector as V
import Numeric.Natural (Natural)
import qualified Prettyprinter as PP
import System.IO (stdout)

import qualified Cryptol.Parser.AST.Builder as C
import qualified Cryptol.TypeCheck.Type as Cryptol

import qualified Lang.Crucible.Analysis.Postdom as Crucible
import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Backend.Online as Crucible
import qualified Lang.Crucible.CFG.Core as Crucible
import qualified Lang.Crucible.CFG.Extension as Crucible
import qualified Lang.Crucible.FunctionHandle as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Simulator.GlobalState as Crucible
import qualified Lang.Crucible.Simulator.PathSatisfiability as Crucible
import qualified Lang.Crucible.Simulator.SimError as Crucible

import qualified Mir.DefId as Mir
import qualified Mir.Mir as Mir
import qualified Mir.Generator as Mir
import Mir.Intrinsics (MIR)
import qualified Mir.Intrinsics as Mir
import qualified Mir.ParseTranslate as Mir
import Mir.TransCustom (customOps)
import qualified Mir.Trans as Mir
import qualified Mir.TransTy as Mir

import qualified What4.Config as W4
import qualified What4.Interface as W4
import qualified What4.ProgramLoc as W4

import SAWCore.FiniteValue (ppFirstOrderValue)
import SAWCore.Name (VarName(..))
import SAWCore.Recognizer ((:*:)(..), asTupleType, asVecType)
import SAWCore.SharedTerm
import SAWCoreWhat4.ReturnTrip
import qualified SAWSupport.Pretty as PPS (defaultOpts)
import qualified CryptolSAWCore.CryptolEnv as CryEnv
import CryptolSAWCore.TypedTerm

import SAWCentral.Builtins (eval_bool_inner, eval_int_inner, ghost_value)
import SAWCentral.Crucible.Common
import qualified SAWCentral.Crucible.Common.MethodSpec as MS
import SAWCentral.Crucible.Common.Override
import qualified SAWCentral.Crucible.Common.Setup.Builtins as Setup
import qualified SAWCentral.Crucible.Common.Setup.Type as Setup
import qualified SAWCentral.Crucible.Common.Vacuity as Vacuity
import SAWCentral.Crucible.MIR.MethodSpecIR
import SAWCentral.Crucible.MIR.Override
import SAWCentral.Crucible.MIR.ResolveSetupValue
import SAWCentral.Crucible.MIR.TypeShape
import SAWCentral.Exceptions
import SAWCentral.Options
import SAWCentral.Panic
import qualified SAWCentral.Position as SS
import SAWCentral.Proof
import SAWCentral.Prover.SolverStats
import SAWCentral.Utils (neGroupOn)
import SAWCentral.Value
import SAWCentral.Crucible.MIR.Setup.Value(mccUninterp)

type AssumptionReason = (MS.ConditionMetadata, String)
type SetupValue = MS.SetupValue MIR
type Lemma = MS.ProvedSpec MIR
type MethodSpec = MS.CrucibleMethodSpecIR MIR
type SetupCondition = MS.SetupCondition MIR

-- TODO: something useful with the global pair?
ppMIRAbortedResult :: Crucible.AbortedResult Sym a
                   -> PP.Doc ann
ppMIRAbortedResult = ppAbortedResult (\_gp -> mempty)

-----
-- Commands
-----

mir_alloc :: Mir.Ty -> MIRSetupM SetupValue
mir_alloc = MIRSetupM . mir_alloc_internal MirPointerRef Mir.Immut 1

mir_alloc_mut :: Mir.Ty -> MIRSetupM SetupValue
mir_alloc_mut = MIRSetupM . mir_alloc_internal MirPointerRef Mir.Mut 1

mir_alloc_raw_ptr_const :: Mir.Ty -> MIRSetupM SetupValue
mir_alloc_raw_ptr_const = MIRSetupM . mir_alloc_internal MirPointerRaw Mir.Immut 1

mir_alloc_raw_ptr_mut :: Mir.Ty -> MIRSetupM SetupValue
mir_alloc_raw_ptr_mut = MIRSetupM . mir_alloc_internal MirPointerRaw Mir.Mut 1

mir_alloc_raw_ptr_const_multi :: Int -> Mir.Ty -> MIRSetupM SetupValue
mir_alloc_raw_ptr_const_multi len = MIRSetupM . mir_alloc_internal MirPointerRaw Mir.Immut len

mir_alloc_raw_ptr_mut_multi :: Int -> Mir.Ty -> MIRSetupM SetupValue
mir_alloc_raw_ptr_mut_multi len = MIRSetupM . mir_alloc_internal MirPointerRaw Mir.Mut len

-- | The workhorse for the @mir_alloc@ family of commands.
mir_alloc_internal ::
  MirPointerKind ->
  Mir.Mutability ->
  Int ->
  Mir.Ty ->
  CrucibleSetup MIR SetupValue
mir_alloc_internal pkind mut len mty = do
  st <- get
  let mcc = st ^. Setup.csCrucibleContext
      col = mcc ^. mccRustModule ^. Mir.rmCS ^. Mir.collection

  -- We disallow creating slice references (e.g., &[u8] or &str) using
  -- mir_alloc, as it is unclear what length to give the resulting slice
  -- value.
  case mty of
    Mir.TySlice _ ->
      fail $ unlines
        [ "mir_alloc and mir_alloc_mut cannot be used to create slice references."
        , "Use the mir_slice_value or mir_slice_range_value functions to take a"
        , "slice of an array reference instead."
        ]
    Mir.TyStr ->
      fail $ unlines
        [ "mir_alloc and mir_alloc_mut cannot be used to create str references."
        , "Use the mir_str_slice_value or mir_str_slice_range_value functions"
        , "to take a slice of a `u8` array reference instead."
        ]
    _ ->
      pure ()

  loc <- getW4Position "mir_alloc"
  Some tpr <- case Mir.tyToRepr col mty of
    Left err -> fail ("Unsupported type in mir_alloc: " ++ err)
    Right x -> return x
  n <- Setup.csVarCounter <<%= MS.nextAllocIndex
  tags <- view Setup.croTags
  let md = MS.ConditionMetadata
          { MS.conditionLoc = loc
          , MS.conditionTags = tags
          , MS.conditionType = "fresh allocation"
          , MS.conditionContext = ""
          }
  Setup.currentState . MS.csAllocs . at n ?=
    Some (MirAllocSpec { _maConditionMetadata = md
                      , _maType = tpr
                      , _maPtrKind = pkind
                      , _maMutbl = mut
                      , _maMirType = mty
                      , _maLen = len
                      })
  return (MS.SetupVar n)

-- | Allocate an immutable MIR reference and initialize it to point to a given SetupValue.
-- This is a convenience function that avoids requiring the caller to manually
-- pair @mir_alloc@ and @mir_points_to@.
mir_ref_of :: SetupValue -> MIRSetupM SetupValue
mir_ref_of = mir_ref_of_internal "ref-of" Mir.Immut

-- | Allocate an mutable MIR reference and initialize it to point to a given SetupValue.
-- This is a convenience function that avoids requiring the caller to manually
-- pair @mir_alloc_mut@ and @mir_points_to@.
mir_ref_of_mut :: SetupValue -> MIRSetupM SetupValue
mir_ref_of_mut = mir_ref_of_internal "ref-of-mut" Mir.Mut

-- | The workhorse for @mir_ref_of@' and  @mir_ref_of_mut@.
mir_ref_of_internal :: String -> Mir.Mutability -> SetupValue -> MIRSetupM SetupValue
mir_ref_of_internal label mut val = MIRSetupM $ do
  cc  <- getMIRCrucibleContext
  loc <- getW4Position (Text.pack label)
  st  <- get

  let env     = MS.csAllocations (st ^. Setup.csMethodSpec)
      nameEnv = MS.csTypeNames (st ^. Setup.csMethodSpec)

  ty  <- typeOfSetupValue cc env nameEnv val
  ptr <- mir_alloc_internal MirPointerRef mut 1 ty

  tags <- view Setup.croTags
  let md = MS.ConditionMetadata
            { MS.conditionLoc     = loc
            , MS.conditionTags    = tags
            , MS.conditionType    = "MIR " ++ label
            , MS.conditionContext = ""
            }

  Setup.addPointsTo (MirPointsTo md ptr (MirPointsToSingleTarget val))
  return ptr

mir_execute_func :: [SetupValue] -> MIRSetupM ()
mir_execute_func args =
  MIRSetupM $
  do st <- get
     let cc = st ^. Setup.csCrucibleContext
     let mspec = st ^. Setup.csMethodSpec
     let env = MS.csAllocations mspec
     let nameEnv = MS.csTypeNames mspec
     let argTys = mspec ^. MS.csArgs
     let
       checkArg i expectedTy val =
         do valTy <- typeOfSetupValue cc env nameEnv val
            unless (checkCompatibleTys expectedTy valTy) $
              X.throwM (MIRArgTypeMismatch i expectedTy valTy)
     let
       checkArgs _ [] [] = pure ()
       checkArgs i [] vals =
         X.throwM (MIRArgNumberWrong i (i + length vals))
       checkArgs i tys [] =
         X.throwM (MIRArgNumberWrong (i + length tys) i)
       checkArgs i (ty : tys) (val : vals) =
         do checkArg i ty val
            checkArgs (i + 1) tys vals
     checkArgs 0 argTys args
     Setup.crucible_execute_func args

mir_equal :: SetupValue -> SetupValue -> MIRSetupM ()
mir_equal val1 val2 =
  MIRSetupM $
  do cc <- getMIRCrucibleContext
     loc <- getW4Position "mir_equal"
     st <- get
     let env = MS.csAllocations (st ^. Setup.csMethodSpec)
         nameEnv = MS.csTypeNames (st ^. Setup.csMethodSpec)
     ty1 <- typeOfSetupValue cc env nameEnv val1
     ty2 <- typeOfSetupValue cc env nameEnv val2

     let b = checkCompatibleTys ty1 ty2
     unless b $ throwCrucibleSetup loc $ unlines
       [ "Incompatible types when asserting equality:"
       , show ty1
       , show ty2
       ]
     Setup.crucible_equal loc val1 val2

-- | Extract a MIR function of the given name to SAWCore. See the SAW user
-- manual for more details on what argument/result types this can support.
mir_extract :: Mir.RustModule -> Text -> TopLevel TypedTerm
mir_extract rm nm =
  do opts <- getOptions
     sc <- getSharedContext
     cc <- setupCrucibleContext rm
     fn <- findFn rm nm
     let sig = fn ^. Mir.fsig
     let argTys = sig ^. Mir.fsarg_tys
     let retTy = sig ^. Mir.fsreturn_ty
     acfg <- lookupDefIdCFG rm (fn ^. Mir.fname)
     io $ extractFromMirCFG opts sc cc argTys retTy acfg

-- | Consult the given 'Mir.RustModule' to find an 'Mir.Adt' with the given
-- 'String' as a mangled identifier (i.e., an identifier for an ADT that is
-- already instantiated with type arguments). If such a 'Mir.Adt' cannot be
-- found in the 'Mir.RustModule', this will raise an error.
mir_find_mangled_adt :: Mir.RustModule -> Text -> TopLevel Mir.Adt
mir_find_mangled_adt rm name = do
  let cs = rm ^. Mir.rmCS
      col = cs ^. Mir.collection
  did <- findDefId cs name
  findAdtMangled col did

-- | Consult the given 'Mir.RustModule' to find an 'Mir.Adt'" with the given
-- 'String' as an identifier and the given 'Mir.Ty's as the types used to
-- instantiate the type parameters. If such a 'Mir.Adt' cannot be found in the
-- 'Mir.RustModule', this will raise an error.
mir_find_adt :: Mir.RustModule -> Text -> [Mir.Ty] -> TopLevel Mir.Adt
mir_find_adt rm origName substs = do
  let cs = rm ^. Mir.rmCS
      col = cs ^. Mir.collection
  origDid <- findDefId cs origName
  findAdt col origDid (Mir.Substs substs)

-- | Find an instantiation of a polymorphic function.
mir_find_name :: MonadFail m => Mir.RustModule -> Text -> [Mir.Ty] -> m Text
mir_find_name rm origName tys =
  do
    let cs  = rm ^. Mir.rmCS
        col = cs ^. Mir.collection
    origId <- findDefId cs origName
    findFnInstance col origId (Mir.Substs tys)

-- | Generate a fresh term of the given Cryptol type. The name will be used when
-- pretty-printing the variable in debug output.
mir_fresh_cryptol_var ::
  Text ->
  Cryptol.Schema ->
  MIRSetupM TypedTerm
mir_fresh_cryptol_var name s =
  MIRSetupM $
  do loc <- getW4Position "mir_fresh_var"
     case s of
       Cryptol.Forall [] [] ty ->
         do sc <- lift $ lift getSharedContext
            Setup.freshVariable sc name ty
       _ ->
         throwCrucibleSetup loc $ "Unsupported polymorphic Cryptol type schema: " ++ show s

-- | Create a MIR value entirely populated with fresh symbolic variables.
-- For compound types such as structs and arrays, this will explicitly set
-- each field or element to contain a fresh symbolic variable. The Text
-- argument is used as a prefix in each of the symbolic variables.
mir_fresh_expanded_value ::
  Text                 {- ^ Prefix to use in each symbolic variable -} ->
  Mir.Ty               {- ^ value type -} ->
  MIRSetupM SetupValue {- ^ elaborated setup value -}
mir_fresh_expanded_value pfx ty =
  MIRSetupM $
  do sc <- lift $ lift getSharedContext
     cc <- getMIRCrucibleContext
     let col = cc ^. mccRustModule . Mir.rmCS . Mir.collection
     Some shp <- pure $ tyToShape col ty
     constructExpandedSetupValue cc sc pfx shp

-- | See 'mir_fresh_expanded_val'.
--
-- This is the recursively-called worker function.
constructExpandedSetupValue ::
  MIRCrucibleContext ->
  SharedContext ->
  Text ->
  TypeShape tp ->
  CrucibleSetup MIR SetupValue
constructExpandedSetupValue cc sc = go
  where
    col = cc ^. mccRustModule . Mir.rmCS . Mir.collection

    go :: forall tp.
          Text ->
          TypeShape tp ->
          CrucibleSetup MIR SetupValue
    go pfx shp =
      case shp of
        PrimShape ty _ -> do
          fv <- freshPrimVariable pfx ty
          pure $ MS.SetupTerm fv
        TupleShape _ elems -> do
          flds <- mapM (goAgElem pfx) (zip [0..] elems)
          pure $ MS.SetupTuple () flds
        ArrayShape ty elemTy _ elemShp _ ->
          case ty of
            Mir.TyArray _ n -> do
              elems <-
                traverse
                  (\i -> go (pfx <> "_" <> Text.pack (show i)) elemShp)
                  [0..n-1]
              pure $ MS.SetupArray elemTy elems
            _ ->
              panic "constructExpandedSetupValue" [
                  "ArrayShape with non-TyArray type: " ,
                  "   " <> Text.pack (show (PP.pretty ty))
              ]
        StructShape ty _ fldShps ->
          case ty of
            Mir.TyAdt adtName _ _ ->
              case col ^. Mir.adts . at adtName of
                Just adt@(Mir.Adt _ kind _ _ _ _ _) ->
                  case kind of
                    Mir.Struct -> do
                      flds <- goFlds pfx fldShps
                      pure $ MS.SetupStruct adt flds
                    _ ->
                      panic "constructExpandedSetupValue" [
                          "Expected struct, encountered " <> Text.pack (show kind)
                      ]
                Nothing ->
                  adt_not_found_panic "StructShape" adtName
            _ ->
              non_adt_type_panic "StructShape" ty
        EnumShape ty _ variantShps _ discrShp ->
          case ty of
            Mir.TyAdt adtName _ _ ->
              case col ^. Mir.adts . at adtName of
                Just adt@(Mir.Adt _ kind _ _ _ _ _) ->
                  case kind of
                    Mir.Enum _ ->
                      MS.SetupEnum <$> goEnum pfx adt discrShp variantShps
                    Mir.Struct ->
                      panic "constructExpandedSetupValue" [
                          "Expected enum, encountered struct"
                      ]
                    Mir.Union ->
                      panic "constructExpandedSetupValue" [
                          "Expected enum, encountered union"
                      ]
                Nothing ->
                  adt_not_found_panic "EnumShape" adtName
            _ ->
              non_adt_type_panic "EnumShape" ty
        TransparentShape ty shp' ->
          case ty of
            Mir.TyAdt adtName _ _ -> do
              case col ^. Mir.adts . at adtName of
                Just adt@(Mir.Adt adtNm kind variants _ _ _ _) ->
                  case kind of
                    Mir.Struct -> do
                      val <- go pfx shp'
                      pure $ MS.SetupStruct adt [val]
                    Mir.Enum{}
                      -- `repr(transparent)` enum values use MirSetupEnumVariant
                      -- rather than MirSetupEnumSymbolic. See the Haddocks for
                      -- MirSetupEnumSymbolic for an explanation.
                      |  [variant] <- variants
                      -> do val <- go pfx shp'
                            pure $ MS.SetupEnum
                                 $ MirSetupEnumVariant adt variant 0 [val]

                      |  otherwise
                      -> panic "constructExpandedSetupValue" [
                             "`repr(transparent)` enum that doesn't have exactly one variant",
                             "Enum: " <> Text.pack (show adtNm),
                             "Number of variants: " <> Text.pack (show (length variants))
                         ]
                    Mir.Union ->
                      panic "constructExpandedSetupValue" [
                          "Unexpected `repr(transparent)` union: " <>
                              Text.pack (show adtName)
                      ]
                Nothing ->
                  adt_not_found_panic "TransparentShape" adtName
            _ ->
              non_adt_type_panic "TransparentShape" ty
        RefShape ty _ _ _ ->
          X.throwM $ MIRFreshExpandedValueUnsupportedType ty
        SliceShape ty _ _ _ ->
          X.throwM $ MIRFreshExpandedValueUnsupportedType ty
        FnPtrShape ty _ _ ->
          X.throwM $ MIRFreshExpandedValueUnsupportedType ty

    -- Create a fresh symbolic enum value, as described in
    -- Note [Symbolic enums] in SAWCentral.Crucible.MIR.Setup.Value.
    goEnum ::
      forall discrShp variantCtx.
      Text ->
      Mir.Adt ->
      TypeShape discrShp ->
      Ctx.Assignment VariantShape variantCtx ->
      CrucibleSetup MIR MirSetupEnum
    goEnum pfx adt@(Mir.Adt _ _ variants _ _ _ _) discrShp variantShps =
      mccWithBackend cc $ \bak ->
      do -- First, create a symbolic discriminant value.
         IsBVShape discrTy discrW <- pure $ testDiscriminantIsBV discrShp
         let discrPfx = pfx <> "_discr"
         discrVar <- freshPrimVariable discrPfx discrTy
         let discrVal = MS.SetupTerm discrVar

         -- Next, add Crucible assumptions that constraint the discriminant
         -- to be equal to one of the possible variants' discriminant values.
         -- This assumption will be of the form:
         --
         --   (discr == 0) \/ (discr == 1) \/ ...
         --
         -- It's tempting to simplify this assumption to just
         -- `discr < num_variants`, but this will not work in the event that
         -- the enum uses explicit discriminants for some variants, e.g.,
         --
         --   enum E {
         --       E0 = 42,
         --       E1,
         --   }
         discrWNat <- liftIO $ scNat sc $ natValue discrW
         possibleDiscrTerms <- liftIO $
           traverse (\discr -> do
                      discrNat  <- scNat sc $ fromInteger discr
                      scBvNat sc discrWNat discrNat)
                    (map getEnumVariantDiscr variants)
         scFalse <- liftIO $ scBool sc False
         possibleDiscrPredTerm <- liftIO $
           foldM
             (\z possibleDiscrTerm -> do
               p <- scBvEq sc discrWNat (ttTerm discrVar) possibleDiscrTerm
               scOr sc p z)
             scFalse
             possibleDiscrTerms
         possibleDiscrPred <- liftIO $ resolveSAWPred cc possibleDiscrPredTerm
         loc <- SS.toW4Loc "mir_fresh_expanded_value" <$> lift (lift getPosition)
         liftIO $ Crucible.addAssumption bak $
           Crucible.GenericAssumption
             loc "Symbolic enum discriminant constraints" possibleDiscrPred

         -- Finally, create symbolic fields for each of the possible variants.
         let variantAssns :: [Some (Ctx.Assignment FieldShape)]
             variantAssns =
               FC.toListFC
                 (\(VariantShape fldShps) -> Some fldShps)
                 variantShps
         variantVals <-
           zipWithM
             (\variant (Some fldShps) ->
               let variantPfx = pfx <> "_" <> getEnumVariantShortName variant in
               goFlds variantPfx fldShps)
             variants
             variantAssns

         pure $ MirSetupEnumSymbolic adt discrVal variantVals

    goFlds :: forall ctx.
              Text ->
              Ctx.Assignment FieldShape ctx ->
              CrucibleSetup MIR [SetupValue]
    goFlds pfx fldShps = sequenceA $
      FCI.itoListFC
        (\idx fldShp ->
          let pfx' = pfx <> "_" <> Text.pack (show idx) in
          case fldShp of
            ReqField shp' -> go pfx' shp'
            OptField shp' -> go pfx' shp')
        fldShps

    goAgElem :: Text ->
                (Int, AgElemShape) ->
                CrucibleSetup MIR SetupValue
    goAgElem pfx (idx, AgElemShape _off _sz shp) =
      let pfx' = pfx <> "_" <> Text.pack (show idx) in
      go pfx' shp

    -- Create a fresh variable of a primitive MIR type (where \"primitive\"
    -- is defined by the @cryptolTypeOfActual@ function).
    freshPrimVariable ::
      Text ->
      Mir.Ty ->
      CrucibleSetup MIR TypedTerm
    freshPrimVariable pfx ty =
      case cryptolTypeOfActual ty of
        Nothing ->
          X.throwM $ MIRFreshExpandedValueUnsupportedType ty
        Just cty ->
          Setup.freshVariable sc pfx cty

    adt_not_found_panic :: Text -> Mir.DefId -> a
    adt_not_found_panic shapeName adtName =
      panic "constructExpandedSetupValue" [
          "Could not find ADT in " <> shapeName <> ": " <> Text.pack (show adtName)
      ]

    non_adt_type_panic :: Text -> Mir.Ty -> a
    non_adt_type_panic shapeName ty =
      panic "constructExpandedSetupValue" [
          shapeName <> " with non-TyAdt type: ",
          "   " <> Text.pack (show $ PP.pretty ty)
      ]

-- | Generate a fresh variable term. The name will be used when
-- pretty-printing the variable in debug output.
mir_fresh_var ::
  Text                {- ^ variable name    -} ->
  Mir.Ty              {- ^ variable type    -} ->
  MIRSetupM TypedTerm {- ^ fresh typed term -}
mir_fresh_var name mty =
  MIRSetupM $
  do sc <- lift $ lift getSharedContext
     case cryptolTypeOfActual mty of
       Nothing -> X.throwM $ MIRFreshVarInvalidType mty
       Just cty -> Setup.freshVariable sc name cty

mir_ghost_value ::
  MS.GhostGlobal ->
  TypedTerm ->
  MIRSetupM ()
mir_ghost_value ghost val = MIRSetupM $
  ghost_value ghost val

-- | Load a MIR JSON file and return a handle to it.
mir_load_module :: FilePath -> TopLevel Mir.RustModule
mir_load_module inputFile = do
   b <- io $ BSL.readFile inputFile

   opts <- getOptions
   halloc <- getHandleAlloc

   withImplicitParams opts $ do
     col <- io $ Mir.parseMIR inputFile b
     io $ Mir.translateMIR col halloc

mir_return :: SetupValue -> MIRSetupM ()
mir_return retVal =
  MIRSetupM $
  do st <- get
     let cc = st ^. Setup.csCrucibleContext
     let mspec = st ^. Setup.csMethodSpec
     let env = MS.csAllocations mspec
     let nameEnv = MS.csTypeNames mspec
     valTy <- typeOfSetupValue cc env nameEnv retVal
     case mspec ^. MS.csRet of
       Nothing ->
         unless (checkCompatibleTys (Mir.TyTuple []) valTy) $
           X.throwM (MIRReturnUnexpected valTy)
       Just retTy ->
         unless (checkCompatibleTys retTy valTy) $
           X.throwM (MIRReturnTypeMismatch retTy valTy)
     Setup.crucible_return retVal


mir_assert :: TypedTerm -> MIRSetupM ()
mir_assert term = MIRSetupM $ do
  loc <- SS.toW4Loc "mir_assert" <$> lift (lift getPosition)
  tags <- view Setup.croTags
  let md = MS.ConditionMetadata
           { MS.conditionLoc = loc
           , MS.conditionTags = tags
           , MS.conditionType = "specification assertion"
           , MS.conditionContext = ""
           }
  Setup.addCondition (MS.SetupCond_Pred md term)

mir_precond :: TypedTerm -> MIRSetupM ()
mir_precond term = MIRSetupM $ do
  loc <- SS.toW4Loc "mir_precond" <$> lift (lift getPosition)
  Setup.crucible_precond loc term

mir_postcond :: TypedTerm -> MIRSetupM ()
mir_postcond term = MIRSetupM $ do
  loc <- SS.toW4Loc "mir_postcond" <$> lift (lift getPosition)
  Setup.crucible_postcond loc term

mir_cast_raw_ptr ::
  SetupValue {- ^ raw pointer -} ->
  Mir.Ty     {- ^ new pointee type -} ->
  SetupValue
mir_cast_raw_ptr ptr mty = MS.SetupCast mty ptr

-- | Which kind of @mir_points_to@.
data MirPointsToMode = PointsToSingle | PointsToMulti

mirPointsToCommandName :: IsString a => MirPointsToMode -> a
mirPointsToCommandName PointsToSingle = "mir_points_to"
mirPointsToCommandName PointsToMulti = "mir_points_to_multi"

mir_points_to ::
  SetupValue {- ^ LHS reference/pointer -} ->
  SetupValue {- ^ RHS value -} ->
  MIRSetupM ()
mir_points_to = mir_points_to_internal PointsToSingle

mir_points_to_multi ::
  SetupValue {- ^ LHS raw pointer -} ->
  SetupValue {- ^ RHS array value -} ->
  MIRSetupM ()
mir_points_to_multi = mir_points_to_internal PointsToMulti

mir_points_to_internal ::
  MirPointsToMode {- ^ Which kind of @mir_points_to@ -} ->
  SetupValue {- ^ LHS reference/pointer -} ->
  SetupValue {- ^ RHS value -} ->
  MIRSetupM ()
mir_points_to_internal mode ref val =
  MIRSetupM $
  do cc <- getMIRCrucibleContext
     loc <- getW4Position $ mirPointsToCommandName mode
     st <- lift get
     let env = MS.csAllocations (st ^. Setup.csMethodSpec)
         nameEnv = MS.csTypeNames (st ^. Setup.csMethodSpec)

     referentTy <- mir_points_to_check_lhs_validity ref loc mode
     valTy <- typeOfSetupValue cc env nameEnv val

     target <-
       case mode of
         PointsToSingle -> do
           checkTypes referentTy valTy
           pure $ MirPointsToSingleTarget val
         PointsToMulti ->
           case valTy of
             Mir.TyArray elemTy _ -> do
               checkTypes referentTy elemTy
               pure $ MirPointsToMultiTarget val
             _ ->
              fail $ unlines
                [ "Second argument of `mir_points_to_multi` must be an array, but got type:"
                , show (PP.pretty valTy)
                ]
     tags <- view Setup.croTags
     let md = MS.ConditionMetadata
              { MS.conditionLoc = loc
              , MS.conditionTags = tags
              , MS.conditionType = "MIR points-to"
              , MS.conditionContext = ""
              }
     Setup.addPointsTo (MirPointsTo md ref target)

  where
    checkTypes referentTy valTy =
      unless (checkCompatibleTys referentTy valTy) $
        fail $ unlines
          [ "Referent type incompatible with value in `"
            ++ mirPointsToCommandName mode ++ "` statement:"
           , "  Referent type: " ++ show (PP.pretty referentTy)
           , "  Value type:    " ++ show (PP.pretty valTy)
           ]

mir_unint :: [Text] -> MIRSetupM ()
mir_unint term = MIRSetupM (Setup.declare_unint "mir_unint" mccUninterp term)

-- | Perform a set of validity checks on the LHS reference or pointer value in a
-- 'mir_points_to' or 'mir_points_to_multi' command. In particular:
--
-- * Check that the LHS is the expected type (reference or raw pointer for
--   'mir_points_to', and only raw pointer for 'mir_points_to_multi').
-- * Make sure that it does not contain any casts.
--
-- Returns the 'Mir.Ty' that the LHS points to.
mir_points_to_check_lhs_validity ::
  SetupValue {- ^ LHS reference/pointer -} ->
  W4.ProgramLoc {- ^ The location in the program -} ->
  MirPointsToMode {- ^ Which kind of @mir_points_to@ -} ->
  Setup.CrucibleSetupT MIR TopLevel Mir.Ty
mir_points_to_check_lhs_validity ref loc mode =
  do cc <- getMIRCrucibleContext
     st <- get
     let env = MS.csAllocations (st ^. Setup.csMethodSpec)
         nameEnv = MS.csTypeNames (st ^. Setup.csMethodSpec)
     refTy <- typeOfSetupValue cc env nameEnv ref
     when (containsCast ref) $
       throwCrucibleSetup loc $
         "The first argument of " ++ mirPointsToCommandName mode
         ++ " must not contain any casts"
     let throwWrongType acceptedType =
           throwCrucibleSetup loc $ "lhs not a " ++ acceptedType ++ ": "
                                 ++ show (PP.pretty refTy)
     case mode of
       PointsToSingle ->
         case refTy of
           Mir.TyRef referentTy _ -> pure referentTy
           Mir.TyRawPtr referentTy _ -> pure referentTy
           _ -> throwWrongType "reference or raw pointer type"
       PointsToMulti ->
         case refTy of
           Mir.TyRawPtr referentTy _ -> pure referentTy
           _ -> throwWrongType "raw pointer type"

mir_unsafe_assume_spec ::
  Mir.RustModule ->
  Text         {- ^ Name of the function -} ->
  MIRSetupM () {- ^ Boundary specification -} ->
  TopLevel Lemma
mir_unsafe_assume_spec rm nm setup =
  do cc <- setupCrucibleContext rm
     pos <- getPosition
     let loc = SS.toW4Loc "_SAW_mir_unsafe_assume_spec" pos
     fn <- findFn rm nm
     let st0 = initialCrucibleSetupState cc fn loc
     ms <- execMIRSetup setup st0
     ps <- io (MS.mkProvedSpec MS.SpecAdmitted ms mempty mempty mempty 0)
     returnMIRProof ps

execMIRSetup ::
  MIRSetupM a ->
  Setup.CrucibleSetupState MIR ->
  TopLevel MethodSpec
execMIRSetup setup st0 = do
  st' <- execStateT
           (runReaderT (runMIRSetupM setup) Setup.makeCrucibleSetupRO)
           st0

  -- Exactly one mir_execute_func is required
  unless (st' ^. Setup.csPrePost == MS.PostState) $
    X.throwM MIRExecuteMissing

  let mspec = st' ^. Setup.csMethodSpec

  -- mir_return is required unless the return type is ()
  case mspec ^. MS.csRet of
    Nothing ->
      pure ()

    Just retTy ->
      -- non-unit return types: mir_return is required
      case mspec ^. MS.csRetValue of
        Just _  -> pure ()
        Nothing -> X.throwM (MIRReturnMissing retTy)

  pure mspec

mir_verify ::
  Mir.RustModule ->
  Text {- ^ method name -} ->
  [Lemma] {- ^ overrides -} ->
  Bool {- ^ path sat checking -} ->
  MIRSetupM () ->
  ProofScript () ->
  TopLevel Lemma
mir_verify rm nm lemmas checkSat setup tactic =
  do start <- io getCurrentTime
     opts <- getOptions

     -- set up the metadata map for tracking proof obligation metadata
     mdMap <- io $ newIORef mempty

     cc <- setupCrucibleContext rm
     SomeOnlineBackend bak <- pure (cc^.mccBackend)
     let sym = cc^.mccSym
     let globals0 = cc^.mccSymGlobalState

     sosp <- rwSingleOverrideSpecialCase <$> getTopLevelRW
     let ?singleOverrideSpecialCase = sosp

     pos <- getPosition
     let loc = SS.toW4Loc "_SAW_mir_verify" pos

     profFile <- rwProfilingFile <$> getTopLevelRW
     (writeFinalProfile, pfs) <- io $ setupProfiling sym "mir_verify" profFile

     fn <- findFn rm nm
     let st0 = initialCrucibleSetupState cc fn loc

     -- execute commands of the method spec
     io $ W4.setCurrentProgramLoc sym loc
     methodSpec <- execMIRSetup setup st0

     printOutLnTop Info $
       unwords ["Verifying", show (methodSpec ^. MS.csMethod), "..."]

     -- construct the initial state for verifications
     (args, assumes, env, globals1) <- io $ verifyPrestate cc methodSpec globals0

     -- save initial path conditions
     frameIdent <- io $ Crucible.pushAssumptionFrame bak

     -- check for contradictory preconditions
     when (detectVacuity opts) $
       Vacuity.checkAssumptionsForContradictions
         sym
         methodSpec
         tactic
         assumes

     -- run the symbolic execution
     printOutLnTop Info $
       unwords ["Simulating", show (methodSpec ^. MS.csMethod), "..."]
     top_loc <- SS.toW4Loc "mir_verify" <$> getPosition
     (ret, globals2) <-
       io $ verifySimulate opts cc pfs methodSpec args assumes top_loc lemmas globals1 checkSat mdMap

     -- collect the proof obligations
     asserts <- verifyPoststate cc
                    methodSpec env globals2 ret mdMap

     -- restore previous assumption state
     _ <- io $ Crucible.popAssumptionFrame bak frameIdent

     -- attempt to verify the proof obligations
     printOutLnTop Info $
       unwords ["Checking proof obligations", show (methodSpec ^. MS.csMethod), "..."]
     (stats,vcstats) <- verifyObligations cc methodSpec tactic assumes asserts
     io $ writeFinalProfile

     let lemmaSet = Set.fromList (map (view MS.psSpecIdent) lemmas)
     end <- io getCurrentTime
     let diff = diffUTCTime end start
     ps <- io (MS.mkProvedSpec MS.SpecProved methodSpec stats vcstats lemmaSet diff)
     returnMIRProof ps

-----
-- MIR enums
-----

-- | Construct a specific enum variant. This does a light amount of validity
-- checking, which is the only reason that this function is monadic.
mir_enum_value ::
  X.MonadThrow m =>
  Mir.Adt ->
  Text ->
  [MS.SetupValue MIR] ->
  m (MS.SetupValue MIR)
mir_enum_value adt variantNm vs =
  case adt of
    Mir.Adt adtNm (Mir.Enum _) variants _ _ _ _ -> do
      (variantIdx, variant) <-
        case FWI.ifind (\_ v -> variantDefIdMatches v) variants of
          Just iv ->
            pure iv
          Nothing ->
            X.throwM $ MIREnumValueVariantNotFound adtNm variantNm
      pure $ MS.SetupEnum $ MirSetupEnumVariant adt variant variantIdx vs
    Mir.Adt adtNm Mir.Struct _ _ _ _ _ ->
      X.throwM $ MIREnumValueNonEnum adtNm "struct"
    Mir.Adt adtNm Mir.Union _ _ _ _ _ ->
      X.throwM $ MIREnumValueNonEnum adtNm "union"
  where
    -- Check if the user-supplied String argument matches the name of the given
    -- variant's DefId. For instance, the variant DefId might be named
    -- @core::option[0]::Option[0]::Some[0]@, but the user will simply write
    -- @Some@, so we must strip off the other parts of the DefId before checking
    -- if the two are the same.
    variantDefIdMatches :: Mir.Variant -> Bool
    variantDefIdMatches variant =
      getEnumVariantShortName variant == variantNm

-----
-- MIR slices
-----

-- Array slices ([T])

mir_slice_value :: MS.SetupValue MIR -> MS.SetupValue MIR
mir_slice_value arrRef =
  MS.SetupSlice (MirSetupSlice MirArraySlice arrRef)

mir_slice_range_value ::
  MS.SetupValue MIR -> Int -> Int -> MS.SetupValue MIR
mir_slice_range_value arrRef start end =
  MS.SetupSlice (MirSetupSliceRange MirArraySlice arrRef start end)

-- String slices (str)

mir_str_slice_value :: MS.SetupValue MIR -> MS.SetupValue MIR
mir_str_slice_value arrRef =
  MS.SetupSlice (MirSetupSlice MirStrSlice arrRef)

mir_str_slice_range_value ::
  MS.SetupValue MIR -> Int -> Int -> MS.SetupValue MIR
mir_str_slice_range_value arrRef start end =
  MS.SetupSlice (MirSetupSliceRange MirStrSlice arrRef start end)

-----
-- MIR projections
-----

mir_elem_value :: MS.SetupValue MIR -> Int -> MS.SetupValue MIR
mir_elem_value = MS.SetupElem MirIndexIntoVal

mir_elem_ref :: MS.SetupValue MIR -> Int -> MS.SetupValue MIR
mir_elem_ref = MS.SetupElem MirIndexIntoRef

-----
-- MIR muxing
-----

mir_mux_values ::
  TypedTerm ->
  MS.SetupValue MIR ->
  MS.SetupValue MIR ->
  MS.SetupValue MIR
mir_mux_values = MS.SetupMux ()

-----
-- Rust Vecs
-----

mir_vec_of ::
  Text ->
  Mir.Ty ->
  SetupValue ->
  MIRSetupM SetupValue
mir_vec_of prefix elemTy contents = do
  st <- MIRSetupM get
  let cc = st ^. Setup.csCrucibleContext
      mspec = st ^. Setup.csMethodSpec
      env = MS.csAllocations mspec
      nameEnv = MS.csTypeNames mspec

  -- Check the type of contents
  contentsTy <- MIRSetupM $ typeOfSetupValue cc env nameEnv contents
  case contentsTy of
    Mir.TyArray elemTy' len -> do

      -- Ensure array element type matches passed-in type
      unless (checkCompatibleTys elemTy elemTy') $
        MIRSetupM $ X.throwM $ MIRVecOfTypeMismatch elemTy elemTy'

      -- Find all the internal ADTs used in Vec
      let rm = cc ^. mccRustModule
          col = rm ^. Mir.rmCS . Mir.collection
          find name tyArgs = mirTopLevel $ mir_find_adt rm name tyArgs
      globalAllocAdt <-
        find globalAllocId []
      vecTAdt <-
        find vecId [elemTy, mir_adt globalAllocAdt]
      rawVecTAdt <-
        find "alloc::raw_vec::RawVec" [elemTy, mir_adt globalAllocAdt]
      typedAllocatorTAdt <-
        find "crucible::alloc::TypedAllocator" [elemTy]
      rawVecInnerTAdt <-
        find "alloc::raw_vec::RawVecInner" [mir_adt typedAllocatorTAdt]
      uniqueU8Adt <-
        find "core::ptr::unique::Unique" [mir_u8]
      nonNullU8Adt <-
        find "core::ptr::non_null::NonNull" [mir_u8]
      phantomDataU8Adt <-
        find "core::marker::PhantomData" [mir_u8]
      phantomDataTAdt <-
        find "core::marker::PhantomData" [elemTy]
      usizeNoHighBitAdt <-
        find "core::num::niche_types::UsizeNoHighBit" []

      -- Set up Cryptol environment
      sc <- mirTopLevel getSharedContext
      let transCry cryEnv =
            let ?fileReader = BSS.readFile
            in  MIRSetupM . liftIO . CryEnv.pExprToTypedTerm sc cryEnv
      cryEnv <- mirTopLevel getCryptolEnv
      let sizeBits = knownNat @Mir.SizeBits

      -- Declare symbolic variables and assertions
      ptr <- mir_alloc_raw_ptr_const_multi len elemTy
      mir_points_to_multi ptr contents
      cap <-
        case Map.lookup elemTy (col ^. Mir.layouts) of
          Just (Just Mir.Layout { Mir._laySize = elemSize })
            | elemSize == 0 ->
              -- The ZST case won't work yet at least until crucible issues
              -- #1497 and #1504 are fixed. When that happens, uncomment the
              -- code below and also the ZST tests in
              -- intTests/test2032/test.saw.
              fail "mir_vec_of: Vec of ZST not supported yet"
              -- -- For ZST, cap is always 0
              -- transCry cryEnv $ C.bvLit 0 (natValue sizeBits)
            | otherwise -> do
              cap <- mir_fresh_var (prefix <> "_cap") mir_usize
              let capIdent = "cap"
                  cryEnv' = CryEnv.bindTypedTerm (capIdent, cap) cryEnv
                  maxCap = maxSigned sizeBits `div` toInteger elemSize
              -- cap <= isize::MAX / sizeof::<elemTy>
              mir_assert =<< transCry cryEnv'
                (C.var capIdent C.<= C.intLit maxCap)
              -- cap >= len
              mir_assert =<< transCry cryEnv'
                (C.var capIdent C.>= C.intLit len)
              pure cap
          Just Nothing -> MIRSetupM $ X.throwM $ MIRVecOfElemTyNotSized elemTy
          Nothing -> MIRSetupM $ X.throwM $ MIRVecOfElemTyNoLayoutInfo elemTy
      lenTerm <- transCry cryEnv $
        C.bvLit (fromIntegral len) (natValue sizeBits)

      -- Construct and return the Vec
      let vec =
            MS.SetupStruct vecTAdt
                           [rawVec, MS.SetupTerm lenTerm]
            where
            rawVec =
              MS.SetupStruct rawVecTAdt
                             [rawVecInner, globalAlloc, phantomDataT]
              where
              rawVecInner =
                MS.SetupStruct rawVecInnerTAdt
                               [uniqueU8Ptr, capNoHighBit, typedAllocator]
                where
                uniqueU8Ptr =
                  MS.SetupStruct uniqueU8Adt
                                 [nonNullU8Ptr, phantomDataU8]
                  where
                  nonNullU8Ptr =
                    MS.SetupStruct nonNullU8Adt
                                   [u8Ptr]
                    where
                    u8Ptr = mir_cast_raw_ptr ptr mir_u8
                capNoHighBit =
                  MS.SetupStruct usizeNoHighBitAdt
                                 [MS.SetupTerm cap]
                typedAllocator =
                  MS.SetupStruct typedAllocatorTAdt
                                 [phantomDataT]
              globalAlloc = MS.SetupStruct globalAllocAdt []
            phantomDataT = MS.SetupStruct phantomDataTAdt []
            phantomDataU8 = MS.SetupStruct phantomDataU8Adt []

      pure vec

    _ -> MIRSetupM $ X.throwM $ MIRVecOfContentsNotArray contentsTy

-----
-- Mir.Types
-----

mir_adt :: Mir.Adt -> Mir.Ty
mir_adt = mirAdtToTy

mir_array :: Int -> Mir.Ty -> Mir.Ty
mir_array n t = Mir.TyArray t n

mir_bool :: Mir.Ty
mir_bool = Mir.TyBool

mir_char :: Mir.Ty
mir_char = Mir.TyChar

-- | A constant value used to instantiate a const generic parameter. This is
-- intended to be used in conjunction with @mir_find_adt@ to look up
-- instantiations of const generic ADTs.
mir_const :: Mir.Ty -> TypedTerm -> TopLevel Mir.Ty
mir_const ty term = do
  constVal <-
    case ty of
      Mir.TyBool -> extractConstBool term
      Mir.TyChar -> extractConstChar term
      Mir.TyInt bs -> extractConstInt bs term
      Mir.TyUint bs -> extractConstUint bs term
      _ -> unsupportedType
  pure $ Mir.TyConst constVal
  where
    extractConstBool :: TypedTerm -> TopLevel Mir.ConstVal
    extractConstBool t = do
      b <- eval_bool_inner "mir_const" t
      pure $ Mir.ConstBool b

    extractConstChar :: TypedTerm -> TopLevel Mir.ConstVal
    extractConstChar t = do
      (actualWidth, val) <- eval_int_inner "mir_const" t
      checkBitvectorWidth 32 actualWidth
      pure $ Mir.ConstChar $ chr $ fromInteger @Int val

    extractConstInt :: Mir.BaseSize -> TypedTerm -> TopLevel Mir.ConstVal
    extractConstInt bs t = do
      (actualWidth, val) <- eval_int_inner "mir_const" t
      (expectedWidth, intLit) <-
        case bs of
          Mir.USize -> pure (intValue (knownNat @Mir.SizeBits), Mir.Isize val)
          Mir.B8 -> pure (8, Mir.I8 val)
          Mir.B16 -> pure (16, Mir.I16 val)
          Mir.B32 -> pure (32, Mir.I32 val)
          Mir.B64 -> pure (64, Mir.I64 val)
          Mir.B128 -> pure (128, Mir.I128 val)
      checkBitvectorWidth expectedWidth actualWidth
      pure $ Mir.ConstInt intLit

    extractConstUint :: Mir.BaseSize -> TypedTerm -> TopLevel Mir.ConstVal
    extractConstUint bs t = do
      (actualWidth, val) <- eval_int_inner "mir_const" t
      (expectedWidth, uintLit) <-
        case bs of
          Mir.USize -> pure (intValue (knownNat @Mir.SizeBits), Mir.Usize val)
          Mir.B8 -> pure (8, Mir.U8 val)
          Mir.B16 -> pure (16, Mir.U16 val)
          Mir.B32 -> pure (32, Mir.U32 val)
          Mir.B64 -> pure (64, Mir.U64 val)
          Mir.B128 -> pure (128, Mir.U128 val)
      checkBitvectorWidth expectedWidth actualWidth
      pure $ Mir.ConstInt uintLit

    checkBitvectorWidth :: Integer -> Integer -> TopLevel ()
    checkBitvectorWidth expectedWidth actualWidth =
      unless (expectedWidth == actualWidth) $
        malformed $
          "Expected " ++ show expectedWidth ++
          "-bit bitvector, but bitvector is actually " ++
          show actualWidth ++ " bits"

    unsupportedType :: TopLevel a
    unsupportedType =
      malformed $ "Unsupported constant type " ++ show (PP.pretty ty)

    malformed :: String -> TopLevel a
    malformed msg = fail $ "mir_const: " ++ msg

mir_i8 :: Mir.Ty
mir_i8 = Mir.TyInt Mir.B8

mir_i16 :: Mir.Ty
mir_i16 = Mir.TyInt Mir.B16

mir_i32 :: Mir.Ty
mir_i32 = Mir.TyInt Mir.B32

mir_i64 :: Mir.Ty
mir_i64 = Mir.TyInt Mir.B64

mir_i128 :: Mir.Ty
mir_i128 = Mir.TyInt Mir.B128

mir_isize :: Mir.Ty
mir_isize = Mir.TyInt Mir.USize

mir_f32 :: Mir.Ty
mir_f32 = Mir.TyFloat Mir.F32

mir_f64 :: Mir.Ty
mir_f64 = Mir.TyFloat Mir.F64

mir_lifetime :: Mir.Ty
mir_lifetime = Mir.TyLifetime

mir_raw_ptr_const :: Mir.Ty -> Mir.Ty
mir_raw_ptr_const ty = Mir.TyRawPtr ty Mir.Immut

mir_raw_ptr_mut :: Mir.Ty -> Mir.Ty
mir_raw_ptr_mut ty = Mir.TyRawPtr ty Mir.Mut

mir_ref :: Mir.Ty -> Mir.Ty
mir_ref ty = Mir.TyRef ty Mir.Immut

mir_ref_mut :: Mir.Ty -> Mir.Ty
mir_ref_mut ty = Mir.TyRef ty Mir.Mut

mir_slice :: Mir.Ty -> Mir.Ty
mir_slice = Mir.TySlice

mir_str :: Mir.Ty
mir_str = Mir.TyStr

mir_tuple :: [Mir.Ty] -> Mir.Ty
mir_tuple = Mir.TyTuple

mir_u8 :: Mir.Ty
mir_u8 = Mir.TyUint Mir.B8

mir_u16 :: Mir.Ty
mir_u16 = Mir.TyUint Mir.B16

mir_u32 :: Mir.Ty
mir_u32 = Mir.TyUint Mir.B32

mir_u64 :: Mir.Ty
mir_u64 = Mir.TyUint Mir.B64

mir_u128 :: Mir.Ty
mir_u128 = Mir.TyUint Mir.B128

mir_usize :: Mir.Ty
mir_usize = Mir.TyUint Mir.USize

mir_vec :: Mir.RustModule -> Mir.Ty -> TopLevel Mir.Ty
mir_vec rm elemTy = do
  globalAllocAdt <- mir_find_adt rm globalAllocId []
  vecTAdt <- mir_find_adt rm vecId [elemTy, mir_adt globalAllocAdt]
  pure $ mir_adt vecTAdt

--------------------------------------------------------------------------------
-- mir_verify
--------------------------------------------------------------------------------

-- | Create a SAWCore formula asserting that two 'MIRVal's are equal.
assertEqualVals ::
  MIRCrucibleContext ->
  MIRVal ->
  MIRVal ->
  IO Term
assertEqualVals cc v1 v2 =
  do let sym = cc^.mccSym
     st <- sawCoreState sym
     toSC sym st =<< equalValsPred cc v1 v2

registerOverride ::
  (?singleOverrideSpecialCase :: Bool) =>
  Options ->
  MIRCrucibleContext ->
  Crucible.SimContext (SAWCruciblePersonality Sym) Sym MIR ->
  W4.ProgramLoc ->
  IORef MetadataMap {- ^ metadata map -} ->
  NonEmpty MethodSpec ->
  Crucible.OverrideSim (SAWCruciblePersonality Sym) Sym MIR rtp args ret ()
registerOverride opts cc _ctx _top_loc mdMap cs =
  do let sym = cc^.mccSym
     let c0 = NE.head cs
     let method = c0 ^. MS.csMethod
     let rm = cc^.mccRustModule

     sc <- saw_ctx <$> liftIO (sawCoreState sym)

     Crucible.AnyCFG cfg <- lookupDefIdCFG rm method
     let h = Crucible.cfgHandle cfg
     let retTy = Crucible.handleReturnType h

     Crucible.bindFnHandle h
       $ Crucible.UseOverride
       $ Crucible.mkOverride'
           (Crucible.handleName h)
           retTy
           (methodSpecHandler opts sc cc mdMap cs h)

resolveArguments ::
  MIRCrucibleContext ->
  MethodSpec ->
  Map MS.AllocIndex (Some (MirPointer Sym)) ->
  IO [(Mir.Ty, MIRVal)]
resolveArguments cc mspec env = mapM resolveArg [0..(nArgs-1)]
  where
    nArgs = toInteger (length (mspec ^. MS.csArgs))
    tyenv = MS.csAllocations mspec
    nameEnv = mspec ^. MS.csPreState . MS.csVarTypeNames
    nm = mspec ^. MS.csMethod

    checkArgTy i mt mt' =
      unless (checkCompatibleTys mt mt') $
           fail $ unlines [ "Type mismatch in argument " ++ show i ++ " when verifying " ++ show nm
                          , "Argument is declared with type: " ++ show mt
                          , "but provided argument has incompatible type: " ++ show mt'
                          , "Note: this may be because the signature of your " ++
                            "function changed during compilation."
                          ]
    resolveArg i =
      case Map.lookup i (mspec ^. MS.csArgBindings) of
        Just (mt, sv) -> do
          mt' <- typeOfSetupValue cc tyenv nameEnv sv
          checkArgTy i mt mt'
          v <- resolveSetupVal cc env tyenv nameEnv sv
          return (mt, v)
        Nothing -> fail $ unwords ["Argument", show i, "unspecified when verifying", show nm]

-- | For each points-to constraint in the pre-state section of the
-- function spec, write the given value to the address of the given
-- pointer.
setupPrePointsTos ::
  MethodSpec ->
  MIRCrucibleContext ->
  Map MS.AllocIndex (Some (MirPointer Sym)) ->
  [MirPointsTo] ->
  Crucible.SymGlobalState Sym ->
  IO (Crucible.SymGlobalState Sym)
setupPrePointsTos mspec cc env pts mem0 =
  foldM (doPointsTo mspec cc env) mem0 pts

-- | Sets up globals (ghost variable), and collects boolean terms
-- that should be assumed to be true.
setupPrestateConditions ::
  MethodSpec ->
  MIRCrucibleContext ->
  Map MS.AllocIndex (Some (MirPointer Sym)) ->
  Crucible.SymGlobalState Sym ->
  [SetupCondition] ->
  IO ( Crucible.SymGlobalState Sym, [Crucible.LabeledPred Term AssumptionReason]
     )
setupPrestateConditions mspec cc env = aux []
  where
    tyenv   = MS.csAllocations mspec
    nameEnv = mspec ^. MS.csPreState . MS.csVarTypeNames

    aux acc globals [] = return (globals, acc)

    aux acc globals (MS.SetupCond_Equal loc val1 val2 : xs) =
      do val1' <- resolveSetupVal cc env tyenv nameEnv val1
         val2' <- resolveSetupVal cc env tyenv nameEnv val2
         t     <- assertEqualVals cc val1' val2'
         let lp = Crucible.LabeledPred t (loc, "equality precondition")
         aux (lp:acc) globals xs

    aux acc globals (MS.SetupCond_Pred loc tm : xs) =
      let lp = Crucible.LabeledPred (ttTerm tm) (loc, "precondition") in
      aux (lp:acc) globals xs

    aux acc globals (MS.SetupCond_Ghost _md var val : xs) =
      case val of
        TypedTerm (TypedTermSchema sch) tm ->
          aux acc (Crucible.insertGlobal var (sch,tm) globals) xs
        TypedTerm tp _ ->
          fail $ unlines
            [ "Setup term for global variable expected to have Cryptol schema type, but got"
            , show (prettyTypedTermTypePure tp)
            ]

verifyObligations ::
  MIRCrucibleContext ->
  MethodSpec ->
  ProofScript () ->
  [Crucible.LabeledPred Term AssumptionReason] ->
  [(String, MS.ConditionMetadata, Term)] ->
  TopLevel (SolverStats, [MS.VCStats])
verifyObligations cc mspec tactic assumes asserts =
  do let sym = cc^.mccSym
     st <- io $ sawCoreState sym
     let sc = saw_ctx st
     assume <- io $ scAndList sc (toListOf (folded . Crucible.labeledPred) assumes)
     let nm = show $ mspec ^. MS.csMethod
     outs <- forM (zip [(0::Int)..] asserts) $ \(n, (msg, md, assert)) -> do
       goal   <- io $ scImplies sc assume assert
       goal'  <- io $ boolToProp sc [] goal -- TODO, generalize over inputs
       let ploc = MS.conditionLoc md
       let gloc = (unwords [show (W4.plSourceLoc ploc)
                          ,"in"
                          , show (W4.plFunction ploc)]) ++
                  (if Prelude.null (MS.conditionContext md) then [] else
                     "\n" ++ MS.conditionContext md)
       let goalname = concat [nm, " (", takeWhile (/= '\n') msg, ")"]
       let proofgoal = ProofGoal
                       { goalNum  = n
                       , goalType = MS.conditionType md
                       , goalName = nm
                       , goalLoc  = gloc
                       , goalDesc = msg
                       , goalSequent = propToSequent goal'
                       , goalTags = MS.conditionTags md
                       }
       res <- runProofScript tactic goal' proofgoal (Just ploc)
                (Text.unwords
                 ["MIR verification condition:", Text.pack (show n), Text.pack goalname])
                False -- do not record in the theorem database
                False -- TODO, useSequentGoals...
       case res of
         ValidProof stats thm ->
           return (stats, MS.VCStats md stats (thmSummary thm) (thmNonce thm) (thmDepends thm) (thmElapsedTime thm))
         InvalidProof stats vals _pst -> do
           printOutLnTop Info $ unwords ["Subgoal failed:", nm, msg]
           printOutLnTop Info (show stats)
           printOutLnTop OnlyCounterExamples "----------Counterexample----------"
           opts <- rwPPOpts <$> getTopLevelRW
           let showVar x = Text.unpack (vnName x)
           let showAssignment (name, val) = "  " ++ showVar name ++ ": " ++ show (ppFirstOrderValue opts val)
           mapM_ (printOutLnTop OnlyCounterExamples . showAssignment) vals
           io $ fail "Proof failed." -- Mirroring behavior of llvm_verify
         UnfinishedProof pst ->
           io $ fail $ "Proof failed " ++ show (length (psGoals pst)) ++ " goals remaining."

     printOutLnTop Info $ unwords ["Proof succeeded!", nm]

     let stats = mconcat (map fst outs)
     let vcstats = map snd outs
     return (stats, vcstats)

verifyPoststate ::
  MIRCrucibleContext                        {- ^ crucible context        -} ->
  MethodSpec                                {- ^ specification           -} ->
  Map MS.AllocIndex (Some (MirPointer Sym)) {- ^ allocation substitution -} ->
  Crucible.SymGlobalState Sym               {- ^ global variables        -} ->
  Maybe MIRVal                              {- ^ optional return value   -} ->
  IORef MetadataMap                         {- ^ metadata map            -} ->
  TopLevel [(String, MS.ConditionMetadata, Term)] {- ^ generated labels and verification conditions -}
verifyPoststate cc mspec env0 globals ret mdMap =
  mccWithBackend cc $ \bak ->
  do opts <- getOptions
     sc <- getSharedContext
     poststateLoc <- SS.toW4Loc "_SAW_MIR_verifyPoststate" <$> getPosition
     io $ W4.setCurrentProgramLoc sym poststateLoc

     -- This discards all the obligations generated during
     -- symbolic execution itself, i.e., which are not directly
     -- generated from specification postconditions. This
     -- is, in general, unsound.
     skipSafetyProofs <- gets rwSkipSafetyProofs
     when skipSafetyProofs (io (Crucible.clearProofObligations bak))

     let vars0 = IntMap.fromList
           [ (vnIndex vn, (vn, tvType tt))
           | tt <- mspec ^. MS.csPreState . MS.csFreshVars
           , let vn = tvName tt ]
     terms0 <- io $ scVariables sc vars0

     let initialFree = Set.fromList (map (vnIndex . tvName)
                                    (view (MS.csPostState . MS.csFreshVars) mspec))
     matchPost <- io $
          runOverrideMatcher sym globals env0 terms0 initialFree poststateLoc $
           do matchResult opts sc
              learnCond opts sc cc mspec MS.PostState (mspec ^. MS.csPostState)

     st <- case matchPost of
             Left err      -> fail (show err)
             Right (_, st) -> return st
     io $ forM_ (view osAsserts st) $ \(md, Crucible.LabeledPred p r) ->
       do (ann,p') <- W4.annotateTerm sym p
          modifyIORef mdMap (Map.insert ann md)
          Crucible.addAssertion bak (Crucible.LabeledPred p' r)

     finalMdMap <- io $ readIORef mdMap
     obligations <- io $ Crucible.getProofObligations bak
     io $ Crucible.clearProofObligations bak
     io $ mapM (verifyObligation sc finalMdMap) (maybe [] Crucible.goalsToList obligations)

  where
    sym = cc^.mccSym

    verifyObligation sc finalMdMap
      (Crucible.ProofGoal hyps (Crucible.LabeledPred concl (Crucible.SimError loc err))) =
      do st         <- sawCoreState sym
         hypTerm <- toSC sym st =<< Crucible.assumptionsPred sym hyps
         conclTerm  <- toSC sym st concl
         obligation <- scImplies sc hypTerm conclTerm
         let defaultMd = MS.ConditionMetadata
                         { MS.conditionLoc = loc
                         , MS.conditionTags = mempty
                         , MS.conditionType = "safety assertion"
                         , MS.conditionContext = ""
                         }
         let md = fromMaybe defaultMd $
                    do ann <- W4.getAnnotation sym concl
                       Map.lookup ann finalMdMap
         return (Crucible.simErrorReasonMsg err, md, obligation)

    matchResult opts sc =
      case (mspec ^. MS.csRet, ret, mspec ^. MS.csRetValue) of

        -- Non-unit function:
        --
        -- mir_return has *already* checked that the user-specified SetupValue
        -- has the correct *type* for the function’s return.
        --
        -- What mir_return does NOT check is whether the *actual* value produced
        -- by symbolic execution matches what the spec requested.
        --
        -- This branch enforces that semantic obligation: it compares the
        -- symbolic execution result `r` (a MIRVal) against the spec’s expected
        -- value `expect` using matchArg, generating the equality constraints
        -- needed in the post-state.
        (Just _, Just r, Just expect) ->
          let md = MS.ConditionMetadata
                   { MS.conditionLoc     = mspec ^. MS.csLoc
                   , MS.conditionTags    = mempty
                   , MS.conditionType    = "return value matching"
                   , MS.conditionContext = ""
                   }
          in
          matchArg opts sc cc mspec MS.PostState md r expect

        -- Unit-returning function:
        --
        -- There is no post-state obligation about the return value itself,
        -- because unit-returning functions do not produce a meaningful MIR
        -- return value. ret = Nothing always.
        --
        -- This branch exists solely to prevent valid unit cases (implicit or
        -- explicit mir_return ()) from falling into the failure case below.
        (Nothing, Nothing, _) ->
          pure ()

        -- Any other combination indicates a broken invariant in execMIRSetup
        -- or verifySimulate and should not occur for well-formed specs.
        _ ->
          panic "verifyPoststate (MIR)" ["inconsistent return/type information"]

-- | Evaluate the precondition part of a Crucible method spec:
--
-- * Allocate heap space for each 'mir_alloc' statement.
--
-- * Record an equality precondition for each 'mir_equal'
-- statement.
--
-- * Write to memory for each 'mir_points_to' statement. (Writes
-- to already-initialized locations are transformed into equality
-- preconditions.)
--
-- * Evaluate the function arguments from the 'mir_execute_func'
-- statement.
--
-- Returns a tuple of (arguments, preconditions, pointer values,
-- memory).
verifyPrestate ::
  MIRCrucibleContext ->
  MS.CrucibleMethodSpecIR MIR ->
  Crucible.SymGlobalState Sym ->
  IO ([(Mir.Ty, MIRVal)],
      [Crucible.LabeledPred Term AssumptionReason],
      Map MS.AllocIndex (Some (MirPointer Sym)),
      Crucible.SymGlobalState Sym)
verifyPrestate cc mspec globals0 =
  do let sym = cc^.mccSym
     let prestateLoc = W4.mkProgramLoc "_SAW_MIR_verifyPrestate" W4.InternalPos
     liftIO $ W4.setCurrentProgramLoc sym prestateLoc

     (env, globals1) <- runStateT
       (traverse
         (\alloc -> StateT (\globals -> doAlloc cc globals alloc))
         (mspec ^. MS.csPreState . MS.csAllocs))
       globals0

     globals2 <- setupPrePointsTos mspec cc env (mspec ^. MS.csPreState . MS.csPointsTos) globals1
     (globals3, cs) <-
       setupPrestateConditions mspec cc env globals2 (mspec ^. MS.csPreState . MS.csConditions)
     args <- resolveArguments cc mspec env



     return (args, cs, env, globals3)

-- | Simulate a MIR function with Crucible as part of a 'mir_verify' command,
-- making sure to install any overrides that the user supplies.
verifySimulate ::
  (?singleOverrideSpecialCase :: Bool) =>
  Options ->
  MIRCrucibleContext ->
  [Crucible.GenericExecutionFeature Sym] ->
  MethodSpec ->
  [(a, MIRVal)] ->
  [Crucible.LabeledPred Term AssumptionReason] ->
  W4.ProgramLoc ->
  [Lemma] ->
  Crucible.SymGlobalState Sym ->
  Bool {- ^ path sat checking -} ->
  IORef MetadataMap {- ^ metadata map -} ->
  IO (Maybe MIRVal, Crucible.SymGlobalState Sym)
verifySimulate opts cc pfs mspec args assumes top_loc lemmas globals checkSat mdMap =
  mccWithBackend cc $ \bak ->
  do let rm = cc^.mccRustModule
     let cs = rm ^. Mir.rmCS
     let col = cs ^. Mir.collection
     let method = mspec ^. MS.csMethod
     let verbosity = simVerbose opts
     let simctx = cc^.mccSimContext

     when (verbosity > 2) $
          putStrLn "starting executeCrucibleMIR"

     -- Find and run the target function
     Crucible.AnyCFG methodCfg <- lookupDefIdCFG rm method
     let methodHndl = Crucible.cfgHandle methodCfg
     let methodArgTys = Crucible.handleArgTypes methodHndl
     let methodRetTy = Crucible.handleReturnType methodHndl

     pathSatFeature <-
       Crucible.pathSatisfiabilityFeature (cc ^. mccSym)
         (Crucible.considerSatisfiability bak)

     regmap <- prepareArgs methodArgTys (map snd args)
     (_, Crucible.GlobalPair retval globals1) <-
       do let feats = if checkSat then pathSatFeature : pfs else pfs
          let fnCall = Crucible.regValue <$> Crucible.callCFG methodCfg regmap
          let overrideSim =
                do mapM_ (registerOverride opts cc simctx top_loc mdMap)
                           (neGroupOn (view MS.csMethod) (map (view MS.psSpec) lemmas))
                   liftIO $
                     for_ assumes $ \(Crucible.LabeledPred p (md, reason)) ->
                       do expr <- resolveSAWPred cc p
                          let loc = MS.conditionLoc md
                          Crucible.addAssumption bak (Crucible.GenericAssumption loc reason expr)
                   fnCall
          runCrucible opts simctx globals (map Crucible.genericToExecutionFeature feats)
                      methodRetTy overrideSim

     let ret_ty = mspec ^. MS.csRet
     retval' <-
       case ret_ty of
         Nothing -> return Nothing
         Just ret_mt ->
           case retval of
             Crucible.RegEntry ty val ->
               case decodeMIRVal col ret_mt (Crucible.AnyValue ty val) of
                 Nothing -> error $ "FIXME: Unsupported return type: " ++ show ret_ty
                 Just v -> return (Just v)
     return (retval', globals1)

  where
    prepareArg :: forall tp. Crucible.TypeRepr tp -> MIRVal -> IO (Crucible.RegValue Sym tp)
    prepareArg ty (MIRVal vTy vVal) =
      case testEquality ty (shapeType vTy) of
        Just Refl -> pure vVal
        Nothing   -> fail $ unlines
          [ "argument type mismatch"
          , show ty
          , show (shapeType vTy)
          ]

    prepareArgs ::
      forall xs.
      Ctx.Assignment Crucible.TypeRepr xs ->
      [MIRVal] ->
      IO (Crucible.RegMap Sym xs)
    prepareArgs ctx xs | length xs /= Ctx.sizeInt (Ctx.size ctx) =
      fail $ "Wrong number of arguments: found " ++ show (length xs) ++ ", expected " ++ show (Ctx.sizeInt (Ctx.size ctx))
    prepareArgs ctx xs =
      Crucible.RegMap <$>
      Ctx.traverseWithIndex (\idx tr ->
        do v <- prepareArg tr (xs !! Ctx.indexVal idx)
           return (Crucible.RegEntry tr v))
      ctx

--------------------------------------------------------------------------------
-- Internal MIR identifiers
--------------------------------------------------------------------------------

globalAllocId :: Text
globalAllocId = "alloc::alloc::Global"

vecId :: Text
vecId = "alloc::vec::Vec"

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- | Returns the Cryptol type of a MIR type, returning 'Nothing' if it is not
-- easily expressible in Cryptol's type system or if it is not currently
-- supported.
cryptolTypeOfActual :: Mir.Ty -> Maybe Cryptol.Type
cryptolTypeOfActual mty =
  case mty of
    Mir.TyBool      -> Just Cryptol.tBit
    Mir.TyChar      -> Just $ Cryptol.tWord $ Cryptol.tNum (32 :: Integer)
    Mir.TyUint bs   -> baseSizeType bs
    Mir.TyInt  bs   -> baseSizeType bs
    Mir.TyArray t n -> Cryptol.tSeq (Cryptol.tNum n) <$> cryptolTypeOfActual t
    Mir.TyTuple tys -> Cryptol.tTuple <$> traverse cryptolTypeOfActual tys

    Mir.TyFloat _      -> Nothing
    Mir.TyStr          -> Nothing
    Mir.TyAdt _ _ _    -> Nothing
    Mir.TyRef _ _      -> Nothing
    Mir.TyFnDef _      -> Nothing
    Mir.TyFnPtr _      -> Nothing
    Mir.TyRawPtr _ _   -> Nothing
    Mir.TyClosure _    -> Nothing
    Mir.TySlice _      -> Nothing
    Mir.TyDowncast _ _ -> Nothing
    Mir.TyNever        -> Nothing
    Mir.TyForeign      -> Nothing
    Mir.TyLifetime     -> Nothing
    Mir.TyConst _      -> Nothing
    Mir.TyErased       -> Nothing
    Mir.TyInterned _   -> Nothing
    Mir.TyDynamic _    -> Nothing
    Mir.TyCoroutine {} -> Nothing
    Mir.TyCoroutineClosure _ -> Nothing
  where
    baseSizeType :: Mir.BaseSize -> Maybe Cryptol.Type
    baseSizeType Mir.B8    = Just $ Cryptol.tWord $ Cryptol.tNum (8 :: Integer)
    baseSizeType Mir.B16   = Just $ Cryptol.tWord $ Cryptol.tNum (16 :: Integer)
    baseSizeType Mir.B32   = Just $ Cryptol.tWord $ Cryptol.tNum (32 :: Integer)
    baseSizeType Mir.B64   = Just $ Cryptol.tWord $ Cryptol.tNum (64 :: Integer)
    baseSizeType Mir.B128  = Just $ Cryptol.tWord $ Cryptol.tNum (128 :: Integer)
    baseSizeType Mir.USize = Just $ Cryptol.tWord $ Cryptol.tNum $ natValue $ knownNat @Mir.SizeBits

-- | Extract a SAWCore term from a @crucible-mir@ CFG.
extractFromMirCFG ::
  Options ->
  SharedContext ->
  MIRCrucibleContext ->
  -- | The CFG's MIR argument types.
  [Mir.Ty] ->
  -- | The CFG's MIR return type.
  Mir.Ty ->
  Crucible.AnyCFG MIR ->
  IO TypedTerm
extractFromMirCFG opts sc cc argTys retTy (Crucible.AnyCFG cfg) =
  do let h = Crucible.cfgHandle cfg
     (ecs, args) <- setupArgs sc cc argTys h
     let simCtx  = cc^.mccSimContext
     let globals = cc^.mccSymGlobalState
     res <- runCFG simCtx globals h cfg args
     case res of
       Crucible.FinishedResult _ pr ->
         do gp <- getGlobalPair opts pr
            let regv = gp^.Crucible.gpValue
                rt = Crucible.regType regv
                rv = Crucible.regValue regv
            cty <-
              case cryptolTypeOfActual retTy of
                Just cty -> pure cty
                Nothing ->
                  fail $ unwords
                    [ "Unsupported type for Crucible extraction:"
                    , show (PP.pretty retTy)
                    ]
            term <- setupResultTerm sc cc retTy rt rv
            let tt = TypedTerm (TypedTermSchema (Cryptol.tMono cty)) term
            tt' <- abstractTypedVars sc (toList ecs) tt
            pure tt'
       Crucible.AbortedResult _ ar ->
         do let resultDoc = ppMIRAbortedResult ar
            fail $ unlines [ "Symbolic execution failed."
                           , show resultDoc
                           ]

       Crucible.TimeoutResult _ ->
         fail "Symbolic execution timed out."

-- Find the ADT definition that is monomorphized from `origName` with `substs`.
-- This should only be used on types that are known to be present in the crate
-- after dead code elimination - for example, because the type appears in the
-- signature of a function that's being translated.
findAdt :: Mir.Collection -> Mir.DefId -> Mir.Substs -> TopLevel Mir.Adt
findAdt col origName substs =
    case List.find (\adt -> adt ^. Mir.adtOrigSubsts == substs) insts of
        Just x -> return x
        Nothing -> fail $ "Unknown ADT: " ++ show (origName, substs)
  where
    insts = col ^. Mir.adtsOrig . at origName . to (fromMaybe [])

findFnInstance :: MonadFail m => Mir.Collection -> Mir.DefId -> Mir.Substs -> m Text
findFnInstance col origName substs =
  case found of
    Just i -> pure (Mir.idText i)
    Nothing
      | hasInstances -> fail ("Could not find function instance: " ++ show (Mir.cleanVariantName origName))
      | origName `Map.member` (col ^. Mir.functions) -> pure (Mir.idText origName)
      | otherwise -> fail ("Could not find function " ++ show (Mir.cleanVariantName origName))
  where
  (hasInstances, found) = foldr check (False, Nothing) (col ^. Mir.intrinsics)
  check i (hasIs, rest) =
    let inst = i ^. Mir.intrInst
    in case inst ^. Mir.inKind of
          Mir.IkItem
            | inst ^. Mir.inDefId == origName ->
              (True, if inst ^. Mir.inSubsts == substs
                       then Just (i ^. Mir.intrName)
                       else rest)
          _ -> (hasIs, rest)



-- | Find the ADT definition corresponding to a mangled identifier (i.e., an
-- identifier for an ADT that is already instantiated with type arguments). See
-- 'findAdt' for a variant of this function that looks up non-mangled
-- identifiers.
findAdtMangled :: Mir.Collection -> Mir.DefId -> TopLevel Mir.Adt
findAdtMangled col name =
  case col ^. Mir.adts . at name of
    Just x -> return x
    Nothing -> fail $ "Unknown ADT: " ++ show name

-- | Find the 'Mir.Fn' corresponding to the given function name (supplied as a
-- 'String'). If none can be found or if there are multiple functions
-- corresponding to that name (see the Haddocks for 'findDefId'), then this will
-- fail.
findFn :: Mir.RustModule -> Text -> TopLevel Mir.Fn
findFn rm nm = do
  let cs = rm ^. Mir.rmCS
      col = cs ^. Mir.collection
  did <- findDefId cs nm
  case Map.lookup did (col ^. Mir.functions) of
      Just x -> return x
      Nothing -> fail $ Text.unpack $ "Couldn't find MIR function named: " <> nm

-- | Given a full enum variant identifier (e.g.,
-- @core::option[0]::Option[0]::Some[0]@, retrieve the part of the identifier
-- that corresponds to the variant's shorthand name (e.g., @Some@).
getEnumVariantShortName :: Mir.Variant -> Text
getEnumVariantShortName variant
  | Just (_, (variantNm, _)) <- List.unsnoc (variant ^. Mir.vname . Mir.didPath)
  = variantNm

  | otherwise
  = panic "getEnumVariantShortName" [
        "Malformed enum variant identifier: " <> Text.pack (show $ variant ^. Mir.vname)
    ]

getMIRCrucibleContext :: CrucibleSetup MIR MIRCrucibleContext
getMIRCrucibleContext = view Setup.csCrucibleContext <$> get

-- | Look up the control-flow graph (CFG) for a 'Mir.DefId', failing if a CFG
-- cannot be found.
lookupDefIdCFG ::
     MonadFail m
  => Mir.RustModule
  -> Mir.DefId
  -> m (Crucible.AnyCFG MIR)
lookupDefIdCFG rm method =
  case Map.lookup (Mir.idText method) (rm ^. Mir.rmCFGs) of
    Just x -> return x
    Nothing -> fail $ "Couldn't find CFG for MIR function: " ++ show method

-- | Some boilerplate code needed to invoke 'Crucible.executeCrucible' and
-- extract the results.
runCrucible ::
  Crucible.IsSyntaxExtension ext =>
  Options ->
  Crucible.SimContext p Sym ext ->
  Crucible.SymGlobalState Sym ->
  [Crucible.ExecutionFeature p Sym ext (Crucible.RegEntry Sym a)] ->
  Crucible.TypeRepr a ->
  Crucible.OverrideSim p Sym ext (Crucible.RegEntry Sym a) Crucible.EmptyCtx a (Crucible.RegValue Sym a) ->
  IO (Crucible.SimContext p Sym ext, Crucible.GlobalPair Sym (Crucible.RegEntry Sym a))
runCrucible opts simCtx globals execFeatures ovRetTpr ovSim = do
  let initExecState =
        Crucible.InitialState simCtx globals Crucible.defaultAbortHandler ovRetTpr $
        Crucible.runOverrideSim ovRetTpr ovSim
  res <- Crucible.executeCrucible execFeatures initExecState
  case res of
    Crucible.FinishedResult simctx pr -> do
      gp <- getGlobalPair opts pr
      return (simctx, gp)

    Crucible.AbortedResult _ ar -> do
      let resultDoc = ppMIRAbortedResult ar
      fail $ unlines [ "Symbolic execution failed."
                     , show resultDoc
                     ]

    Crucible.TimeoutResult _cxt ->
      fail "Symbolic execution timed out."

-- | Create a fresh argument variable of the appropriate type, suitable for use
-- in an extracted function derived from @mir_extract@.
setupArg ::
  forall tp.
  SharedContext ->
  MIRCrucibleContext ->
  IORef (Seq TypedVariable) ->
  -- | The argument's MIR type.
  Mir.Ty ->
  -- | The argument's corresponding Crucible type.
  Crucible.TypeRepr tp ->
  IO (Crucible.RegEntry Sym tp)
setupArg sc cc ecRef mty0 tp0 =
  mccWithBackend cc $ \bak -> do
    let sym = backendGetSym bak
    let rm = cc ^. mccRustModule
    let cs = rm ^. Mir.rmCS
    let col = cs ^. Mir.collection

    let -- Throw a user-facing error message if a MIR type is not supported
        -- for extraction.
        unsupportedType :: forall a. Mir.Ty -> IO a
        unsupportedType ty =
          fail $ unwords
            [ "Unsupported type for Crucible extraction:"
            , show (PP.pretty ty)
            ]

    let -- Given a TypeShape, compute the corresponding Cryptol type
        -- (Cryptol.Type) and SAWCore type (Term). If the TypeShape is
        -- unsupported for extraction, throw an error message.
        typeShapeToSAWTypes ::
          forall tp'.
          TypeShape tp' ->
          IO (Cryptol.Type, Term)
        typeShapeToSAWTypes shp =
          case shp of
            TupleShape _ elems -> do
              (eltCtys, eltScTps) <-
                mapAndUnzipM
                  (\(AgElemShape _ _ shp') -> typeShapeToSAWTypes shp')
                  elems
              scTp <- scTupleType sc eltScTps
              pure (Cryptol.tTuple eltCtys, scTp)
            PrimShape {} ->
              typeReprToSAWTypes sym sc (shapeType shp)
            ArrayShape mty _ _ eltShp _ -> do
              arraySz <-
                case mty of
                  Mir.TyArray _ arraySz -> pure arraySz
                  _ -> panic
                         "setupArg"
                         [ "ArrayShape with non-TyArray type:"
                         , Text.pack $ show $ PP.pretty mty
                         ]
              (eltCty, eltScTp) <- typeShapeToSAWTypes eltShp
              arraySzTerm <- scNat sc $ fromIntegral @Int @Natural arraySz
              let cty = Cryptol.tSeq (Cryptol.tNum (toInteger @Int arraySz)) eltCty
              scTp <- scVecType sc arraySzTerm eltScTp
              pure (cty, scTp)

            StructShape mty _ _ ->
              unsupportedType mty
            EnumShape mty _ _ _ _ ->
              unsupportedType mty
            TransparentShape mty _ ->
              unsupportedType mty
            RefShape mty _ _ _ ->
              unsupportedType mty
            SliceShape mty _ _ _ ->
              unsupportedType mty
            FnPtrShape mty _ _ ->
              unsupportedType mty

    let -- Panic if we encounter an unsupported type that should have been
        -- caught earlier by typeShapeToSAWTypes.
        impossibleType :: forall a. Term -> IO a
        impossibleType ty = do
          ty' <- ppTerm sc PPS.defaultOpts ty
          panic
            "setupArg"
            [ "Type that should have been rejected by typeShapeToSAWTypes:"
            , Text.pack ty'
            ]

    let -- Convert a fresh SAWCore term to a MIR-related Crucible.RegValue,
        -- binding fresh What4 constants as needed and associating them to the
        -- corresponding SAWCore subterms.
        termToMirRegValue ::
          forall tp'.
          -- | The TypeShape of the SAWCore term.
          TypeShape tp' ->
          -- | The corresponding SAWCore type.
          Term ->
          -- | The SAWCore term.
          Term ->
          IO (Crucible.RegValue Sym tp')
        termToMirRegValue shp scTp t =
          case shp of
            TupleShape _ elems -> do
              eltScTps <-
                case asTupleType scTp of
                  Just eltScTps -> pure eltScTps
                  Nothing -> do
                    scTp' <- ppTerm sc PPS.defaultOpts scTp
                    panic
                      "setupArg"
                      [ "TupleShape with non-tuple type:"
                      , Text.pack $ scTp'
                      ]
              let tupleSz = length elems
              buildMirAggregate sym elems (zip [0..] eltScTps) $
                \_off _sz shp' (idx, eltScTp) -> do
                  let oneBasedIdx = idx + 1
                  t' <- scTupleSelector sc t oneBasedIdx tupleSz
                  termToMirRegValue shp' eltScTp t'
            PrimShape {} ->
              termToRegValue sym (shapeType shp) t
            ArrayShape _ _ eltSz eltShp len -> do
              (arraySz :*: eltScTp) <-
                case asVecType scTp of
                  Just nt -> pure nt
                  Nothing -> do
                    scTp' <- ppTerm sc PPS.defaultOpts scTp
                    panic
                      "setupArg"
                      [ "ArrayShape with non-Vec type:"
                      , Text.pack scTp'
                      ]
              arraySzTerm <- scNat sc arraySz
              generateMirAggregateArray sym eltSz eltShp len $
                \idx -> do
                  idxTerm <- scNat sc $ fromIntegral @Word @Natural idx
                  t' <- scAt sc arraySzTerm eltScTp t idxTerm
                  termToMirRegValue eltShp eltScTp t'

            StructShape {} ->
              impossibleType scTp
            EnumShape {} ->
              impossibleType scTp
            TransparentShape {} ->
              impossibleType scTp
            RefShape {} ->
              impossibleType scTp
            SliceShape {} ->
              impossibleType scTp
            FnPtrShape {} ->
              impossibleType scTp

    let shp = tyToShapeEq col mty0 tp0
    (cty, scTp) <- typeShapeToSAWTypes shp

    ecs <- readIORef ecRef
    vn <- scFreshVarName sc ("arg_" <> Text.pack (show (length ecs)))
    writeIORef ecRef (ecs Seq.|> TypedVariable cty vn scTp)

    t <- scVariable sc vn scTp
    Crucible.RegEntry tp0 <$> termToMirRegValue shp scTp t

-- | Create fresh argument variables of the appropriate types, suitable for use
-- in an extracted function derived from @mir_extract@.
setupArgs ::
  SharedContext ->
  MIRCrucibleContext ->
  -- | The extracted function's MIR argument types. Precondition: this should
  -- be the same length as the number of argument types in the
  -- 'Crucible.FnHandle'.
  [Mir.Ty] ->
  Crucible.FnHandle init ret ->
  IO (Seq TypedVariable, Crucible.RegMap Sym init)
setupArgs sc cc mirArgTys fn =
  do ecRef  <- newIORef Seq.empty
     let fnArgTys = Crucible.handleArgTypes fn
     let mirArgTysVec = V.fromList mirArgTys
     let mirArgTysCtx =
           Ctx.generate (Ctx.size fnArgTys) $ \idx ->
             -- This is in bounds because of the precondition on `mirArgTys`.
             Const (mirArgTysVec V.! Ctx.indexVal idx)
     regmap <-
       Crucible.RegMap <$>
       Ctx.zipWithM (\(Const mty) -> setupArg sc cc ecRef mty) mirArgTysCtx fnArgTys
     ecs    <- readIORef ecRef
     return (ecs, regmap)

setupCrucibleContext :: Mir.RustModule -> TopLevel MIRCrucibleContext
setupCrucibleContext rm =
  do halloc <- getHandleAlloc
     sc <- getSharedContext
     pathSatSolver <- gets rwPathSatSolver
     sym <- io $ newSAWCoreExprBuilder sc False
     timeout <- gets rwCrucibleTimeout
     someBak@(SomeOnlineBackend bak) <- io $
           newSAWCoreBackendWithTimeout pathSatSolver sym timeout
     let cs     = rm ^. Mir.rmCS
     let col    = cs ^. Mir.collection
     let cfgMap = rm ^. Mir.rmCFGs
     opts <- getOptions
     io $ do let cfg = W4.getConfiguration sym
             verbSetting <- W4.getOptionSetting W4.verbosity cfg
             _ <- W4.setOpt verbSetting $ toInteger $ simVerbose opts
             return ()

     -- TODO! there's a lot of options setup we need to replicate
     --  from SAWCentral.Crucible.LLVM.Builtins

     -- There is quite a bit of faff below, all for the sake of translating
     -- top-level static values. See Note [Translating MIR statics in SAW] for
     -- a high-level description of what this code is doing.
     Crucible.AnyCFG staticInitCfg <-
       withImplicitParams opts $ io $ Mir.transStatics cs halloc
     let staticInitHndl   = Crucible.cfgHandle staticInitCfg
     let staticInitArgTys = Crucible.handleArgTypes staticInitHndl
     let staticInitRetTy  = Crucible.handleReturnType staticInitHndl
     Refl <- case testEquality staticInitArgTys Ctx.Empty of
       Just e ->
         pure e
       Nothing ->
         panic "setupCrucibleContext" [
             "static initializer should not require arguments; found:",
             "   " <> Text.pack (show staticInitArgTys)
         ]

     Refl <- case testEquality staticInitRetTy Crucible.UnitRepr of
       Just e ->
         pure e
       Nothing ->
         panic "setupCrucibleContext" [
             "static initializer should return ():",
             Text.pack (show staticInitRetTy)
         ]

     let bindings = Crucible.fnBindingsFromList $
                    map (\(Crucible.AnyCFG cfg) ->
                          Crucible.FnBinding
                            (Crucible.cfgHandle cfg)
                            (Crucible.UseCFG cfg (Crucible.postdomInfo cfg))) $
                    Map.elems cfgMap
     let simctx0 = Crucible.initSimContext bak
                     intrinsics halloc stdout
                     bindings Mir.mirExtImpl
                     SAWCruciblePersonality
     let globals0 = Crucible.emptyGlobals
     let setupGlobals = Crucible.regValue <$> Crucible.callCFG staticInitCfg Crucible.emptyRegMap
     -- Step (1) in Note [Translating MIR statics in SAW]
     (simctx1, gp) <- io $ runCrucible opts simctx0 globals0 [] Crucible.UnitRepr setupGlobals
     let globalsAllStatics = gp ^. Crucible.gpGlobals
     -- Step (2) in Note [Translating MIR statics in SAW]
     let (globalsImmutStaticsOnly, staticInitializerPairs) =
           mapAccumL
             (\globals (staticDefId, Mir.StaticVar gv) ->
               let static =
                     case Map.lookup staticDefId (col ^. Mir.statics) of
                       Just static' ->
                         static'
                       Nothing ->
                         panic "setupCrucibleContext" [
                             "staticDefId not in statics map: " <>
                                 Text.pack (show staticDefId)
                         ]
               in
               case Crucible.lookupGlobal gv globalsAllStatics of
                 Just rv ->
                   let pair = MapF.Pair gv (Crucible.RV rv) in
                   if static ^. Mir.sMutable
                     then (globals, pair)
                     else (Crucible.insertGlobal gv rv globals, pair)
                 Nothing ->
                   panic "setupCrucibleContext" [
                       "Static GlobalVar not in SymGlobalState: " <> Text.pack (show gv)
                   ]
             )
             globals0
             (cs ^. Mir.staticMap . to Map.toList)
     let staticInitializerMap = MapF.fromList staticInitializerPairs

     return MIRCrucibleContext { _mccRustModule = rm
                               , _mccBackend = someBak
                               , _mccSimContext = simctx1
                               , _mccSymGlobalState = globalsImmutStaticsOnly
                               , _mccStaticInitializerMap = staticInitializerMap
                               , _mccUninterp = mempty
                               }

-- | Create a result value of the appropriate type, suitable for use in an
-- extracted function derived from @mir_extract@.
setupResultTerm ::
  SharedContext ->
  MIRCrucibleContext ->
  -- | The result's MIR type.
  Mir.Ty ->
  -- | The result's corresponding Crucible type.
  Crucible.TypeRepr tp ->
  Crucible.RegValue Sym tp ->
  IO Term
setupResultTerm sc cc mty0 tpr0 val0 =
  mccWithBackend cc $ \bak -> do
    let sym = backendGetSym bak
    let rm = cc ^. mccRustModule
    let cs = rm ^. Mir.rmCS
    let col = cs ^. Mir.collection

    let unsupportedType :: forall a. Mir.Ty -> IO a
        unsupportedType ty =
          fail $ unwords
            [ "Unsupported type for Crucible extraction:"
            , show (PP.pretty ty)
            ]

    let go ::
          forall tp'.
          Mir.Ty ->
          Crucible.TypeRepr tp' ->
          Crucible.RegValue Sym tp' ->
          IO Term
        go mty tpr val =
          let shp = tyToShapeEq col mty tpr in
          case shp of
            TupleShape _ elems -> do
              tys <-
                case mty of
                  Mir.TyTuple tys -> pure tys
                  _ -> panic
                         "setupResultTerm"
                         [ "TupleShape with non-TyTuple type:"
                         , Text.pack $ show $ PP.pretty mty
                         ]
              terms <- accessMirAggregate' sym elems tys val $
                  \_off _sz shp' val' tval' -> go tval' (shapeType shp') val'
              scTupleReduced sc terms
            PrimShape {} -> do
              st <- sawCoreState sym
              toSC sym st val
            ArrayShape _ _ eltSz eltShp len -> do
              eltTy <-
                case mty of
                  Mir.TyArray eltTy _ -> pure eltTy
                  _ -> panic
                         "setupResultTerm"
                         [ "ArrayShape with non-TyArray type:"
                         , Text.pack $ show $ PP.pretty mty
                         ]
              eltTypeTerm <- shapeToTerm sc eltShp
              typedElts <- accessMirAggregateArray sym eltSz eltShp len val $
                  \_off val' -> go eltTy (shapeType eltShp) val'
              scVectorReduced sc eltTypeTerm typedElts

            StructShape {} ->
              unsupportedType mty
            EnumShape {} ->
              unsupportedType mty
            TransparentShape {} ->
              unsupportedType mty
            RefShape {} ->
              unsupportedType mty
            SliceShape {} ->
              unsupportedType mty
            FnPtrShape {} ->
              unsupportedType mty

    go mty0 tpr0 val0

{-
Note [Translating MIR statics in SAW]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Translating top-level static values in the SAW MIR backend requires some care.
This is because we want to treat immutable and mutable static differently:

* Immutable statics should be implicitly initialized in each specification
  without any action required on the user's end.

* Mutable statics should /not/ be initialized in a specification unless a user
  explicitly declares it with `mir_points_to (mir_static ...) ...`. This is
  because a mutable static's value can change over the course of a program, so
  we require users to be precise about what the value should be before and after
  invoking a function.

This poses a challenge when translating static values in SAW. It is tempting to
only translate the immutable statics and not the mutable statics (similarly to
how the SAW LLVM backend handles translation), but this will not work in
general. Consider this program:

  static mut S1: u32 = 1;
  static S2: u32 = unsafe { S1 };

  pub fn f() {
      ... S2 ...
  }

The initial value of S2 (an immutable static) depends on having first translated
the initial value of S1 (a mutable static). If we do not translate mutable
statics in SAW, the translation of S1 will not succeed.

We solve this problem by doing the following:

1. Use Crucible to translate all top-level static values (both immutable and
   mutable). This produces a SymGlobalState that contains every static's
   initializer value.

2. Consult the updated SymGlobalState to produce the following:

   (a) A subset of the SymGlobalState that only contains the initializer values
       for the immutable statics. This will be used later to initialize the
       Crucible state when translating the function being verified with
       mir_verify.

   (b) A MirStaticInitializerMap mapping all static variables (both immutable
       and mutable) to their initializer values. This will be used later to
       power the mir_static_initializer function.

This is a bit clunky, but it's unclear how to do better without significantly
changing how crucible-mir translates top-level static values.
-}

-- | Define several commonly used implicit parameters in @crucible-mir@ and
-- call a continuation with these parameters.
withImplicitParams ::
  Options ->
  ( ( ?debug :: Int, ?customOps :: Mir.CustomOpMap
    , ?assertFalseOnError :: Bool, ?printCrucible :: Bool
    ) => r) ->
  r
withImplicitParams opts k =
  let ?debug = simVerbose opts in
      -- For now, we use the same default settings for implicit parameters as in
      -- crux-mir. We may want to add options later that allow configuring these.
  let ?assertFalseOnError = True in
  let ?customOps          = customOps in
  let ?printCrucible      = False in
  k

--------------------------------------------------------------------------------
-- Errors
--------------------------------------------------------------------------------

data MIRSetupError
  = MIRFreshVarInvalidType Mir.Ty
  | MIRFreshExpandedValueUnsupportedType Mir.Ty
  | MIRArgTypeMismatch Int Mir.Ty Mir.Ty -- argument position, expected, found
  | MIRArgNumberWrong Int Int -- number expected, number found
  | MIRReturnUnexpected Mir.Ty -- found
  | MIRReturnTypeMismatch Mir.Ty Mir.Ty -- expected, found
  | MIRReturnMissing Mir.Ty -- expected
  | MIREnumValueVariantNotFound Mir.DefId Text
  | MIREnumValueNonEnum Mir.DefId String -- The String is either \"struct\" or \"union\"
  | MIRVecOfContentsNotArray Mir.Ty
  | MIRVecOfTypeMismatch
      Mir.Ty -- ^ type passed as the second argument
      Mir.Ty -- ^ element type of the contents argument
  | MIRVecOfElemTyNotSized Mir.Ty
  | MIRVecOfElemTyNoLayoutInfo Mir.Ty
  | MIRExecuteMissing

instance X.Exception MIRSetupError where
  toException = topLevelExceptionToException
  fromException = topLevelExceptionFromException

instance Show MIRSetupError where
  show err =
    case err of
      MIRFreshVarInvalidType jty ->
        "mir_fresh_var: Invalid type: " ++ show jty
      MIRFreshExpandedValueUnsupportedType ty ->
        "mir_fresh_expanded_value: " ++ show (PP.pretty ty) ++
        " not supported"
      MIRArgTypeMismatch i expected found ->
        unlines
        [ "mir_execute_func: Argument type mismatch"
        , "Argument position: " ++ show i
        , "Expected type: " ++ show (PP.pretty expected)
        , "Given type:    " ++ show (PP.pretty found)
        ]
      MIRArgNumberWrong expected found ->
        unlines
        [ "mir_execute_func: Wrong number of arguments"
        , "Expected: " ++ show expected
        , "Given:    " ++ show found
        ]
      MIRReturnUnexpected found ->
        unlines
        [ "mir_return: Unexpected return value for void method"
        , "Given type: " ++ show (PP.pretty found)
        ]
      MIRReturnTypeMismatch expected found ->
        unlines
        [ "mir_return: Return type mismatch"
        , "Expected type: " ++ show (PP.pretty expected)
        , "Given type:    " ++ show (PP.pretty found)
        ]
      MIRReturnMissing expected ->
        unlines
        [ "mir_return: Missing return value specification"
        , "Expected type: " ++ show (PP.pretty expected)
        ]
      MIREnumValueVariantNotFound adtNm variantNm ->
        unlines
        [ "mir_enum_value: Could not find a variant named `" ++ Text.unpack variantNm ++ "`"
        , "in the enum " ++ show adtNm
        ]
      MIREnumValueNonEnum adtNm what ->
        unlines
        [ "mir_enum_value: Expected enum, received " ++ what
        , show adtNm
        ]
      MIRVecOfContentsNotArray contentsTy ->
        "mir_vec_of: Expected array MIRValue as third argument, but got "
          ++ show (PP.pretty contentsTy)
      MIRVecOfTypeMismatch passedElemTy contentsElemTy ->
        unlines
        [ "mir_vec_of: Type mismatch between passed type and element type of contents array"
        , "Passed type: " ++ show (PP.pretty passedElemTy)
        , "Element type of contents array: " ++ show (PP.pretty contentsElemTy)
        ]
      MIRVecOfElemTyNotSized elemTy ->
        "mir_vec_of: Cannot construct Vec of unsized element type "
          ++ show (PP.pretty elemTy)
      MIRVecOfElemTyNoLayoutInfo elemTy ->
        "mir_vec_of: No layout info for element type "
          ++ show (PP.pretty elemTy)
      MIRExecuteMissing ->
        "MIRSetup: Missing mir_execute_func specification"
