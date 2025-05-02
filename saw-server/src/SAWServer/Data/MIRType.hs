{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module SAWServer.Data.MIRType (JSONMIRType, mirType) where

import Control.Applicative
import qualified Control.Exception as X
import Control.Lens ((^.))
import qualified Data.Aeson as JSON
import Data.Aeson (withObject, withText, (.:))

import qualified Mir.Mir as Mir

-- XXX why are we importing what's theoretically the top-level interface from inside?
import SAWServer.SAWServer (SAWEnv, ServerName, getMIRAdtEither)

data MIRTypeTag
  = TagAdt
  | TagArray
  | TagBool
  | TagChar
  | TagI8
  | TagI16
  | TagI32
  | TagI64
  | TagI128
  | TagIsize
  | TagF32
  | TagF64
  | TagLifetime
  | TagRef
  | TagRefMut
  | TagSlice
  | TagStr
  | TagTuple
  | TagU8
  | TagU16
  | TagU32
  | TagU64
  | TagU128
  | TagUsize

instance JSON.FromJSON MIRTypeTag where
  parseJSON =
    withText "MIR type tag" $
    \case
      "adt" -> pure TagAdt
      "array" -> pure TagArray
      "bool" -> pure TagBool
      "char" -> pure TagChar
      "i8" -> pure TagI8
      "i16" -> pure TagI16
      "i32" -> pure TagI32
      "i64" -> pure TagI64
      "i128" -> pure TagI128
      "isize" -> pure TagIsize
      "f32" -> pure TagF32
      "f64" -> pure TagF64
      "lifetime" -> pure TagLifetime
      "ref" -> pure TagRef
      "ref mut" -> pure TagRefMut
      "slice" -> pure TagSlice
      "str" -> pure TagStr
      "tuple" -> pure TagTuple
      "u8" -> pure TagU8
      "u16" -> pure TagU16
      "u32" -> pure TagU32
      "u64" -> pure TagU64
      "u128" -> pure TagU128
      "usize" -> pure TagUsize
      _ -> empty

-- | This is like 'Mir.Ty', but with the following differences:
--
-- 1. This only contains the subset of MIR types that are currently supported
--    by the SAW remote API.
--
-- 2. 'JSONTyAdt' only contains a 'ServerName' that points points to an
--    'Mir.Adt', as opposed to 'Mir.TyAdt', which contains a full 'Mir.Adt'.
--    The advantage of only containing a 'Mir.TyAdt' is that we do not have to
--    represent the entirety of a 'Mir.Adt' definition in JSON each time we want
--    to reference the ADT in a type.
data JSONMIRType
  = JSONTyAdt !ServerName
  | JSONTyArray !JSONMIRType !Int
  | JSONTyBool
  | JSONTyChar
  | JSONTyFloat !Mir.FloatKind
  | JSONTyInt !Mir.BaseSize
  | JSONTyLifetime
  | JSONTyRef !JSONMIRType !Mir.Mutability
  | JSONTySlice !JSONMIRType
  | JSONTyStr
  | JSONTyTuple ![JSONMIRType]
  | JSONTyUint !Mir.BaseSize

instance JSON.FromJSON JSONMIRType where
  parseJSON =
    primType

    where
      primType =
        withObject "MIR type" $ \o ->
        o .: "type" >>=
        \case
          TagAdt -> JSONTyAdt <$> o .: "ADT server name"
          TagArray -> JSONTyArray <$> o .: "element type" <*> o .: "size"
          TagBool -> pure JSONTyBool
          TagChar -> pure JSONTyChar
          TagI8 -> pure $ JSONTyInt Mir.B8
          TagI16 -> pure $ JSONTyInt Mir.B16
          TagI32 -> pure $ JSONTyInt Mir.B32
          TagI64 -> pure $ JSONTyInt Mir.B64
          TagI128 -> pure $ JSONTyInt Mir.B128
          TagIsize -> pure $ JSONTyInt Mir.USize
          TagF32 -> pure $ JSONTyFloat Mir.F32
          TagF64 -> pure $ JSONTyFloat Mir.F64
          TagLifetime -> pure JSONTyLifetime
          TagRef -> JSONTyRef <$> o .: "referent type" <*> pure Mir.Immut
          TagRefMut -> JSONTyRef <$> o .: "referent type" <*> pure Mir.Mut
          TagSlice -> JSONTySlice <$> o .: "slice type"
          TagStr -> pure JSONTyStr
          TagTuple -> JSONTyTuple <$> o .: "tuple types"
          TagU8 -> pure $ JSONTyUint Mir.B8
          TagU16 -> pure $ JSONTyUint Mir.B16
          TagU32 -> pure $ JSONTyUint Mir.B32
          TagU64 -> pure $ JSONTyUint Mir.B64
          TagU128 -> pure $ JSONTyUint Mir.B128
          TagUsize -> pure $ JSONTyUint Mir.USize

-- | Convert a 'JSONMIRType' to a 'Mir.Ty'. The only interesting case is the
-- 'JSONTyAdt' case, which looks up a 'Mir.Adt' from a 'ServerName'.
mirType :: SAWEnv -> JSONMIRType -> Mir.Ty
mirType sawenv = go
  where
    go :: JSONMIRType -> Mir.Ty
    go (JSONTyAdt sn) =
      case getMIRAdtEither sawenv sn of
        Left ex -> X.throw ex
        Right adt ->
          Mir.TyAdt (adt ^. Mir.adtname)
                    (adt ^. Mir.adtOrigDefId)
                    (adt ^. Mir.adtOrigSubsts)

    go (JSONTyArray ty n) = Mir.TyArray (go ty) n
    go JSONTyBool = Mir.TyBool
    go JSONTyChar = Mir.TyChar
    go (JSONTyFloat fk) = Mir.TyFloat fk
    go (JSONTyInt bs) = Mir.TyInt bs
    go JSONTyLifetime = Mir.TyLifetime
    go (JSONTyRef ty mut) = Mir.TyRef (go ty) mut
    go (JSONTySlice ty) = Mir.TySlice (go ty)
    go JSONTyStr = Mir.TyStr
    go (JSONTyTuple ts) = Mir.TyTuple (map go ts)
    go (JSONTyUint bs) = Mir.TyUint bs
