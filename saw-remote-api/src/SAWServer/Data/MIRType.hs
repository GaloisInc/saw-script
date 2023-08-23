{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module SAWServer.Data.MIRType (JSONMIRType, mirType) where

import Control.Applicative
import qualified Data.Aeson as JSON
import Data.Aeson (withObject, withText, (.:))

import Mir.Mir (BaseSize(..), FloatKind(..), Ty(..))

data MIRTypeTag
  = TagArray
  | TagBool
  | TagI8
  | TagI16
  | TagI32
  | TagI64
  | TagI128
  | TagIsize
  | TagF32
  | TagF64
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
      "array" -> pure TagArray
      "bool" -> pure TagBool
      "i8" -> pure TagI8
      "i16" -> pure TagI16
      "i32" -> pure TagI32
      "i64" -> pure TagI64
      "i128" -> pure TagI128
      "isize" -> pure TagIsize
      "f32" -> pure TagF32
      "f64" -> pure TagF64
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

newtype JSONMIRType = JSONMIRType { getMIRType :: Ty }

instance JSON.FromJSON JSONMIRType where
  parseJSON =
    primType

    where
      primType =
        withObject "MIR type" $ \o -> fmap JSONMIRType $
        o .: "type" >>=
        \case
          TagArray -> TyArray <$> (getMIRType <$> o .: "element type") <*> o .: "size"
          TagBool -> pure TyBool
          TagI8 -> pure $ TyInt B8
          TagI16 -> pure $ TyInt B16
          TagI32 -> pure $ TyInt B32
          TagI64 -> pure $ TyInt B64
          TagI128 -> pure $ TyInt B128
          TagIsize -> pure $ TyInt USize
          TagF32 -> pure $ TyFloat F32
          TagF64 -> pure $ TyFloat F64
          TagSlice -> TySlice <$> (getMIRType <$> o .: "slice type")
          TagStr -> pure TyStr
          TagTuple -> TyTuple <$> (fmap getMIRType <$> o .: "tuple types")
          TagU8 -> pure $ TyUint B8
          TagU16 -> pure $ TyUint B16
          TagU32 -> pure $ TyUint B32
          TagU64 -> pure $ TyUint B64
          TagU128 -> pure $ TyUint B128
          TagUsize -> pure $ TyUint USize

mirType :: JSONMIRType -> Ty
mirType = getMIRType
