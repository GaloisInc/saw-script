{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module SAWServer.Data.SetupValue (CrucibleSetupVal) where

import Control.Applicative
import Data.Aeson (FromJSON(..), withObject, withText, (.:), (.:?))

import SAWServer

data SetupValTag
  = TagNamedValue
  | TagNullValue
  | TagCryptol
  | TagArrayValue
  | TagStructValue
  | TagEnumValue
  | TagTupleValue
  | TagSliceValue
  | TagSliceRangeValue
  | TagStrSliceValue
  | TagStrSliceRangeValue
  | TagFieldLValue
  | TagCastLValue
  | TagUnionLValue
  | TagElemLValue
  | TagGlobalInit
  | TagGlobalLValue
  | TagFreshExpandedValue

instance FromJSON SetupValTag where
  parseJSON =
    withText "tag for setup value" $
    \case
      "named" -> pure TagNamedValue
      "null" -> pure TagNullValue
      "Cryptol" -> pure TagCryptol
      "array" -> pure TagArrayValue
      "struct" -> pure TagStructValue
      "enum" -> pure TagEnumValue
      "tuple" -> pure TagTupleValue
      "slice" -> pure TagSliceValue
      "slice range" -> pure TagSliceRangeValue
      "str slice" -> pure TagStrSliceValue
      "str slice range" -> pure TagStrSliceRangeValue
      "field" -> pure TagFieldLValue
      "cast"  -> pure TagCastLValue
      "union" -> pure TagUnionLValue
      "element lvalue" -> pure TagElemLValue
      "global initializer" -> pure TagGlobalInit
      "global lvalue" -> pure TagGlobalLValue
      "fresh expanded" -> pure TagFreshExpandedValue
      _ -> empty

instance (FromJSON ty, FromJSON cryptolExpr) => FromJSON (CrucibleSetupVal ty cryptolExpr) where
  parseJSON v = fromObject v
    where
      fromObject = withObject "saved value or Cryptol expression" $ \o ->
        o .: "setup value" >>=
        \case
          TagNamedValue -> NamedValue <$> o .: "name"
          TagNullValue -> pure NullValue
          TagCryptol -> CryptolExpr <$> o .: "expression"
          TagArrayValue -> ArrayValue <$> o .:? "element type" <*> o .: "elements"
          TagStructValue -> StructValue <$> o .:? "MIR ADT server name" <*> o .: "elements"
          TagEnumValue -> EnumValue <$> o .: "MIR ADT server name" <*> o .: "variant name" <*> o .: "elements"
          TagTupleValue -> TupleValue <$> o .: "elements"
          TagSliceValue -> SliceValue <$> o .: "base"
          TagSliceRangeValue -> SliceRangeValue <$> o .: "base" <*> o .: "start" <*> o .: "end"
          TagStrSliceValue -> StrSliceValue <$> o .: "base"
          TagStrSliceRangeValue -> StrSliceRangeValue <$> o .: "base" <*> o .: "start" <*> o .: "end"
          TagFieldLValue -> FieldLValue <$> o .: "base" <*> o .: "field"
          TagCastLValue -> CastLValue <$> o .: "base" <*> o .: "type"
          TagUnionLValue -> UnionLValue <$> o .: "base" <*> o .: "field"
          TagElemLValue -> ElementLValue <$> o .: "base" <*> o .: "index"
          TagGlobalInit -> GlobalInitializer <$> o .: "name"
          TagGlobalLValue -> GlobalLValue <$> o .: "name"
          TagFreshExpandedValue -> FreshExpandedValue <$> o .: "prefix" <*> o .: "type"
