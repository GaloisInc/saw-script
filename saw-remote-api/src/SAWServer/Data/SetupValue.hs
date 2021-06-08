{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module SAWServer.Data.SetupValue (CrucibleSetupVal) where

import Control.Applicative
import Data.Aeson (FromJSON(..), withObject, withText, (.:))

import SAWServer

data SetupValTag
  = TagNamedValue
  | TagNullValue
  | TagCryptol
  | TagArrayValue
  | TagTupleValue
  | TagFieldLValue
  | TagElemLValue
  | TagGlobalInit
  | TagGlobalLValue

instance FromJSON SetupValTag where
  parseJSON =
    withText "tag for setup value" $
    \case
      "named" -> pure TagNamedValue
      "null" -> pure TagNullValue
      "Cryptol" -> pure TagCryptol
      "array" -> pure TagArrayValue
      "tuple" -> pure TagTupleValue
      "field" -> pure TagFieldLValue
      "element lvalue" -> pure TagElemLValue
      "global initializer" -> pure TagGlobalInit
      "global lvalue" -> pure TagGlobalLValue
      _ -> empty

instance FromJSON cryptolExpr => FromJSON (CrucibleSetupVal cryptolExpr) where
  parseJSON v = fromObject v
    where
      fromObject = withObject "saved value or Cryptol expression" $ \o ->
        o .: "setup value" >>=
        \case
          TagNamedValue -> NamedValue <$> o .: "name"
          TagNullValue -> pure NullValue
          TagCryptol -> CryptolExpr <$> o .: "expression"
          TagArrayValue -> ArrayValue <$> o .: "elements"
          TagTupleValue -> TupleValue <$> o .: "elements"
          TagFieldLValue -> FieldLValue <$> o .: "base" <*> o .: "field"
          TagElemLValue -> ElementLValue <$> o .: "base" <*> o .: "index"
          TagGlobalInit -> GlobalInitializer <$> o .: "name"
          TagGlobalLValue -> GlobalLValue <$> o .: "name"
