{-# LANGUAGE OverloadedStrings #-}
module SAWServer.Term (JSONModuleName(..)) where

import Control.Applicative ( Alternative((<|>)) )
import Data.Aeson as JSON
    ( withArray, withText, FromJSON(parseJSON), ToJSON(toJSON) )
import qualified Data.Text as T
import qualified Data.Vector as V

import Verifier.SAW.Term.Functor ( mkModuleName, ModuleName )

newtype JSONModuleName = JSONModuleName ModuleName

instance FromJSON JSONModuleName where
  parseJSON val = literal val <|> structured val
    where
      literal =
        withText "module name as string" $
        pure . JSONModuleName . mkModuleName . T.splitOn "."
      structured =
        withArray "module name as list of parts" $ \v ->
        do parts <- traverse parseJSON (V.toList v)
           pure $ JSONModuleName $ mkModuleName parts

instance ToJSON JSONModuleName where
  toJSON (JSONModuleName n) = toJSON (show n)
