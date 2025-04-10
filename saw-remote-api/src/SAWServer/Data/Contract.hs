{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module SAWServer.Data.Contract
  ( ContractMode(..)
  , Contract(..)
  , ContractVar(..)
  , Allocated(..)
  , GhostValue(..)
  , PointsTo(..)
  , PointsToBitfield(..)
  ) where

import Control.Applicative
import Data.Aeson (FromJSON(..), withObject, withText, (.:), (.:?), (.!=))
import Data.Text (Text)

import SAWScript.Crucible.Common.Setup.Builtins (CheckPointsToType(..))

import SAWServer
import SAWServer.Data.SetupValue ()

-- | How to use a contract: as a verification goal or an assumption.
data ContractMode
  = VerifyContract
  | AssumeContract

data Contract ty cryptolExpr =
  Contract
    { preVars       :: [ContractVar ty]
    , preConds      :: [cryptolExpr]
    , preAllocated  :: [Allocated ty]
    , preGhostValues  :: [GhostValue cryptolExpr]
    , prePointsTos  :: [PointsTo ty cryptolExpr]
    , prePointsToBitfields :: [PointsToBitfield ty cryptolExpr]
    , argumentVals  :: [CrucibleSetupVal ty cryptolExpr]
    , postVars      :: [ContractVar ty]
    , postConds     :: [cryptolExpr]
    , postAllocated :: [Allocated ty]
    , postGhostValues :: [GhostValue cryptolExpr]
    , postPointsTos :: [PointsTo ty cryptolExpr]
    , postPointsToBitfields :: [PointsToBitfield ty cryptolExpr]
    , returnVal     :: Maybe (CrucibleSetupVal ty cryptolExpr)
    }
    deriving stock (Functor, Foldable, Traversable)

data ContractVar ty =
  ContractVar
    { contractVarServerName :: ServerName
    , contractVarName       :: Text
    , contractVarType       :: ty
    }

data Allocated ty =
  Allocated
    { allocatedServerName :: ServerName
    , allocatedType       :: ty
    , allocatedMutable    :: Bool
    , allocatedAlignment  :: Maybe Int
    }

data PointsTo ty cryptolExpr =
  PointsTo
    { pointer           :: CrucibleSetupVal ty cryptolExpr
    , pointsTo          :: CrucibleSetupVal ty cryptolExpr
    , checkPointsToType :: Maybe (CheckPointsToType ty)
    , condition         :: Maybe cryptolExpr
    } deriving stock (Functor, Foldable, Traversable)

data PointsToBitfield ty cryptolExpr =
  PointsToBitfield
    { bfPointer   :: CrucibleSetupVal ty cryptolExpr
    , bfFieldName :: Text
    , bfPointsTo  :: CrucibleSetupVal ty cryptolExpr
    } deriving stock (Functor, Foldable, Traversable)

data CheckAgainstTag
  = TagCheckAgainstPointerType
  | TagCheckAgainstCastedType


data GhostValue cryptolExpr =
  GhostValue
    { ghostVarName :: ServerName
    , ghostValue   :: cryptolExpr
    } deriving stock (Functor, Foldable, Traversable)

instance (FromJSON ty, FromJSON cryptolExpr) => FromJSON (PointsTo ty cryptolExpr) where
  parseJSON =
    withObject "Points-to relationship" $ \o ->
      PointsTo <$> o .:  "pointer"
               <*> o .:  "points to"
               <*> o .:? "check points to type"
               <*> o .:? "condition"

instance (FromJSON ty, FromJSON cryptolExpr) => FromJSON (PointsToBitfield ty cryptolExpr) where
  parseJSON =
    withObject "Points-to-bitfield relationship" $ \o ->
      PointsToBitfield <$> o .: "pointer"
                       <*> o .: "field name"
                       <*> o .: "points to"

instance FromJSON cryptolExpr => FromJSON (GhostValue cryptolExpr) where
  parseJSON =
    withObject "ghost variable value" $ \o ->
      GhostValue <$> o .: "server name"
                 <*> o .: "value"

instance FromJSON ty => FromJSON (Allocated ty) where
  parseJSON =
    withObject "allocated thing" $ \o ->
      Allocated <$> o .:  "server name"
                <*> o .:  "type"
                <*> o .:  "mutable"
                <*> o .:? "alignment"

instance FromJSON ty => FromJSON (ContractVar ty) where
  parseJSON =
    withObject "contract variable" $ \o ->
      ContractVar <$> o .: "server name"
                  <*> o .: "name"
                  <*> o .: "type"

instance (FromJSON ty, FromJSON e) => FromJSON (Contract ty e) where
  parseJSON =
    withObject "contract" $ \o ->
    Contract <$> o .:  "pre vars"
             <*> o .:  "pre conds"
             <*> o .:  "pre allocated"
             <*> o .:? "pre ghost values" .!= []
             <*> o .:  "pre points tos"
             <*> o .:? "pre points to bitfields" .!= []
             <*> o .:  "argument vals"
             <*> o .:  "post vars"
             <*> o .:  "post conds"
             <*> o .:  "post allocated"
             <*> o .:? "post ghost values" .!= []
             <*> o .:  "post points tos"
             <*> o .:? "post points to bitfields" .!= []
             <*> o .:? "return val"

instance FromJSON CheckAgainstTag where
  parseJSON =
    withText "`check points to type` tag" $
    \case
      "pointer type" -> pure TagCheckAgainstPointerType
      "casted type"  -> pure TagCheckAgainstCastedType
      _ -> empty

instance FromJSON ty => FromJSON (CheckPointsToType ty) where
  parseJSON =
    withObject "check points to type" $ \o ->
      o .: "check against" >>=
      \case
        TagCheckAgainstPointerType -> pure CheckAgainstPointerType
        TagCheckAgainstCastedType  -> CheckAgainstCastedType <$> o .: "type"
