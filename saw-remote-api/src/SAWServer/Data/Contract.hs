{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
module SAWServer.Data.Contract
  ( ContractMode(..)
  , Contract(..)
  , ContractVar(..)
  , Allocated(..)
  , PointsTo(..)
  ) where

import Data.Aeson (FromJSON(..), withObject, (.:))
import Data.Text

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
    , prePointsTos  :: [PointsTo cryptolExpr]
    , argumentVals  :: [CrucibleSetupVal cryptolExpr]
    , postVars      :: [ContractVar ty]
    , postConds     :: [cryptolExpr]
    , postAllocated :: [Allocated ty]
    , postPointsTos :: [PointsTo cryptolExpr]
    , returnVal     :: Maybe (CrucibleSetupVal cryptolExpr)
    }
    deriving (Functor, Foldable, Traversable)

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

data PointsTo cryptolExpr =
  PointsTo
    { pointer  :: CrucibleSetupVal cryptolExpr
    , pointsTo :: CrucibleSetupVal cryptolExpr
    } deriving (Functor, Foldable, Traversable)

instance FromJSON cryptolExpr => FromJSON (PointsTo cryptolExpr) where
  parseJSON =
    withObject "Points-to relationship" $ \o ->
      PointsTo <$> o .: "pointer"
               <*> o .: "points to"

instance FromJSON ty => FromJSON (Allocated ty) where
  parseJSON =
    withObject "allocated thing" $ \o ->
      Allocated <$> o .: "server name"
                <*> o .: "type"
                <*> o .: "mutable"
                <*> o .: "alignment"

instance FromJSON ty => FromJSON (ContractVar ty) where
  parseJSON =
    withObject "contract variable" $ \o ->
      ContractVar <$> o .: "server name"
                  <*> o .: "name"
                  <*> o .: "type"

instance (FromJSON ty, FromJSON e) => FromJSON (Contract ty e) where
  parseJSON =
    withObject "contract" $ \o ->
    Contract <$> o .: "pre vars"
             <*> o .: "pre conds"
             <*> o .: "pre allocated"
             <*> o .: "pre points tos"
             <*> o .: "argument vals"
             <*> o .: "post vars"
             <*> o .: "post conds"
             <*> o .: "post allocated"
             <*> o .: "post points tos"
             <*> o .: "return val"
