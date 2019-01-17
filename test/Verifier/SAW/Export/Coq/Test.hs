{- |
Module      : Verifier.SAW.Export.Coq.Test
Copyright   : Galois, Inc. 2019
License     : BSD3
Maintainer  : val@galois.com
Stability   : experimental
Portability : portable
-}

module Verifier.SAW.Export.Coq.Test where

import Data.Map as Map
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Verifier.SAW.SharedTerm
import Verifier.SAW.Export.Coq

configuration :: ExportConfiguration
configuration = ExportConfiguration
  { exportVectorsAsCoqVectors = True
  , traverseConsts            = True
  }

-- Creating a bunch of terms with no sharing, for testing purposes

natOf :: Integer -> IO Term
natOf i = do
  sc <- mkSharedContext
  scNat sc (fromInteger i)

aVector :: IO Term
aVector = do
  sc   <- mkSharedContext
  typ  <- scNatType sc
  args <- mapM (natOf) [0, 1, 2]
  scVector sc typ args

aRecord :: IO Term
aRecord = do
  sc   <- mkSharedContext
  nat  <- natOf 2
  unit <- scUnitValue sc
  scRecord sc $ Map.fromList [("natField", nat), ("unitField", unit)]

aRecordType :: IO Term
aRecordType = do
  sc       <- mkSharedContext
  natType  <- scNatType  sc
  unitType <- scUnitType sc
  scRecordType sc [("natField", natType), ("unitField", unitType)]

export :: IO Term -> IO (Either (TranslationError Term) Doc)
export term = translateDefDocImports "MyDefinition" configuration <$> term
