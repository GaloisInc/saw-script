{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

{- |
Module      : SAWCore.Prelude.Constants
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Prelude.Constants where

import SAWCore.Name

preludeModuleName :: ModuleName
preludeModuleName = mkModuleName ["Prelude"]

preludeNatQualName :: QualName
preludeNatQualName =  mkQualName preludeModuleName "Nat"

preludeZeroQualName :: QualName
preludeZeroQualName =  mkQualName preludeModuleName "Zero"

preludeSuccQualName :: QualName
preludeSuccQualName =  mkQualName preludeModuleName "Succ"

preludeIntegerQualName :: QualName
preludeIntegerQualName =  mkQualName preludeModuleName "Integer"

preludeVecQualName :: QualName
preludeVecQualName =  mkQualName preludeModuleName "Vec"

preludeFloatQualName :: QualName
preludeFloatQualName =  mkQualName preludeModuleName "Float"

preludeDoubleQualName :: QualName
preludeDoubleQualName =  mkQualName preludeModuleName "Double"

preludeStringQualName :: QualName
preludeStringQualName =  mkQualName preludeModuleName "String"

preludeArrayQualName :: QualName
preludeArrayQualName =  mkQualName preludeModuleName "Array"
