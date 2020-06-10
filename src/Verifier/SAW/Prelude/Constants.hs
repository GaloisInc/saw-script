{- |
Module      : Verifier.SAW.Prelude.Constants
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Prelude.Constants where

import Verifier.SAW.Term.Functor

preludeModuleName :: ModuleName
preludeModuleName = mkModuleName ["Prelude"]

preludeNatIdent :: Ident
preludeNatIdent =  mkIdent preludeModuleName "Nat"

preludeNatType :: FlatTermF e
preludeNatType =  DataTypeApp preludeNatIdent [] []

preludeZeroIdent :: Ident
preludeZeroIdent =  mkIdent preludeModuleName "Zero"

preludeSuccIdent :: Ident
preludeSuccIdent =  mkIdent preludeModuleName "Succ"

preludeIntegerIdent :: Ident
preludeIntegerIdent =  mkIdent preludeModuleName "Integer"

preludeIntegerType :: FlatTermF e
preludeIntegerType = GlobalDef preludeIntegerIdent

preludeVecIdent :: Ident
preludeVecIdent =  mkIdent preludeModuleName "Vec"

preludeVecTypeFun :: FlatTermF e
preludeVecTypeFun = GlobalDef preludeVecIdent

preludeFloatIdent :: Ident
preludeFloatIdent =  mkIdent preludeModuleName "Float"

preludeFloatType :: FlatTermF e
preludeFloatType = GlobalDef preludeFloatIdent

preludeDoubleIdent :: Ident
preludeDoubleIdent =  mkIdent preludeModuleName "Double"

preludeDoubleType :: FlatTermF e
preludeDoubleType = GlobalDef preludeDoubleIdent

preludeStringIdent :: Ident
preludeStringIdent =  mkIdent preludeModuleName "String"

preludeStringType :: FlatTermF e
preludeStringType = GlobalDef preludeStringIdent

preludeArrayIdent :: Ident
preludeArrayIdent =  mkIdent preludeModuleName "Array"

preludeArrayTypeFun :: FlatTermF e
preludeArrayTypeFun = GlobalDef preludeArrayIdent
