{- |
Module      : Verifier.SAW.Prelude.Constants
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

{-# LANGUAGE OverloadedStrings #-}

module Verifier.SAW.Prelude.Constants where

import Verifier.SAW.Term.Functor

preludeModuleName :: ModuleName
preludeModuleName = mkModuleName ["Prelude"]

preludeNatIdent :: Ident
preludeNatIdent =  mkIdent preludeModuleName "Nat"

preludeZeroIdent :: Ident
preludeZeroIdent =  mkIdent preludeModuleName "Zero"

preludeSuccIdent :: Ident
preludeSuccIdent =  mkIdent preludeModuleName "Succ"

preludeIntegerIdent :: Ident
preludeIntegerIdent =  mkIdent preludeModuleName "Integer"

preludeVecIdent :: Ident
preludeVecIdent =  mkIdent preludeModuleName "Vec"

preludeFloatIdent :: Ident
preludeFloatIdent =  mkIdent preludeModuleName "Float"

preludeDoubleIdent :: Ident
preludeDoubleIdent =  mkIdent preludeModuleName "Double"

preludeStringIdent :: Ident
preludeStringIdent =  mkIdent preludeModuleName "String"

preludeArrayIdent :: Ident
preludeArrayIdent =  mkIdent preludeModuleName "Array"
