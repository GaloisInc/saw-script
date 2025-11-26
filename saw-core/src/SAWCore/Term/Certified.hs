{- |
Module      : SAWCore.Term.Certified
Copyright   : Galois, Inc. 2025
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Term.Certified
  ( Term -- abstract
  , scTypeOf
  , scSubtype
  , scWhnf
    -- * Building certified terms
  , scApply
  , scLambda
  , scAbstract
  , scPi
  , scGeneralize
  , scFun
  , scConstant
  , scGlobal
  , scVariable
  , scUnitValue
  , scUnitType
  , scPairValue
  , scPairType
  , scPairLeft
  , scPairRight
  , scRecursor
  , scRecordType
  , scRecordValue
  , scRecordProj
  , scSort
  , scSortWithFlags
  , scNat
  , scVector
  , scString
  ) where

import qualified Data.Map as Map

import SAWCore.Name
import SAWCore.SharedTerm
import SAWCore.Term.Functor

scGlobal :: SharedContext -> Ident -> IO Term
scGlobal sc ident = scGlobalDef sc ident

-- possible errors: not a variable, context mismatch, variable free in context
scAbstract :: SharedContext -> Term -> Term -> IO Term
scAbstract sc var body = scAbstractTerms sc [var] body

scGeneralize :: SharedContext -> Term -> Term -> IO Term
scGeneralize sc var body = scGeneralizeTerms sc [var] body

-- possible errors: constant not defined
scConstant :: SharedContext -> Name -> IO Term
scConstant = scConst

-- possible errors: duplicate field name
scRecordValue :: SharedContext -> [(FieldName, Term)] -> IO Term
scRecordValue sc fields = scRecord sc (Map.fromList fields)

-- possible errors: not a record type, field name not found
scRecordProj :: SharedContext -> Term -> FieldName -> IO Term
scRecordProj sc t fname = scRecordSelect sc t fname
