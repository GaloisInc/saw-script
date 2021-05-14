{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- |
Module      : Verifier.SAW.TypedAST
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.TypedAST
 ( -- * Module operations.
   Module
 , emptyModule
 , ModuleName, mkModuleName
 , moduleName
 , preludeName
 , ModuleMap
 , ModuleDecl(..)
 , moduleDecls
 , allModuleDecls
 , moduleDataTypes
 , moduleImports
 , findDataType
 , findDataTypeInMap
 , moduleCtors
 , findCtor
 , findCtorInMap
 , moduleDefs
 , allModuleDefs
 , findDef
 , insImport
 , insDataType
 , insDef
 , moduleActualDefs
 , allModuleActualDefs
 , modulePrimitives
 , allModulePrimitives
 , moduleAxioms
 , allModuleAxioms
   -- * Data types and definitions.
 , DataType(..)
 , dtPrimName
 , Ctor(..)
 , ctorNumParams
 , ctorPrimName
 , CtorArg(..)
 , Def(..)
 , DefQualifier(..)
   -- * Terms and associated operations.
 , incVarsSimpleTerm
 , piArgCount
 , TermF(..)
 , FlatTermF(..)
 , unwrapTermF
 , zipWithFlatTermF
 , freesTermF
 , termToPat
 , CompiledRecursor(..)

 , PPOpts(..)
 , defaultPPOpts
 , ppTerm
 , ppTermDepth
 , showTerm
 , scPrettyTerm
 , scPrettyTermInCtx
   -- * Primitive types.
 , Sort, mkSort, propSort, sortOf, maxSort
 , Ident(..), identName, mkIdent
 , NameInfo(..), toShortName, toAbsoluteName
 , parseIdent
 , isIdent
 , DeBruijnIndex
 , FieldName
 , LocalName
 , ExtCns(..)
 , PrimName(..)
 , VarIndex
   -- * Utility functions
  , BitSet, emptyBitSet, inBitSet, unionBitSets, intersectBitSets
  , decrBitSet, completeBitSet
 ) where

import Control.Exception (assert)

import Prelude hiding (all, foldr)

import Verifier.SAW.Module
import Verifier.SAW.Term.Functor
import Verifier.SAW.Term.Pretty

-- | Returns the number of nested pi expressions.
piArgCount :: Term -> Int
piArgCount = go 0
  where go i t = case unwrapTermF t of
          Pi _ _ rhs -> go (i+1) rhs
          _          -> i

-- | @instantiateVars f l t@ substitutes each dangling bound variable
-- @LocalVar j t@ with the term @f i j t@, where @i@ is the number of
-- binders surrounding @LocalVar j t@.
instantiateVars :: (DeBruijnIndex -> DeBruijnIndex -> Term)
                -> DeBruijnIndex -> Term -> Term
instantiateVars f initialLevel = go initialLevel
  where go :: DeBruijnIndex -> Term -> Term
        go l (unwrapTermF -> tf) =
          case tf of
            FTermF ftf      -> Unshared $ FTermF $ fmap (go l) ftf
            App x y         -> Unshared $ App (go l x) (go l y)
            Constant{}      -> Unshared tf -- assume rhs is a closed term, so leave it unchanged
            Lambda i tp rhs -> Unshared $ Lambda i (go l tp) (go (l+1) rhs)
            Pi i lhs rhs    -> Unshared $ Pi i (go l lhs) (go (l+1) rhs)
            LocalVar i
              | i < l -> Unshared $ LocalVar i
              | otherwise -> f l i

-- | @incVars j k t@ increments free variables at least @j@ by @k@.
-- e.g., incVars 1 2 (C ?0 ?1) = C ?0 ?3
incVarsSimpleTerm :: DeBruijnIndex -> DeBruijnIndex -> Term -> Term
incVarsSimpleTerm _ 0 = id
incVarsSimpleTerm initialLevel j = assert (j > 0) $ instantiateVars fn initialLevel
  where fn _ i = Unshared $ LocalVar (i+j)
