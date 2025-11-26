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
  , rawTerm
  , scTypeOf
  , scTypeConvertible
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
import Data.Text (Text)
import Numeric.Natural (Natural)

import SAWCore.Name
import SAWCore.Recognizer
import SAWCore.SharedTerm (SharedContext, scSubtype)
import qualified SAWCore.SharedTerm as Raw
import SAWCore.Term.Functor

--------------------------------------------------------------------------------
-- * Certified typed terms

-- | An abstract datatype containing a well-formed 'Raw.Term'.
data Term = Term Raw.Term

-- | The raw term of a 'Term'.
rawTerm :: Term -> Raw.Term
rawTerm (Term trm) = trm

--------------------------------------------------------------------------------

-- | Check if two terms are "convertible for type-checking", meaning that they
-- are convertible up to 'natConversions'.
scTypeConvertible :: SharedContext -> Raw.Term -> Raw.Term -> IO Bool
scTypeConvertible sc t1 t2 = Raw.scConvertibleEval sc Raw.scWhnf True t1 t2

--------------------------------------------------------------------------------
-- * Operations on typed terms

-- | Compute the type of a 'Term'.
scTypeOf :: SharedContext -> Term -> IO Term
scTypeOf sc (Term tm) = Term <$> Raw.scTypeOf sc tm

-- | Reduce a 'Cterm' to weak head-normal form..
scWhnf :: SharedContext -> Term -> IO Term
scWhnf sc (Term tm) = Term <$> Raw.scWhnf sc tm

scGlobal :: SharedContext -> Ident -> IO Term
scGlobal sc ident = Term <$> Raw.scGlobalDef sc ident

--------------------------------------------------------------------------------
-- * Building certified terms

-- possible errors: not a pi type, bad argument type, context mismatch
scApply :: SharedContext -> Term -> Term -> IO Term
scApply sc f arg = Term <$> Raw.scApply sc (rawTerm f) (rawTerm arg)

-- possible errors: not a type, context mismatch, variable free in context
scLambda :: SharedContext -> VarName -> Term -> Term -> IO Term
scLambda sc x t body = Term <$> Raw.scLambda sc x (rawTerm t) (rawTerm body)

-- possible errors: not a variable, context mismatch, variable free in context
scAbstract :: SharedContext -> Term -> Term -> IO Term
scAbstract sc var body =
  case asVariable (rawTerm var) of
    Nothing -> fail "scAbstract: Not a variable"
    Just (x, ty) -> Term <$> Raw.scLambda sc x ty (rawTerm body)

-- possible errors: not a type, context mismatch, variable free in context
scPi :: SharedContext -> VarName -> Term -> Term -> IO Term
scPi sc x t body = Term <$> Raw.scPi sc x (rawTerm t) (rawTerm body)

scGeneralize :: SharedContext -> Term -> Term -> IO Term
scGeneralize sc var body =
  case asVariable (rawTerm var) of
    Nothing -> fail "scGeneralize: Not a variable"
    Just (x, ty) -> scPi sc x (Term ty) body

-- possible errors: not a type, context mismatch
scFun :: SharedContext -> Term -> Term -> IO Term
scFun sc a b = Term <$> Raw.scFun sc (rawTerm a) (rawTerm b)

-- possible errors: constant not defined
scConstant :: SharedContext -> Name -> IO Term
scConstant sc nm = Term <$> Raw.scConst sc nm

-- possible errors: not a type
scVariable :: SharedContext -> VarName -> Term -> IO Term
scVariable sc vn t = Term <$> Raw.scVariable sc vn (rawTerm t)

-- possible errors: none
scUnitValue :: SharedContext -> IO Term
scUnitValue sc = Term <$> Raw.scUnitValue sc

-- possible errors: none
scUnitType :: SharedContext -> IO Term
scUnitType sc = Term <$> Raw.scUnitType sc

-- possible errors: none (could redesign to require types in sort 0)
scPairValue :: SharedContext -> Term -> Term -> IO Term
scPairValue sc x y = Term <$> Raw.scPairValue sc (rawTerm x) (rawTerm y)

-- possible errors: not a type
scPairType :: SharedContext -> Term -> Term -> IO Term
scPairType sc x y = Term <$> Raw.scPairType sc (rawTerm x) (rawTerm y)

-- possible errors: not a pair
scPairLeft :: SharedContext -> Term -> IO Term
scPairLeft sc x = Term <$> Raw.scPairLeft sc (rawTerm x)

-- possible errors: not a pair
scPairRight :: SharedContext -> Term -> IO Term
scPairRight sc x = Term <$> Raw.scPairRight sc (rawTerm x)

-- possible errors: not a datatype, bad elimination sort
scRecursor :: SharedContext -> Name -> Sort -> IO Term
scRecursor sc nm s = Term <$> Raw.scRecursor sc nm s

-- possible errors: field not a type, context mismatch
scRecordType :: SharedContext -> [(FieldName, Term)] -> IO Term
scRecordType sc fields = Term <$> Raw.scRecordType sc (map (fmap rawTerm) fields)

-- possible errors: duplicate field name
scRecordValue :: SharedContext -> [(FieldName, Term)] -> IO Term
scRecordValue sc fields = Term <$> Raw.scRecord sc (fmap rawTerm (Map.fromList fields))

-- possible errors: not a record type, field name not found
scRecordProj :: SharedContext -> Term -> FieldName -> IO Term
scRecordProj sc t fname = Term <$> Raw.scRecordSelect sc (rawTerm t) fname

-- no possible errors
scSort :: SharedContext -> Sort -> IO Term
scSort sc s = scSortWithFlags sc s noFlags

-- | A variant of 'scSort' that also takes a 'SortFlags' argument.
-- No possible errors.
scSortWithFlags :: SharedContext -> Sort -> SortFlags -> IO Term
scSortWithFlags sc s flags = Term <$> Raw.scSortWithFlags sc s flags

-- no possible errors
scNat :: SharedContext -> Natural -> IO Term
scNat sc n = Term <$> Raw.scNat sc n

-- possible errors: context mismatch, element type not a type, element wrong type
scVector :: SharedContext -> Term -> [Term] -> IO Term
scVector sc e xs = Term <$> Raw.scVector sc (rawTerm e) (map rawTerm xs)

-- no possible errors
scString :: SharedContext -> Text -> IO Term
scString sc s = Term <$> Raw.scString sc s
