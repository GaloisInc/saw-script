module Verifier.SAW.TypedAST
 ( Ident
 , AST.ParamType(..)
 , Builtin(..)
 , LambdaVar
 , TermF(..)
 , Term(..)
 ) where

import Verifier.SAW.Lexer (Parser)

import qualified Verifier.SAW.UntypedAST as AST

import Data.Map (Map)
import qualified Data.Map as Map

type Ident = String

type ParamType = AST.ParamType

data Builtin
  = TypeType

  | BoolType
  | TrueCtor
  | FalseCtor
  | IteFn
  | AssertFn
  | TrueProp
  | AtomicProof
  | FalseProp

  | EqClass
  | EqFn
  | BoolEqInstance

  | OrdClass
  | LeqFn
  | LtFn
  | GeqFn
  | GtFn
  | BoolOrdInstance

  | NumClass
  | NegFn
  | AddFn
  | SubFn
  | MulFn
  | DivFn
  | RemFn

  | BitsClass
  | NotFn
  | AndFn
  | OrFn
  | XorFn
  | ImpliesFn
  | ShlFn
  | ShrFn

  | IntegerType
  | IntegerEqInstance
  | IntegerOrdInstance
  | IntegerNumInstance
  | IntegerBitsInstance
  
  | ArrayType
  | ArrayEqInstance
  | ArrayOrdInstance
  | ArrayBitsInstance
  | GetFn
  | SetFn
  | GenerateFn
  
  | SignedType
  | UnsignedType
  | SignedEqInstance
  | SignedOrdInstance
  | SignedNumInstance
  | UnsignedEqInstance
  | UnsignedOrdInstance
  | UnsignedNumInstance

  | SignedToInteger
  | UnsignedToInteger
  | IntegerToSigned
  | IntegerToUnsigned

  | SignedToArray
  | UnsignedToArray
  | ArrayToSigned
  | ArrayToUnsigned
  deriving (Eq, Ord)

type LambdaVar e = (ParamType, Ident, e)


-- The TermF representation requires that record and field expressions contain
-- the arguments to the record and a term for applying the field to.  Both of
-- these decisions were made so that terms have a well-specified type, and we do
-- not need to be concerned about record subtyping.

data TermF e
  = BuiltinLit Builtin
  | IntegerLit Integer
  | LocalVar Integer   -- ^ Local variables are referenced by deBrujin index.
  | GlobalVar Integer  -- ^ Global variables are referenced by deBrujin level.
  | App e e
  | Lambda (LambdaVar e) e
  | Tuple Integer
  | Record (Map String e)
  | FieldOf e String 
  deriving (Eq,Ord)

data Term = Term (TermF Term)

infer :: AST.Expr -> Parser Term
infer _ = undefined