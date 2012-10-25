module Verifier.SAW.TypedAST where

import Verifier.SAW.Lexer (Parser)

import Verifier.SAW.Position
import qualified Verifier.SAW.AST as AST

import Data.Map (Map)
import qualified Data.Map as Map

type Ident = String

type ParamType = AST.ParamType

type LambdaVar = (Pos, ParamType, Ident, Term)

data Term
  = IntLit Pos Integer
  | Ident Pos Ident
  | App Term Term
  | Tuple Integer            -- ^ @Tuple n@ is an n-tuple.
  | Record (Map String Term) -- ^ A structural record.
  | FieldOf Term String      -- ^ @FieldOf t nm@ is a reference to field nm in t@.
  | Lambda LambdaVar Term
  -- ^ Case statement;  We still need to investigate if case statements are
  -- appropriate, or should be desugared to something simpler.
  | Case Term [([LambdaVar],Term,Term)]

infer :: AST.Expr -> Parser Term
infer _ = undefined