module Verifier.SAW.TypedAST where

import Verifier.SAW.Position

type Ident = String

data Term
  = IntLit Pos Integer
  | Ident Pos Ident
  | 

data Term = 