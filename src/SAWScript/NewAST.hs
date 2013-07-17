
module SAWScript.NewAST where

import qualified SAWScript.AST as A
import SAWScript.AST (Bind)

import qualified Data.Map as M

-- Type Decls {{{

data Expr
  -- Constants
  = Bit Bool
  | String String
  | Z Integer
  | Undefined
  -- Structures
  | Array  [Expr]
  | Block  [BlockStmt]
  | Tuple  [Expr]
  | Record (M.Map Name Expr)
  -- Accessors
  | Index  Expr Expr
  | Lookup Expr Name
  -- LC
  | Var A.ResolvedName
  | Function    Name (Maybe A.Type) Expr
  | Application Expr Expr
  -- Sugar
  | Let [Bind Expr] Expr
  | TSig Expr A.Schema
  deriving (Show)

data BlockStmt
  = Bind          (Maybe Name) (Maybe A.Type) (Maybe A.Type) Expr
  -- | BlockTypeDecl Name             typeT  
  | BlockLet      [Bind Expr]
  deriving (Show)


type Name = String

-- }}}
