
module SAWScript.TypeCheck where

import Control.Applicative
import Control.Monad.State

data Module a = Module
  { declarations :: [TopStmt a]
  , main         :: [BlockStmt a]
  }
  deriving (Eq,Show)

data TopStmt a
  = Import      Name               (Maybe [Name])   (Maybe Name)
  | TypeDef     Name               a
  | TopTypeDecl Name               a
  | TopLet      [(Name,Expr a)]
  deriving (Eq,Show)

data BlockStmt a
  = Bind          (Maybe Name)     (Expr a)
  | BlockTypeDecl Name             a
  | BlockLet      [(Name,Expr a)]
  deriving (Eq,Show)

data Expr a
  -- Constants
  = Bit         Bool                          a
  | Quote       String                        a
  | Z           Integer                       a
  -- Structures
  | Array       [Expr a]                      a
  | Block       [BlockStmt a]                 a
  | Tuple       [Expr a]                      a
  | Record      [(Name, Expr a)]              a
  -- Accessors
  | Index       (Expr a)           (Expr a)   a
  | Lookup      (Expr a)           Name       a
  -- LC
  | Var         Name                          a
  | Function    Name a             (Expr a)   a
  | Application (Expr a)           (Expr a)   a
  -- Sugar
  | LetBlock    [(Name,Expr a)]    (Expr a)
  deriving (Eq,Show)

data TypeF f
  -- Constants
  = Bit'
  | Z'
  | Quote'
  -- Structures
  | Array'       (Mu TypeF f)          Int
  | Block'       Context               (Mu TypeF f)
  | Tuple'       [Mu TypeF f]

data Context

type Name = String
type Mu t f = f (t f)

