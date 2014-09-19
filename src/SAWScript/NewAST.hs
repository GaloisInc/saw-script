
module SAWScript.NewAST where

import qualified SAWScript.AST as A
import SAWScript.AST (Bind, LBind, Schema(..), Type(..), TyVar(..), LName, Located)
import SAWScript.Compiler

import Control.Applicative
import qualified Data.Map as M

-- Type Decls {{{

data Expr
  -- Constants
  = Bit Bool
  | String String
  | Z Integer
  | Undefined
  | Code (Located String)
  -- Structures
  | Array  [Expr]
  | Block  [BlockStmt]
  | Tuple  [Expr]
  | Record (M.Map Name Expr)
  -- Accessors
  | Index  Expr Expr
  | Lookup Expr Name
  | TLookup Expr Integer
  -- LC
  | Var (Located A.ResolvedName)
  | Function    LName (Maybe Type) Expr
  | Application Expr Expr
  -- Sugar
  | Let [LBind Expr] Expr
  | TSig Expr Schema
  deriving (Show)

data BlockStmt
  = Bind          (Maybe LName) (Maybe Type) (Maybe Type) Expr
  | BlockLet      [LBind Expr]
  | BlockCode     (Located String)
  deriving (Show)


type Name = String

-- }}}

-- Expr translation {{{

translateExpr :: A.Expr A.ResolvedName A.ResolvedT -> Err Expr
translateExpr expr = case expr of
  A.Bit b t              -> sig t $ (Bit b)
  A.Quote s t            -> sig t $ (String s)
  A.Z i t                -> sig t $ (Z i)
  A.Undefined t          -> sig t $ Undefined
  A.Code s t             -> sig t $ (Code s)
  A.Array es t           -> sig t =<< (Array <$> mapM translateExpr es)
  A.Block bs t           -> sig t =<< (Block <$> mapM translateBStmt bs)
  A.Tuple es t           -> sig t =<< (Tuple <$> mapM translateExpr es)
  A.Record fs t          -> sig t =<< (Record . M.fromList <$> mapM translateField fs)
  A.Index ar ix t        -> sig t =<< (Index <$> translateExpr ar <*> translateExpr ix)
  A.Lookup rec fld t     -> sig t =<< (Lookup <$> translateExpr rec <*> pure fld)
  A.TLookup tpl idx t    -> sig t =<< (TLookup <$> translateExpr tpl <*> pure idx)
  A.Var x t              -> sig t $ (Var x)
  A.Function x xt body t -> sig t =<< (Function x <$> translateMType xt <*> translateExpr body)
  A.Application f v t    -> sig t =<< (Application <$> translateExpr f <*> translateExpr v)
  A.LetBlock nes e       ->         Let <$> mapM translateField nes <*> translateExpr e
  where
  sig :: A.ResolvedT -> Expr -> Err Expr
  sig Nothing e = return e
  sig (Just t) e = TSig e <$> translateTypeS t

translateBStmt :: A.BlockStmt A.ResolvedName A.ResolvedT -> Err BlockStmt
translateBStmt bst = case bst of
  A.Bind Nothing       ctx e -> Bind Nothing Nothing <$> translateMType ctx <*> translateExpr e
  A.Bind (Just (n, t)) ctx e -> Bind (Just $ n) <$> translateMType t
                                <*> translateMType ctx <*> translateExpr e
  A.BlockLet bs   -> BlockLet <$> mapM translateField bs
  A.BlockCode s -> pure $ BlockCode s

translateField :: (a,A.Expr A.ResolvedName A.ResolvedT) -> Err (a,Expr)
translateField (n,e) = (,) <$> pure n <*> translateExpr e

translateTypeField :: (a,A.FullT) -> Err (a,Type)
translateTypeField (n,e) = (,) <$> pure n <*> translateType e

translateMTypeS :: A.ResolvedT -> Err Schema
translateMTypeS (Just t) = translateTypeS t
translateMTypeS Nothing  = fail "Cannot translate type of prim, received Nothing"

translateTypeS :: A.FullT -> Err Schema
translateTypeS s = return s

translateMType :: Maybe A.FullT -> Err (Maybe Type)
translateMType mt = case mt of
  Just t  -> translateType t >>= return . Just
  Nothing -> return Nothing

translateType :: A.FullT -> Err Type
translateType typ = do t' <- translateTypeS typ
                       case t' of
                         Forall [] t -> return t
                         s -> fail $ "can't translate schema to a monomorphic type: " ++ show s


importTypeS :: Schema -> Err Schema
importTypeS = return

-- }}}
