
module SAWScript.NewAST where

import qualified SAWScript.AST as A
import SAWScript.AST (Bind)

import qualified Data.Map as M
import qualified Text.PrettyPrint.HughesPJ as PP

-- Type Decls {{{

data Expr
  -- Constants
  = Bit Bool
  | String String
  | Z Integer
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
  | Function    Name (Maybe Type) Expr
  | Application Expr Expr
  -- Sugar
  | Let [Bind Expr] Expr
  | TSig Expr Schema
  deriving (Show)

data BlockStmt
  = Bind          (Maybe Name) (Maybe Type) Expr
  -- | BlockTypeDecl Name             typeT  
  | BlockLet      [Bind Expr]
  deriving (Show)


type Name = String

data Type
  = TyCon TyCon [Type]
  | TyRecord (M.Map Name Type)
  | TyVar TyVar
 deriving (Eq,Show) 

data TyVar
  = FreeVar Integer
  | BoundVar Name
 deriving (Eq,Ord,Show) 

data TyCon
 = TupleCon Integer
 | ArrayCon
 | FunCon
 | StringCon
 | BoolCon
 | ZCon
 | NumCon Integer
 | BlockCon
 | ContextCon A.Context
 | AbstractCon String
 deriving (Eq,Show) 

data Schema = Forall [Name] Type deriving (Show)

-- }}}

-- Pretty Printing {{{

pShow :: PrettyPrint a => a -> String
pShow = show . pretty True

class PrettyPrint p where
  -- Bool indicates whether term should be parenthesized, eg. if rendering is space separated.
  pretty :: Bool -> p -> PP.Doc

instance PrettyPrint Schema where
  pretty _ (Forall ns t) = case ns of
    [] -> pretty False t
    _  -> PP.braces (commaSepAll $ map PP.text ns) PP.<+> pretty False t

instance PrettyPrint Type where
  pretty par t@(TyCon tc ts) = case (tc,ts) of
    (_,[])                 -> pretty par tc
    (TupleCon n,_)         -> PP.parens $ commaSepAll $ map (pretty False) ts
    (ArrayCon,[len,TyCon BoolCon []]) -> PP.brackets (pretty False len)
    (ArrayCon,[len,typ])   -> PP.brackets (pretty False len) PP.<> (pretty True typ)
    (FunCon,[f,v])         -> (if par then PP.parens else id) $
                                pretty False f PP.<+> PP.text "->" PP.<+> pretty False v
    (BlockCon,[cxt,typ])   -> (if par then PP.parens else id) $
                                pretty True cxt PP.<+> pretty True typ
    _ -> error $ "malformed TyCon: " ++ pShow t
  pretty par (TyRecord fs) =
      PP.braces
    $ commaSepAll
    $ map (\(n,t) -> PP.text n `prettyTypeSig` pretty False t)
    $ M.toList fs
  pretty par (TyVar tv) = pretty par tv

instance PrettyPrint TyVar where
  pretty par tv = case tv of
    FreeVar n  -> PP.text "fv." PP.<> PP.integer n
    BoundVar n -> PP.text n

instance PrettyPrint TyCon where
  pretty par tc = case tc of
    TupleCon n     -> PP.parens $ replicateDoc (n - 1) $ PP.char ','
    ArrayCon       -> PP.parens $ PP.brackets $ PP.empty
    FunCon         -> PP.parens $ PP.text "->"
    StringCon      -> PP.text "String"
    BoolCon        -> PP.text "Bit"
    ZCon           -> PP.text "Int"
    NumCon n       -> PP.integer n
    BlockCon       -> PP.text "<Block>"
    ContextCon cxt -> pretty par cxt
    AbstractCon n  -> PP.text n

instance PrettyPrint A.Context where
  pretty _ c = case c of
    A.CryptolSetup -> PP.text "CryptolSetup"
    A.JavaSetup    -> PP.text "JavaSetup"
    A.LLVMSetup    -> PP.text "LLVMSetup"
    A.ProofScript  -> PP.text "ProofScript"
    A.TopLevel     -> PP.text "TopLevel"

replicateDoc :: Integer -> PP.Doc -> PP.Doc
replicateDoc n d 
  | n < 1 = PP.empty
  | True  = d PP.<> replicateDoc (n-1) d

prettyTypeSig :: PP.Doc -> PP.Doc -> PP.Doc
prettyTypeSig n t = n PP.<+> PP.char ':' PP.<+> t

commaSep :: PP.Doc -> PP.Doc -> PP.Doc
commaSep = ((PP.<+>) . (PP.<> PP.comma))

commaSepAll :: [PP.Doc] -> PP.Doc
commaSepAll ds = case ds of
  [] -> PP.empty
  _  -> foldl1 commaSep ds

-- }}}

-- Type Constructors {{{

tMono :: Type -> Schema
tMono = Forall []

tForall :: [Name] -> Schema -> Schema
tForall xs (Forall ys t) = Forall (xs ++ ys) t

tTuple :: [Type] -> Type
tTuple ts = TyCon (TupleCon $ fromIntegral $ length ts) ts

tArray :: Type -> Type -> Type
tArray l t = TyCon ArrayCon [l,t]

tFun :: Type -> Type -> Type
tFun f v = TyCon FunCon [f,v]

tString :: Type
tString = TyCon StringCon []

tBool :: Type
tBool = TyCon BoolCon []

tZ :: Type
tZ = TyCon ZCon []

tNum :: Integral a => a -> Type
tNum n = TyCon (NumCon $ toInteger n) []

tBlock :: Type -> Type -> Type
tBlock c t = TyCon BlockCon [c,t]

tContext :: A.Context -> Type
tContext c = TyCon (ContextCon c) []

tAbstract :: Name -> Type
tAbstract n = TyCon (AbstractCon n) []

-- }}}

