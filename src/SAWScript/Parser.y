{
{-# OPTIONS_GHC -fno-warn-name-shadowing      #-}
{-# OPTIONS_GHC -fno-warn-unused-matches      #-}
{-# OPTIONS_GHC -fno-warn-unused-binds        #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing      #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures  #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# OPTIONS_GHC -fno-warn-tabs                #-}
module SAWScript.Parser
  ( parseModule
  , parseStmt
  , parseStmtSemi
  , parseExpression
  , parseSchema
  , ParseError(..)
  ) where

import Data.List
import qualified Data.Map as Map (fromList)
import Data.Text (pack)
import SAWScript.Token
import SAWScript.Lexer
import SAWScript.AST
import SAWScript.Position
import SAWScript.Utils

import qualified Cryptol.Parser.AST as P
import qualified Cryptol.Utils.Ident as P (packIdent, packModName)

import qualified Text.Show.Pretty as PP

import Control.Applicative
import Control.Exception

}

%name parseModule StmtsEOF
%name parseStmt StmtEOF
%name parseStmtSemi StmtSemiEOF
%name parseExpression ExpressionEOF
%name parseSchema PolyTypeEOF
%error { parseError }
%tokentype { Token Pos }
%monad { Either ParseError }

%token
  'import'       { TReserved _ "import"         }
  'and'          { TReserved _ "and"            }
  'as'           { TReserved _ "as"             }
  'hiding'       { TReserved _ "hiding"         }
  'let'          { TReserved _ "let"            }
  'rec'          { TReserved _ "rec"            }
  'in'           { TReserved _ "in"             }
  'do'           { TReserved _ "do"             }
  'if'           { TReserved _ "if"             }
  'then'         { TReserved _ "then"           }
  'else'         { TReserved _ "else"           }
  'typedef'      { TReserved _ "typedef"        }
  'CryptolSetup' { TReserved _ "CryptolSetup"   }
  'JavaSetup'    { TReserved _ "JavaSetup"      }
  'LLVMSetup'    { TReserved _ "LLVMSetup"      }
  'MIRSetup'     { TReserved _ "MIRSetup"       }
  'ProofScript'  { TReserved _ "ProofScript"    }
  'TopLevel'     { TReserved _ "TopLevel"       }
  'CrucibleSetup'{ TReserved _ "CrucibleSetup"  }
  'CrucibleMethodSpec' { TReserved _ "CrucibleMethodSpec" }
  'LLVMSpec'     { TReserved _ "LLVMSpec"       }
  'JVMMethodSpec'{ TReserved _ "JVMMethodSpec"  }
  'JVMSpec'      { TReserved _ "JVMSpec"        }
  'MIRSpec'      { TReserved _ "MIRSpec"        }
  'Bool'         { TReserved _ "Bool"           }
  'Int'          { TReserved _ "Int"            }
  'String'       { TReserved _ "String"         }
  'Term'         { TReserved _ "Term"           }
  'Type'         { TReserved _ "Type"           }
  'AIG'          { TReserved _ "AIG"            }
  'CFG'          { TReserved _ "CFG"		}
  ';'            { TPunct    _ ";"              }
  '['            { TPunct    _ "["              }
  ']'            { TPunct    _ "]"              }
  '('            { TPunct    _ "("              }
  ')'            { TPunct    _ ")"              }
  '{'            { TPunct    _ "{"              }
  '}'            { TPunct    _ "}"              }
  ':'            { TPunct    _ ":"              }
  ','            { TPunct    _ ","              }
  '.'            { TPunct    _ "."              }
  '\\'           { TPunct    _ "\\"             }
  '='            { TPunct    _ "="              }
  '->'           { TPunct    _ "->"             }
  '<-'           { TPunct    _ "<-"             }
  string         { TLit      _ _                }
  code           { TCode     _ _                }
  ctype          { TCType    _ _                }
  num            { TNum      _ _ _              }
  name           { TVar      _ _                }
  EOF            { TEOF      _ _                }

%right 'else'
%left ':'
%left '['
%left '.'

%%

StmtsEOF :: { [Stmt] }
 : Stmts EOF                            { $1 }

StmtEOF :: { Stmt }
 : Stmt EOF                             { $1 }

StmtSemiEOF :: { Stmt }
 : StmtSemi EOF                         { $1 }

ExpressionEOF :: { Expr }
 : Expression EOF                       { $1 }

PolyTypeEOF :: { Schema }
 : PolyType EOF                         { $1 }

Stmts :: { [Stmt] }
 : termBy(Stmt, ';')                    { $1 }

StmtSemi :: { Stmt }
 : fst(Stmt, opt(';'))                  { $1 }

Import :: { Import }
 : string mbAs mbImportSpec             { Import (Left (tokStr $1)) (fst $2) (fst $3) (maxSpan [tokPos $1, snd $2, snd $3])}
 -- TODO: allow imports by module name instead of path

mbAs :: { (Maybe P.ModName, Pos) }
 : 'as' name                            { (Just (P.packModName [pack (tokStr $2)]), maxSpan [$1, $2]) }
 | {- empty -}                          { (Nothing, Unknown) }

mbImportSpec :: { (Maybe P.ImportSpec, Pos) }
 : '(' list(name) ')'                   { (Just $ P.Only   [ P.packIdent (tokStr n) | n <- $2 ], maxSpan [tokPos $1, tokPos $3]) }
 | 'hiding' '(' list(name) ')'          { (Just $ P.Hiding [ P.packIdent (tokStr n) | n <- $3 ], maxSpan [tokPos $1, tokPos $4]) }
 | {- empty -}                          { (Nothing, Unknown) }

Stmt :: { Stmt }
 : Expression                           { StmtBind (getPos $1) (PWild (leadingPos $ getPos $1) Nothing) Nothing $1 }
 | AExpr '<-' Expression                {% fmap (\x -> StmtBind (maxSpan' x $3) x Nothing $3) (toPattern $1) }
 | 'rec' sepBy1(Declaration, 'and')     { StmtLet (maxSpan [tokPos $1, maxSpan $2]) (Recursive $2) }
 | 'let' Declaration                    { StmtLet (maxSpan [tokPos $1, getPos $2]) (NonRecursive $2) }
 | 'let' Code                           { StmtCode (maxSpan [tokPos $1, getPos $2]) $2 }
 | 'import' Import                      { StmtImport (maxSpan [tokPos $1, getPos $2]) $2 }
 | 'typedef' name '=' Type              { StmtTypedef (maxSpan [tokPos $1, getPos $4]) (toLName $2) $4 }

Declaration :: { Decl }
 : Arg list(Arg) '=' Expression         { Decl (maxSpan' $1 $4) $1 Nothing (buildFunction $2 $4) }
 | Arg list(Arg) ':' Type '=' Expression
                                        { Decl (maxSpan' $1 $6) $1 Nothing (buildFunction $2 (TSig (maxSpan' $4 $6) $6 $4)) }

Pattern :: { Pattern }
 : Arg                                  { $1 }
 | name ':' Type                        { PVar (maxSpan [tokPos $1, getPos $3]) (toLName $1) (Just $3) }

Arg :: { Pattern }
 : name                                 { PVar (tokPos $1) (toLName $1) Nothing }
 | '(' ')'                              { PTuple (maxSpan [tokPos $1, tokPos $2]) [] }
 | '(' commas(Pattern) ')'              { case $2 of [p] -> p; _ -> PTuple (maxSpan [tokPos $1, tokPos $3]) $2 }

Expression :: { Expr }
 : IExpr                                { $1 }
 | IExpr ':' Type                       { TSig (maxSpan' $1 $3) $1 $3 }
 | '\\' list1(Arg) '->' Expression      { buildFunction $2 $4 }
 | 'let' Declaration 'in' Expression    { Let (maxSpan [tokPos $1, getPos $4]) (NonRecursive $2) $4 }
 | 'rec' sepBy1(Declaration, 'and')
   'in' Expression                      { Let (maxSpan [tokPos $1, getPos $4]) (Recursive $2) $4 }
 | 'if' Expression 'then' Expression
                   'else' Expression    { IfThenElse (maxSpan [tokPos $1, getPos $6]) $2 $4 $6 }

IExpr :: { Expr }
 : AExprs                               { $1 }

AExprs :: { Expr }
 : list1(AExpr)                         { buildApplication $1 }

AExpr :: { Expr }
: '(' ')'                               { Tuple (maxSpan [tokPos $1, tokPos $2]) [] }
 | '[' ']'                              { Array (maxSpan [tokPos $1, tokPos $2]) [] }
 | string                               { String (tokPos $1) (tokStr $1) }
 | Code                                 { Code $1 }
 | CType                                { CType $1 }
 | num                                  { Int (tokPos $1) (tokNum $1) }
 | name                                 { Var (Located (tokStr $1) (tokStr $1) (tokPos $1)) }
 | '(' Expression ')'                   { $2 } -- { Parens (maxSpan [tokPos $1, tokPos $3]) $2 }
 | '(' commas2(Expression) ')'          { Tuple (maxSpan [tokPos $1, tokPos $3]) $2 }
 | '[' commas(Expression) ']'           { Array (maxSpan [tokPos $1, tokPos $3]) $2 }
 | '{' commas(Field) '}'                { Record (maxSpan [tokPos $1, tokPos $3]) (Map.fromList $2) }
 | 'do' '{' termBy(Stmt, ';') '}'       { Block (maxSpan [tokPos $1, tokPos $4]) $3 }
 | AExpr '.' name                       { Lookup (maxSpan [getPos $1, tokPos $3]) $1 (tokStr $3) }
 | AExpr '.' num                        { TLookup (maxSpan [getPos $1, tokPos $3]) $1 (tokNum $3) }

Code :: { Located String }
 : code                                 { Located (tokStr $1) (tokStr $1) (tokPos $1) }

CType :: { Located String }
 : ctype                                { Located (tokStr $1) (tokStr $1) (tokPos $1) }

Field :: { (Name, Expr) }
 : name '=' Expression                  { (tokStr $1, $3) }

Names :: { [Name] }
 : name                                 { [tokStr $1] }
 | name ',' Names                       { tokStr $1:$3 }

PolyType :: { Schema }
 : Type                                 { tMono $1                }
 | '{' Names '}' Type                   { Forall $2 $4            }

Type :: { Type }
 : BaseType                             { $1                      }
 | BaseType '->' Type                   { LType (maxSpan [$1, $3]) (tFun $1 $3) }

FieldType :: { (Name, Type) }
  : name ':' BaseType                   { (tokStr $1, $3)         }

BaseType :: { Type }
 : name                                 { LType (getPos $1) (tVar (tokStr $1))  }
 | Context BaseType                     { tBlock $1 $2                          }
 | '(' ')'                              { LType (maxSpan [$1, $2]) (tTuple [])  }
 | 'Bool'                               { LType (getPos $1) tBool               }
 | 'Int'                                { LType (getPos $1) tInt                }
 | 'String'                             { LType (getPos $1) tString             }
 | 'Term'                               { LType (getPos $1) tTerm               }
 | 'Type'                               { LType (getPos $1) tType               }
 | 'AIG'                                { LType (getPos $1) tAIG                }
 | 'CFG' 				{ LType (getPos $1) tCFG                }
 | 'CrucibleMethodSpec'			{ LType (getPos $1) tLLVMSpec           }
 | 'LLVMSpec' 				{ LType (getPos $1) tLLVMSpec           }
 | 'JVMMethodSpec'			{ LType (getPos $1) tJVMSpec            }
 | 'JVMSpec' 				{ LType (getPos $1) tJVMSpec            }
 | 'MIRSpec' 				{ LType (getPos $1) tMIRSpec            }
 | '(' Type ')'                         { LType (maxSpan [$1, $3]) $2           }
 | '(' commas2(Type) ')'                { LType (maxSpan [$1, $3]) (tTuple $2)  }
 | '[' Type ']'                         { LType (maxSpan [$1, $3]) (tArray $2)  }
 | '{' commas(FieldType) '}'            { LType (maxSpan [$1, $3]) (tRecord $2) }

Context :: { Type }
 : 'CryptolSetup'                       { tContext CryptolSetup   }
 | 'JavaSetup'                          { tContext JavaSetup      }
 | 'LLVMSetup'                          { tContext LLVMSetup      }
 | 'MIRSetup'                           { tContext MIRSetup       }
 | 'ProofScript'                        { tContext ProofScript    }
 | 'TopLevel'                           { tContext TopLevel       }
 | 'CrucibleSetup'                      { tContext LLVMSetup      }
 | name                                 { tVar (tokStr $1)        }

-- Parameterized productions, most come directly from the Happy manual.
fst(p, q)  : p q   { $1 }
snd(p, q)  : p q   { $2 }
both(p, q) : p q   { ($1, $2) }

phrase(p) : p EOF { $1 }

-- p bracketed with some delims o-c
bracketed(o, p, c) : o p c { $2 }

-- p and q, connected by some connective c
connected(p, c, q) : p c q { ($1, $3) }

-- an optional p
opt(p) : p            { Just $1 }
       | {- empty -}  { Nothing }

-- A reversed list of at least 1 p's
rev_list1(p) : p              { [$1]    }
             | rev_list1(p) p { $2 : $1 }

-- A list of at least 1 p's
list1(p) : rev_list1(p)   { reverse $1 }

-- A potentially empty list of p's
list(p) : {- empty -}    { [] }
        | list1(p)       { $1 }

-- A reversed list of at least 1 p's
seprev_list(p,q) : seprev_list(p,q) p { $2 : $1 }
                 | seprev_list(p,q) q { $1 }
                 | {- empty -}    { [] }

-- A potentially empty list of p's separated by zero or more qs (which are ignored).
seplist(p,q) : seprev_list(p,q)  { reverse $1 }

-- A list of at least one 1 p's, separated by q's
sepBy1(p, q) : p list(snd(q, p)) { $1 : $2 }

sepBy2(p, q) : p q sepBy1(p, q) { $1 : $3 }

-- A list of 0 or more p's, separated by q's
sepBy(p, q) : {- empty -}  { [] }
            | sepBy1(p, q) { $1 }

-- A list of at least one 1 p's, terminated by q's
termBy1(p, q) : list1(fst(p, q)) { $1 }

-- A list of 0 or more p's, terminated by q's
termBy(p, q) : {- empty -}    { [] }
             | termBy1(p, q)  { $1 }

-- one or the other
either(p, q) : p  { Left  $1 }
             | q  { Right $1 }

commas(p) : sepBy1(p, ',') { $1 }
commas2(p) : sepBy2(p, ',') { $1 }

{

data ParseError
  = UnexpectedEOF
  | UnexpectedToken (Token Pos)
  | InvalidPattern Expr

instance Exception ParseError

instance Show ParseError where
  show e =
    case e of
      UnexpectedEOF     -> "Parse error: unexpected end of file"
      UnexpectedToken t -> "Parse error at " ++ show (tokPos t) ++ ": Unexpected `" ++ tokStr t ++ "'"
        where Range _ sl sc el ec = tokPos t -- TODO show token span consistently
      InvalidPattern x  -> "Parse error: invalid pattern " ++ pShow x

parseError :: [Token Pos] -> Either ParseError b
parseError toks = case toks of
  []    -> Left UnexpectedEOF
  t : _ -> Left (UnexpectedToken t)

buildFunction :: [Pattern] -> Expr -> Expr
buildFunction args e =
  let once :: Pattern -> Expr -> Expr
      once pat e = Function (maxSpan' pat e) pat e
  in
  foldr once e args

buildApplication :: [Expr] -> Expr
buildApplication es =
  foldl1 (\e body -> Application (maxSpan' e body) e body) es

toPattern :: Expr -> Either ParseError Pattern
toPattern expr =
  case expr of
    Tuple pos es       -> PTuple pos `fmap` mapM toPattern es
    TSig pos (Var x) t -> return (PVar pos x (Just t))
    Var x              -> return (PVar (getPos x) x Nothing)
    _              -> Left (InvalidPattern expr)

}
