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
import SAWScript.Utils

import qualified Cryptol.Parser.AST as P
import qualified Cryptol.Utils.Ident as P (packIdent, packModName)

import qualified Text.Show.Pretty as PP

import Control.Applicative

}

%name parseModule Stmts
%name parseStmt Stmt
%name parseStmtSemi StmtSemi
%name parseExpression Expression
%name parseSchema PolyType
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
  'ProofScript'  { TReserved _ "ProofScript"    }
  'TopLevel'     { TReserved _ "TopLevel"       }
  'CrucibleSetup'{ TReserved _ "CrucibleSetup"  }
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

%right 'else'
%left ':'
%left '['
%left '.'

%%

Stmts :: { [Stmt] }
 : termBy(Stmt, ';')                    { $1 }

StmtSemi :: { Stmt }
 : fst(Stmt, opt(';'))                  { $1 }

Import :: { Import }
 : string mbAs mbImportSpec             { Import (Left (tokStr $1)) $2 $3 }
 -- TODO: allow imports by module name instead of path

mbAs :: { Maybe P.ModName }
 : 'as' name                            { Just (P.packModName [pack (tokStr $2)]) }
 | {- empty -}                          { Nothing }

mbImportSpec :: { Maybe P.ImportSpec }
 : '(' list(name) ')'                   { Just $ P.Only   [ P.packIdent (tokStr n) | n <- $2 ] }
 | 'hiding' '(' list(name) ')'          { Just $ P.Hiding [ P.packIdent (tokStr n) | n <- $3 ] }
 | {- empty -}                          { Nothing }

Stmt :: { Stmt }
 : Expression                           { StmtBind (PWild Nothing) Nothing $1   }
 | AExpr '<-' Expression                {% fmap (\x -> StmtBind x Nothing $3) (toPattern $1) }
 | 'rec' sepBy1(Declaration, 'and')     { StmtLet (Recursive $2)                  }
 | 'let' Declaration                    { StmtLet (NonRecursive $2)               }
 | 'let' Code                           { StmtCode $2                 }
 | 'import' Import                      { StmtImport $2               }
 | 'typedef' name '=' Type              { StmtTypedef (toLName $2) $4 }

Declaration :: { Decl }
 : Arg list(Arg) '=' Expression         { Decl (maxSpan [getPos $1, getPos $4]) $1 Nothing (buildFunction $2 $4) }
 | Arg list(Arg) ':' Type '=' Expression
                                        { Decl (maxSpan [getPos $1, getPos $6]) $1 Nothing (buildFunction $2 (TSig $6 $4)) }

Pattern :: { Pattern }
 : Arg                                  { $1 }
 | name ':' Type                        { PVar (toLName $1) (Just $3) }

Arg :: { Pattern }
 : name                                 { LPattern (tokPos $1) (PVar (toLName $1) Nothing) }
 | '(' commas(Pattern) ')'              { LPattern (maxSpan [tokPos $1, tokPos $3]) (case $2 of [p] -> p; _ -> PTuple $2) }

Expression :: { Expr }
 : IExpr                                { $1 }
 | IExpr ':' Type                       { TSig $1 $3          }
 | '\\' list1(Arg) '->' Expression      { buildFunction $2 $4 }
 | 'let' Declaration 'in' Expression    { Let (NonRecursive $2) $4 }
 | 'rec' sepBy1(Declaration, 'and')
   'in' Expression                      { Let (Recursive $2) $4 }
 | 'if' Expression 'then' Expression
                   'else' Expression    { IfThenElse $2 $4 $6 }

IExpr :: { Expr }
 : AExprs                               { $1 }

AExprs :: { Expr }
 : list1(AExpr)                         { LExpr (maxSpan $1) (buildApplication $1) }

AExpr :: { Expr }
: '(' ')'                               { LExpr (maxSpan [tokPos $1, tokPos $2]) (Tuple []) }
 | '[' ']'                              { LExpr (maxSpan [tokPos $1, tokPos $2]) (Array []) }
 | string                               { LExpr (tokPos $1) (String (tokStr $1)) }
 | Code                                 { Code $1                 }
 | CType                                { CType $1                }
 | num                                  { LExpr (tokPos $1) (Int (tokNum $1)) }
 | name                                 { Var (Located (tokStr $1) (tokStr $1) (tokPos $1)) }
 | '(' Expression ')'                   { LExpr (maxSpan [tokPos $1, tokPos $3]) $2 }
 | '(' commas2(Expression) ')'          { LExpr (maxSpan [tokPos $1, tokPos $3]) (Tuple $2) }
 | '[' commas(Expression) ']'           { LExpr (maxSpan [tokPos $1, tokPos $3]) (Array $2) }
 | '{' commas(Field) '}'                { LExpr (maxSpan [tokPos $1, tokPos $3]) (Record (Map.fromList $2)) }
 | 'do' '{' termBy(Stmt, ';') '}'       { LExpr (maxSpan [tokPos $1, tokPos $4]) (Block $3) }
 | AExpr '.' name                       { LExpr (maxSpan [getPos $1, tokPos $3]) (Lookup $1 (tokStr $3)) }
 | AExpr '.' num                        { LExpr (maxSpan [getPos $1, tokPos $3]) (TLookup $1 (tokNum $3))           }

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
 | BaseType '->' Type                   { tFun $1 $3              }

FieldType :: { Bind Type }
  : name ':' BaseType                   { (tokStr $1, $3)         }

BaseType :: { Type }
 : name                                 { tVar (tokStr $1)        }
 | Context BaseType                     { tBlock $1 $2            }
 | '(' ')'                              { tTuple []               }
 | 'Bool'                               { tBool                   }
 | 'Int'                                { tInt                    }
 | 'String'                             { tString                 }
 | 'Term'                               { tTerm                   }
 | 'Type'                               { tType                   }
 | 'AIG'                                { tAIG                    }
 | 'CFG' 				{ tCFG			  }
 | '(' Type ')'                         { $2                      }
 | '(' commas2(Type) ')'                { tTuple $2               }
 | '[' Type ']'                         { tArray $2               }
 | '{' commas(FieldType) '}'            { tRecord $2              }

Context :: { Type }
 : 'CryptolSetup'                       { tContext CryptolSetup   }
 | 'JavaSetup'                          { tContext JavaSetup      }
 | 'LLVMSetup'                          { tContext LLVMSetup      }
 | 'ProofScript'                        { tContext ProofScript    }
 | 'TopLevel'                           { tContext TopLevel       }
 | 'CrucibleSetup'                      { tContext CrucibleSetup  }
 | name                                 { tVar (tokStr $1)        }

-- Parameterized productions, most come directly from the Happy manual.
fst(p, q)  : p q   { $1 }
snd(p, q)  : p q   { $2 }
both(p, q) : p q   { ($1, $2) }

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
buildFunction args e = foldr Function e args

buildApplication :: [Expr] -> Expr
buildApplication = foldl1 (\e body -> Application e body)

toPattern :: Expr -> Either ParseError Pattern
toPattern expr =
  case expr of
    Tuple es       -> PTuple `fmap` mapM toPattern es
    TSig (Var x) t -> return (PVar x (Just t))
    Var x          -> return (PVar x Nothing)
    LExpr pos e    -> LPattern pos `fmap` toPattern e
    _              -> Left (InvalidPattern expr)

}
