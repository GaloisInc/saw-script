{
{-# OPTIONS_GHC -fno-warn-name-shadowing      #-}
{-# OPTIONS_GHC -fno-warn-unused-matches      #-}
{-# OPTIONS_GHC -fno-warn-unused-binds        #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing      #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures  #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module SAWScript.Parser(parseSAW) where

import SAWScript.MethodAST
import SAWScript.Token
import SAWScript.Utils
import {-# SOURCE #-} SAWScript.ParserActions
}

%expect 0
%tokentype { Token Pos }
%monad { Parser }
%lexer { lexer } { TEOF _ }
%error { parseError }
%name parseSAW SAWScript

%token
   'import'       { TReserved  _ "import"       }
   'extern'       { TReserved  _ "extern"       }
   'let'          { TReserved  _ "let"          }
   'SBV'          { TReserved  _ "SBV"          }
   'Bit'          { TReserved  _ "Bit"          }
   'method'       { TReserved  _ "method"       }
   'rule'         { TReserved  _ "rule"         }
   'mayAlias'     { TReserved  _ "mayAlias"     }
   'assume'       { TReserved  _ "assume"       }
   'ensures'      { TReserved  _ "ensures"      }
   'arbitrary'    { TReserved  _ "arbitrary"    }
   'const'        { TReserved  _ "const"        }
   'verifyUsing'  { TReserved  _ "verifyUsing"  }
   'enable'       { TReserved  _ "enable"       }
   'disable'      { TReserved  _ "disable"      }
   'blast'        { TReserved  _ "blast"        }
   'rewrite'      { TReserved  _ "rewrite"      }
   'set'          { TReserved  _ "set"          }
   'verification' { TReserved  _ "verification" }
   'on'           { TReserved  _ "on"           }
   'off'          { TReserved  _ "off"          }
   'type'         { TReserved  _ "type"         }
   'args'         { TReserved  _ "args"         }
   'this'         { TReserved  _ "this"         }
   'int'          { TReserved  _ "int"          }
   'long'         { TReserved  _ "long"         }
   'true'         { TReserved  _ "true"         }
   'false'        { TReserved  _ "false"        }
   'not'          { TReserved  _ "not"          }
   'forAll'       { TReserved  _ "forAll"       }
   var            { TVar       _ _              }
   str            { TLit       _ $$             }
   num            { TNum       _ _              }
   ';'            { TPunct     _ ";"            }
   '['            { TPunct     _ "["            }
   ']'            { TPunct     _ "]"            }
   '('            { TPunct     _ "("            }
   ')'            { TPunct     _ ")"            }
   '{'            { TPunct     _ "{"            }
   '}'            { TPunct     _ "}"            }
   ':'            { TPunct     _ ":"            }
   ','            { TPunct     _ ","            }
   '.'            { TPunct     _ "."            }
   '='            { TPunct     _ "="            }
   '->'           { TPunct     _ "->"           }
   ':='           { TPunct     _ ":="           }
   '~'            { TOp        _ "~"            }
   '-'            { TOp        _ "-"            }
   '*'            { TOp        _ "+"            }
   '+'            { TOp        _ "*"            }
   '/s'           { TOp        _ "/s"           }
   '%s'           { TOp        _ "%s"           }
   '<<'           { TOp        _ "<<"           }
   '>>s'          { TOp        _ ">>s"          }
   '>>u'          { TOp        _ ">>u"          }
   '&'            { TOp        _ "&"            }
   '^'            { TOp        _ "^"            }
   '|'            { TOp        _ "|"            }
   '#'            { TOp        _ "#"            }
   '=='           { TOp        _ "=="           }
   '!='           { TOp        _ "!="           }
   '>=s'          { TOp        _ ">=s"          }
   '>=u'          { TOp        _ ">=u"          }
   '>s'           { TOp        _ ">s"           }
   '>u'           { TOp        _ ">u"           }
   '<=s'          { TOp        _ "<=s"          }
   '<=u'          { TOp        _ "<=u"          }
   '<s'           { TOp        _ "<s"           }
   '<u'           { TOp        _ "<u"           }
   '&&'           { TOp        _ "&&"           }
   '||'           { TOp        _ "||"           }

-- Operators, precedence increases as you go down in this list
%left '||'
%left '&&'
%nonassoc '>=s' '>=u' '>s' '>u' '<=s' '<=u' '<s' '<u'
%nonassoc '==' '!='
%right '#'
%left '|'
%left '^'
%left '&'
%left '<<' '>>s' '>>u'
%left '+' '-'
%left '*' '/s' '%s'
%left ':'
%left '.'
%right NEG 'not' '~'
%%

-- SAWScript
SAWScript :: { [VerifierCommand] }
SAWScript : termBy(VerifierCommand, ';') { $1 }

-- Verifier commands
VerifierCommand :: { VerifierCommand }
VerifierCommand : 'import' str                              { ImportCommand     (getPos $1) $2                      }
                | 'extern' 'SBV' var '(' str ')' ':' FnType { ExternSBV         (getPos $1) (getString $3) $5 $8    }
                | 'let' var '=' Expr                        { GlobalLet         (getPos $1) (getString $2) $4       }
                | 'set' 'verification' 'on'                 { SetVerification   (getPos $1) True                    }
                | 'set' 'verification' 'off'                { SetVerification   (getPos $1) False                   }
                | 'enable' var                              { Enable            (getPos $1) (getString $2)          }
                | 'disable' var                             { Disable           (getPos $1) (getString $2)          }
                | 'method' Qvar '{' MethodSpecDecls '}'     { DeclareMethodSpec (getPos $1) (snd $2) $4             }
                | 'rule' var ':' RuleParams Expr '->' Expr  { Rule              (getPos $1) (getString $2) $4 $5 $7 }

-- Types
FnType  :: { FnType }
FnType  :     ExprType      '->' ExprType  { FnType [$1] $3 }
        | '(' ExprTypes ')' '->' ExprType  { FnType $2 $5   }

-- Comma separated types, at least one
ExprTypes :: { [ExprType] }
ExprTypes : sepBy1(ExprType, ',') { $1 }

ExprType :: { ExprType }
ExprType : 'Bit'                           {  BitType    (getPos $1)                 }
         | '[' ExprWidth ']' opt(ExprType) {% mkExprType (getPos $1) $2 $4           }
         | var                             {  ShapeVar   (getPos $1) (getString $1)  }

ExprWidth :: { ExprWidth }
ExprWidth : int              {  WidthConst $1           }
          | var              {  WidthVar (getString $1) }

-- Rule parameters
RuleParams :: { [(Pos, String, ExprType)] }
RuleParams : {- empty -}                      { [] }
           | 'forAll' sepBy1(Param, ',')  '.' { $2 }

Param :: { (Pos, String, ExprType) }
Param : var ':' ExprType { (getPos $1, getString $1, $3) }

-- Comma separated expressions, potentially none
Exprs :: { [Expr] }
Exprs : sepBy(Expr, ',') { $1 }

-- Expressions
Expr :: { Expr }
Expr : var                { Var          (getPos $1) (getString $1)    }
     | 'this'             { ThisExpr     (getPos $1)                   }
     | 'true'             { ConstantBool (getPos $1) True              }
     | 'false'            { ConstantBool (getPos $1) False             }
     | num                { ConstantInt  (getPos $1) (getInteger $1)   }
     | '{' RecordExpr '}' { MkRecord     (getPos $1) $2                }
     | Expr ':' ExprType  { TypeExpr     (getPos $2) $1 $3             }
     | Expr '.' var       { DerefField   (getPos $2) $1 (getString $3) }
     | var '(' Exprs ')'  { ApplyExpr    (getPos $1) (getString $1) $3 }
     | 'args' '[' int ']' { ArgsExpr     (getPos $1) $3                }
     | '[' Exprs ']'      { MkArray      (getPos $1) $2                }
     | '~' Expr           { BitComplExpr (getPos $1) $2                }
     | 'not' Expr         { NotExpr      (getPos $1) $2                }
     | '-' Expr %prec NEG { NegExpr      (getPos $1) $2                }
     | Expr '*'   Expr    { MulExpr      (getPos $2) $1 $3             }
     | Expr '/s'  Expr    { SDivExpr     (getPos $2) $1 $3             }
     | Expr '%s'  Expr    { SRemExpr     (getPos $2) $1 $3             }
     | Expr '+'   Expr    { PlusExpr     (getPos $2) $1 $3             }
     | Expr '-'   Expr    { SubExpr      (getPos $2) $1 $3             }
     | Expr '<<'  Expr    { ShlExpr      (getPos $2) $1 $3             }
     | Expr '>>s' Expr    { SShrExpr     (getPos $2) $1 $3             }
     | Expr '>>u' Expr    { UShrExpr     (getPos $2) $1 $3             }
     | Expr '&'   Expr    { BitAndExpr   (getPos $2) $1 $3             }
     | Expr '^'   Expr    { BitXorExpr   (getPos $2) $1 $3             }
     | Expr '|'   Expr    { BitOrExpr    (getPos $2) $1 $3             }
     | Expr '#'   Expr    { AppendExpr   (getPos $2) $1 $3             }
     | Expr '=='  Expr    { EqExpr       (getPos $2) $1 $3             }
     | Expr '!='  Expr    { IneqExpr     (getPos $2) $1 $3             }
     | Expr '>=s' Expr    { SGeqExpr     (getPos $2) $1 $3             }
     | Expr '>=u' Expr    { UGeqExpr     (getPos $2) $1 $3             }
     | Expr '>s'  Expr    { SGtExpr      (getPos $2) $1 $3             }
     | Expr '>u'  Expr    { UGtExpr      (getPos $2) $1 $3             }
     | Expr '<=s' Expr    { SLeqExpr     (getPos $2) $1 $3             }
     | Expr '<=u' Expr    { ULeqExpr     (getPos $2) $1 $3             }
     | Expr '<s'  Expr    { SLtExpr      (getPos $2) $1 $3             }
     | Expr '<u'  Expr    { ULtExpr      (getPos $2) $1 $3             }
     | Expr '&&'  Expr    { AndExpr      (getPos $2) $1 $3             }
     | Expr '||'  Expr    { OrExpr       (getPos $2) $1 $3             }

-- Records
RecordExpr :: { [(Pos, String, Expr)] }
RecordExpr : sepBy(connected(var, '=', Expr), ';')  { map ((\ (v, e) -> (getPos v, getString v, e))) $1 }

-- Method spec body
MethodSpecDecls :: { [MethodSpecDecl] }
MethodSpecDecls : termBy(MethodSpecDecl, ';') { $1 }

MethodSpecDecl :: { MethodSpecDecl }
MethodSpecDecl : 'type'        JavaRefs ':' JavaType  { Type        (getPos $1) $2 $4             }
               | 'mayAlias'    '{' JavaRefs '}'       { MayAlias    (getPos $1) $3                }
               | 'const'       JavaRef ':=' Expr      { Const       (getPos $1) $2 $4             }
               | 'let'         var '='  Expr          { MethodLet   (getPos $1) (getString $2) $4 }
               | 'assume'      Expr                   { Assume      (getPos $1) $2                }
               | 'ensures'     JavaRef ':=' Expr      { Ensures     (getPos $1) $2 $4             }
               | 'arbitrary'   ':' JavaRefs           { Arbitrary   (getPos $1) $3                }
               | 'verifyUsing' ':' VerificationMethod { VerifyUsing (getPos $1) $3                }

-- Comma separated Sequence of JavaRef's, at least one
JavaRefs :: { [JavaRef] }
JavaRefs : sepBy1(JavaRef, ',') { $1 }

JavaRef :: { JavaRef }
JavaRef : 'this'             { This          (getPos $1)                   }
        | 'args' '[' int ']' { Arg           (getPos $1) $3                }
        | JavaRef '.' var    { InstanceField (getPos $2) $1 (getString $3) }

JavaType :: { JavaType }
JavaType : Qvar               { RefType   (fst $1)    (snd $1) }
         | 'int'  '[' int ']' { IntArray  (getPos $1) $3       }
         | 'long' '[' int ']' { LongArray (getPos $1) $3       }

VerificationMethod :: { VerificationMethod }
VerificationMethod : 'blast'    { Blast   }
                   | 'rewrite'  { Rewrite }

-- A qualified variable
Qvar :: { (Pos, [String]) }
Qvar : sepBy1(var, '.') { (head (map getPos $1), map getString $1) }

-- A literal that must fit into a Haskell Int
int :: { Int }
int : num       {% parseIntRange (getPos $1) (0, maxBound) (getInteger $1) }

-- Parameterized productions, most of these come directly from the Happy manual..
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

-- A list of at least one 1 p's, separated by q's
sepBy1(p, q) : p list(snd(q, p)) { $1 : $2 }

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
