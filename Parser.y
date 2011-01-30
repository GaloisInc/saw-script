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

%expect 1
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
%%

-- SAWScript
SAWScript :: { [VerifierCommand] }
SAWScript : termBy(VerifierCommand, ';') { $1 }

-- Verifier commands
VerifierCommand :: { VerifierCommand }
VerifierCommand : 'import' str                              { ImportCommand     (getPos $1) $2                   }
                | 'extern' 'SBV' var '(' str ')' ':' FnType { ExternSBV         (getPos $1) (getString $3) $5 $8 }
                | 'let' var '=' JavaExpr                    { GlobalLet         (getPos $1) (getString $2) $4    }
                | 'set' 'verification' 'on'                 { SetVerification   (getPos $1) True                 }
                | 'set' 'verification' 'off'                { SetVerification   (getPos $1) False                }
                | 'enable' var                              { Enable            (getPos $1) (getString $2)       }
                | 'disable' var                             { Disable           (getPos $1) (getString $2)       }
                | 'method' Qvar '{' MethodSpecDecls '}'     { DeclareMethodSpec (getPos $1) $2 $4                }

-- Types
FnType  :: { FnType }
FnType  :     ExprType      '->' ExprType  { FnType [$1] $3 }
        | '(' ExprTypes ')' '->' ExprType  { FnType $2 $5   }

-- Comma separated types, at least one
ExprTypes :: { [ExprType] }
ExprTypes : sepBy1(ExprType, ',') { $1 }

ExprType :: { ExprType }
ExprType : 'Bit'                           {  BitType                      }
         | '[' ExprWidth ']' opt(ExprType) {% mkExprType (getPos $1) $2 $4 }
         | var                             {  ShapeVar (getString $1)      }

ExprWidth :: { ExprWidth }
ExprWidth : int              {  WidthConst $1           }
          | var              {  WidthVar (getString $1) }

-- Comma separated expressions, at least one
JavaExprs :: { [JavaExpr] }
JavaExprs : sepBy1(JavaExpr, ',') { $1 }

-- Expressions
JavaExpr :: { JavaExpr }
JavaExpr : JavaRef                { Extern       $1                            }
         | var                    { Var          (getPos $1) (getString $1)    }
         | 'true'                 { ConstantBool (getPos $1) True              }
         | 'false'                { ConstantBool (getPos $1) False             }
         | num                    { ConstantInt  (getPos $1) (getInteger $1)   }
         | JavaExpr ':' ExprType  { TypeExpr     (getPos $2) $1 $3             }
         | var '(' JavaExprs ')'  { ApplyExpr    (getPos $1) (getString $1) $3 }
         | '{' RecordExpr '}'     { MkRecord     (getPos $1) $2                }
         | JavaExpr '.' var       { DerefField   (getPos $2) $1 (getString $3) }

-- Records
RecordExpr :: { [(Pos, String, JavaExpr)] }
RecordExpr : sepBy(connected(var, '=', JavaExpr), ';')  { map ((\ (v, e) -> (getPos v, getString v, e))) $1 }

-- Method spec body
MethodSpecDecls :: { [MethodSpecDecl] }
MethodSpecDecls : termBy(MethodSpecDecl, ';') { $1 }

MethodSpecDecl :: { MethodSpecDecl }
MethodSpecDecl : 'type'        JavaRefs ':' JavaType  { Type        (getPos $1) $2 $4             }
               | 'mayAlias'    '{' JavaRefs '}'       { MayAlias    (getPos $1) $3                }
               | 'const'       JavaRef ':=' JavaExpr  { Const       (getPos $1) $2 $4             }
               | 'let'         var '=' JavaExpr       { MethodLet   (getPos $1) (getString $2) $4 }
               | 'assume'      JavaExpr               { Assume      (getPos $1) $2                }
               | 'ensures'     JavaRef ':=' JavaExpr  { Ensures     (getPos $1) $2 $4             }
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
JavaType : Qvar               { RefType   $1 }
         | 'int'  '[' int ']' { IntArray  $3 }
         | 'long' '[' int ']' { LongArray $3 }

VerificationMethod :: { VerificationMethod }
VerificationMethod : 'blast'    { Blast   }
                   | 'rewrite'  { Rewrite }

-- A qualified variable
Qvar :: { [String] }
Qvar : sepBy1(var, '.') { map getString $1 }

-- A literal that must fit into a Haskell Int
int :: { Int }
int : num       {% parseIntRange (getPos $1) (0, maxBound) (getInteger $1) }

-- Parameterized productions, these come directly from the Happy manual..
fst(p, q)  : p q   { $1 }
snd(p, q)  : p q   { $2 }
both(p, q) : p q   { ($1, $2) }

-- p bracketed with some delims o-c
bracketed(o,p,c) : o p c { $2 }

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
sepBy1(p,q) : p list(snd(q, p)) { $1 : $2 }

-- A list of 0 or more p's, separated by q's
sepBy(p,q) : {- empty -}  { [] }
           | sepBy1(p, q) { $1 }

-- A list of at least one 1 p's, terminated by q's
termBy1(p,q) : list1(fst(p, q)) { $1 }

-- A list of 0 or more p's, terminated by q's
termBy(p, q) : {- empty -}    { [] }
             | termBy1(p, q)  { $1 }

-- one or the other
either(p, q) : p  { Left  $1 }
             | q  { Right $1 }
