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
   'import'      { TReserved  _ "import"      }
   'extern'      { TReserved  _ "extern"      }
   'let'         { TReserved  _ "let"         }
   'SBV'         { TReserved  _ "SBV"         }
   'Bit'         { TReserved  _ "Bit"         }
   'method'      { TReserved  _ "method"      }
   'verifyUsing' { TReserved  _ "verifyUsing" }
   'blast'       { TReserved  _ "blast"       }
   'rewrite'     { TReserved  _ "rewrite"     }
   'type'        { TReserved  _ "type"        }
   'args'        { TReserved  _ "args"        }
   'this'        { TReserved  _ "this"        }
   'int'         { TReserved  _ "int"         }
   'long'        { TReserved  _ "long"        }
   var           { TVar       _ $$            }
   str           { TLit       _ $$            }
   num           { TNum       _ _             }
   ';'           { TPunct     _ ";"           }
   '['           { TPunct     _ "["           }
   ']'           { TPunct     _ "]"           }
   '('           { TPunct     _ "("           }
   ')'           { TPunct     _ ")"           }
   '{'           { TPunct     _ "{"           }
   '}'           { TPunct     _ "}"           }
   ':'           { TPunct     _ ":"           }
   ','           { TPunct     _ ","           }
   '.'           { TPunct     _ "."           }
   '='           { TPunct     _ "="           }
   '->'          { TPunct     _ "->"          }
%%

-- SAWScript
SAWScript :: { [VerifierCommand] }
SAWScript : termBy(VerifierCommand, ';') { $1 }

-- Verifier commands
VerifierCommand :: { VerifierCommand }
VerifierCommand : 'import' str                               { ImportCommand (getPos $1) $2        }
                | 'extern' 'SBV' var '(' str ')' ':' FnType  { ExternSBV (getPos $1) $3 $5 $8      }
                | 'let' var '=' JavaExpr                     { GlobalLet (getPos $1) $2 $4         }
                | 'method' Qvar '{' MethodSpecDecls '}'      { DeclareMethodSpec (getPos $1) $2 $4 }

-- Types
FnType  :: { FnType }
FnType  :     ExprType      '->' ExprType  { FnType [$1] $3 }
        | '(' ExprTypes ')' '->' ExprType  { FnType $2 $5   }

-- Comma separated types, at least one
ExprTypes :: { [ExprType] }
ExprTypes : sepBy1(ExprType, ',') { $1 }

ExprType :: { ExprType }
ExprType : 'Bit'             {  BitType          }
         | '[' ExprWidth ']' {  BitvectorType $2 }

ExprWidth :: { ExprWidth }
ExprWidth : int              {  WidthConst $1 }
          | var              {  WidthVar $1   }

-- Expressions
JavaExpr :: { JavaExpr }
JavaExpr : num                    { ConstantInt (getPos $1) (getInteger $1) }
         | JavaExpr ':' ExprType  { TypeExpr $1 $3                          }

-- Method spec body
MethodSpecDecls :: { [MethodSpecDecl] }
MethodSpecDecls : termBy(MethodSpecDecl, ';') { $1 }

MethodSpecDecl :: { MethodSpecDecl }
MethodSpecDecl : 'type' JavaRefs ':' JavaType         { Type $2 $4 }
               | 'verifyUsing' ':' VerificationMethod { VerifyUsing $3 }

-- Comma separated Sequence of JavaRef's, at least one
JavaRefs :: { [JavaRef] }
JavaRefs : sepBy1(JavaRef, ',') { $1 }

JavaRef :: { JavaRef }
JavaRef : 'this'                { This (getPos $1)                }
        | 'args' '[' int ']'    { Arg  (getPos $1) $3             }
        | JavaRef '.' var       { InstanceField (getPos $2) $1 $3 }

JavaType :: { JavaType }
JavaType : Qvar               { RefType   $1 }
         | 'int'  '[' int ']' { IntArray  $3 }
         | 'long' '[' int ']' { LongArray $3 }

VerificationMethod :: { VerificationMethod }
VerificationMethod : 'blast'    { Blast   }
                   | 'rewrite'  { Rewrite }

-- A qualified variable
Qvar :: { [String] }
Qvar : sepBy1(var, '.') { $1 }

-- A literal that must fit into a Haskell Int
int :: { Int }
int : num       {% parseIntRange (0, maxBound) (getInteger $1) }

-- Parameterized productions, these come directly from the Happy manual..
fst(p,q)    : p q   { $1 }
snd(p,q)    : p q   { $2 }
both(p,q)   : p q   { ($1,$2) }

-- p bracketed with some delims o-c
bracketed(o,p,c) : o p c { $2 }

-- an optional p
opt(p) : p            { Just $ 1}
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

-- A list of at least one 1 p's, terminated by q's
termBy1(p,q) : list1(fst(p, q)) { $1 }

-- A list of 0 or more p's, terminated by q's
termBy(p, q) : {- empty -}    { [] }
             | termBy1(p, q)  { $1 }

-- one or the other
either(p, q) : p  { Left  $1 }
             | q  { Right $1 }
