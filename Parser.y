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
%name parseSAW VerifierCommands

%token
   'import' { TReserved  _ "import" }
   'extern' { TReserved  _ "extern" }
   'let'    { TReserved  _ "let" }
   'SBV'    { TReserved  _ "SBV"    }
   'Bit'    { TReserved  _ "Bit"    }
   var      { TVar       _ $$       }
   str      { TLit       _ $$       }
   num      { TNum       _ _        }
   ';'      { TPunct     _ ";"      }
   '['      { TPunct     _ "["      }
   ']'      { TPunct     _ "]"      }
   '('      { TPunct     _ "("      }
   ')'      { TPunct     _ ")"      }
   ':'      { TPunct     _ ":"      }
   ','      { TPunct     _ ","      }
   '='      { TPunct     _ "="      }
   '->'     { TPunct     _ "->"     }
%%

-- Top level program structure
VerifierCommands :: { [VerifierCommand] }
VerifierCommands : {- empty -}                          { []      }
                 | VerifierCommands VerifierCommand ';' { $2 : $1 }

-- Verifier commands
VerifierCommand :: { VerifierCommand }
VerifierCommand : 'import' str                               { ImportCommand (getPos $1) $2   }
                | 'extern' 'SBV' var '(' str ')' ':' FnType  { ExternSBV (getPos $1) $3 $5 $8 }
                | 'let' var '=' JavaExpr                     { GlobalLet (getPos $1) $2 $4    }

-- Types
FnType  :: { FnType }
FnType  :     ExprType      '->' ExprType  { FnType [$1] $3          }
        | '(' ExprTypes ')' '->' ExprType  { FnType (reverse $2)  $5 }

-- result will be reversed!
ExprTypes :: { [ExprType] }
ExprTypes : ExprType               { [$1]    }
          | ExprTypes ',' ExprType { $3 : $1 }

ExprType :: { ExprType }
ExprType : 'Bit'       { BitType                                                                 }
         | '[' num ']' {% parseIntRange (0, maxBound) (getInteger $2) >>= return . BitvectorType }

-- Expressions
JavaExpr :: { JavaExpr }
JavaExpr : num                    { ConstantInt (getPos $1) (getInteger $1) }
         | JavaExpr ':' ExprType  { TypeExpr $1 $3                          }
