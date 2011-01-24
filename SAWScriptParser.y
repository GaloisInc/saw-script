{
module SAWScript.SAWScriptParser(parseSAW, lexSAW) where

import Data.Char
}

%name parseSAW
%tokentype { SAWToken }
%error { sawParseError }

%token
   let { TokenLet    }
   var { TokenVar $$ }
   int { TokenInt $$ }
   in  { TokenIn     }
   '=' { TokenEq     }
   '+' { TokenPlus   }
   '(' { TokenOB     }
   ')' { TokenCB     }

%%

Exp  : let var '=' Exp in Exp	{ Let $2 $4 $6 }
     | Exp1			{ Exp1 $1      }

Exp1 : Exp1 '+' Exp1            { Plus $1 $3   }
     | int			{ Num $1       }
     | var			{ Var $1       }
     | '(' Exp ')'		{ Brack $2     }

{
sawParseError :: [SAWToken] -> a
sawParseError _ = error "SAWScript: cannot parse the input"

data Exp = Let  String Exp Exp
	 | Exp1 Exp1
	 deriving Show

data Exp1 = Var String
	  | Plus Exp1 Exp1
	  | Num Int
	  | Brack Exp
	 deriving Show

data SAWToken = TokenLet
	      | TokenVar String
	      | TokenIn
	      | TokenEq
	      | TokenPlus
   	      | TokenInt Int
	      | TokenOB
	      | TokenCB

lexSAW [] = []
lexSAW (c:cs) 
      | isSpace c = lexSAW cs
      | isAlpha c = lexVar (c:cs)
      | isDigit c = lexNum (c:cs)
lexSAW ('=':cs) = TokenEq : lexSAW cs
lexSAW ('+':cs) = TokenPlus : lexSAW cs
lexSAW ('(':cs) = TokenOB : lexSAW cs
lexSAW (')':cs) = TokenCB : lexSAW cs

lexNum cs = TokenInt (read num) : lexSAW rest
      where (num,rest) = span isDigit cs

lexVar cs =
   case span isAlpha cs of
      ("let",rest) -> TokenLet : lexSAW rest
      ("in",rest)  -> TokenIn : lexSAW rest
      (var,rest)   -> TokenVar var : lexSAW rest
}
