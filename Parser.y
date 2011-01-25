{
{-# OPTIONS_GHC -fno-warn-name-shadowing      #-}
{-# OPTIONS_GHC -fno-warn-unused-matches      #-}
{-# OPTIONS_GHC -fno-warn-unused-binds        #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing      #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures  #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module SAWScript.Parser(parse) where

import Control.Monad.Error
import Control.Monad.Reader

import SAWScript.MethodAST()
import SAWScript.Token
import SAWScript.Lexer(lexSAW)
import SAWScript.Utils
}

%name parseSAW
%expect 1
%tokentype { Token }
%monad { Parser }
%lexer { lexer } { TokenEOF }
%error { parseError }

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

Exp  :: { Exp }
Exp  : let pos var '=' Exp in Exp   { Let $2 $3 $5 $7 }
     | Exp1 pos                     { Exp1 $2 $1      }

Exp1 :: { Exp1 }
Exp1 : Exp1 '+' pos Exp1            { Plus $3 $1 $4   }
     | int pos                      { Num $2 $1       }
     | var pos                      { Var $2 $1       }
     | '(' pos Exp ')'              { Brack $2 $3     }

pos :: { Pos }
    :  {- empty -}                  {% getPos }
{
newtype Parser a = Parser { unP :: [Token] -> Pos -> IO (Either String a) }

instance Monad Parser where
  return x       = Parser (\_  _ -> return (Right x))
  Parser f >>= g = Parser (\ts p -> do er <- f ts p
                                       case er of
                                        Left  e -> return $ Left e
                                        Right r -> unP (g r) ts p)
  fail s = Parser (\_ _ -> return (Left s))

getTokens :: Parser [Token]
getTokens = Parser (\ts _ -> return (Right ts))

getPos :: Parser Pos
getPos = Parser (\ts p -> return (Right p))

happyError :: Parser a
happyError = do ts <- getTokens
		parseError (if null ts then TokenEOF else head ts)

parseError :: Token -> Parser a
parseError t = Parser (\_ p -> return $ Left $ show p ++ ": Parse error at <" ++ show t ++ ">")

lexer :: (Token -> Parser a) -> Parser a
lexer cont = Parser (\ts p ->
	case ts of
	   []		  -> unP (cont TokenEOF) [] p
	   (TokenNL : ts) -> unP (lexer cont)    ts (incLineNo p)
	   (t : ts)       -> unP (cont t)        ts p)

parse :: FilePath -> String -> IO (Either String Exp)
parse f s = unP parseSAW (lexSAW s) (initPos f)

data Exp = Let  Pos String Exp Exp
         | Exp1 Pos Exp1
         deriving Show

data Exp1 = Var Pos String
          | Plus Pos Exp1 Exp1
          | Num Pos Int
          | Brack Pos Exp
         deriving Show
}
