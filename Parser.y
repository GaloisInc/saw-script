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

%expect 2
%tokentype { Token Pos }
%monad { Parser }
%lexer { lexer } { TokenEOF _ }
%error { parseError }
%name parseSAW Exp

%token
   let { TokenLet  _    }
   var { TokenVar  _ _  }
   int { TokenInt  _ _  }
   in  { TokenIn   _    }
   '=' { TokenEq   _    }
   '+' { TokenPlus _    }
   '(' { TokenOB   _    }
   ')' { TokenCB   _    }
%%

Exp  :: { Exp }
Exp  : let var '=' Exp in Exp   { Let   (getPos $1) (getTokVar $2) $4 $6 }
     | Exp '+' Exp              { Plus  (getPos $2) $1 $3          	 }
     | int                      { Num   (getPos $1) (getTokInt $1)       }
     | var                      { Var   (getPos $1) (getTokVar $1)       }
     | '(' Exp ')'              { Brack (getPos $1) $2                   }

{
newtype Parser a = Parser { unP :: FilePath -> [Token Pos] -> IO (Either String a) }

instance Monad Parser where
  return x       = Parser (\_ _ -> return (Right x))
  Parser h >>= k = Parser (\f ts -> do er <- h f ts
                                       case er of
                                         Left  e -> return $ Left e
                                         Right r -> unP (k r) f ts)
  fail s = Parser (\_ _ -> return (Left s))

happyError :: Parser a
happyError = Parser $ \_ ts -> return $ failAt ts

parseError :: Token Pos -> Parser a
parseError t = Parser (\_ _ -> return $ failAt [t])

failAt :: [Token Pos] -> Either String a
failAt (t:_) = Left $ show (getPos t) ++ ": Parse error at <" ++ show t ++ ">"

lexer :: (Token Pos -> Parser a) -> Parser a
lexer cont = Parser (\f ts ->
        case ts of
           []       -> unP (cont (TokenEOF (endPos f))) f []
           (t : ts) -> unP (cont t)                     f ts)

parse :: FilePath -> String -> IO (Either String Exp)
parse f s = unP parseSAW f (lexSAW f s)

data Exp = Let   Pos String Exp Exp
         | Var   Pos String
         | Plus  Pos Exp Exp
         | Num   Pos Int
         | Brack Pos Exp
         deriving Show
}
