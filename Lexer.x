{
{-# OPTIONS_GHC -fno-warn-name-shadowing     #-}
{-# OPTIONS_GHC -fno-warn-unused-matches     #-}
{-# OPTIONS_GHC -fno-warn-unused-binds       #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing     #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
module SAWScript.Lexer (lexSAW) where

import SAWScript.Token
import SAWScript.Utils
}

%wrapper "posn"

$digit = 0-9
$alpha = [a-zA-Z]

@reservedid = let|in
@reservedop = "+"

sawTokens :-

$white+                          ;
"\n"                             ;
"--".*                           ;
let                              { cnst TokenLet                   }
in                               { cnst TokenIn                    }
$digit+                          { \p s -> TokenInt p (read s)     }
"+"                              { cnst TokenPlus                  }
"("                              { cnst TokenOB                    }
")"                              { cnst TokenCB                    }
"="                              { cnst TokenEq                    }
$alpha [$alpha $digit \_ \']*    { TokenVar                        }
.                                { \p s -> TokenUnknown p (head s) }

{
cnst f p _ = f p

lexSAW :: FilePath -> String -> [Token Pos]
lexSAW f = map (fmap fixPos) . alexScanTokens
  where fixPos (AlexPn _ l c) = Pos f l c
}
