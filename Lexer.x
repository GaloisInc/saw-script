{
{-# OPTIONS_GHC -fno-warn-name-shadowing     #-}
{-# OPTIONS_GHC -fno-warn-unused-matches     #-}
{-# OPTIONS_GHC -fno-warn-unused-binds       #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing     #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
module SAWScript.Lexer (lexSAW) where

import SAWScript.Token
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]

@reservedid = let|in
@reservedop = "+"

sawTokens :-

$white+                          ;
"--".*                           ;
let                              { const TokenLet      }
in                               { const TokenIn       }
$digit+                          { TokenInt . read     }
"+"                              { const TokenPlus     }
"("                              { const TokenOB       }
")"                              { const TokenCB       }
"="                              { const TokenEq       }
$alpha [$alpha $digit \_ \']*    { TokenVar            }
"\n"                             { const TokenNL       }
.                                { TokenUnknown . head }

{
lexSAW :: String -> [Token]
lexSAW = alexScanTokens
}
