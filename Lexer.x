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

$whitechar = [ \t\n\r\f\v]
$special   = [\(\)\,\;\[\]\`\{\}]
$digit     = 0-9
$large     = [A-Z]
$small     = [a-z]
$alpha     = [$small $large]
$symbol    = [\!\#\$\%\&\*\+\.\/\<\=\>\?\@\\\^\|\-\~] # [$special \_\:\"\']
$graphic   = [$alpha $symbol $digit $special \:\"\']
$octit     = 0-7
$hexit     = [0-9 A-F a-f]
$idchar    = [$alpha $digit \']
$symchar   = [$symbol \:]
$nl        = [\n\r]

@reservedid  = import
@reservedop  = "+"
@varid       = $alpha $idchar*
@decimal     = $digit+
@octal       = $octit+
@hexadecimal = $hexit
$cntrl       = [$large \@\[\\\]\^\_]
@ascii       = \^ $cntrl | NUL | SOH | STX | ETX | EOT | ENQ | ACK
             | BEL | BS | HT | LF | VT | FF | CR | SO | SI | DLE
	     | DC1 | DC2 | DC3 | DC4 | NAK | SYN | ETB | CAN | EM
	     | SUB | ESC | FS | GS | RS | US | SP | DEL
$charesc     = [abfnrtv\\\"\'\&]
@escape      = \\ ($charesc | @ascii | @decimal | o @octal | x @hexadecimal)
@gap         = \\ $whitechar+ \\
@string      = $graphic # [\"\\] | " " | @escape | @gap

sawTokens :-

$white+                          ;
"\n"                             ;
"//".*                           ;
@reservedid			 { mkReserved      }
";"                              { cnst TSemi      }
@varid				 { TVar            }
\" @string* \"			 { TLit `via` read }
.                                { TUnknown        }

{
cnst f p _ = f p
via c g p s = c p (g s)
mkReserved p "import" = TImport p
mkReserved p s        = TUnknown p s

lexSAW :: FilePath -> String -> [Token Pos]
lexSAW f = map (fmap fixPos) . alexScanTokens
  where fixPos (AlexPn _ l c) = Pos f l c
}
