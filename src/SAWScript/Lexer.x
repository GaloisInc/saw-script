{
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing     #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing     #-}
{-# OPTIONS_GHC -fno-warn-unused-binds       #-}
{-# OPTIONS_GHC -fno-warn-unused-imports     #-}
{-# OPTIONS_GHC -fno-warn-unused-matches     #-}
{-# OPTIONS_GHC -fno-warn-tabs               #-}
{-# LANGUAGE BangPatterns #-}
module SAWScript.Lexer
  ( scan
  , lexSAW
  ) where

import SAWScript.Token
import SAWScript.Panic (panic)
import SAWScript.Position
import SAWScript.Utils

import Numeric (readInt)
import Data.Char (ord)
import qualified Data.Char as Char
import Data.List
import Data.Word (Word8)

}

-- Caution: these must match the magic numbers in byteForChar below
$uniupper       = \x1
$unilower       = \x2
$unidigit       = \x3
$unisymbol      = \x4
$unispace       = \x5
$uniother       = \x6
$unitick        = \x7

$whitechar = [\ \t\n\r\f\v $unispace]
$special   = [\(\)\,\;\[\]\`\{\}]
$digit     = 0-9
$large     = [A-Z $uniupper]
$small     = [a-z $unilower]
$alpha     = [$small $large]
$symbol    = [\!\#\$\%\&\*\+\.\/\<\=\>\?\@\\\^\|\-\~ $unisymbol] # [$special \_\:\"\']
$graphic   = [$alpha $symbol $digit $special \:\"\'\_]
$binit     = 0-1
$octit     = 0-7
$hexit     = [0-9 A-F a-f]
$idfirst   = [$alpha \_]
$idchar    = [$alpha $digit $unidigit $unitick \' \_]
$codechar  = [$graphic $whitechar]

@reservedid  = import|and|let|rec|in|do|if|then|else|as|hiding|typedef
             |CryptolSetup|JavaSetup|LLVMSetup|MIRSetup|ProofScript|TopLevel|CrucibleSetup
             |Int|String|Term|Type|Bool|AIG|CFG
             |CrucibleMethodSpec|LLVMSpec|JVMMethodSpec|JVMSpec|MIRSpec

@punct       = "," | ";" | "(" | ")" | ":" | "::" | "[" | "]" | "<-" | "->"
             | "=" | "{" | "}" | "." | "\"
@reservedop  = "~"  | "-" | "*" | "+" | "/" | "%" | ">>" | "<<" | "|" | "&"
             | "^" | "#"  | "==" | "!=" | ">=" | ">" | "<=" |"<" | "&&"
             | "||" | "==>" | "@"
@varid       = $idfirst $idchar*
@decimal     = $digit+
@binary      = $binit+
@octal       = $octit+
@hexadecimal = $hexit+
$cntrl       = [$large \@\[\\\]\^\_]
@ascii       = \^ $cntrl | NUL | SOH | STX | ETX | EOT | ENQ | ACK
             | BEL | BS | HT | LF | VT | FF | CR | SO | SI | DLE
             | DC1 | DC2 | DC3 | DC4 | NAK | SYN | ETB | CAN | EM
             | SUB | ESC | FS | GS | RS | US | SP | DEL
$charesc     = [abfnrtv\\\"\'\&]
@escape      = \\ ($charesc | @ascii | @decimal | o @octal | x @hexadecimal)
@gap         = \\ $whitechar+ \\
@string      = $graphic # [\"\\] | " " | @escape | @gap
@code        = ($codechar # \}) | \} ($codechar # \})
@ctype       = ($codechar # \|) | \| ($codechar # \})
@num         = @decimal | 0[bB] @binary | 0[oO] @octal | 0[xX] @hexadecimal

sawTokens :-

$white+                          ;
"//".*                           ;
"/*"                             { cnst TCmntS           }
"*/"                             { cnst TCmntE           }
@reservedid                      { TReserved             }
@punct                           { TPunct                }
@reservedop                      { TOp                   }
@varid                           { TVar                  }
\" @string* \"                   { TLit  `via'` read     }
\{\{ @code* \}\}                 { TCode `via'` readCode }
\{\| @ctype* \|\}                { TCType`via'` readCode }
@decimal                         { TNum  `via`  read     }
0[bB] @binary                    { TNum  `via`  readBin  }
0[oO] @octal                     { TNum  `via`  read     }
0[xX] @hexadecimal               { TNum  `via`  read     }
.                                { TUnknown              }

{

-- token helpers

cnst f p s   = f p s
via  c g p s = c p s (g s)
via' c g p s = c p (g s)

-- drop the {{ }} or {| |} from Cryptol blocks
readCode :: String -> String
readCode = reverse . drop 2 . reverse . drop 2

-- read a binary integer
readBin :: String -> Integer
readBin s = case readInt 2 isDigit cvt s' of
              [(a, "")] -> a
              _         -> error $ "Cannot read a binary number from: " ++ show s
  where cvt c = ord c - ord '0'
        isDigit = (`elem` "01")
        s' | "0b" `isPrefixOf` s = drop 2 s
           | "0B" `isPrefixOf` s = drop 2 s
           | True                = s


-- alex support and lexer mechanism

-- current position
data AlexPos = AlexPos {
    apLine :: !Int,
    apCol :: !Int
  }

-- input state
type AlexInput = (
    AlexPos,    -- ^ Current position
    String      -- ^ Remaining input
  )

-- initial position
startPos :: AlexPos
startPos = AlexPos { apLine = 1, apCol = 1 }

-- feed alex a byte describing the current char
-- this came from Cryptol's lexer, which came from LexerUtils, which
-- adapted the technique used in GHC's lexer.
byteForChar :: Char -> Word8
byteForChar c
  | c <= '\7' = non_graphic
  | Char.isAscii c = fromIntegral (ord c)
  | otherwise = case Char.generalCategory c of
      Char.LowercaseLetter       -> lower
      Char.OtherLetter           -> lower
      Char.UppercaseLetter       -> upper
      Char.TitlecaseLetter       -> upper
      Char.DecimalNumber         -> digit
      Char.OtherNumber           -> digit
      Char.ConnectorPunctuation  -> symbol
      Char.DashPunctuation       -> symbol
      Char.OtherPunctuation      -> symbol
      Char.MathSymbol            -> symbol
      Char.CurrencySymbol        -> symbol
      Char.ModifierSymbol        -> symbol
      Char.OtherSymbol           -> symbol
      Char.Space                 -> sp
      Char.ModifierLetter        -> other
      Char.NonSpacingMark        -> other
      Char.SpacingCombiningMark  -> other
      Char.EnclosingMark         -> other
      Char.LetterNumber          -> other
      Char.OpenPunctuation       -> other
      Char.ClosePunctuation      -> other
      Char.InitialQuote          -> other
      Char.FinalQuote            -> tick
      _                          -> non_graphic
  where
  -- CAUTION: these must match the $uni* values at the top of the file
  non_graphic     = 0
  upper           = 1
  lower           = 2
  digit           = 3
  symbol          = 4
  sp              = 5
  other           = 6
  tick            = 7

-- input handler for alex
alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte (pos, text) = case text of
  [] -> Nothing
  c : text' -> Just (byteForChar c, (move pos c, text'))
    where
      move pos c = case c of
          '\n' -> AlexPos { apLine = apLine pos + 1, apCol = 1 }
          _ -> pos { apCol = apCol pos + 1 }

-- the lexer we're generating doesn't use this hook
alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar _ = panic "Lexer" ["alexInputPrevChar"]

-- read the text of a file, passing in the filename for use in positions
scanTokens :: FilePath -> String -> [Token Pos]
scanTokens filename str = go (startPos, str)
  where
    fillPos pos height width =
        let startLine = apLine pos
            startCol = apCol pos
            endLine = startLine + height
            endCol = startCol + width
        in
        Range filename startLine startCol endLine endCol

    go inp@(pos, str) = case alexScan inp 0 of
        AlexEOF ->
            let pos' = fillPos pos 0 0 in
            [TEOF pos' "EOF"]
        AlexError (pos, _) ->
            let line' = show $ apLine pos
                col' = show $ apCol pos
            in
            error $ line' ++ ":" ++ col' ++ ": unspecified lexical error"
        AlexSkip inp' len ->
            go inp'
        AlexToken inp' len act ->
            let text = take len str
                (height, width) = case reverse $ lines text of
                    [] -> (0, 0)
                    [line] -> (0, length line)
                    last : lines -> (length lines, length last)
                pos' = fillPos pos height width
            in
            act pos' text : go inp'

-- postprocess to drop comments (this allows comments to be nested)
dropComments :: [Token Pos] -> [Token Pos]
dropComments = go 0
  where go :: Int -> [Token Pos] -> [Token Pos]
        go _  []                 = []
        go !i (TCmntS _ _ : ts)  = go (i+1) ts
        go !i (TCmntE _ _ : ts)
         | i > 0                 = go (i-1) ts
        go !i (t : ts)
         | i /= 0                = go i ts
         | True                  = t : go i ts

-- entry point
lexSAW :: FilePath -> String -> [Token Pos]
lexSAW f text = dropComments $ scanTokens f text

-- alternate monadic entry point (XXX: does this have any value?)
scan :: Monad m => FilePath -> String -> m [Token Pos]
scan f = return . lexSAW f
}
