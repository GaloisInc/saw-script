{
{-# LANGUAGE OverloadedStrings #-}
module SAWScript.Lexer
  ( scan
  , lexSAW
  ) where

import SAWCentral.Options (Verbosity(..))
import SAWScript.Token
import SAWScript.Panic (panic)
import SAWCentral.Position
import SAWCentral.Utils

import Numeric (readInt)
import Data.Char (ord)
import qualified Data.Char as Char
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Word (Word8)
import Text.Read (readMaybe)

}

-- Caution: these must match the magic numbers in byteForChar below
$uniupper       = \x1
$unilower       = \x2
$unidigit       = \x3
$unisymbol      = \x4
$unispace       = \x5
$uniother       = \x6
$unitick        = \x7

$whitechar = [\ \t\r\f\v $unispace]
$gapchar   = [$whitechar \n]
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
$codechar  = [$graphic $whitechar \n]

@reservedid  = import|submodule|and|let|rec|in|do|if|then|else|as|hiding|typedef
             |rebindable
             |ProofScript|TopLevel|CrucibleSetup
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
@gap         = \\ $gapchar+ \\
@string      = $graphic # [\"\\] | " " | @escape
@code        = ($codechar # \}) | \} ($codechar # \})
@ctype       = ($codechar # \|) | \| ($codechar # \})
@num         = @decimal | 0[bB] @binary | 0[oO] @octal | 0[xX] @hexadecimal

sawTokens :-

<0,comment,code,ctype> {
\/\*                             { startComment }
}

<comment> {
\*+\/                            { endComment   }
[^\*\/]+                         { addToComment }
\*                               { addToComment }
\/                               { addToComment }
\n                               { addToComment }
}

<0,code,ctype> "//".*            { startLineComment }
<0,code,ctype> \"                { startString }

<linecomment> \n                 { endLineComment }

<string> {
@string                          { addToString }
@gap                             ;
\"                               { endString   }
\n                               { lexFail "Invalid multiline string" }
\\.                              { lexFail "Invalid character escape in string" }
}

<0> {
$whitechar+                      ;
\n                               ;
@reservedid                      { plain          TReserved }
@punct                           { plain          TPunct    }
@reservedop                      { plain          TOp       }
@varid                           { plain          TVar      }
\{\{                             { startCode                }
\{\|                             { startCType               }
@decimal                         { addon read'    TNum      }
0[bB] @binary                    { addon readBin  TNum      }
0[oO] @octal                     { addon read'    TNum      }
0[xX] @hexadecimal               { addon read'    TNum      }
0[bB]                            { lexFail "binary literal with no contents" }
0[oO]                            { lexFail "octal literal with no contents" }
0[xX]                            { lexFail "hexadecimal literal with no contents" }
.                                { plain          TUnknown  }
}

<code> {
[^\}\/\*]+                       { addToCode }
\n                               { addToCode }
.                                { addToCode }
\}\}                             { endCode   }
}

<ctype> {
[^\|\}\/\*]+                     { addToCType }
\n                               { addToCType }
.                                { addToCType }
\|\}                             { endCType   }
}
{

-- token helpers

type Action = Pos -> Text -> LexS -> ([Token Pos], LexS)
plain ::                   (Pos -> Text -> Token Pos)   -> Action
xform :: (Text -> Text) -> (Pos -> Text -> Token Pos)   -> Action
addon :: (Text -> a) -> (Pos -> Text -> a -> Token Pos) -> Action
lexFail :: Text -> Action

addToComment, startComment, endComment :: Action
addToCode, startCode, endCode :: Action
addToString, startString, endString :: Action
addToCType, startCType, endCType :: Action

plain   tok pos txt = \s -> ([tok pos txt], s)         -- ^ just the contents
xform f tok pos txt = \s -> ([tok pos (f txt)], s)     -- ^ transform contents
addon f tok pos txt = \s -> ([tok pos txt (f txt)], s) -- ^ also variant contents
lexFail msg pos txt = \_ -> ([], LexFailed msg pos txt)

startComment p txt s = ([], InComment p stack chunks done')
  where (stack, chunks, done') = case s of
          Normal                 -> ([], [txt], Normal)
          InComment q qs cs done -> (q : qs, txt : cs, done)
          InCode q ctxt          -> ([], [txt], InCode q ctxt)
          InCType q ctxt         -> ([], [txt], InCType q ctxt)
          _                      -> panic "[Lexer] startComment" ["not in normal or cryptol block or comment"]

endComment _p txt s =
  case s of
    InComment f [] cs done     -> ([], addWhitespace f (Text.concat (reverse cs) <> txt) done)
    InComment _ (q:qs) cs done -> ([], InComment q qs (txt : cs) done)
    _                          -> panic "[Lexer] endComment" ["outside comment"]

addToComment _ txt s = ([], InComment p stack (txt : chunks) done')
  where
  (p, stack, chunks, done') =
     case s of
       InComment q qs cs done -> (q,qs,cs,done)
       _                   -> panic "[Lexer] addToComment" ["outside comment"]

startLineComment p txt s = ([], InLineComment p txt s)

endLineComment p txt s =
  case s of
    InLineComment _f cs done -> ([], addWhitespace p (cs <> txt) done)
    _                    -> panic "[Lexer] endLineComment" ["outside line comment"]

-- Cryptol is indentation-sensitive. Just deleting the comments could produce
-- unparsable Cryptol , so we replace the removed comments with matching
-- whitespace
addWhitespace p txt s@(InCode _q _x) = snd $ addToCode p (whiteout txt) s
addWhitespace p txt s@(InCType _q _x) = snd $ addToCType p (whiteout txt) s
addWhitespace _ _ s = s

whiteout = Text.map (\c -> if c == '\n' then '\n' else ' ')

startString p txt s = ([],InString p txt s)

endString pe txt s = case s of
  InString ps str done -> ([mkToken ps str], done)
  _               -> panic "[Lexer] endString" ["outside string"]
  where
  mkToken ps str = TLit (spanPos ps pe) (read' $ str `Text.append` txt)

addToString _ txt s = case s of
  InString p str done -> ([],InString p (str `Text.append` txt) done)
  _              -> panic "[Lexer] addToString" ["outside string"]

startCode p _ _ = ([],InCode p Text.empty)

endCode pe _ s = case s of
  InCode ps str -> ([TCode (spanPos ps pe) str], Normal)
  _               -> panic "[Lexer] endCode" ["outside code"]

addToCode _ txt s = case s of
  InCode p str -> ([],InCode p (str `Text.append` txt))
  _              -> panic "[Lexer] addToCode" ["outside code"]

startCType p _ _ = ([],InCType p Text.empty)

endCType pe _ s = case s of
  InCType ps str -> ([TCType (spanPos ps pe) str], Normal)
  _               -> panic "[Lexer] endCType" ["outside ctype"]

addToCType _ txt s = case s of
  InCType p str -> ([],InCType p (str `Text.append` txt))
  _              -> panic "[Lexer] addToCType" ["outside ctype"]

-- fetch a value via Read
--
-- XXX: we should not use this for string literals, because as much as
-- it's convenient to have the stdlib decode escape sequences for us,
-- the escape sequences available in SAWScript strings should properly
-- be defined by SAWScript (that is, explicitly here) and not by
-- what's in GHC's standard library.
--
-- FUTURE: it would be nice to get the source position into the panic
-- message in case it ever actually happens, but that seems difficult
-- to arrange.
read' :: Read a => Text -> a
read' txt = case readMaybe txt' of
    Just x -> x
    Nothing -> panic "Lexer" ["Failed to decode string or number literal", txt]
  where txt' = Text.unpack txt

-- read a binary integer
readBin :: Text -> Integer
readBin s = case readInt 2 isDigit cvt (Text.unpack s') of
              [(a, "")] -> a
              _         -> panic "Lexer" ["Cannot read a binary number from: ", s]
  where cvt c = ord c - ord '0'
        isDigit c = c == '0' || c == '1'
        s' | "0b" `Text.isPrefixOf` s = Text.drop 2 s
           | "0B" `Text.isPrefixOf` s = Text.drop 2 s
           | True                     = s


-- alex support and lexer mechanism

-- current position
data AlexPos = AlexPos {
    apLine :: !Int,
    apCol :: !Int
  }

-- input state
type AlexInput = (
    AlexPos,    -- ^ Current position
    Text        -- ^ Remaining input
  )

data LexS
  = Normal
  | InComment !Pos ![Pos] [Text] LexS
  | InLineComment !Pos Text LexS
  | InString !Pos Text LexS
  | InCode   !Pos Text
  | InCType  !Pos Text
  | LexFailed Text !Pos Text
  deriving (Show)

stateToInt Normal = 0
stateToInt (InComment {}) = comment
stateToInt (InLineComment {}) = linecomment
stateToInt (InString {}) = string
stateToInt (InCode {}) = code
stateToInt (InCType {}) = ctype
stateToInt (LexFailed msg pos _) = panic "stateToInt"
  [ "called on lex failure state, message"
  , Text.pack $ show msg
  , "position"
  , Text.pack $ show pos
  ]

-- initial position
initialPos :: AlexPos
initialPos = AlexPos { apLine = 1, apCol = 1 }

-- feed alex a byte describing the current char
-- this came from Cryptol's lexer, which came from LexerUtils, which
-- adapted the technique used in GHC's lexer.
--
-- FUTURE: it would be nice to share this with the saw-core lexer
-- (and maybe also the Cryptol lexer) instead of pasting it repeatedly
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
alexGetByte (pos, text) = fmap doGet $ Text.uncons text
    where
      doGet (c, text') = (byteForChar c, (move c, text'))
      move c = case c of
          '\n' -> AlexPos { apLine = apLine pos + 1, apCol = 1 }
          _ -> pos { apCol = apCol pos + 1 }

-- the lexer we're generating doesn't use this hook
alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar _ = panic "Lexer" ["alexInputPrevChar"]

-- read the text of a file, passing in the filename for use in positions
scanTokens :: FilePath -> Text -> LexResult
scanTokens filename str0 = go (initialPos, str0) Normal
  where
    fillPos pos height width =
        let startLine = apLine pos
            startCol = apCol pos
            endLine = startLine + height
            endCol = startCol + width
        in
        Range filename startLine startCol endLine endCol

    go inp@(strPos, str) s = case alexScan inp (stateToInt s) of
        AlexEOF -> let strPos' = fillPos strPos 0 0
                       tok = [TEOF strPos' "EOF"]
                   in case s of
            Normal ->
                Right (tok, Nothing)
            InLineComment _beginPos _ _ ->
                Right (tok, Just (Warn, strPos', "Missing newline at end of file"))
            InComment beginPos _ _ _ ->
                Left (Error, beginPos, "Unclosed block comment")
            InString beginPos _ _ ->
                Left (Error, beginPos, "Unterminated string")
            InCode beginPos _ ->
                Left (Error, beginPos, "Unclosed Cryptol block")
            InCType beginPos _ ->
                Left (Error, beginPos, "Unclosed Cryptol type block")
            LexFailed msg failPos _ -> -- should never happen, but this is its semantics anyway
                Left (Error, failPos, msg)
        AlexError (failPos, _) ->
            let line' = Text.pack $ show $ apLine failPos
                col' = Text.pack $ show $ apCol failPos
            in
            panic "Lexer" [line' <> ":" <> col' <> ": no possible token matched"]
        AlexSkip inp' _len ->
            go inp' s
        AlexToken inp' len act ->
            let text = Text.take len str
                (height, width) = case reverse $ Text.lines text of
                    [] -> (0, 0)
                    [line] -> (0, Text.length line)
                    last_ : rest -> (length rest, Text.length last_)
                strPos' = fillPos strPos height width
            in
            case act strPos' text s of
              (_t, LexFailed msg failPos _rest) -> Left (Error, failPos, msg)
              (t, s') -> case go inp' s' of
                Left x -> Left x
                Right (ts, mmsg) -> Right (t ++ ts, mmsg)

-- | Type to hold a diagnostic message (error or warning).
--
-- This should cease to be needed once we clean out the message
-- printing infrastructure. It's here only to shorten the type
-- signatures below, and represents the possibility of having
-- generated a message.
type DiagMsg = (Verbosity, Pos, Text)
type OptMsg = Maybe DiagMsg
type LexResult = Either DiagMsg ([Token Pos], OptMsg)

-- entry point
lexSAW :: FilePath -> Text -> LexResult
lexSAW f text = scanTokens f text

-- alternate monadic entry point (XXX: does this have any value?)
scan :: Monad m => FilePath -> Text -> m LexResult
scan f = return . lexSAW f
}
