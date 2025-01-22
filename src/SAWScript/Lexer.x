{
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing     #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing     #-}
{-# OPTIONS_GHC -fno-warn-unused-binds       #-}
{-# OPTIONS_GHC -fno-warn-unused-imports     #-}
{-# OPTIONS_GHC -fno-warn-unused-matches     #-}
{-# OPTIONS_GHC -fno-warn-tabs               #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
module SAWScript.Lexer
  ( scan
  , lexSAW
  ) where

import SAWScript.Options (Verbosity(..))
import SAWScript.Token
import SAWScript.Panic (panic)
import SAWScript.Position
import SAWScript.Utils

import Numeric (readInt)
import Data.Char (ord)
import qualified Data.Char as Char
import Data.List
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Text (Text)
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
@gap         = \\ $gapchar+ \\
@string      = $graphic # [\"\\] | " " | @escape | @gap
@code        = ($codechar # \}) | \} ($codechar # \})
@ctype       = ($codechar # \|) | \| ($codechar # \})
@num         = @decimal | 0[bB] @binary | 0[oO] @octal | 0[xX] @hexadecimal

sawTokens :-

\n                               { plain          TEOL      }
"//"                             { plain          TCommentL }
"/*"                             { plain          TCommentS }
"*/"                             { plain          TCommentE }
$whitechar+                      ;
@reservedid                      { plain          TReserved }
@punct                           { plain          TPunct    }
@reservedop                      { plain          TOp       }
@varid                           { plain          TVar      }
\" @string* \"                   { xform read'    TLit      }
\{\{ @code* \}\}                 { xform readCode TCode     }
\{\| @ctype* \|\}                { xform readCode TCType    }
@decimal                         { addon read'    TNum      }
0[bB] @binary                    { addon readBin  TNum      }
0[oO] @octal                     { addon read'    TNum      }
0[xX] @hexadecimal               { addon read'    TNum      }
.                                { plain          TUnknown  }

{

-- token helpers

plain ::                   (Pos -> Text -> Token Pos)   -> Pos -> Text -> Token Pos
xform :: (Text -> Text) -> (Pos -> Text -> Token Pos)   -> Pos -> Text -> Token Pos
addon :: (Text -> a) -> (Pos -> Text -> a -> Token Pos) -> Pos -> Text -> Token Pos

plain   tok pos txt = tok pos txt         -- ^ just the contents
xform f tok pos txt = tok pos (f txt)     -- ^ transform contents
addon f tok pos txt = tok pos txt (f txt) -- ^ also variant contents

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
    Nothing -> panic "Lexer" ["Failed to decode string or number literal", txt']
  where txt' = Text.unpack txt

-- drop the {{ }} or {| |} from Cryptol blocks
readCode :: Text -> Text
readCode txt = Text.drop 2 $ Text.dropEnd 2 txt

-- read a binary integer
readBin :: Text -> Integer
readBin s = case readInt 2 isDigit cvt (Text.unpack s') of
              [(a, "")] -> a
              _         -> error $ "Cannot read a binary number from: " ++ show s
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
alexGetByte (pos, text) = fmap doGet $ Text.uncons text
    where
      doGet (c, text') = (byteForChar c, (move pos c, text'))
      move pos c = case c of
          '\n' -> AlexPos { apLine = apLine pos + 1, apCol = 1 }
          _ -> pos { apCol = apCol pos + 1 }

-- the lexer we're generating doesn't use this hook
alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar _ = panic "Lexer" ["alexInputPrevChar"]

-- read the text of a file, passing in the filename for use in positions
scanTokens :: FilePath -> Text -> [Token Pos]
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
            let text = Text.take len str
                (height, width) = case reverse $ Text.lines text of
                    [] -> (0, 0)
                    [line] -> (0, Text.length line)
                    last : lines -> (length lines, Text.length last)
                pos' = fillPos pos height width
            in
            act pos' text : go inp'

-- | State for processing comments.
--
-- CNone is the ground state (not in a comment)
--
-- CBlock startpos n is when we're within a block comment starting at
-- startpos, and n is the number of additional nested block comments
-- that have been opened.
--
-- CLine is when we're in a line (//-type) comment.
data CommentState = CNone | CBlock Pos !Int | CLine

-- | Type to hold a diagnostic message (error or warning).
--
-- This should cease to be needed once we clean out the message
-- printing infrastructure. It's here only to shorten the type
-- signatures below, and represents the possibility of having
-- generated a message.
type OptMsg = Maybe (Verbosity, Pos, Text)

-- | Postprocess to drop comments; this allows block comments to nest.
--
-- Also returns a message (error or warning) along with the updated
-- token list if there's an unclosed comment when we reach EOF. Since
-- we aren't in a monad here and can't print, dispatching the message
-- is the caller's responsibility.
dropComments :: [Token Pos] -> ([Token Pos], OptMsg)
dropComments = go CNone
  where go :: CommentState -> [Token Pos] -> ([Token Pos], OptMsg)
        go state ts = case ts of
          [] ->
            -- should always see TEOF before we hit the end
            panic "Lexer" ["dropComments: tokens ran out"]
          TEOF _ _ : _ : _ ->
            -- should only see TEOF at the end of the list
            panic "Lexer" ["dropComments: misplaced EOF in tokens"]

          t : ts' ->
            let take state' =
                    let (results, optmsg) = go state' ts' in
                    (t : results, optmsg)
                drop state' = go state' ts'
                finish = ([t], Nothing)
                finishWith msg = ([t], Just msg)
            in
            case state of
              CNone -> case t of
                TEOF _ _ ->
                    -- plain EOF
                    finish
                TCommentS pos _ ->
                    -- open block-comment
                    drop (CBlock pos 0)
                TCommentL _ _  ->
                    -- begin line-comment
                    drop CLine
                TEOL _ _ ->
                    -- ordinary EOL, doesn't need to be seen downstream; drop it
                    drop CNone
                _ ->
                    -- uncommented token, keep it
                    take CNone

              CBlock startpos depth -> case t of
                TEOF pos _ ->
                    -- EOF in /**/-comment; unclosed, which is an error
                    finishWith (Error, startpos, "Unclosed block comment")
                TCommentS _ _ ->
                    -- open nested comment, keep original start position
                    drop (CBlock startpos (depth + 1))
                TCommentE _ _
                 | depth == 0 ->
                     -- end outer block comment
                     drop CNone
                 | otherwise ->
                     -- end nested block comment
                     drop (CBlock startpos (depth - 1))
                _ ->
                     -- anything else in a block comment, drop it
                     -- (this includes any TCommentLs that come through)
                     drop state

              CLine -> case t of
                TEOF pos _ ->
                    -- EOF in //-comment; missing a newline
                    finishWith (Warn, pos, "Missing newline at end of file")
                TEOL _ _ ->
                    -- EOL ending a line comment, drop it
                    -- (EOLs aren't sent downstream)
                    drop CNone
                _ ->
                    -- anything else in a line comment, drop it
                    -- (this includes any TCommentS/TCommentE that appear)
                    drop CLine

-- entry point
lexSAW :: FilePath -> Text -> ([Token Pos], OptMsg)
lexSAW f text = dropComments $ scanTokens f text

-- alternate monadic entry point (XXX: does this have any value?)
scan :: Monad m => FilePath -> Text -> m ([Token Pos], OptMsg)
scan f = return . lexSAW f
}
