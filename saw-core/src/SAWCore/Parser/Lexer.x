{
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
{-# OPTIONS_GHC -fno-warn-tabs #-}

{- |
Module      : SAWCore.Parser.Lexer
Copyright   : Galois, Inc. 2012-2014
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Parser.Lexer
  ( Token(..)
  , LexerMessage(..)
  , LexerState
  , initialLexerState
  , lexSAWCore
  ) where

import Codec.Binary.UTF8.Generic ()
import Control.Monad.State.Strict
import qualified Data.Text as Text
import qualified Data.Text.Lazy as LText
import Data.Word (Word8)
import Data.Bits
import qualified Data.Char as Char
import Numeric.Natural

import SAWCore.Parser.Position

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
$binit     = 0-1
$octit     = 0-7
$hexit     = [0-9 A-F a-f]
$large     = [A-Z $uniupper]
$small     = [a-z $unilower]
$alpha     = [$small $large]
$symbol    = [\!\#\$\%\&\*\+\.\/\<\=\>\?\@\\\^\|\-\~ $unisymbol] # [$special \_\:\"\']
$graphic   = [$alpha $symbol $digit $special \:\"\'\_]
$charesc   = [abfnrtv\\\"\'\&]
$cntrl     = [A-Z \@\[\\\]\^\_]
@ascii     = \^ $cntrl | NUL | SOH | STX | ETX | EOT | ENQ | ACK
           | BEL | BS | HT | LF | VT | FF | CR | SO | SI | DLE
           | DC1 | DC2 | DC3 | DC4 | NAK | SYN | ETB | CAN | EM
           | SUB | ESC | FS | GS | RS | US | SP | DEL
@num       = $digit+
@decimal   = $digit+
@binary    = $binit+
@octal     = $octit+
@hex       = $hexit+
$idfirst   = [$alpha \_]
$idchar    = [$alpha $digit $unidigit $unitick \' \_]
@ident     = $idfirst $idchar*
@punct = "#" | "," | "->" | "." | ";" | ":" | "=" | "*"
       | "\" | "(" | ")" | "[" | "]" | "{" | "}" | "|"
       | "@" | "!?" | "`" | "::" | ":|:" | "|:"
@keywords = "data" | "hiding" | "import" | "module" | "injectCode"
          | "sort" | "isort" | "qsort" | "qisort"
          | "Prop" | "where" | "primitive" | "axiom" | "let" | "in"
@key = @punct | @keywords

@escape      = \\ ($charesc | @ascii | @decimal | o @octal | x @hex)
@gap         = \\ $gapchar+ \\
@string      = $graphic # [\"\\] | " " | @escape | @gap

sawTokens :-

$whitechar+;
\n          { \_ -> TEOL }
"--"        { \_ -> TCommentL }
"{-"        { \_ -> TCommentS }
"-}"        { \_ -> TCommentE }
\" @string* \" { TString . read   }
@num        { TNat . read }
"0x"@hex    { TBitvector . readHexBV . drop 2 }
"0b"[0-1]+  { TBitvector . readBinBV . drop 2 }
@key        { TKey }
@ident      { TIdent }

@ident "#rec" [0-9]*
            { TRecursor . parseRecursor }
@ident "#ind"
            { TInductor . dropIndSuffix }
.           { TIllegal }

{
data Token
  = TIdent { tokIdent :: String }   -- ^ Identifier
  | TRecursor { tokRecursor :: (String, Natural) }   -- ^ Recursor
  | TInductor { tokInductor :: String }   -- ^ Recursor at sort Prop
  | TNat { tokNat :: Natural }  -- ^ Natural number literal
  | TBitvector { tokBits :: [Bool] } -- ^ Bitvector literal
  | TString { tokString :: String } -- ^ String literal
  | TKey String     -- ^ Keyword or predefined symbol
  | TEnd            -- ^ End of file.
  | TCommentS       -- ^ Start of a block comment
  | TCommentE       -- ^ End of a block comment
  | TCommentL       -- ^ Start of a line comment
  | TEOL            -- ^ End of line (ends a line comment)
  | TIllegal String -- ^ Illegal character
  deriving (Show)

data LexerMessage = InvalidInput Text.Text | UnclosedComment | MissingEOL

data Buffer = Buffer Char !LText.Text
type AlexInput = PosPair Buffer

-- Wrap the input type for export, in case we end up wanting other state
type LexerState = AlexInput

-- | Parse a recursor identifier with "#rec" followed by a Natural.
-- A missing number is treated as 0.
parseRecursor :: String -> (String, Natural)
parseRecursor str =
  case span (/= '#') str of
    (name, rest) -> (name, parseNatural (drop 4 rest))

-- | Parse a string of decimal digits as a Natural.
-- The empty string maps to 0.
parseNatural :: String -> Natural
parseNatural "" = 0
parseNatural str = read str

-- | Remove the "#ind" suffix of an inductor string
dropIndSuffix :: String -> String
dropIndSuffix str = take (length str - 4) str

-- | Convert a hexadecimal string to a big endian list of bits
readHexBV :: String -> [Bool]
readHexBV =
  concatMap (\c -> let i = Char.digitToInt c in
                   [testBit i 3, testBit i 2, testBit i 1, testBit i 0])

-- | Convert a binary string to a big endian list of bits
readBinBV :: String -> [Bool]
readBinBV = map (\c -> c == '1')

initialAlexInput :: FilePath -> FilePath -> LText.Text -> AlexInput
initialAlexInput base path b = PosPair pos input
  where pos = Pos { posBase = base
                  , posPath = path
                  , posLine = 1
                  , posCol = 0
                  }
        prevChar = error "internal: runLexer prev char undefined"
        input = Buffer prevChar b

initialLexerState :: FilePath -> FilePath -> LText.Text -> LexerState
initialLexerState = initialAlexInput

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar (val -> Buffer c _) = c

-- feed alex a byte describing the current char
-- this came from Cryptol's lexer, which came from LexerUtils, which
-- adapted the technique used in GHC's lexer.
--
-- FUTURE: it would be nice to share this with the saw-script lexer
-- (and maybe also the Cryptol lexer) instead of pasting it repeatedly
byteForChar :: Char -> Word8
byteForChar c
  | c <= '\7' = non_graphic
  | Char.isAscii c = fromIntegral (Char.ord c)
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

-- Get the next byte to feed alex, where the byte is a character class
-- describing the current character as generated above. Update the
-- input state accordingly.
alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte (PosPair pos (Buffer _ txt)) = fmap fn (LText.uncons txt)
  where fn (c, txt') = (byte, PosPair pos' (Buffer c txt'))
          where byte  = byteForChar c
                isNew = c == '\n'
                pos'  = if isNew then incLine pos else incCol pos

-- this is here mostly to shorten the type signatures
type MsgList = [(Pos, LexerMessage)]

-- Get the next token.
--
-- Recurses until we have one. If we get AlexError, concatenate all the
-- adjacent invalid characters into a single error message.
--
-- Returns the updated input state, a list of messages, and the token.
scanToken :: AlexInput -> MsgList -> (AlexInput, MsgList, PosPair Token)
scanToken inp0 errors0 =
  let go inp errors pendingError =
        let (PosPair p (Buffer _ txt)) = inp
            finishAnyError = case pendingError of
                Nothing -> errors
                Just (pos, chars) ->
                    let badText = Text.pack $ reverse chars in
                    (pos, InvalidInput badText) : errors
            end =
                (inp, finishAnyError, PosPair p TEnd)
        in case alexScan inp 0 of
            AlexEOF ->
                end
            AlexError _ -> case alexGetByte inp of
              Nothing ->
                  end
              Just (_byte, inp') ->
                -- ignore the classification byte; get the actual failing char
                let badChar = alexInputPrevChar inp' in
                case pendingError of
                    Nothing ->
                        go inp' errors (Just (p, [badChar]))
                    Just (pos, badChars) ->
                        go inp' errors (Just (pos, badChar : badChars))
            AlexSkip inp' _ ->
                go inp' finishAnyError Nothing
            AlexToken inp' l act ->
                let v = act (LText.unpack (LText.take (fromIntegral l) txt)) in
                (inp', finishAnyError, PosPair p v)
  in
  go inp0 errors0 Nothing

-- | State for processing comments.
--
-- CNone is the ground state (not in a comment)
--
-- CBlock startpos n is when we're within a block comment starting at
-- startpos, and n is the number of additional nested block comments
-- that have been opened.
--
-- CLine is when we're in a line (-- type) comment.
data CommentState = CNone | CBlock Pos !Int | CLine

-- Get the next token, dropping comments.
--
-- Recurses until we get one.
--
-- Returns the updated input state, a list of messages, and the token.
scanSkipComments :: AlexInput -> (AlexInput, MsgList, PosPair Token)
scanSkipComments inp0 =
  let go state inp errors =
        let (inp', errors', tok) = scanToken inp errors
            again nextState = go nextState inp' errors'
            againWith nextState err = go nextState inp' (err : errors')
            accept = (inp', errors', tok)
            acceptWith err = (inp', err : errors', tok)
        in
        case state of
          CNone -> case val tok of
            TEnd ->
                -- plain EOF
                accept
            TCommentS ->
                -- open block-comment
                again (CBlock (pos tok) 0)
            TCommentE ->
                -- misplaced close-comment
                let err = (pos tok, InvalidInput "-}") in
                againWith CNone err
            TCommentL ->
                -- begin line-comment
                again CLine
            TEOL ->
                -- ordinary end-of-line, doesn't need to be seen downstream
                again CNone
            _ ->
                -- uncommented token, take it
                accept

          CBlock startpos depth -> case val tok of
            TEnd ->
                -- EOF in block comment
                let err = (startpos, UnclosedComment) in
                acceptWith err
            TCommentS ->
                -- nested open-comment; keep the original start position
                again (CBlock startpos (depth + 1))
            TCommentE
             | depth == 0 ->
                -- end outer block comment
                again CNone
             | otherwise ->
                -- end nested block comment
                again (CBlock startpos (depth - 1))
            _ ->
                -- anything else in a block comment; get another token
                again state

          CLine -> case val tok of
            TEnd ->
                -- EOF in line-comment; missing a newline, which is a warning
                let err = (pos tok, MissingEOL) in
                acceptWith err
            TEOL ->
                -- EOL ending the comment; drop it but end the comment
                again CNone
            _ ->
                -- anything else in a line comment; drop it
                again CLine
  in
  let (inp0', errors, tok) = go CNone inp0 [] in
  (inp0', reverse errors, tok)

-- Entry point, which has become vacuous (but that might change in the
-- future, so keep it around)
lexSAWCore :: AlexInput -> (AlexInput, MsgList, PosPair Token)
lexSAWCore inp = scanSkipComments inp

}
