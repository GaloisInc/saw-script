{
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
{-# OPTIONS_GHC -fno-warn-tabs #-}

{- |
Module      : Verifier.SAW.Lexer
Copyright   : Galois, Inc. 2012-2014
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Lexer
  ( Token(..)
  , LexerMessage(..)
  , LexerState
  , initialLexerState
  , lexSAWCore
  ) where

import Codec.Binary.UTF8.Generic ()
import Control.Monad.State.Strict
import qualified Data.ByteString.Lazy as B
import qualified Data.ByteString.Lazy.UTF8 as BU
import Data.ByteString.Lazy.UTF8 (toString)
import Data.Word (Word8)
import Data.Bits
import Data.Char (digitToInt)
import Numeric.Natural

import Verifier.SAW.Position

}

$whitechar = [\ \t\r\f\v]
$gapchar   = [$whitechar \n]
$special   = [\(\)\,\;\[\]\`\{\}]
$digit     = 0-9
$binit     = 0-1
$octit     = 0-7
$hexit     = [0-9 A-F a-f]
$large     = [A-Z]
$small     = [a-z]
$alpha     = [$small $large]
$symbol    = [\!\#\$\%\&\*\+\.\/\<\=\>\?\@\\\^\|\-\~] # [$special \_\:\"\']
$graphic   = [$alpha $symbol $digit $special \:\"\'\_]
$charesc   = [abfnrtv\\\"\'\&]
$cntrl     = [$large \@\[\\\]\^\_]
@ascii     = \^ $cntrl | NUL | SOH | STX | ETX | EOT | ENQ | ACK
           | BEL | BS | HT | LF | VT | FF | CR | SO | SI | DLE
           | DC1 | DC2 | DC3 | DC4 | NAK | SYN | ETB | CAN | EM
           | SUB | ESC | FS | GS | RS | US | SP | DEL
@num       = $digit+
@decimal   = $digit+
@binary    = $binit+
@octal     = $octit+
@hex       = $hexit+
$idchar    = [a-z A-Z 0-9 \' \_]
@ident     = [a-z A-Z \_] $idchar*

@punct = "#" | "," | "->" | "." | ";" | ":" | "=" | "*"
       | "\" | "(" | ")" | "[" | "]" | "{" | "}" | "|"
@keywords = "data" | "hiding" | "import" | "module" | "injectCode"
          | "sort" | "isort" | "qsort" | "qisort"
          | "Prop" | "where" | "primitive" | "axiom"
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
@ident "#rec" { TRecursor . dropRecSuffix }
.           { TIllegal }

{
data Token
  = TIdent { tokIdent :: String }   -- ^ Identifier
  | TRecursor { tokRecursor :: String }   -- ^ Recursor
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

data LexerMessage = InvalidInput [Word8] | UnclosedComment | MissingEOL

data Buffer = Buffer Char !B.ByteString
type AlexInput = PosPair Buffer

-- Wrap the input type for export, in case we end up wanting other state
type LexerState = AlexInput

-- | Remove the "#rec" suffix of a recursor string
dropRecSuffix :: String -> String
dropRecSuffix str = take (length str - 4) str

-- | Convert a hexadecimal string to a big endian list of bits
readHexBV :: String -> [Bool]
readHexBV =
  concatMap (\c -> let i = digitToInt c in
                   [testBit i 3, testBit i 2, testBit i 1, testBit i 0])

-- | Convert a binary string to a big endian list of bits
readBinBV :: String -> [Bool]
readBinBV = map (\c -> c == '1')

initialAlexInput :: FilePath -> FilePath -> B.ByteString -> AlexInput
initialAlexInput base path b = PosPair pos input
  where pos = Pos { posBase = base
                  , posPath = path
                  , posLine = 1
                  , posCol = 0
                  }
        prevChar = error "internal: runLexer prev char undefined"
        input = Buffer prevChar b

initialLexerState :: FilePath -> FilePath -> B.ByteString -> LexerState
initialLexerState = initialAlexInput

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar (val -> Buffer c _) = c

alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte (PosPair p (Buffer _ b)) = fmap fn (B.uncons b)
  where fn (w,b') = (w, PosPair p' (Buffer c b'))
          where c     = toEnum (fromIntegral w)
                isNew = c == '\n'
                p'    = if isNew then incLine p else incCol p

type MsgList = [(Pos, LexerMessage)]

scanToken :: AlexInput -> MsgList -> (AlexInput, MsgList, PosPair Token)
scanToken inp0 errors0 =
  let go inp errors pendingError =
        let (PosPair p (Buffer _ b)) = inp
            finishAnyError = case pendingError of
                Nothing -> errors
                Just (pos, chars) -> (pos, InvalidInput (reverse chars)) : errors
            end =
                (inp, finishAnyError, PosPair p TEnd)
        in case alexScan inp 0 of
            AlexEOF ->
                end
            AlexError _ -> case alexGetByte inp of
              Nothing ->
                  end
              Just (w, inp') -> case pendingError of
                Nothing ->
                    go inp' errors (Just (p, [w]))
                Just (pos, l) ->
                    go inp' errors (Just (pos, w:l))
            AlexSkip inp' _ ->
                go inp' finishAnyError Nothing
            AlexToken inp' l act ->
                let v = act (BU.toString (BU.take (fromIntegral l) b)) in
                (inp', finishAnyError, PosPair p v)
  in
  go inp0 errors0 Nothing

-- state for processing comments
data CommentState = CNone | CBlock Pos !Int | CLine

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
                let err = (pos tok, InvalidInput (fmap (fromIntegral . fromEnum) "-}")) in
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

lexSAWCore :: AlexInput -> (AlexInput, MsgList, PosPair Token)
lexSAWCore inp = scanSkipComments inp

}
