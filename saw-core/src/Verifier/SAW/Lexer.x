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
  , LexerError(..)
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

$whitechar = [ \t\n\r\f\v]
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
@gap         = \\ $whitechar+ \\
@string      = $graphic # [\"\\] | " " | @escape | @gap

sawTokens :-

$white+;
"--".*;
"{-"        { \_ -> TCmntS }
"-}"        { \_ -> TCmntE }
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
  | TCmntS          -- ^ Start of a block comment
  | TCmntE          -- ^ End of a block comment.
  | TIllegal String -- ^ Illegal character
  deriving (Show)

newtype LexerError = LexerError [Word8]

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

scanToken :: AlexInput -> (AlexInput, [(Pos, LexerError)], PosPair Token)
scanToken inp0 =
  let go :: AlexInput -> [(Pos, LexerError)] -> Maybe (Pos, [Word8]) -> (AlexInput, [(Pos, LexerError)], PosPair Token)
      go inp errors pendingError =
        let (PosPair p (Buffer _ b)) = inp
            finishAnyError =
              case pendingError of
                Nothing -> errors
                Just (pos, chars) -> (pos, LexerError (reverse chars)) : errors
            end =
              (inp, finishAnyError, PosPair p TEnd)
        in case alexScan inp 0 of
          AlexEOF -> end
          AlexError _ ->
            case alexGetByte inp of
              Just (w, inp') ->
                case pendingError of
                  Nothing -> go inp' errors (Just (p, [w]))
                  Just (pos, l) -> go inp' errors (Just (pos, w:l))
              Nothing -> end
          AlexSkip inp' _ ->
            go inp' finishAnyError Nothing
          AlexToken inp' l act ->
            let v = act (BU.toString (BU.take (fromIntegral l) b)) in
            (inp', finishAnyError, PosPair p v)
  in
  go inp0 [] Nothing

lexSAWCore :: AlexInput -> (AlexInput, [(Pos, LexerError)], PosPair Token)
lexSAWCore inp0 =
  let read :: Integer -> AlexInput -> [(Pos, LexerError)] -> Either () (AlexInput, [(Pos, LexerError)], PosPair Token)
      read i inp errors = do
        let (inp', moreErrors, tkn) = scanToken inp
            errors' = moreErrors ++ errors
        case val tkn of
          TCmntS ->
                read (i+1) inp' errors'
          TCmntE
            | i > 0 ->
                read (i-1) inp' errors'
            | otherwise -> do
                let err = (pos tkn, LexerError (fmap (fromIntegral . fromEnum) "-}"))
                read 0 inp' (err : errors')
          _ | i > 0 ->
                read i inp' errors'
            | otherwise ->
                return (inp', errors', tkn)
      result = do
        (inp0', errors, tok) <- read (0::Integer) inp0 []
        return (inp0', reverse errors, tok)
  in
  case result of
      Left () -> error "oops"
      Right result' -> result'
}
