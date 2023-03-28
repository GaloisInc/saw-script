{
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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
  ( module Verifier.SAW.Position
  , Token(..)
  , ppToken
  , Buffer(..)
  , AlexInput
  , initialAlexInput
  , alexScan
  , alexGetByte
  , AlexReturn(..)
  ) where

import Codec.Binary.UTF8.Generic ()
import Control.Monad.State.Strict
import qualified Data.ByteString.Lazy as B
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

ppToken :: Token -> String
ppToken tkn =
  case tkn of
    TIdent s -> s
    TRecursor s -> s ++ "#rec"
    TNat n -> show n
    TBitvector bits ->
      "0b" ++ map (\b -> if b then '1' else '0') bits
    TString s -> show s
    TKey s -> s
    TEnd -> "END"
    TCmntS -> "XXXS"
    TCmntE -> "XXXE"
    TIllegal s -> "illegal " ++ show s

data Buffer = Buffer Char !B.ByteString

type AlexInput = PosPair Buffer

initialAlexInput :: FilePath -> FilePath -> B.ByteString -> AlexInput
initialAlexInput base path b = PosPair pos input
  where pos = Pos { posBase = base
                  , posPath = path
                  , posLine = 1
                  , posCol = 0
                  }
        prevChar = error "internal: runLexer prev char undefined"
        input = Buffer prevChar b

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar (val -> Buffer c _) = c

alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte (PosPair p (Buffer _ b)) = fmap fn (B.uncons b)
  where fn (w,b') = (w, PosPair p' (Buffer c b'))
          where c     = toEnum (fromIntegral w)
                isNew = c == '\n'
                p'    = if isNew then incLine p else incCol p
}
