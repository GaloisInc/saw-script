{
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-lazy-unlifted-bindings #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
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

import Verifier.SAW.Position

}

$idchar = [a-z A-Z 0-9 \' \_]
@num = [0-9]+
@var = [a-z] $idchar*
@unvar = [\_]+ ([a-z] $idchar*)? 
@con = [A-Z] $idchar*

@punct = "#" | "," | "->" | "." | ".." | ";" | "::" | "=" | "?" | "??" | "???"
       | "\" | "(" | ")" | "[" | "]" | "{" | "}"
@keywords = "as" | "data" | "hiding" | "import" | "in" | "let" | "module"
          | "qualified" | "sort" | "where"
@key = @punct | @keywords

sawTokens :-

$white+; 
"--".*;
"{-"        { \_ -> TCmntS }
"-}"        { \_ -> TCmntE }
@num        { TNat . read }
@key        { TKey }
@var        { TVar }
@unvar      { TUnVar }
@con        { TCon }
.           { TIllegal }

{
data Token
  = TVar { tokVar :: String }   -- ^ Variable identifier (lower case).
  | TUnVar { tokVar :: String } -- ^ Variable identifier prefixed by underscore.
  | TCon { tokCon :: String }   -- ^ Start of a constructor (may be pattern matched). 
  | TNat { tokNat :: Integer }  -- ^ Natural number literal
  | TKey String     -- ^ Keyword or predefined symbol
  | TEnd            -- ^ End of file.
  | TCmntS          -- ^ Start of a block comment
  | TCmntE          -- ^ End of a block comment. 
  | TIllegal String -- ^ Illegal character
  deriving (Show)

ppToken :: Token -> String
ppToken tkn = 
  case tkn of
    TVar s -> s
    TUnVar s -> s
    TCon s -> s   
    TNat n -> show n
    TKey s -> s
    TEnd -> "END"
    TCmntS -> "XXXS"
    TCmntE -> "XXXE"
    TIllegal s -> "illegal " ++ show s

data Buffer = Buffer Char !B.ByteString

type AlexInput = PosPair Buffer

initialAlexInput :: FilePath -> B.ByteString -> AlexInput
initialAlexInput path b = PosPair pos input
  where pos = Pos { posPath = path, posLine = 1, posCol = 0 }
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