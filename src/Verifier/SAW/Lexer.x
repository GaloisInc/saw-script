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
  ( module Verifier.SAW.AST
  , Token(..)
  , ppToken
  , ParseError(..)
  , Parser
  , lexer
	, runParser
  , addError
  ) where

import Codec.Binary.UTF8.Generic ()
import Control.Monad.State.Strict
import qualified Data.ByteString.Lazy as B
import Data.ByteString.Lazy.UTF8 (toString)
import Data.Word (Word8)

import Verifier.SAW.AST

}

$alpha = [a-z A-Z]
$digit = [0-9]
$idchar = [$alpha $digit \' \_]
@num = $digit+
@varid = [$alpha \_] $idchar*
@punct = "(" | ")" | "->" | "." | ";" | "::" | "=" | "?" | "??" | "???" | "\\" | "{" | "}"
@keywords = "data" | "where"
@key = @punct | @keywords

sawTokens :-

$white+; 
"--".*;
"{-"        { \_ -> TCmntS }
"-}"        { \_ -> TCmntE }
@num        { TNat . read }
@key        { TKey }
@varid      { TSym }
.           { TIllegal }


{
data Token
  = TSym { tokSym :: String }   -- ^ Start of a variable.
  | TNat { tokNat :: Integer }  -- ^ Natural number literal
  | TKey String    -- ^ Keyword or predefined symbol
  | TEnd           -- ^ End of file.
  | TCmntS         -- ^ Start of a block comment
  | TCmntE         -- ^ End of a block comment. 
  | TIllegal String -- ^ Illegal character
  deriving (Show)

ppToken :: Token -> String
ppToken tkn = 
  case tkn of
    TSym s -> s
    TNat n -> show n
    TKey s -> s
    TEnd -> "END"
    TCmntS -> "XXXS"
    TCmntE -> "XXXE"
    TIllegal s -> "illegal " ++ show s

data ParseError
  = UnexpectedLex [Word8]
  | UnexpectedEndOfBlockComment
  | UnexpectedToken Token
  | ParseError String
  | UnexpectedEnd
  deriving (Show)

data Buffer = Buffer Char !B.ByteString

type AlexInput = Positioned Buffer

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar (val -> Buffer c _) = c

alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte (Positioned p (Buffer _ b)) = fmap fn (B.uncons b)
  where fn (w,b') = (w, Positioned p' (Buffer c b'))
          where c     = toEnum (fromIntegral w)
                isNew = c == '\n'
                p'    = if isNew then incLine p else incCol p

type ErrorList = [Positioned ParseError]

data ParserState = PS { psInput :: AlexInput, psErrors :: [Positioned ParseError] }

newtype Parser a = Parser { _unParser :: State ParserState a }
  deriving (Functor, Monad)

addError :: Pos -> ParseError -> Parser ()
addError p err = Parser $ modify $ \s -> s { psErrors = Positioned p err : psErrors s }

setInput :: AlexInput -> Parser ()
setInput inp = Parser $ modify $ \s -> s { psInput = inp }

parsePos :: Parser Pos
parsePos = Parser $ gets (pos . psInput)


lexer :: (Positioned Token -> Parser a) -> Parser a
lexer f = do
  let go prevErr next = do
        let addErrors =
              case prevErr of
                Nothing -> return ()
                Just (po,l) -> addError po (UnexpectedLex (reverse l))
        s <- Parser get
        let inp@(Positioned p (Buffer _ b)) = psInput s
            end = addErrors >> next (Positioned p TEnd)
        case alexScan inp 0 of
          AlexEOF -> end
          AlexError _ ->
            case alexGetByte inp of
              Just (w,inp') -> do
                setInput inp'
                case prevErr of
                  Nothing -> go (Just (p,[w])) next
                  Just (po,l) -> go (Just (po,w:l)) next
              Nothing -> end
          AlexSkip inp' _ -> addErrors >> setInput inp' >> go Nothing next
          AlexToken inp' l act -> do
            addErrors
            setInput inp'
            let v = act (toString (B.take (fromIntegral l) b))
            next (Positioned p v)
  let read i tkn =
        case val tkn of
          TCmntS -> go Nothing (read (i+1))
          TCmntE | i > 0 -> go Nothing (read (i-1))
                 | otherwise -> do
                     addError (pos tkn) (UnexpectedLex (fmap (fromIntegral . fromEnum) "-}"))
                     go Nothing (read 0)
          _ | i > 0 -> go Nothing (read i)
            | otherwise -> f tkn 
  go Nothing (read (0::Integer))

runParser :: FilePath -> B.ByteString -> Parser a -> (a,ErrorList)
runParser path b (Parser m) = (r, reverse (psErrors s))
  where prevChar = error "internal: runLexer prev char undefined"
        pos = Pos { posPath = path, posLine = 1, posCol = 0 }
        input = Buffer prevChar b
        initState = PS { psInput = Positioned pos input, psErrors = [] }
        (r,s) = runState m initState
}