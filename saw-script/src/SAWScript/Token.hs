{- |
Module      : SAWScript.Token
Description : Token type for SAW-Script lexer.
Maintainer  : atomb
Stability   : provisional
-}

{-# LANGUAGE DeriveFunctor #-}
module SAWScript.Token where

import Data.Text (Text)

import SAWCentral.Position (Positioned(..))

-- | Lexer tokens for saw-script.
--
-- All tokens have tokStr carrying the matched text (even TEOF where
-- it doesn't entirely make sense) so that tokStr can be applied to
-- any variant of the type.
--
-- The comment and EOL tokens are internal to the lexer and not seen
-- downstream.
--
-- The tokens are:
--   TVar       variable/identifier
--   TQVar      qualified variable/identifier
--   TLit       string constant
--   TCode      Cryptol code block
--   TCType     Cryptol type bllock
--   TUnknown   Anything else that doesn't fit
--   TPunct     Punctuation tokens used in the grammar
--   TReserved  All reserved words
--   TOp        Punctuation tokens apparently not used in the grammar
--   TNum       Number
--   TCommentS  Start of a block comment
--   TCommentE  End of a block comment
--   TCommentL  Start of a line comment
--   TEOL       End of line
--   TEOF       End of file/input
--
-- FUTURE: many of these could stand to be renamed
--
data Token p = TVar      { tokPos :: p, tokStr :: Text                               }
             | TQVar     { tokPos :: p, tokStr :: Text, tokVars :: ([Text], Text)    }
             | TLit      { tokPos :: p, tokStr :: Text                               }
             | TCode     { tokPos :: p, tokStr :: Text                               }
             | TCType    { tokPos :: p, tokStr :: Text                               }
             | TUnknown  { tokPos :: p, tokStr :: Text                               }
             | TPunct    { tokPos :: p, tokStr :: Text                               }
             | TReserved { tokPos :: p, tokStr :: Text                               }
             | TOp       { tokPos :: p, tokStr :: Text                               }
             | TNum      { tokPos :: p, tokStr :: Text, tokNum :: Integer            }
             | TEOF      { tokPos :: p, tokStr :: Text                               }
             deriving (Show, Functor)

instance Positioned p => Positioned (Token p) where
  getPos = getPos . tokPos
