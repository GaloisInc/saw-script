{- |
Module      : SAWScript.Token
Description : Token type for SAW-Script lexer.
Maintainer  : atomb
Stability   : provisional
-}

{-# LANGUAGE DeriveFunctor #-}
module SAWScript.Token where

import Data.Text (Text)

import SAWScript.Position (Positioned(..))

-- All tokens have tokStr carrying the matched text (even TEOF where
-- it doesn't entirely make sense) so that tokStr can be applied to
-- any variant of the type.
--
-- The comment and EOL tokens are internal to the lexer and not seen
-- downstream.
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
             | TCommentS { tokPos :: p, tokStr :: Text                               }
             | TCommentE { tokPos :: p, tokStr :: Text                               }
             | TCommentL { tokPos :: p, tokStr :: Text                               }
             | TEOL      { tokPos :: p, tokStr :: Text                               }
             | TEOF      { tokPos :: p, tokStr :: Text                               }
             deriving (Show, Functor)

instance Positioned p => Positioned (Token p) where
  getPos = getPos . tokPos
