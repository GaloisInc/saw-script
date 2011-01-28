module SAWScript.ParserActions where

import SAWScript.Token(Token)
import SAWScript.Utils(Pos)

data Parser a
instance Monad Parser
happyError :: Parser a
parseError :: Token Pos -> Parser a
lexer :: (Token Pos -> Parser a) -> Parser a
parseIntRange :: (Int, Int) -> Integer -> Parser Int
