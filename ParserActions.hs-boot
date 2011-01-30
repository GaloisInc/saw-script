module SAWScript.ParserActions where

import SAWScript.MethodAST
import SAWScript.Token(Token)
import SAWScript.Utils(Pos)

data Parser a
instance Monad Parser

happyError    :: Parser a
parseError    :: Token Pos -> Parser a
lexer         :: (Token Pos -> Parser a) -> Parser a
parseIntRange :: Pos -> (Int, Int) -> Integer -> Parser Int
mkExprType    :: Pos -> ExprWidth -> Maybe ExprType -> Parser ExprType
