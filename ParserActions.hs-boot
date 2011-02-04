module SAWScript.ParserActions where

import SAWScript.MethodAST
import SAWScript.Token(Token)
import SAWScript.Utils(Pos)

data Parser a
instance Monad Parser

happyError    :: Parser a
parseError    :: Token Pos -> Parser a
lexer         :: (Token Pos -> Parser a) -> Parser a
parseIntRange :: Pos -> (Int, Int) -> Integer -> Parser (Pos, Int)
mkExprType    :: Pos -> ExprWidth -> Maybe ExprType -> Parser ExprType
mkRecordT     :: Pos -> [(Pos, String, ExprType)] -> Parser ExprType
mkRecordV     :: Pos -> [(Pos, String, Expr)] -> Parser Expr
