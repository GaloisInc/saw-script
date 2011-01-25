module SAWScript.Token where

data Token = TokenLet
           | TokenIn
           | TokenEq
           | TokenPlus
           | TokenInt  Int
           | TokenOB
           | TokenCB
           | TokenVar String
           | TokenNL
           | TokenUnknown Char
           | TokenEOF

instance Show Token where
  show TokenLet         = "let"
  show TokenIn          = "in"
  show TokenEq          = "="
  show TokenPlus        = "+"
  show (TokenInt n)     = show n
  show TokenOB          = "("
  show TokenCB          = ")"
  show (TokenVar v)     = v
  show TokenNL          = "<new-line>"
  show (TokenUnknown c) = show c
  show TokenEOF         = "<end-of-file>"
