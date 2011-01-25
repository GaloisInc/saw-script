module SAWScript.Token where

data Token p = TokenLet     { getPos :: p }
             | TokenIn      { getPos :: p }
             | TokenEq      { getPos :: p }
             | TokenPlus    { getPos :: p }
             | TokenInt     { getPos :: p, getTokInt :: Int }
             | TokenOB      { getPos :: p }
             | TokenCB      { getPos :: p }
             | TokenVar     { getPos :: p, getTokVar :: String }
             | TokenUnknown { getPos :: p, getTokUnk :: Char }
             | TokenEOF     { getPos :: p }

instance Show (Token a) where
  show (TokenLet _)       = "let"
  show (TokenIn _)        = "in"
  show (TokenEq _)        = "="
  show (TokenPlus _)      = "+"
  show (TokenInt _ n)     = show n
  show (TokenOB _)        = "("
  show (TokenCB _)        = ")"
  show (TokenVar _ v)     = v
  show (TokenUnknown _ c) = show c
  show (TokenEOF _)       = "<end-of-file>"

instance Functor Token where
  fmap f (TokenLet     p)   = TokenLet     (f p)
  fmap f (TokenIn      p)   = TokenIn      (f p)
  fmap f (TokenEq      p)   = TokenEq      (f p)
  fmap f (TokenPlus    p)   = TokenPlus    (f p)
  fmap f (TokenInt     p n) = TokenInt     (f p) n
  fmap f (TokenOB      p)   = TokenOB      (f p)
  fmap f (TokenCB      p)   = TokenCB      (f p)
  fmap f (TokenVar     p v) = TokenVar     (f p) v
  fmap f (TokenUnknown p c) = TokenUnknown (f p) c
  fmap f (TokenEOF     p)   = TokenEOF     (f p)
