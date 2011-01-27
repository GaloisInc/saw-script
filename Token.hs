module SAWScript.Token where

data Token p = TImport  p
             | TVar     p String
             | TSemi    p
             | TLit     p String
             | TUnknown p String
             | TCmntS   p
             | TCmntE   p
             | TEOF     p

getPos :: Token p -> p
getPos (TImport  p)   = p
getPos (TVar     p _) = p
getPos (TSemi    p)   = p
getPos (TLit     p _) = p
getPos (TUnknown p _) = p
getPos (TCmntS   p)   = p
getPos (TCmntE   p)   = p
getPos (TEOF     p)   = p

instance Show (Token p) where
  show (TImport _)    = "import"
  show (TVar _ n)     = n
  show (TSemi _)      = ";"
  show (TLit _ s)     = show s
  show (TUnknown _ s) = show s
  show (TCmntS _)     = "/*"
  show (TCmntE _)     = "*/"
  show (TEOF _)       = "<end-of-file>"

instance Functor Token where
  fmap f (TImport  p)   = TImport  (f p)
  fmap f (TVar     p n) = TVar     (f p) n
  fmap f (TSemi    p)   = TSemi    (f p)
  fmap f (TLit     p s) = TLit     (f p) s
  fmap f (TUnknown p c) = TUnknown (f p) c
  fmap f (TCmntS   p)   = TCmntS   (f p)
  fmap f (TCmntE   p)   = TCmntE   (f p)
  fmap f (TEOF     p)   = TEOF     (f p)
