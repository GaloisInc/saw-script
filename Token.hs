module SAWScript.Token where

data Token p = TVar       { getPos :: p, _gs :: String   }
             | TLit       { getPos :: p, _gs :: String   }
             | TUnknown   { getPos :: p, _gs :: String   }
             | TPunct     { getPos :: p, _gs :: String   }
             | TReserved  { getPos :: p, _gs :: String   }
             | TNum       { getPos :: p, getInteger :: Integer  }
             | TCmntS     { getPos :: p }
             | TCmntE     { getPos :: p }
             | TEOF       { getPos :: p }

instance Show (Token p) where
  show (TVar _ n)       = n
  show (TLit _ s)       = show s
  show (TUnknown _ s)   = s
  show (TPunct _ s)     = s
  show (TReserved _ s)  = s
  show (TNum _ i)       = show i
  show (TCmntS _)       = "/*"
  show (TCmntE _)       = "*/"
  show (TEOF _)         = "<end-of-file>"

instance Functor Token where
  fmap g (TVar       p n) = TVar       (g p) n
  fmap g (TLit       p s) = TLit       (g p) s
  fmap g (TUnknown   p c) = TUnknown   (g p) c
  fmap g (TPunct     p s) = TPunct     (g p) s
  fmap g (TReserved  p s) = TReserved  (g p) s
  fmap g (TNum       p i) = TNum       (g p) i
  fmap g (TCmntS     p)   = TCmntS     (g p)
  fmap g (TCmntE     p)   = TCmntE     (g p)
  fmap g (TEOF       p)   = TEOF       (g p)
