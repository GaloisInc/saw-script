module SAWScript.Token where

data Token p = TVar      { tokPos :: p, tokStr :: String                     }
             | TLit      { tokPos :: p, tokStr :: String                     }
             | TUnknown  { tokPos :: p, tokStr :: String                     }
             | TPunct    { tokPos :: p, tokStr :: String                     }
             | TReserved { tokPos :: p, tokStr :: String                     }
             | TOp       { tokPos :: p, tokStr :: String                     }
             | TNum      { tokPos :: p, tokStr :: String, tokNum :: Integer  }
             | TCmntS    { tokPos :: p, tokStr :: String                     }
             | TCmntE    { tokPos :: p, tokStr :: String                     }
             | TEOF      { tokPos :: p, tokStr :: String                     }
             deriving Show

instance Functor Token where
  fmap g (TVar       p n)   = TVar      (g p) n
  fmap g (TLit       p s)   = TLit      (g p) s
  fmap g (TUnknown   p c)   = TUnknown  (g p) c
  fmap g (TPunct     p s)   = TPunct    (g p) s
  fmap g (TReserved  p s)   = TReserved (g p) s
  fmap g (TOp        p s)   = TOp       (g p) s
  fmap g (TNum       p s i) = TNum      (g p) s i
  fmap g (TCmntS     p s)   = TCmntS    (g p) s
  fmap g (TCmntE     p s)   = TCmntE    (g p) s
  fmap g (TEOF       p s)   = TEOF      (g p) s
