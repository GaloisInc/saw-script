module SAWScript.Utils(Pos, incLineNo, initPos) where

data Pos = Pos !FilePath -- file
               !Int      -- line

incLineNo :: Pos -> Pos
incLineNo (Pos f i) = Pos f (i+1)

initPos :: String -> Pos
initPos f = Pos f 1

instance Show Pos where
  show (Pos f l) = f ++ ":" ++ show l
