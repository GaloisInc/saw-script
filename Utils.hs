module SAWScript.Utils(endPos, Pos(..)) where

data Pos = Pos !FilePath -- file
               !Int      -- line
               !Int      -- col

endPos :: FilePath -> Pos
endPos f = Pos f 0 0

instance Show Pos where
  show (Pos f 0 0) = f ++ ":end-of-file"
  show (Pos f l c) = f ++ ":" ++ show l ++ ":" ++ show c
