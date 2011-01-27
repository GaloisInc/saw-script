module SAWScript.Utils where

data Pos = Pos !FilePath -- file
               !Int      -- line
               !Int      -- col

endPos :: FilePath -> Pos
endPos f = Pos f 0 0

instance Show Pos where
  show (Pos f 0 0) = '[' : show f ++ ":end-of-file]" 
  show (Pos f l c) = '[' : show f ++ ":" ++ show l ++ ":" ++ show c ++ "]"

data SSOpts = SSOpts {
          verbose :: Bool
       }

defaultSSOpts :: SSOpts
defaultSSOpts = SSOpts {
          verbose = False
        }
