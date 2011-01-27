{-# LANGUAGE DeriveDataTypeable  #-}
module SAWScript.Utils where

import Data.List(intercalate)
import System.Console.CmdArgs(Data, Typeable)

data Pos = Pos !FilePath -- file
               !Int      -- line
               !Int      -- col

endPos :: FilePath -> Pos
endPos f = Pos f 0 0

fmtPos :: Pos -> String -> String
fmtPos p m = show p ++ ":\n" ++ m'
  where m' = intercalate "\n" . map ("  " ++) . lines $ m

instance Show Pos where
  show (Pos f 0 0) = f ++ ":end-of-file"
  show (Pos f l c) = f ++ ":" ++ show l ++ ":" ++ show c

data SSOpts = SSOpts {
          classpath  :: String
       ,  jars       :: String
       ,  verbose    :: Int
       ,  dump       :: Bool
       ,  entryPoint :: String
       }
       deriving (Show, Data, Typeable)

verboseAtLeast :: Int -> SSOpts -> Bool
verboseAtLeast i o = verbose o >= i

notQuiet :: SSOpts -> Bool
notQuiet = verboseAtLeast 1
