{-# LANGUAGE DeriveDataTypeable  #-}
module SAWScript.Utils where

import Data.List(intercalate)
import System.Console.CmdArgs(Data, Typeable)
import System.Directory(makeRelativeToCurrentDirectory)
import System.FilePath(makeRelative)

data Pos = Pos !FilePath -- file
               !Int      -- line
               !Int      -- col

endPos :: FilePath -> Pos
endPos f = Pos f 0 0

fmtPos :: Pos -> String -> String
fmtPos p m = show p ++ ":\n" ++ m'
  where m' = intercalate "\n" . map ("  " ++) . lines $ m

posRelativeToCurrentDirectory :: Pos -> IO Pos
posRelativeToCurrentDirectory (Pos f l c) = do f' <- makeRelativeToCurrentDirectory f
                                               return $ Pos f' l c

posRelativeTo :: FilePath -> Pos -> Pos
posRelativeTo d (Pos f l c) = Pos (makeRelative d f) l c

instance Show Pos where
  show (Pos f 0 0) = show f ++ ":end-of-file"
  show (Pos f l c) = show f ++ ":" ++ show l ++ ":" ++ show c

data SSOpts = SSOpts {
          classpath  :: String
       ,  jars       :: String
       ,  verbose    :: Int
       ,  dump       :: Bool
       ,  entryPoint :: FilePath
       }
       deriving (Show, Data, Typeable)

verboseAtLeast :: Int -> SSOpts -> Bool
verboseAtLeast i o = verbose o >= i

notQuiet :: SSOpts -> Bool
notQuiet = verboseAtLeast 1
