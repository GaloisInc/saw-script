{-# LANGUAGE CPP #-}

{- |
Module      : $Header$
Description : Loading and parsing SAW-Script files.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
module SAWScript.Import
  ( loadFile
  , findAndLoadFile
  ) where


import SAWScript.AST
import SAWScript.Lexer (lexSAW)
import SAWScript.Options
import SAWScript.Parser

import System.Directory
import Control.Exception

loadFile :: Options -> FilePath -> IO [Stmt]
loadFile opts fname = do
  printOutLn opts Info $ "Loading file " ++ show fname
  ftext <- readFile fname
  either throwIO return (parseFile fname ftext)

parseFile :: FilePath -> String -> Either ParseError [Stmt]
parseFile fname input =
  case parseModule (lexSAW fname input) of
    Left err -> Left err
    Right stmts -> Right stmts

findAndLoadFile :: Options -> FilePath -> IO [Stmt]
findAndLoadFile opts fp = do
  let paths = importPath opts
  mfname <- findFile paths fp
  case mfname of
    Nothing -> fail $ unlines $
        [ "Couldn't find file: " ++ show fp
        , "  Searched in directories:"
        ] ++ map ("    " ++) paths
    Just fname -> loadFile opts fname

#if __GLASGOW_HASKELL__ < 706
findFile :: [FilePath] -> String -> IO (Maybe FilePath)
findFile paths fileName = search paths
  where
    search :: [FilePath] -> IO (Maybe FilePath)
    search [] = return Nothing
    search (d:ds) = do
        let path = d </> fileName
        b <- doesFileExist path
        if b then return (Just path)
             else search ds
#endif
