{- |
Module      : SAWScript.Import
Description : Loading and parsing SAW-Script files.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
{-# LANGUAGE CPP #-}

module SAWScript.Import
  ( loadFile
  , findAndLoadFile
  ) where

import qualified Data.Text.IO as TextIO (readFile)
import qualified Data.Text as Text
import Control.Exception
import System.Directory

import SAWCentral.Position (Pos)
import SAWScript.AST
import SAWScript.Lexer (lexSAW)
import SAWCentral.Options
import SAWScript.Parser
import SAWScript.Token (Token)

loadFile :: Options -> FilePath -> IO [Stmt]
loadFile opts fname = do
  printOutLn opts Info $ "Loading file " ++ show fname
  ftext <- TextIO.readFile fname
  let (tokens, optmsg) = lexSAW fname ftext
  case optmsg of
      Nothing -> return ()
      Just (vrb, pos, txt) -> do
          -- XXX: the print functions should take care of printing the position
          -- (clean this up when we clean out the printing infrastructure)
          let txt' = show pos ++ ": " ++ Text.unpack txt
          -- XXX: the print functions should also take care of exiting on an error
          -- (immediately or later). For now, throw errors and print anything else.
          case vrb of
              Error -> throwIO $ userError txt'
              _ -> printOutLn opts vrb txt'
  either throwIO return (parseFile tokens)

parseFile :: [Token Pos] -> Either ParseError [Stmt]
parseFile tokens = do
  case parseModule tokens of
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
