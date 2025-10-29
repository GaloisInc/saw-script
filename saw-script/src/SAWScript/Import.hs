{- |
Module      : SAWScript.Import
Description : Loading and parsing SAW-Script files.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}

module SAWScript.Import
  ( findAndLoadFile
  ) where

import qualified Data.Text.IO as TextIO (readFile)
import qualified Data.Text as Text
import Control.Exception
import System.Directory
import System.FilePath (normalise)

import SAWCentral.Position (Pos)
import SAWCentral.AST
import SAWScript.Lexer (lexSAW)
import SAWCentral.Options
import SAWScript.Parser
import SAWScript.Token (Token)

parseFile :: [Token Pos] -> Either ParseError [Stmt]
parseFile tokens = do
  case parseModule tokens of
    Left err -> Left err
    Right stmts -> Right stmts

-- | Load the 'Stmt's in a @.saw@ file.
loadFile :: Options -> FilePath -> IO [Stmt]
loadFile opts fname = do
  printOutLn opts Info $ "Loading file " ++ show fname
  ftext <- TextIO.readFile fname
  -- XXX: the print functions should take care of printing the position
  -- (clean this up when we clean out the printing infrastructure)
  -- XXX: the print functions should also take care of exiting on an error
  -- (immediately or later). For now, throw errors and print anything else.
  case lexSAW fname ftext of
    Left (_, pos, txt) -> do
      let txt' = show pos ++ ": " ++ Text.unpack txt
      throwIO $ userError txt'

    Right (tokens, optmsg) -> do
      case optmsg of
        Nothing -> return ()
        Just (vrb, pos, txt) -> do
          let txt' = show pos ++ ": " ++ Text.unpack txt
          case vrb of
            Error -> throwIO $ userError txt'
            _ -> printOutLn opts vrb txt'
      either throwIO return (parseFile tokens)

-- | Find a file, potentially looking in a list of multiple search paths (as
-- specified via the @SAW_IMPORT_PATH@ environment variable or
-- @-i@/@--import-path@ command-line options). If the file was successfully
-- found, load it. If not, raise an error.
findAndLoadFile :: Options -> FilePath -> IO [Stmt]
findAndLoadFile opts fp = do
  let paths = importPath opts
  mfname <- findFile paths fp
  case mfname of
    Nothing -> fail $ unlines $
        [ "Couldn't find file: " ++ show fp
        , "  Searched in directories:"
        ] ++ map ("    " ++) paths
    Just fname ->
      -- NB: Normalise the path name. The default SAW_IMPORT_PATH contains ".",
      -- and the behavior of filepath's 'normalise' function is to prepend a
      -- search path to the front of the file path that is found, which can
      -- cause paths like "./foo.saw" to be returned. This looks ugly in error
      -- messages, where we would rather display "foo.saw" instead.
      loadFile opts (normalise fname)
