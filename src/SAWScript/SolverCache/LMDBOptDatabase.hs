{- |
Module      : SAWScript.SolverCache
Description : Optionally LMDB-backed databases
License     : BSD3
Maintainer  : m-yac
Stability   : provisional

This module implements a 'HashTable'-inspired interface for key-value databases
optionally backed by an LMDB database on disk.

Instead of using something like the Haskell library @lmdb-simple@, which
requires that the user have the LMDB dynamically-linked C libraries installed
even if an LMDB database is never used at runtime, this module connects to a
Python process on database creation and uses the Python LMDB bindings only when
the user provides a file path at which to open an LMDB database. This means that
the user only needs to have Python installed if they create an 'LMDBOptDatabase'
object at runtime, and only needs to have the Python LMDB bindings, which are
self-contained and can be installed via @pip@, if they provide a file path.
-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}

module SAWScript.SolverCache.LMDBOptDatabase
  ( encodeHex
  , decodeHex
  , LMDBOptDatabase
  , new
  , setPath
  , getPath
  , size
  , lookup
  , insert
  , delete
  , toList
  , filterByHexPrefix
  , cleanByJSONObjValues
  ) where

import Prelude hiding (lookup)
import System.Timeout (timeout)
import System.IO.Temp (withSystemTempFile)
import System.Process
import System.IO

import Control.Concurrent (forkIO, ThreadId)
import Control.Concurrent.MVar (MVar, newEmptyMVar, putMVar, takeMVar)
import Control.Monad ((>=>), forever)
import Data.Char (isHexDigit)
import Text.Printf (printf)
import Text.Read (readEither)
import Numeric (readHex)

import Language.Haskell.TH (runIO)
import Language.Haskell.TH.Syntax (qAddDependentFile, liftString)

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS

import Data.Aeson (FromJSON, ToJSON)
import qualified Data.Aeson as JSON

-- | The contents of @lmdb_opt_database.py@
lmdb_opt_database__py :: String
lmdb_opt_database__py = $(do
  let fp = "src/SAWScript/SolverCache/lmdb_opt_database.py"
  qAddDependentFile fp
  s <- runIO $ readFile fp
  liftString s)


-- Helper functions for encoding/decoding hex strings --------------------------

-- | Remove all characters except hex digits (i.e. `[0-9a-fA-F]`) from the
-- given string
sanitizeHex :: String -> String
sanitizeHex = filter isHexDigit

-- | Encode a 'ByteString' as a hex string
encodeHex :: ByteString -> String
encodeHex = concatMap (printf "%02x") . BS.unpack

-- | Decode a hex string as a 'ByteString'
decodeHex :: String -> Either String ByteString
decodeHex s = BS.pack <$> go s
  where go (c0:c1:cs) | [(b,[])] <- readHex [c0,c1] = (b:) <$> go cs
        go _ = Left $ "Hex decoding failure on:\n" ++ s

-- | Encode an element of a 'ToJSON' type as a hex string
encodeJSONHex :: ToJSON a => a -> String
encodeJSONHex = encodeHex . LBS.toStrict . JSON.encode

-- | Decode a hex string as an element of a 'FromJSON' type
decodeJSONHex :: FromJSON a => String -> Either String a
decodeJSONHex = decodeHex >=> JSON.eitherDecodeStrict'

-- | Given a list of strings, each of which containing exactly one space
-- character, apply the two given decoding functions to each respective part of
-- each string and return the result as a list of pairs
decodePairs :: (String -> Either String a) ->
               (String -> Either String b) ->
               [String] -> Either String [(a, b)]
decodePairs f1 f2 = mapM $ \l -> case words l of
  [s1, s2] -> (,) <$> f1 s1 <*> f2 s2
  _ -> Left $ "Expected two strings separated by a space, got: " ++ show l

-- | Given a list of at most one string, apply the given decoding function to
-- the string if there is one, otherwise return 'Nothing'
decodeMaybe :: (String -> Either String a) -> [String] ->
               Either String (Maybe a)
decodeMaybe f [l] = Just <$> f l
decodeMaybe _ [] = Right Nothing
decodeMaybe _ ls = Left $ "Expected at most one line, got: " ++ show (unlines ls)

-- | Given a list of exactly one string, apply the given decoding function to it
decodeSingle :: (String -> Either String a) -> [String] -> Either String a
decodeSingle f [l] = f l
decodeSingle _ ls = Left $ "Expected one line, got: " ++ show (unlines ls)


-- Helper functions for IO -----------------------------------------------------

-- | Apply 'hGetLine' to the given 'Handle' until the given 'String' is
-- received, then return all the prior collected results of 'hGetLine'
hGetLinesUntil :: String -> Handle -> IO [String]
hGetLinesUntil stop_str h = do
  l <- hGetLine h
  if l == stop_str then return []
  else (l:) <$> hGetLinesUntil stop_str h

-- | Apply 'hGetLine' with a 'timeout' of the given number of microseconds
-- repeatedly until either 'hReady' returns 'False' or the operation times out
hGetLinesTimeout :: Int -> Handle -> IO [String]
hGetLinesTimeout t_micros h =
  timeout t_micros (hGetLine h) >>= \case
    Just l -> hReady h >>= \case
      True -> (l:) <$> hGetLinesTimeout t_micros h
      False -> return [l]
    Nothing -> return []


-- Internal definition of and operations on LMDBOptDatabase --------------------

-- | A key-value database which is either stored in memory, or if the user has
-- supplied a path (see 'setPath'/'getPath'), as an LMDB database. Keys are
-- represented as 'ByteString's, but values can be of any JSON-serialisable type
-- (see 'ToJSON'/'FromJSON'). This is implemented by connecting to a @python3@
-- process, so Python must be installed to use this type. To use the LMDB
-- backend, the Python LMDB bindings must also be installed.
data LMDBOptDatabase a =
  LMDBOptDatabase
  { dbIOVar :: MVar (String, MVar [String])
  , dbIOTID :: ThreadId
  , dbErr   :: Handle
  , dbShell :: ProcessHandle
  }

-- | The timeout to use when attempting to get lines from @stderr@
dbInternalTimeout :: Int
dbInternalTimeout = 100000

-- | Open a new @LMDBOptDatabase@ by connecting to a @python3@ process
dbOpen :: IO (LMDBOptDatabase a)
dbOpen = withSystemTempFile "lmdb_opt_database.py" $ \fnm fh -> do
  -- First, start a python3 process with a temp file containing the contents of
  -- lmdb_opt_database.py and the "shell" option for lmdb_opt_database.py
  -- TODO: Actually use pip to install this file so we don't have to use a temp
  -- file every time we open a database
  hPutStr fh lmdb_opt_database__py >> hClose fh
  (mb_i, mb_o, mb_e, p) <- createProcess $
    (shell $ "python3 " ++ fnm ++ " shell")
    {std_in = CreatePipe, std_out = CreatePipe, std_err = CreatePipe}
  mb_exit <- getProcessExitCode p
  case (mb_i, mb_o, mb_e, mb_exit) of
    -- If the process was created successfully...
    (Just i, Just o, Just e, Nothing) -> do
      hSetBuffering i NoBuffering
      -- First we create a thread which, when given a string and an MVar to
      -- which to send output, will send the string to the Python process,
      -- gather the output, and send it back over the MVar.
      -- We make this thread to ensure each new command waits for any currently
      -- executing commands to finish before trying to send input to and/or
      -- read output from the Python process.
      i_var <- newEmptyMVar
      io_tid <- forkIO $ forever $ do
        (inp_str, outp_var) <- takeMVar i_var
        hPutStrLn i inp_str
        outp_ls <- hGetLinesUntil ">>><<<" o
        putMVar outp_var outp_ls
      -- Finally we initialize the python process with a line which sets the
      -- REPL's command prompt to ">>><<<\n" (which the process above waits for)
      let db = LMDBOptDatabase i_var io_tid e p
          decodeInit l = if l == ">>> ()" then Right ()
                         else Left $ "Unexpected: " ++ l
      u <- dbExec (decodeSingle decodeInit)
        "import sys; sys.ps1 = '>>><<<\\n'; sys.ps2 = ''; print(())" db
      return $ u `seq` db
    -- Otherwise, either the process or one of its pipes failed to be created,
    -- so we clean up anything that was created and fail
    _ -> do
      mapM_ hClose mb_i
      terminateProcess p
      mb_e_ls <- mapM (hGetLinesTimeout dbInternalTimeout) mb_e
      fail $ "Failed to spawn Python LMDB process"
          ++ maybe ": Pipe not created" (unlines . (":":)) mb_e_ls

-- | Send the given 'String' to the @python3@ process and decode the resulting
-- lines (if any) using the given function
dbExec :: ([String] -> Either String b) -> String -> LMDBOptDatabase a -> IO b
dbExec decodeFn inp_str LMDBOptDatabase{..} = do
  outp_var <- newEmptyMVar
  putMVar dbIOVar (inp_str, outp_var)
  outp_ls <- takeMVar outp_var
  case length outp_ls `seq` decodeFn outp_ls of
    Right b -> return b
    Left read_err -> do
      e_ls <- hGetLinesTimeout dbInternalTimeout dbErr
      fail $ if length e_ls == 0 then "Decoding Error:\n" ++ read_err
               else unlines $ "Python error:" : e_ls


-- Exposed interface of LMDBOptDatabase ----------------------------------------

-- | Create a new, empty, 'LMDBOptDatabase'. This will fail if the @python3@
-- executable cannot be found.
new :: IO (LMDBOptDatabase a)
new = do db <- dbOpen
         () <- dbExec (decodeSingle readEither) "db = LMDBOptDatabase(); ()" db
         return db

-- | Open an LMDB database at the given 'FilePath' with the given maximum size
-- (in MiB), add all current entries in the database to the LMDB database, then
-- set the current implementation of this database to be the LMDB database. This
-- will fail if the Python LMDB bindings cannot be loaded.
setPath :: FilePath -> Int -> LMDBOptDatabase a -> IO ()
setPath path map_size = dbExec (decodeSingle readEither) $
  "db.setPath(jsonHex('" ++ encodeJSONHex path ++ "'), " ++
             "jsonHex('" ++ encodeJSONHex map_size ++ "')); ()"

-- | Return the location of the directory in which this database is stored, if
-- this database is implemented as an LMDB database
getPath :: LMDBOptDatabase a -> IO (Maybe FilePath)
getPath = dbExec (decodeSingle decodeJSONHex)
  "pJSONHex(db.getPath())"

-- | Return the number of entries in the database
size :: LMDBOptDatabase a -> IO Int
size = dbExec (decodeSingle decodeJSONHex)
  "pJSONHex(len(db))"

-- | Return the JSON-serializable value associated to the given 'ByteString'
-- key in the database, if one exists
lookup :: FromJSON a => ByteString -> LMDBOptDatabase a -> IO (Maybe a)
lookup k = dbExec (decodeMaybe decodeJSONHex) $
  "pHex(db.get(hex('" ++ encodeHex k ++ "')))"

-- | Insert a 'ByteString' key / JSON-serializable value entry into the database
insert :: ToJSON a => ByteString -> a -> LMDBOptDatabase a -> IO ()
insert k v = dbExec (decodeSingle readEither) $
  "db[hex('" ++ encodeHex k ++ "')] = hex('" ++ encodeJSONHex v ++ "'); ()"

-- | Delete the entry associated to the given 'ByteString' key in the database
delete :: ByteString -> LMDBOptDatabase a -> IO ()
delete k = dbExec (decodeSingle readEither) $
  "del db[hex('" ++ encodeHex k ++ "')]; ()"

-- | Return the list of all entries in the database
toList :: FromJSON a => LMDBOptDatabase a -> IO [(ByteString, a)]
toList = dbExec (decodePairs decodeHex decodeJSONHex) $
  "pHexPairs(db.items())"

-- | Return all entries in the database whose keys have the given string as a
-- prefix of their hex representation
filterByHexPrefix :: FromJSON a => String -> LMDBOptDatabase a ->
                     IO [(ByteString, a)]
filterByHexPrefix s = dbExec (decodePairs decodeHex decodeJSONHex) $
  "pHexPairs(db.filterByKeyHexPrefix('" ++ sanitizeHex s ++ "'))"

-- | Delete all entries @k, v@ in the database for which @v@, when converted to
-- JSON, does not match the given value @ref@, when converted to JSON - in the
-- sense that there is some key in both @v@ and @ref@ which has differing values 
-- in each (see @mismatchedJSONObjValues@ in @lmdb_opt_database.py@). Each such
-- @k@, paired with @v@'s list of mismatches, is returned.
cleanByJSONObjValues :: (ToJSON b, FromJSON b) => b -> LMDBOptDatabase a ->
                        IO [(ByteString, [(b, b)])]
cleanByJSONObjValues ref = dbExec (decodePairs decodeHex decodeJSONHex) $
  "pHexJSONPairs(db.filterByMismatchedJSONObjValues(" ++
    "jsonHex('" ++ encodeJSONHex ref ++ "'), delete = True))"
