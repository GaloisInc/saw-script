{- |
Module      : SAWScript.SolverCache
Description : Optionally LMDB-backed databases
License     : BSD3
Maintainer  : m-yac
Stability   : provisional

...
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
import Control.DeepSeq (deepseq)
import Control.Monad ((>=>), forever)

import Language.Haskell.TH (runIO)
import Language.Haskell.TH.Syntax (qAddDependentFile, liftString)

import qualified Data.Text as T
import qualified Text.Hex as Hex

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS

import Data.Aeson (FromJSON, ToJSON)
import qualified Data.Aeson as JSON

-- | ...
lmdb_opt_database__py :: String
lmdb_opt_database__py = $(do
  let fp = "src/SAWScript/SolverCache/lmdb_opt_database.py"
  qAddDependentFile fp
  s <- runIO $ readFile fp
  liftString s)


-- Helper functions for encoding/decoding hex strings --------------------------

-- | ...
sanitizeHex :: String -> String
sanitizeHex = filter (`elem` "0123456789abcdefABCDEF")

-- | ...
encodeHex :: ByteString -> String
encodeHex bs = T.unpack $ Hex.encodeHex bs

-- | ...
decodeHex :: String -> Either String ByteString
decodeHex s = case Hex.decodeHex $ T.pack s of
  Just bs -> Right bs
  Nothing -> Left $ "Hex decoding failure on:\n" ++ s

-- | ...
encodeJSONHex :: ToJSON a => a -> String
encodeJSONHex = encodeHex . BS.toStrict . JSON.encode

-- | ...
decodeJSONHex :: FromJSON a => String -> Either String a
decodeJSONHex = decodeHex >=> JSON.eitherDecodeStrict'

-- | ...
decodePairs :: (String -> Either String a) ->
               (String -> Either String b) ->
               [String] -> Either String [(a, b)]
decodePairs f1 f2 = mapM $ \l -> case words l of
  [s1, s2] -> (,) <$> f1 s1 <*> f2 s2
  _ -> Left $ "Expected two strings separated by a space, got: " ++ show l

-- | ...
decodeMaybe :: (String -> Either String a) -> [String] ->
               Either String (Maybe a)
decodeMaybe f [l] = Just <$> f l
decodeMaybe _ [] = Right Nothing
decodeMaybe _ ls = Left $ "Expected at most one line, got: " ++ show (unlines ls)

-- | ...
decodeSingle :: (String -> Either String a) -> [String] -> Either String a
decodeSingle f [l] = f l
decodeSingle _ ls = Left $ "Expected one line, got: " ++ show (unlines ls)

-- | ...
decodeEmpty :: a -> [String] -> Either String a
decodeEmpty b [] = Right b
decodeEmpty _ ls = Left $ "Expected nothing, got: " ++ show (unlines ls)


-- Helper functions for IO -----------------------------------------------------

-- | ...
hGetLinesUntil :: String -> Handle -> IO [String]
hGetLinesUntil stop_str h = do
  l <- hGetLine h
  if l == stop_str then return []
  else (l:) <$> hGetLinesUntil stop_str h

-- | ...
hGetLinesTimeout :: Int -> Handle -> IO [String]
hGetLinesTimeout t_micros h =
  timeout t_micros (hGetLine h) >>= \case
    Just l -> hReady h >>= \case
      True -> (l:) <$> hGetLinesTimeout t_micros h
      False -> return [l]
    Nothing -> return []


-- Internal definition of and operations on LMDBOptDatabase --------------------

-- | ...
data LMDBOptDatabase a =
  LMDBOptDatabase
  { dbIOVar :: MVar (String, MVar [String])
  , dbIOTID :: ThreadId
  , dbErr   :: Handle
  , dbShell :: ProcessHandle
  }

-- | ...
db_internal_timeout :: Int
db_internal_timeout = 100000

-- | ...
dbOpen :: IO (LMDBOptDatabase a)
dbOpen = withSystemTempFile "lmdb_opt_database.py" $ \fnm fh -> do
  hPutStr fh lmdb_opt_database__py >> hClose fh
  (mb_i, mb_o, mb_e, p) <- createProcess $
    (shell $ "python3 " ++ fnm ++ " shell")
    {std_in = CreatePipe, std_out = CreatePipe, std_err = CreatePipe}
  mb_exit <- getProcessExitCode p
  case (mb_i, mb_o, mb_e, mb_exit) of
    -- If pipes and process were created successfully...
    (Just i, Just o, Just e, Nothing) -> do
      hSetBuffering i NoBuffering
      -- First we create a thread which, when given a string and an MVar to
      -- which to send output, will send the string to the Python process,
      -- gather the output, and send it back over the MVar
      i_var <- newEmptyMVar
      io_tid <- forkIO $ forever $ do
        (inp_str, outp_var) <- takeMVar i_var
        hPutStrLn i inp_str
        outp_ls <- hGetLinesUntil ">>><<<" o
        putMVar outp_var outp_ls
      -- Next we initialize the python process with a one-liner which sets the
      -- REPL's command prompt to ">>><<<\n" (which the process above waits for)
      let db = LMDBOptDatabase i_var io_tid e p
          decodeInit l = if l == ">>> ()" then Right ()
                         else Left $ "Unexpected: " ++ l
      u <- dbExec (decodeSingle decodeInit)
        "import sys; sys.ps1 = '>>><<<\\n'; sys.ps2 = ''; print(())" db
      return $ u `deepseq` db
    -- Otherwise, either a pipe or the process was not created, so we clean up
    -- and fail
    _ -> do
      mapM_ hClose mb_i
      terminateProcess p
      mb_e_ls <- mapM (hGetLinesTimeout db_internal_timeout) mb_e
      fail $ "Failed to spawn Python LMDB process"
          ++ maybe ": Pipe not created" (unlines . (":":)) mb_e_ls

-- | ...
dbExec :: ([String] -> Either String b) -> String -> LMDBOptDatabase a -> IO b
dbExec fn inp_str LMDBOptDatabase{..} = do
  outp_var <- newEmptyMVar
  putMVar dbIOVar (inp_str, outp_var)
  mb_outp_ls <- timeout db_internal_timeout (takeMVar outp_var)
  case mb_outp_ls of
    Just outp_ls -> case outp_ls `deepseq` fn outp_ls of
      Right b -> return b
      Left read_err -> do
        e_ls <- hGetLinesTimeout db_internal_timeout dbErr
        fail $ if length e_ls == 0 then read_err
                 else unlines e_ls
    Nothing -> do
      e_ls <- hGetLinesTimeout db_internal_timeout dbErr
      fail $ unlines e_ls

-- | ...
-- dbClose :: LMDBOptDatabase a -> IO ()
-- dbClose LMDBOptDatabase{..} = do
--   hClose dbIn
--   killThread dbOutTID
--   terminateProcess dbProc


-- Exposed interface of LMDBOptDatabase ----------------------------------------

-- | ...
new :: IO (LMDBOptDatabase a)
new = dbOpen >>= \db -> flip (dbExec (decodeEmpty db)) db
  "db = LMDBOptDatabase()"

-- | ...
setPath :: FilePath -> Int -> LMDBOptDatabase a -> IO ()
setPath path map_size = dbExec (decodeEmpty ()) $
  "db.setPath(jsonHex('" ++ encodeJSONHex path ++ "'), " ++
             "jsonHex('" ++ encodeJSONHex map_size ++ "'))"

-- | ...
getPath :: LMDBOptDatabase a -> IO (Maybe FilePath)
getPath = dbExec (decodeSingle decodeJSONHex)
  "pJSONHex(db.getPath())"

-- | ...
size :: LMDBOptDatabase a -> IO Int
size = dbExec (decodeSingle decodeJSONHex)
  "pJSONHex(len(db))"

-- | ...
lookup :: FromJSON a => ByteString -> LMDBOptDatabase a -> IO (Maybe a)
lookup k = dbExec (decodeMaybe decodeJSONHex) $
  "pHex(db.get(hex('" ++ encodeHex k ++ "')))"

-- | ...
insert :: ToJSON a => ByteString -> a -> LMDBOptDatabase a -> IO ()
insert k v = dbExec (decodeEmpty ()) $
  "db[hex('" ++ encodeHex k ++ "')] = hex('" ++ encodeJSONHex v ++ "')"

-- | ...
delete :: ByteString -> LMDBOptDatabase a -> IO ()
delete k = dbExec (decodeEmpty ()) $
  "del db[hex('" ++ encodeHex k ++ "')]"

-- | ...
toList :: FromJSON a => LMDBOptDatabase a -> IO [(ByteString, a)]
toList = dbExec (decodePairs decodeHex decodeJSONHex) $
  "pHexPairs(db.items())"

-- | ...
filterByHexPrefix :: FromJSON a => String -> LMDBOptDatabase a ->
                     IO [(ByteString, a)]
filterByHexPrefix s = dbExec (decodePairs decodeHex decodeJSONHex) $
  "pHexPairs(db.filterByKeyHexPrefix('" ++ sanitizeHex s ++ "'))"

-- | ...
cleanByJSONObjValues :: (ToJSON b, FromJSON b) => b -> LMDBOptDatabase a ->
                        IO [(ByteString, [(b, b)])]
cleanByJSONObjValues ref = dbExec (decodePairs decodeHex decodeJSONHex) $
  "pHexJSONPairs(db.filterByMismatchedJSONObjValues(" ++
    "jsonHex('" ++ encodeJSONHex ref ++ "'), delete = True))"
