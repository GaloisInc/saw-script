{- |
Module      : SAWCentral.SolverCache
Description : Caching SMT solver results for SAWScript
License     : BSD3
Maintainer  : m-yac
Stability   : provisional

This file defines an interface for caching SMT/SAT solver results using an LMDB
database. The interface, as used in 'applyProverToGoal', works as follows:

1. An 'SMTQuery' is converted into a string using 'scWriteExternal', and
   along with any relevant 'SolverBackendVersion's (obtained using
   'getSolverBackendVersions' from @SAWCentral.SolverVersions@), is then hashed
   using SHA256 ('mkSolverCacheKey').
2. The core of the 'SolverCache' is an LMDB database mapping these hashes to
   previously obtained results ('solverCacheEnv', 'solverCacheDB'). If this is
   the first time solver caching is being used and the `SAW_SOLVER_CACHE_PATH`
   environment variable was set at startup, then open an LMDB database at the
   specified path and use this database for all subsequent uses of the solver
   cache. Note that this only occurs if there have been no prior calls to the
   `set_solver_cache_path` command, which immediately opens an LMDB database at
   specified path when called.
3. If the hash corresponding to the 'SATQuery' and 'SolverBackendVersion's
   can be found in the database ('lookupInSolverCache'), then the corresponding
   result is used.
4. Otherwise, the 'SATQuery' is dispatched to the requested backend and a
   result is obtained. This result is then added to the database using the
   aforementioned hash as the key ('insertInSolverCache').

A interesting detail is how results are represented. For all of the backends
which use 'applyProverToGoal', the type of a result is:
@Maybe [(ExtCns Term, FirstOrderValue)]@, where 'Nothing' represents a result
of "unsat," and 'Just' represents a result of "sat" along with a list of
counterexamples. Since 'ExtCns' contains execution-specific 'VarIndex'es, we
don't want to save these results directly. Instead, we represent each 'ExtCns'
as its index in the 'satVariables' field of 'SATQuery' (which is where they
were obtained by the backends in the first place).
-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module SAWCentral.SolverCache
  ( SolverBackend(..)
  , allBackends
  , sbvBackends
  , SolverBackendOption(..)
  , optionBackends
  , SolverBackendVersions
  , SolverCacheKey(..)
  , mkSolverCacheKey
  , SolverCacheValue(..)
  , toSolverCacheValue
  , fromSolverCacheValue
  , SolverCache(..)
  , lazyOpenSolverCache
  , openSolverCache
  , SolverCacheOp
  , solverCacheOp
  , solverCacheOpDefault
  , lookupInSolverCache
  , insertInSolverCache
  , setSolverCachePath
  , setSolverCacheTimeout
  , printSolverCacheByHex
  , cleanMismatchedVersionsSolverCache
  , printSolverCacheStats
  , testSolverCacheStats
  ) where

import System.Directory (createDirectoryIfMissing)
import Control.Exception (try, SomeException)
import Control.Monad (when, forM_)
import System.Timeout (timeout)

import GHC.Generics (Generic)
import Data.IORef (IORef, newIORef, modifyIORef, readIORef)
import Data.Time.Clock (UTCTime, getCurrentTime)
import Data.Tuple.Extra (first, firstM)
import Data.List (elemIndex, intercalate, isPrefixOf)
import Data.Maybe (fromMaybe, isJust)
import Data.Functor ((<&>))
import Numeric (readHex)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Data.Text (Text)
import qualified Data.Text as Text
import Data.Text.Encoding (encodeUtf8)
import Text.Printf (printf)

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS

import qualified Crypto.Hash.SHA256 as SHA256

import Data.Aeson ( FromJSON(..), ToJSON(..), FromJSONKey(..), ToJSONKey(..)
                  , (.:), (.:?), (.=), fromJSON )
import qualified Data.Aeson as JSON
import Codec.CBOR.JSON (encodeValue, decodeValue)
import Codec.Serialise (Serialise(..))

import qualified Database.LMDB.Simple as LMDB
import qualified Database.LMDB.Simple.Extra as LMDB

import qualified Data.SBV.Dynamic as SBV

import SAWCore.FiniteValue
import SAWCore.SATQuery
import SAWCore.ExternalFormat
import SAWCore.SharedTerm

import SAWCentral.Options
import SAWCentral.Proof


-- Helper Functions ------------------------------------------------------------

-- | Run the given IO action, but if the given 'timeout' (in microseconds) is
-- reached or the action encounters any 'SomeException', 'Left' is returned
tryWithTimeout :: Int -> IO a -> IO (Either String a)
tryWithTimeout t_us m = try (timeout t_us m) <&> \case
  Right (Just a) -> Right a
  Right Nothing -> let t_str | t_us `mod` 1000000 == 0 = show (t_us `div` 1000000) ++ "s"
                             | t_us `mod` 1000    == 0 = show (t_us `div` 1000) ++ "ms"
                             | otherwise               = show t_us ++ "us"
                    in Left $ "Operation timed out (" ++ t_str ++ ")"
  Left (exn :: SomeException) -> Left $ show exn

-- | Encode a 'ByteString' as a hex string
encodeHex :: ByteString -> String
encodeHex = concatMap (printf "%02x") . BS.unpack

-- | Decode a hex string as a 'ByteString'
decodeHex :: String -> Either String ByteString
decodeHex s = BS.pack <$> go s
  where go (c0:c1:cs) | [(b,[])] <- readHex [c0,c1] = (b:) <$> go cs
        go [] = return []
        go _ = Left $ "Hex decoding failure on: " ++ s


-- Solver Backends -------------------------------------------------------------

-- | A datatype including all solver backends currently supported by SAW. This
-- type is most often used in a list (@[SolverBackend]@), since at least one
-- other backend is always used along with 'What4' or 'SBV' (e.g. 'SBV' with
-- 'Z3' or 'W4' with 'AIG' and 'ABC').
-- NOTE: This definition includes all backends supported by SBV, even though not
-- all of them are currently supported by SAW (namely, 'Bitwuzla' and 'DReal').
-- This is to ensure the system for keeping track of solver backend versions
-- is not silently broken if support for these backends is ever added to SAW.
data SolverBackend = What4
                   | SBV
                   | AIG
                   | RME
                   -- External solvers supported by SBV (copied from SBV.Solver)
                   | ABC
                   | Boolector
                   | Bitwuzla
                   | CVC4
                   | CVC5
                   | DReal -- NOTE: Not currently supported by SAW
                   | MathSAT
                   | OpenSMT -- NOTE: Not currently supported by SAW
                   | Yices
                   | Z3
                   deriving (Eq, Ord, Enum, Bounded, Show, Generic)

instance FromJSON SolverBackend where
  parseJSON = JSON.genericParseJSON JSON.defaultOptions
instance ToJSON SolverBackend where
  toJSON = JSON.genericToJSON JSON.defaultOptions
  toEncoding = JSON.genericToEncoding JSON.defaultOptions
instance FromJSONKey SolverBackend where
  fromJSONKey = JSON.genericFromJSONKey JSON.defaultJSONKeyOptions
instance ToJSONKey SolverBackend where
  toJSONKey = JSON.genericToJSONKey JSON.defaultJSONKeyOptions

-- | The list of all available 'SolverBackend's
allBackends :: [SolverBackend]
allBackends = [minBound..]

-- | Given an 'SBV.SMTConfig', return the list of corresponding 'SolverBackend's
sbvBackends :: SBV.SMTConfig -> [SolverBackend]
sbvBackends conf = [SBV, cvtSolver $ SBV.name $ SBV.solver conf]
  where cvtSolver SBV.ABC       = ABC
        cvtSolver SBV.Boolector = Boolector
        cvtSolver SBV.Bitwuzla  = Bitwuzla
        cvtSolver SBV.CVC4      = CVC4
        cvtSolver SBV.CVC5      = CVC5
        cvtSolver SBV.DReal     = DReal
        cvtSolver SBV.MathSAT   = MathSAT
        cvtSolver SBV.OpenSMT   = OpenSMT
        cvtSolver SBV.Yices     = Yices
        cvtSolver SBV.Z3        = Z3

-- | A datatype representing an option to one of the 'SolverBackend's.
-- Currently, there are only the following options for using 'What4': with a
-- tactic ('W4_Tactic'), by converting to SMTLib2 then calling ABC
-- ('W4_SMTLib2'), by converting to Verilog then calling ABC ('W4_Verilog'),
-- or by converting to AIGER then calling ABC ('W4_AIGER'). Note that certain
-- options may imply that additional 'SolverBackend's were used - see
-- 'optionBackends'.
data SolverBackendOption = W4_Tactic String
                         | W4_SMTLib2
                         | W4_Verilog
                         | W4_AIGER
                         deriving (Eq, Ord, Show, Generic)

instance FromJSON SolverBackendOption where
  parseJSON = JSON.genericParseJSON JSON.defaultOptions
                { JSON.sumEncoding = JSON.TwoElemArray }
instance ToJSON SolverBackendOption where
  toJSON = JSON.genericToJSON JSON.defaultOptions
             { JSON.sumEncoding = JSON.TwoElemArray }
  toEncoding = JSON.genericToEncoding JSON.defaultOptions
                { JSON.sumEncoding = JSON.TwoElemArray }

-- | Given a 'SolverBackendOption', return the list of additional
-- 'SolverBackend's that are used
optionBackends :: SolverBackendOption -> [SolverBackend]
optionBackends W4_AIGER = [AIG]
optionBackends _ = []

-- | A map from 'SolverBackend's to their version 'String's, if one could be
-- obtained
type SolverBackendVersions = Map SolverBackend (Maybe String)

-- | Pretty-print a 'SolverBackend' with its version 'String'
showSolverBackendVersion :: SolverBackend -> Maybe String -> [String] -> String
showSolverBackendVersion backend (Just v_str) opt_words =
  unwords $ show backend : v_str : opt_words
showSolverBackendVersion backend Nothing opt_words =
  showSolverBackendVersion backend (Just "[unknown version]") opt_words

-- | Pretty-print a set of 'SolverBackendVersions' and 'SolverBackendOption's
-- with the given 'String' separator
showBackendVersionsWithOptions :: String -> SolverBackendVersions ->
                                  [SolverBackendOption] -> String
showBackendVersionsWithOptions sep vs opts =
  let entries = M.unionWith (<>) (M.map (\v -> (v, [])) vs)
                                 (M.fromList $ optEntry <$> opts)
   in intercalate sep $ showEntry <$> M.toList entries
  where optEntry (W4_Tactic t) = (What4, (Nothing, ["using", t]))
        optEntry W4_SMTLib2    = (What4, (Nothing, ["to", "SMTLib2"]))
        optEntry W4_Verilog    = (What4, (Nothing, ["to", "Verilog"]))
        optEntry W4_AIGER      = (What4, (Nothing, ["to", "AIGER"]))
        showEntry (backend, (mb_v_str, opt_words)) =
          showSolverBackendVersion backend mb_v_str opt_words


-- Solver Cache Keys -----------------------------------------------------------

-- | The key type for 'SolverCache'. Each is a SHA256 hash of a 'SATQuery' (see
-- 'mkSolverCacheKey') along with optional solver version information used only
-- for pretty-printing.
data SolverCacheKey =
  SolverCacheKey
  { solverCacheKeyVersions :: SolverBackendVersions
  , solverCacheKeyOptions  :: [SolverBackendOption]
  , solverCacheKeyHash     :: ByteString
  }

instance Eq SolverCacheKey where
  (SolverCacheKey _ _ bs1) == (SolverCacheKey _ _ bs2) = bs1 == bs2

instance Show SolverCacheKey where
  show (SolverCacheKey vs opts bs) = encodeHex (BS.take 8 bs) ++
    if M.null vs && null opts then ""
    else " (" ++ showBackendVersionsWithOptions ", " vs opts ++ ")"

-- | Make a 'SolverCacheKey' with no version information
solverCacheKeyFromHash :: ByteString -> SolverCacheKey
solverCacheKeyFromHash = SolverCacheKey M.empty []

instance Serialise SolverCacheKey where
  encode = encode . solverCacheKeyHash
  decode = solverCacheKeyFromHash <$> decode

-- | Hash using SHA256 a 'String' representation of a 'SATQuery' and a 'Set' of
-- 'SolverBackendVersion's to get a 'SolverCacheKey'. In particular, this
-- 'String' representation contains all the 'SolverBackendVersion's, the
-- number of 'satVariables' in the 'SATQuery', the number of 'satUninterp's in
-- the 'SATQuery, and finally the 'scWriteExternal' representation of the
-- 'satQueryAsPropTerm' of the 'SATQuery' - with two additional things:
-- 1. Before calling 'scWriteExternal', we generalize ('scGeneralizeExts') over
--    all 'satVariables' and 'satUninterp's. This ensures the hash does not
--    depend on any execution-specific 'VarIndex'es.
-- 2. After calling 'scWriteExternal', all 'LocalName's in 'Pi' and 'Lam'
--    constructors are removed. This ensures that two terms which are alpha
--    equivalent are given the same hash.
mkSolverCacheKey :: SharedContext -> SolverBackendVersions ->
                    [SolverBackendOption] -> SATQuery -> IO SolverCacheKey
mkSolverCacheKey sc vs opts satq = do
  body <- satQueryAsPropTerm sc satq
  let ecs = M.keys (satVariables satq) ++
            filter (\ec -> ecVarIndex ec `elem` satUninterp satq)
                   (getAllExts body)
  tm <- scGeneralizeExts sc ecs body
  let str_prefix = [ showBackendVersionsWithOptions "\n" vs opts
                   , "satVariables " ++ show (M.size (satVariables satq))
                   , "satUninterp "  ++ show (length (satUninterp  satq)) ]
      str_to_hash = unlines str_prefix ++ anonLocalNames (scWriteExternal tm)
  return $ SolverCacheKey vs opts $ SHA256.hash $ encodeUtf8 $ Text.pack $ str_to_hash
  where anonLocalNames = unlines . map (unwords . go . words) . lines
        go (x:y:_:xs) | y `elem` ["Pi", "Lam"] = x:y:"_":xs
        go xs = xs


-- Solver Cache Values ---------------------------------------------------------

-- | The value type for 'SolverCache': solver version information, the timestamp
-- of when the entry was last used, a 'Text' representing the solver used, and
-- an optional list of counterexamples, represented as pairs of indexes into the
-- list of 'satVariables' of an associated 'SATQuery'
data SolverCacheValue =
  SolverCacheValue
  { solverCacheValueVersions   :: SolverBackendVersions
  , solverCacheValueOptions    :: [SolverBackendOption]
  , solverCacheValueSolverName :: Text
  , solverCacheValueCEXs       :: Maybe [(Int, FirstOrderValue)]
  , solverCacheValueLastUsed   :: UTCTime
  } deriving Eq

instance FromJSON SolverCacheValue where
  parseJSON = JSON.withObject "SolverCacheValue" $ \v -> do
    vs      <- v .:  "vs"
    opts    <- v .:? "opts"
    nm      <- v .:  "nm"
    mb_cexs <- v .:? "cexs"
    t       <- v .:  "t"
    return $ SolverCacheValue vs (fromMaybe [] opts) nm mb_cexs t

instance ToJSON SolverCacheValue where
  toJSON (SolverCacheValue vs opts nm mb_cexs t) = JSON.object $
    ["vs" .= vs] ++ (if null opts then [] else ["opts" .= opts]) ++
    ["nm" .= nm] ++ maybe [] (\cexs -> ["cexs" .= cexs]) mb_cexs ++ ["t" .= t]
  toEncoding (SolverCacheValue vs opts nm mb_cexs t) = JSON.pairs $
    "vs" .= vs <> (if null opts then mempty else "opts" .= opts) <>
    "nm" .= nm <> maybe mempty (\cexs -> "cexs" .= cexs) mb_cexs <> "t" .= t

-- NOTE: We go through JSON because the `aeson` library gives us much nicer and
-- more customizable encodings than the `serialise` library, and because there
-- is a bijection between JSON and CBOR so we can freely pass between the two
instance Serialise SolverCacheValue where
  encode = encodeValue . toJSON
  decode = do
    v <- decodeValue False
    case fromJSON v of
      JSON.Success x -> return x
      JSON.Error e -> fail e

-- | Convert the result of a solver call on the given 'SATQuery' to a
-- 'SolverCacheValue'
toSolverCacheValue :: SolverBackendVersions -> [SolverBackendOption] ->
                      SATQuery -> (Maybe CEX, Text) ->
                      IO (Maybe SolverCacheValue)
toSolverCacheValue vs opts satq (cexs, solver_name) = do
  getCurrentTime <&> \t -> case firstsMaybeM (`elemIndex` ecs) cexs of
    Just cexs' -> Just $ SolverCacheValue vs opts solver_name cexs' t
    Nothing -> Nothing
  where ecs = M.keys $ satVariables satq
        firstsMaybeM :: Monad m => (a -> m b) ->
                        Maybe [(a, c)] -> m (Maybe [(b, c)])
        firstsMaybeM = mapM . mapM . firstM

-- | Convert a 'SolverCacheValue' to something which has the same form as the
-- result of a solver call on the given 'SATQuery'
fromSolverCacheValue :: SATQuery -> SolverCacheValue -> (Maybe CEX, Text)
fromSolverCacheValue satq (SolverCacheValue _ _ solver_name cexs _) =
  (firstsMaybe (ecs !!) cexs, solver_name)
  where ecs = M.keys $ satVariables satq
        firstsMaybe :: (a -> b) -> Maybe [(a, c)] -> Maybe [(b, c)]
        firstsMaybe = fmap . fmap . first


-- The Solver Cache ------------------------------------------------------------

-- | A 'SolverCache' consists of a 'FilePath' to an LMDB database (which may or
-- may not exist yet), an optional LMDB database at that path (represented as an
-- 'LMDB.Environment' and 'LMDB.Database' once it is created), counters for how
-- many lookups, failed lookups, insertions, and failed insertions have been made
-- (see 'SolverCacheStat'), a map size for the LMDB database, and a timeout to
-- use for database lookups and inserts. Note that the counters are stored in an
-- 'IORef' to make sure failures are counted correctly.
data SolverCache =
  SolverCache
  { solverCachePath    :: FilePath
  , solverCacheEnv     :: Maybe (LMDB.Environment LMDB.ReadWrite)
  , solverCacheDB      :: Maybe (LMDB.Database SolverCacheKey SolverCacheValue)
  , solverCacheStats   :: IORef (Map SolverCacheStat Integer)
  , solverCacheMapSize :: Int
  , solverCacheTimeout :: Int -- ^ In microseconds.
  }

-- | A statistic to track in 'solverCacheStats'
data SolverCacheStat = Lookups | FailedLookups | Inserts | FailedInserts
                     deriving (Eq, Ord, Bounded, Enum)

-- | Create a 'SolverCache' with the given 'FilePath', but do not yet open an
-- LMDB database at that path (i.e. `solverCacheEnv` and `solverCacheDB` are
-- both set to 'Nothing')
lazyOpenSolverCache :: FilePath -> IO SolverCache
lazyOpenSolverCache path = do
  stats <- newIORef $ M.fromList ((,0) <$> [minBound..])
  return SolverCache { solverCachePath    = path,
                       solverCacheEnv     = Nothing,
                       solverCacheDB      = Nothing,
                       solverCacheStats   = stats,
                       solverCacheMapSize = 4 {- GiB -} * 1073741824,
                       solverCacheTimeout = 2 {- sec -} * 1000000 }

-- | Create a 'SolverCache' with the given 'FilePath' and open an LMDB database
-- at that path (i.e. `solverCacheEnv` and `solverCacheDB` are both 'Just')
openSolverCache :: FilePath -> IO SolverCache
openSolverCache path = do
  (_, _, cache') <- forceSolverCacheOpened =<< lazyOpenSolverCache path
  return cache'

-- | Ensure that the given 'SolverCache' has opened an LMDB database at its set
-- 'FilePath' - returning either the newly created or previously created
-- 'LMDB.Environment' and 'LMDB.Database', as well as an 'SolverCache'
-- containing both of them
forceSolverCacheOpened :: SolverCache ->
                          IO (LMDB.Environment LMDB.ReadWrite,
                              LMDB.Database SolverCacheKey SolverCacheValue,
                              SolverCache)
forceSolverCacheOpened cache@SolverCache{ solverCacheEnv = Just env
                                        , solverCacheDB  = Just db } =
  return (env, db, cache)
forceSolverCacheOpened cache@SolverCache{..} = do
  createDirectoryIfMissing True solverCachePath
  let limits = LMDB.defaultLimits { LMDB.mapSize = solverCacheMapSize }
  env <- LMDB.openEnvironment solverCachePath limits
  db <- LMDB.readOnlyTransaction env (LMDB.getDatabase Nothing)
  let cache' = cache { solverCacheEnv = Just env, solverCacheDB = Just db }
  return (env, db, cache')

-- | Try to call 'forceSolverCacheOpened' then try to perform the given
-- 'LMDB.Transaction' on the LMDB database associated to the given
-- 'SolverCache', returning 'Left' if an error or timeout occurred at any point
-- and 'Right' otherwise, as well as the updated 'SolverCache' returned by
-- 'forceSolverCacheOpened'
tryTransaction :: (LMDB.Mode tmode, LMDB.SubMode LMDB.ReadWrite tmode) =>
                  SolverCache ->
                  (LMDB.Database SolverCacheKey SolverCacheValue ->
                   LMDB.Transaction tmode a) ->
                  IO (Either String a, SolverCache)
tryTransaction cache@SolverCache{..} t =
  tryWithTimeout solverCacheTimeout (forceSolverCacheOpened cache) >>= \case
    Right (env, db, cache') ->
      (,cache') <$> tryWithTimeout solverCacheTimeout
                                   (LMDB.transaction env (t db))
    Left err ->
      return (Left $ "Failed to open LMDB database: " ++ err, cache)

-- | An operation on a 'SolverCache', returning a value of the given type as
-- well as an updated 'SolverCache' ('solverCacheOp'). Additionally, in the case
-- of no enabled solver cache, the operation could either fail or return a
-- default value ('solverCacheOpDefault').
data SolverCacheOp a = SCOpOrFail (Options -> SolverCache -> IO (a, SolverCache))
                     | SCOpOrDefault a (Options -> SolverCache -> IO (a, SolverCache))

-- | Get the operation associated to a 'SolverCacheOp'
solverCacheOp :: SolverCacheOp a -> Options -> SolverCache -> IO (a, SolverCache)
solverCacheOp (SCOpOrFail f) = f
solverCacheOp (SCOpOrDefault _ f) = f

-- | Get the default value associated to a 'SolverCacheOp', if any
solverCacheOpDefault :: SolverCacheOp a -> Maybe a
solverCacheOpDefault (SCOpOrFail _) = Nothing
solverCacheOpDefault (SCOpOrDefault a _) = Just a

-- | Lookup a 'SolverCacheKey' in the solver result cache
lookupInSolverCache :: SolverCacheKey -> SolverCacheOp (Maybe SolverCacheValue)
lookupInSolverCache k = SCOpOrDefault Nothing $ \opts cache@SolverCache{..} ->
  getCurrentTime >>= \now ->
  let upd v = Just v { solverCacheValueLastUsed = now } in
  tryTransaction @LMDB.ReadOnly cache (LMDB.lookup k) >>= \case
    (Right (Just v), cache') -> do
      printOutLn opts Debug ("Using cached result: " ++ show k)
      modifyIORef solverCacheStats $ M.adjust (+1) Lookups
      cache'' <- snd <$> tryTransaction cache' (LMDB.update upd k)
      return (Just v, cache'')
    (Left err, cache') -> do
      printOutLn opts Warn ("Solver cache lookup failed:\n" ++ err)
      modifyIORef solverCacheStats $ M.adjust (+1) FailedLookups
      return (Nothing, cache')
    (Right Nothing, cache') -> do
      return (Nothing, cache')

-- | Add a 'SolverCacheValue' to the solver result cache
insertInSolverCache :: SolverCacheKey -> SolverCacheValue -> SolverCacheOp ()
insertInSolverCache k v = SCOpOrDefault () $ \opts cache@SolverCache{..} ->
  printOutLn opts Debug ("Caching result: " ++ show k) >>
  tryTransaction cache (LMDB.insert k v) >>= \case
    (Right (), cache') -> do
      modifyIORef solverCacheStats $ M.adjust (+1) Inserts
      return ((), cache')
    (Left err, cache') -> do
      printOutLn opts Warn ("Solver cache insert failed:\n" ++ err)
      modifyIORef solverCacheStats $ M.adjust (+1) FailedInserts
      return ((), cache')

-- | Set the 'FilePath' of the solver result cache and save all results cached
-- so far
setSolverCachePath :: FilePath -> SolverCacheOp ()
setSolverCachePath path = SCOpOrFail $ \opts cache@SolverCache{..} ->
  if path == solverCachePath
  then do
    (_, _, cache') <- forceSolverCacheOpened cache
    return ((), cache')
  else do
    (new_env, new_db, cache') <-
        forceSolverCacheOpened cache { solverCachePath = path
                                     , solverCacheEnv  = Nothing
                                     , solverCacheDB   = Nothing }
    case (solverCacheEnv, solverCacheDB) of
      (Just old_env, Just old_db) -> do
        kvs <- LMDB.readOnlyTransaction old_env $ LMDB.toList old_db
        forM_ kvs $ \(k,v) -> LMDB.transaction new_env $ LMDB.insert k v new_db
        printOutLn opts Info ("Saved " ++ show (length kvs) ++ " cached result" ++
                              (if length kvs == 1 then "" else "s") ++ " to disk")
        return ((), cache')
      _ -> return ((), cache')

-- | Set the solver result cache's timeout to use for database lookups and
-- inserts.
setSolverCacheTimeout :: Int -> SolverCacheOp ()
setSolverCacheTimeout tout = SCOpOrFail $ \_opts cache ->
  pure ((), cache { solverCacheTimeout = tout })

-- | Print all entries in the solver result cache whose SHA256 hash keys start
-- with the given string
printSolverCacheByHex :: Text -> SolverCacheOp ()
printSolverCacheByHex hex_pref_txt = SCOpOrFail $ \opts cache -> do
  let hex_pref = Text.unpack hex_pref_txt
  (env, db, cache') <- forceSolverCacheOpened cache
  let flt k v kvs = if hex_pref `isPrefixOf` encodeHex (solverCacheKeyHash k)
                    then (k,v):kvs else kvs
  kvs <- case decodeHex hex_pref of
    Right (solverCacheKeyFromHash -> k) -> do
      LMDB.readOnlyTransaction env (LMDB.lookup k db) >>= \case
        Just v -> return [(k,v)]
        Nothing -> LMDB.readOnlyTransaction env $ LMDB.foldrWithKey flt [] db
    Left _ -> LMDB.readOnlyTransaction env $ LMDB.foldrWithKey flt [] db
  when (length kvs == 0) $ printOutLn opts Info "No keys found"
  forM_ kvs $ \(k, SolverCacheValue vs bk_opts nm mb_cexs t) -> do
    let vs_str = showBackendVersionsWithOptions ", " vs bk_opts
        res_str = maybe "unsat" (("sat " ++) . show) mb_cexs
    printOutLn opts Info $ "SHA: " ++ encodeHex (solverCacheKeyHash k)
    printOutLn opts Info $ "- Result: " ++ res_str
    printOutLn opts Info $ "- Solver: " ++ show nm
    printOutLn opts Info $ "- Versions: " ++ vs_str
    printOutLn opts Info $ "- Last used: " ++ show t ++ "\n"
  return ((), cache')

-- | Remove all entries in the solver result cache which have version(s) that
-- do not match the current version(s) or are marked as stale
cleanMismatchedVersionsSolverCache :: SolverBackendVersions -> SolverCacheOp ()
cleanMismatchedVersionsSolverCache curr_base_vs = SCOpOrFail $ \opts cache -> do
  let known_curr_base_vs = M.filter isJust curr_base_vs
      mismatched_vs vs = M.mapMaybe id $ M.intersectionWith
        (\base_ver v_ver -> if base_ver /= v_ver
                            then Just (base_ver, v_ver) else Nothing)
        known_curr_base_vs vs
      flt k v (ks, mvs) = let mvs' = mismatched_vs (solverCacheValueVersions v)
                           in if M.null mvs' then (ks, mvs)
                                             else (k:ks, M.union mvs mvs')
  (env, db, cache') <- forceSolverCacheOpened cache
  (ks, mvs) <- LMDB.readOnlyTransaction env $ LMDB.foldrWithKey flt ([], M.empty) db
  forM_ ks $ \k -> LMDB.transaction env $ LMDB.delete k db
  let s0 = if length ks == 1 then "" else "s"
      s1 = if M.size mvs == 0 then "" else ":"
  printOutLn opts Info $
    "Removed " ++ show (length ks) ++
    " cached result" ++ s0 ++ " with mismatched version" ++ s0 ++ s1
  forM_ (M.toList mvs) $ \(backend, (v1, v2)) ->
    printOutLn opts Info $
      "- " ++ showSolverBackendVersion backend v1 [] ++
      " (Current: " ++ showSolverBackendVersion backend v2 [] ++ ")"
  sz <- LMDB.readOnlyTransaction env $ LMDB.size db
  let (sz0, sz1) = if sz == 1 then ("is", "") else ("are", "s")
  printOutLn opts Info $ "There " ++ sz0 ++ " " ++ show sz ++ " result"
                                  ++ sz1 ++ " remaining in the cache"
  return ((), cache')

-- | Print out statistics about how the solver cache was used
printSolverCacheStats :: SolverCacheOp ()
printSolverCacheStats = SCOpOrFail $ \opts cache@SolverCache{..} -> do
  (env, db, cache') <- forceSolverCacheOpened cache
  printOutLn opts Info ("== Solver result cache statistics ==")
  sz <- LMDB.readOnlyTransaction env $ LMDB.size db
  printOutLn opts Info ("- " ++ show sz ++ " result" ++ pl sz
                             ++ " cached in " ++ solverCachePath)
  stats <- readIORef solverCacheStats
  let (ls, ls_f) = (stats M.! Lookups, stats M.! FailedLookups)
      (is, is_f) = (stats M.! Inserts, stats M.! FailedInserts)
  printOutLn opts Info $ "- " ++ show is ++ " insertion" ++ pl is
                              ++ " into the cache so far this run ("
                              ++ show is_f ++ " failed attempt" ++ pl is_f ++ ")"
  printOutLn opts Info $ "- " ++ show ls ++ " usage" ++ pl ls
                              ++ " of cached results so far this run ("
                              ++ show ls_f ++ " failed attempt" ++ pl ls_f ++ ")"
  return ((), cache')
  where pl i = if i == 1 then "" else "s"

-- | Check whether the values of the statistics printed out by
-- 'printSolverCacheStats' are equal to those given, failing if this does not
-- hold
testSolverCacheStats :: Integer -> Integer -> Integer -> Integer -> Integer ->
                        SolverCacheOp ()
testSolverCacheStats sz ls ls_f is is_f = SCOpOrFail $ \opts cache@SolverCache{..} -> do
  (env, db, cache') <- forceSolverCacheOpened cache
  sz_actual <- fromIntegral <$> LMDB.readOnlyTransaction env (LMDB.size db)
  test sz sz_actual "Size of solver cache"
  stats <- readIORef solverCacheStats
  test ls (stats M.! Lookups) "Number of usages of solver cache"
  test ls_f (stats M.! FailedLookups) "Number of failed usages of solver cache"
  test is (stats M.! Inserts) "Number of insertions into solver cache"
  test is_f (stats M.! FailedInserts) "Number of failed insertions into solver cache"
  printOutLn opts Info $ "Solver cache stats matched expected (" ++ show sz ++ " " ++
    show ls ++ " " ++ show ls_f ++ " " ++ show is ++ " " ++ show is_f ++ ")"
  return ((), cache')
  where test v v_actual str = when (v /= v_actual) $ fail $
          str ++ " (" ++ show v_actual ++ ")"
              ++ " did not match expected (" ++ show v ++ ")"
