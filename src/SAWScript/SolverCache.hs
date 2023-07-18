{- |
Module      : SAWScript.SolverCache
Description : Caching SMT solver results for SAWScript
License     : BSD3
Maintainer  : m-yac
Stability   : provisional

This file defines an interface for caching SMT/SAT solver results in memory and
on disk. The interface, as used in 'applyProverToGoal', works as follows:

1. An 'SMTQuery' is converted into a string using 'scWriteExternal', and
   along with any relevant 'SolverBackendVersion's (obtained using
   'getSolverBackendVersions' from @SAWScript.SolverVersions@), is then hashed
   using SHA256 ('mkSolverCacheKey').
2. The 'SolverCache' contains an 'LMDBOptDatabase' mapping these hashes to
   previously obtained results ('solverCacheDB'). If the hash corresponding to
   the 'SATQuery' and 'SolverBackendVersion's can be found in the database
   ('lookupInSolverCache'), then the corresponding result is used.
3. Otherwise, the 'SATQuery' is dispatched to the requested backend and a
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
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module SAWScript.SolverCache
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
  , emptySolverCache
  , SolverCacheOp
  , lookupInSolverCache
  , insertInSolverCache
  , setSolverCachePath
  , printSolverCacheByHex
  , cleanSolverCache
  , printSolverCacheStats
  , testSolverCacheStats
  ) where

import System.Directory (createDirectoryIfMissing, makeAbsolute)
import Control.Exception (try, SomeException)
import Control.Monad (when, forM_)
import System.Timeout (timeout)

import GHC.Generics (Generic)
import Data.IORef (IORef, newIORef, modifyIORef, readIORef)
import Data.Tuple.Extra (first, firstM, both)
import Data.List (elemIndex, intercalate)
import Data.Maybe (fromMaybe, isJust)
import Data.Functor ((<&>))

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import qualified Data.Text as T
import Data.Text.Encoding

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS

import qualified Crypto.Hash.SHA256 as SHA256

import Data.Aeson ( FromJSON(..), ToJSON(..), FromJSONKey(..), ToJSONKey(..)
                  , (.:), (.:?), (.=) )
import qualified Data.Aeson as JSON

import qualified Data.SBV.Dynamic as SBV

import Verifier.SAW.FiniteValue
import Verifier.SAW.SATQuery
import Verifier.SAW.ExternalFormat
import Verifier.SAW.SharedTerm

import SAWScript.SolverCache.LMDBOptDatabase (encodeHex, LMDBOptDatabase)
import qualified SAWScript.SolverCache.LMDBOptDatabase as LMDBOpt

import SAWScript.Options
import SAWScript.Proof


-- Orphan Instances and Helper Functions ---------------------------------------

deriving instance Generic FirstOrderType
deriving instance Generic FirstOrderValue

-- | The options for JSON-serializing 'FirstOrderType's and 'FirstOrderValue's:
-- remove the @FOV@/@FOT@ prefixes and encode the different constructors as
-- two-element arrays.
firstOrderJSONOptions :: JSON.Options
firstOrderJSONOptions =
  JSON.defaultOptions { JSON.sumEncoding = JSON.TwoElemArray
                      , JSON.constructorTagModifier = dropFO }
  where dropFO ('F':'O':tv:cs) | tv `elem` ['T', 'V'] = cs
        dropFO cs = cs

instance FromJSON FirstOrderType where
  parseJSON = JSON.genericParseJSON firstOrderJSONOptions
instance FromJSON FirstOrderValue where
  parseJSON = JSON.genericParseJSON firstOrderJSONOptions

instance ToJSON FirstOrderType where
  toJSON = JSON.genericToJSON firstOrderJSONOptions
  toEncoding = JSON.genericToEncoding firstOrderJSONOptions
instance ToJSON FirstOrderValue where
  toJSON = JSON.genericToJSON firstOrderJSONOptions
  toEncoding = JSON.genericToEncoding firstOrderJSONOptions

-- | Run the given IO action, but if the given 'timeout' (in ms) is reached
-- or the action encounters any 'SomeException', 'Left' is returned
tryWithTimeout :: Int -> IO a -> IO (Either String a)
tryWithTimeout t_ms m = try (timeout (t_ms * 1000) m) <&> \case
  Right (Just a) -> Right a
  Right Nothing  -> Left $ "Operation timed out (" ++ show t_ms ++ "ms)"
  Left (exn :: SomeException) -> Left $ show exn


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
                   | Bitwuzla -- NOTE: Not currently supported by SAW
                   | CVC4
                   | CVC5
                   | DReal -- NOTE: Not currently supported by SAW
                   | MathSAT
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
instance ToJSON SolverBackendOption where
  toJSON = JSON.genericToJSON JSON.defaultOptions
  toEncoding = JSON.genericToEncoding JSON.defaultOptions

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

-- | The key type for 'SolverCache'. Each is a SHA256 hash of a 'SATQuery' and
-- a 'Set' of 'SolverBackendVersion's - see 'mkSolverCacheKey'
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
  return $ SolverCacheKey vs opts $ SHA256.hash $ encodeUtf8 $ T.pack $ str_to_hash
  where anonLocalNames = unlines . map (unwords . go . words) . lines
        go (x:y:_:xs) | y `elem` ["Pi", "Lam"] = x:y:"_":xs
        go xs = xs


-- Solver Cache Values ---------------------------------------------------------

-- | The value type for 'SolverCache': a 'Set' of 'SolverBackendVersion's, a
-- 'String' representing the solver used, and an optional list of
-- counterexamples, represented as pairs of indexes into the list of
-- 'satVariables' of an associated 'SATQuery'
data SolverCacheValue =
  SolverCacheValue
  { solverCacheValueVersions   :: SolverBackendVersions
  , solverCacheValueOptions    :: [SolverBackendOption]
  , solverCacheValueSolverName :: String
  , solverCacheValueCEXs       :: Maybe [(Int, FirstOrderValue)]
  } deriving Eq

instance FromJSON SolverCacheValue where
  parseJSON = JSON.withObject "SolverCacheValue" $ \v -> do
    vs      <- v .:  "vs"
    opts    <- v .:? "opts"
    nm      <- v .:  "nm"
    mb_cexs <- v .:? "cexs"
    return $ SolverCacheValue vs (fromMaybe [] opts) nm mb_cexs

instance ToJSON SolverCacheValue where
  toJSON (SolverCacheValue vs opts nm mb_cexs) = JSON.object $
    ["vs" .= vs] ++ (if null opts then [] else ["opts" .= opts]) ++
    ["nm" .= nm] ++ maybe [] (\cexs -> ["cexs" .= cexs]) mb_cexs
  toEncoding (SolverCacheValue vs opts nm mb_cexs) = JSON.pairs $
    "vs" .= vs <> (if null opts then mempty else "opts" .= opts) <>
    "nm" .= nm <> maybe mempty (\cexs -> "cexs" .= cexs) mb_cexs

-- | Convert the result of a solver call on the given 'SATQuery' to a
-- 'SolverCacheValue'
toSolverCacheValue :: SolverBackendVersions -> [SolverBackendOption] ->
                      SATQuery -> (Maybe CEX, String) -> Maybe SolverCacheValue
toSolverCacheValue vs opts satq (cexs, solver_name) =
  SolverCacheValue vs opts solver_name <$> firstsMaybeM (`elemIndex` ecs) cexs
  where ecs = M.keys $ satVariables satq
        firstsMaybeM :: Monad m => (a -> m b) ->
                        Maybe [(a, c)] -> m (Maybe [(b, c)])
        firstsMaybeM = mapM . mapM . firstM

-- | Convert a 'SolverCacheValue' to something which has the same form as the
-- result of a solver call on the given 'SATQuery'
fromSolverCacheValue :: SATQuery -> SolverCacheValue -> (Maybe CEX, String)
fromSolverCacheValue satq (SolverCacheValue _ _ solver_name cexs) =
  (firstsMaybe (ecs !!) cexs, solver_name)
  where ecs = M.keys $ satVariables satq
        firstsMaybe :: (a -> b) -> Maybe [(a, c)] -> Maybe [(b, c)]
        firstsMaybe = fmap . fmap . first
       


-- The Solver Cache ------------------------------------------------------------

-- | A 'SolverCacheDB' of cached solver results, a timeout in milliseconds to
-- use for all lookups and insertions into the DB, as well as counters for how
-- many lookups, failed lookups, insertions, and failed insertions have been
-- made (see 'SolverCacheStat'). The latter are represented as an 'IORef' to
-- make sure failures are counted correctly.
data SolverCache =
  SolverCache
  { solverCacheDB      :: LMDBOptDatabase SolverCacheValue
  , solverCacheStats   :: IORef (Map SolverCacheStat Integer)
  , solverCacheTimeout :: Int
  }

-- | A statistic to track in 'solverCacheStats'
data SolverCacheStat = Lookups | FailedLookups | Inserts | FailedInserts
                     deriving (Eq, Ord, Bounded, Enum)

-- | An empty 'SolverCache' with no associated 'FilePath'
emptySolverCache :: IO SolverCache
emptySolverCache = do
  db <- LMDBOpt.new
  stats <- newIORef $ M.fromList ((,0) <$> [minBound..])
  return $ SolverCache db stats 1000

-- | An operation on a 'SolverCache', returning a value of the given type or
-- returning an optional default value in the case of no enabled 'SolverCache'
type SolverCacheOp a = (Maybe a, Options -> SolverCache -> IO a)

-- | Lookup a 'SolverCacheKey' in the solver result cache
lookupInSolverCache :: SolverCacheKey -> SolverCacheOp (Maybe SolverCacheValue)
lookupInSolverCache k = (Just Nothing,) $ \opts SolverCache{..} ->
  tryWithTimeout solverCacheTimeout
                 (LMDBOpt.lookup (solverCacheKeyHash k)
                                 solverCacheDB) >>= \case
    Right (Just v) -> do
      printOutLn opts Debug ("Using cached result: " ++ show k)
      modifyIORef solverCacheStats $ M.adjust (+1) Lookups
      return (Just v)
    Left err -> do
      printOutLn opts Warn ("Solver cache lookup failed:\n" ++ err)
      modifyIORef solverCacheStats $ M.adjust (+1) FailedLookups
      return Nothing
    Right Nothing -> do
      return Nothing

-- | Add a 'SolverCacheValue' to the solver result cache
insertInSolverCache :: SolverCacheKey -> SolverCacheValue -> SolverCacheOp ()
insertInSolverCache k v = (Just (),) $ \opts SolverCache{..} ->
  printOutLn opts Debug ("Caching result: " ++ show k) >>
  tryWithTimeout solverCacheTimeout
                 (LMDBOpt.insert (solverCacheKeyHash k) v
                                 solverCacheDB) >>= \case
    Right () -> do
      modifyIORef solverCacheStats $ M.adjust (+1) Inserts
    Left err -> do
      printOutLn opts Warn ("Solver cache insert failed:\n" ++ err)
      modifyIORef solverCacheStats $ M.adjust (+1) FailedInserts

-- | Set the 'FilePath' of the solver result cache and save all results cached
-- so far
setSolverCachePath :: FilePath -> SolverCacheOp ()
setSolverCachePath path = (Nothing,) $ \opts SolverCache{..} -> do
  pathAbs <- makeAbsolute path
  createDirectoryIfMissing True pathAbs
  eith_sz <- tryWithTimeout solverCacheTimeout
                            (LMDBOpt.size solverCacheDB)
  eith_db <- tryWithTimeout solverCacheTimeout
                            (LMDBOpt.setPath pathAbs 4096 solverCacheDB)
  case (,) <$> eith_sz <*> eith_db of
    Left err -> fail $ "Could not set solver cache path:\n" ++ err
    Right (sz, ()) | sz == 0 -> return ()
    Right (sz, ()) -> do
      let (s0, s1) = (show sz, if sz == 1 then "" else "s")
      printOutLn opts Info ("Saved " ++ s0 ++ " cached result" ++ s1 ++ " to disk")

-- | Print all entries in the solver result cache whose SHA256 hash keys start
-- with the given string
printSolverCacheByHex :: String -> SolverCacheOp ()
printSolverCacheByHex hex_prefix = (Nothing,) $ \opts SolverCache{..} -> do
  kvs <- LMDBOpt.filterByHexPrefix hex_prefix solverCacheDB
  when (length kvs == 0) $ printOutLn opts Info "No keys found"
  forM_ kvs $ \(k_hash, SolverCacheValue vs bk_opts nm mb_cexs) -> do
    let vs_str = showBackendVersionsWithOptions ", " vs bk_opts
        res_str = maybe "unsat" (("sat " ++) . show) mb_cexs
    printOutLn opts Info $ "SHA: " ++ encodeHex k_hash
    printOutLn opts Info $ "- Result: " ++ res_str
    printOutLn opts Info $ "- Solver: " ++ show nm
    printOutLn opts Info $ "- Versions: " ++ vs_str ++ "\n"

-- | Remove all entries in the solver result cache which have version(s) that
-- do not match the current version(s)
cleanSolverCache :: SolverBackendVersions -> SolverCacheOp ()
cleanSolverCache curr_base_vs = (Nothing,) $ \opts SolverCache{..} -> do
  let curr_base_vs_obj = M.fromList [("vs", curr_base_vs)]
  fs0 <- LMDBOpt.cleanByJSONObjValues curr_base_vs_obj solverCacheDB
  let fs1 = concatMap (fmap (both (M.! ("vs" :: String))) . snd) fs0
      fs2 = M.unions $ fmap (uncurry $ M.intersectionWith (,)) fs1
      s0 = if length fs0 == 1 then "" else "s"
      s1 = if M.size fs2 == 0 then "" else ":"
  printOutLn opts Info $
    "Removed " ++ show (length fs0) ++
    " cached result" ++ s0 ++ " with mismatched version" ++ s0 ++ s1
  forM_ (M.toList fs2) $ \(backend, (v1, v2)) ->
    printOutLn opts Info $
      "- " ++ showSolverBackendVersion backend v1 [] ++
      " (Current: " ++ showSolverBackendVersion backend v2 [] ++ ")"

-- | Print out statistics about how the solver cache was used
printSolverCacheStats :: SolverCacheOp ()
printSolverCacheStats = (Nothing,) $ \opts SolverCache{..} -> do
  printOutLn opts Info ("== Solver result cache statistics ==")
  sz <- LMDBOpt.size solverCacheDB
  loc <- fromMaybe "memory" <$> LMDBOpt.getPath solverCacheDB
  printOutLn opts Info ("- " ++ show sz ++ " result" ++ pl sz
                             ++ " cached in " ++ loc)
  stats <- readIORef solverCacheStats
  let (ls, ls_f) = (stats M.! Lookups, stats M.! FailedLookups)
      (is, is_f) = (stats M.! Inserts, stats M.! FailedInserts)
  printOutLn opts Info $ "- " ++ show is ++ " insertion" ++ pl is
                              ++ " into the cache so far this run ("
                              ++ show is_f ++ " failed attempt" ++ pl is_f ++ ")"
  printOutLn opts Info $ "- " ++ show ls ++ " usage" ++ pl ls
                              ++ " of cached results so far this run ("
                              ++ show ls_f ++ " failed attempt" ++ pl ls_f ++ ")"
  where pl i = if i == 1 then "" else "s"

-- | Check whether the values of the statistics printed out by
-- 'printSolverCacheStats' are equal to those given, failing if this does not
-- hold
testSolverCacheStats :: Integer -> Bool -> Integer -> Integer -> Integer ->
                        Integer -> SolverCacheOp ()
testSolverCacheStats sz p ls ls_f is is_f = (Nothing,) $ \opts SolverCache{..} -> do
  sz_actual <- fromIntegral <$> LMDBOpt.size solverCacheDB
  test sz sz_actual "Size of solver cache"
  p_actual <- isJust <$> LMDBOpt.getPath solverCacheDB
  test p p_actual "Whether solver cache saved to disk"
  stats <- readIORef solverCacheStats
  test ls (stats M.! Lookups) "Number of usages of solver cache"
  test ls_f (stats M.! FailedLookups) "Number of failed usages of solver cache"
  test is (stats M.! Inserts) "Number of insertions into solver cache"
  test is_f (stats M.! FailedInserts) "Number of failed insertions into solver cache"
  printOutLn opts Info $ "Solver cache stats matched expected (" ++ show sz ++
                         (if p then " true " else " false ") ++ show ls ++ " " ++
                         show ls_f ++ " " ++ show is ++ " " ++ show is_f ++ ")"
  where test v v_actual str = when (v /= v_actual) $ fail $
          str ++ " (" ++ show v_actual ++ ")"
              ++ " did not match expected (" ++ show v ++ ")"
