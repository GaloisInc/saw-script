{- |
Module      : SAWScript.SolverCache
Description : Caching SMT solver results for SAWScript
License     : BSD3
Maintainer  : m-yac
Stability   : provisional

This file defines an interface for caching SMT/SAT solver results in memory and
on disk. The interface, as used in 'applyProverToGoal', works as follows:

1. An 'SMTQuery' is converted into a string using 'scWriteExternal', and
   along with any relevant 'SolverBackendVersions' (obtained using
   'getSolverBackendVersions' from @SAWScript.SolverVersions@), is then hashed
   using SHA256 ('mkSolverCacheKey').
2. The 'SolverCache' contains a map from these hashes to previously obtained
   results ('solverCacheMap'). If the hash corresponding to the 'SATQuery' and
   'SolverBackendVersions' can be found in the map, then the corresponding
   result is used.
3. Otherwise, if the 'SolverCache' was given a path to a directory
   ('solverCachePath') and a file whose name is the hash can be found in that
   directory, the file's contents are 'read' and used as the result.
4. Otherwise, the 'SATQuery' is dispatched to the requested backend and a
   result is obtained. Then:
   - This result is added to the 'SolverCache' map using the hash of the
     'SATQuery' and 'SolverBackendVersions' as the key.
   - If the 'SolverCache' was given a path to a directory ('solverCachePath'),
     then a file whose name is the hash and whose contents are 'show' of the
     result is added to the directory.

A interesting detail is how results are represented. For all of the backends
which use 'applyProverToGoal', the type of a result is:
@Maybe [(ExtCns Term, FirstOrderValue)]@, where 'Nothing' represents a result
of "unsat," and 'Just' represents a result of "sat" along with a list of
counterexamples. Since 'ExtCns' contains execution-specific 'VarIndex'es, we
don't want to save these results directly. Instead, we represent each 'ExtCns'
as its index in the 'satVariables' field of 'SATQuery' (which is where they
were obtained by the backends in the first place).
-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module SAWScript.SolverCache
  ( SolverBackendVersions
  , SolverCacheKey(..)
  , solverCacheKeyToHex
  , mkSolverCacheKey
  , SolverCacheValue
  , toSolverCacheValue
  , fromSolverCacheValue
  , SolverCache(..)
  , emptySolverCache
  , SolverCacheOp
  , lookupInSolverCache
  , insertInSolverCache
  , setSolverCachePath
  , printSolverCacheStats
  ) where

import System.Directory
import System.FilePath ((</>))
import Control.Exception
import Text.Read (readMaybe)

import Data.Tuple.Extra (first, second, firstM)
import Data.List (elemIndex, intercalate)
import Data.Hashable
import Data.Bits (shiftL, (.|.))

import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HM
import Data.HashMap.Strict (HashMap)

import qualified Data.Text as T
import Data.Text.Encoding
import Text.Hex

import qualified Data.ByteString as BS

import qualified Crypto.Hash.SHA256 as SHA256

import Verifier.SAW.FiniteValue
import Verifier.SAW.SATQuery
import Verifier.SAW.ExternalFormat
import Verifier.SAW.SharedTerm

import SAWScript.Options
import SAWScript.Proof


-- Solver Cache Keys -----------------------------------------------------------

-- | A set of solver backend versions obtained using 'getSolverBackendVersions'
-- from @SAWScript.SolverVersions@
type SolverBackendVersions = [String]

-- | The key type for 'SolverCache'. Each is a SHA256 hashes of 'SATQuery' and
-- a set of 'SolverBackendVersions' - see 'mkSolverCacheKey'
data SolverCacheKey =
  SolverCacheKey 
  { solverCacheKeyBackendVersions :: SolverBackendVersions
  , solverCacheKeyHash :: ByteString
  }

instance Eq SolverCacheKey where
  (SolverCacheKey _ bs1) == (SolverCacheKey _ bs2) = bs1 == bs2

-- | Truncate a 'SolverCacheKey' (i.e. a SHA256 hash) to an 'Int', used to give
-- the type a fast 'Hashable' instance
solverCacheKeyInt :: SolverCacheKey -> Int
solverCacheKeyInt (SolverCacheKey _ bs) =
  BS.foldl' (\a b -> a `shiftL` 8 .|. fromIntegral b) 0 (BS.take 8 bs)

instance Hashable SolverCacheKey where
  hash = solverCacheKeyInt
  hashWithSalt s = hashWithSalt s . solverCacheKeyInt

instance Show SolverCacheKey where
  show (SolverCacheKey vs bs) = T.unpack (encodeHex (BS.take 8 bs)) ++
                                " (" ++ intercalate ", " vs ++ ")"

-- | Convert a 'SolverCacheKey' to a hexadecimal 'String'
solverCacheKeyToHex :: SolverCacheKey -> String
solverCacheKeyToHex (SolverCacheKey _ bs) = T.unpack $ encodeHex bs

-- | Hash using SHA256 a 'String' representation of a 'SATQuery' and a set of
-- 'SolverBackendVersions' to get a 'SolverCacheKey'. In particular, this
-- 'String' representation contains all the 'SolverBackendVersions', the
-- number of 'satVariables' in the 'SATQuery', the number of 'satUninterp's in
-- the 'SATQuery, and finally the 'scWriteExternal' representation of the
-- 'satQueryAsPropTerm' of the 'SATQuery' - with two additional things:
-- 1. Before calling 'scWriteExternal', we generalize ('scGeneralizeExts') over
--    all 'satVariables' and 'satUninterp's. This ensures the hash does not
--    depend on any execution-specific 'VarIndex'es.
-- 2. After calling 'scWriteExternal', all 'LocalName's in 'Pi' and 'Lam'
--    constructors are removed. This ensures that two terms which are alpha
--    equivalent are given the same hash.
mkSolverCacheKey :: SharedContext -> SolverBackendVersions -> SATQuery ->
                    IO SolverCacheKey
mkSolverCacheKey sc vs satq = do
  body <- satQueryAsPropTerm sc satq
  let ecs = Map.keys (satVariables satq) ++
            filter (\ec -> ecVarIndex ec `elem` satUninterp satq)
                   (getAllExts body)
  tm <- scGeneralizeExts sc ecs body
  let str_prefix = vs ++ [ "satVariables " ++ show (Map.size (satVariables satq))
                         , "satUninterp "  ++ show (length   (satUninterp  satq)) ]
      str_to_hash = unlines str_prefix ++ anonLocalNames (scWriteExternal tm)
  return $ SolverCacheKey vs $ SHA256.hash $ encodeUtf8 $ T.pack $ str_to_hash
  where anonLocalNames = unlines . map (unwords . go . words) . lines
        go (x:y:_:xs) | y `elem` ["Pi", "Lam"] = x:y:"_":xs
        go xs = xs


-- Solver Cache Values ---------------------------------------------------------

-- | The value type for 'SolverCache': a pair of the 'String' representing the
-- solver used and an optional list of counterexamples, represented as pairs
-- of indexes into the list of 'satVariables'
type SolverCacheValue = (String, Maybe [(Int, FirstOrderValue)])

-- | Convert the result of a solver call on the given 'SATQuery' to a
-- 'SolverCacheValue'
toSolverCacheValue :: SATQuery -> (Maybe CEX, String) -> Maybe SolverCacheValue
toSolverCacheValue satq (cexs, solver_name) =
  (solver_name,) <$> mapM (mapM (firstM (`elemIndex` ecs))) cexs
  where ecs = Map.keys $ satVariables satq

-- | Convert a 'SolverCacheValue' to something which has the same form as the
-- result of a solver call on the given 'SATQuery'
fromSolverCacheValue :: SATQuery -> SolverCacheValue -> (Maybe CEX, String)
fromSolverCacheValue satq (solver_name, cexs) =
  (fmap (fmap (first (ecs !!))) cexs ,solver_name)
  where ecs = Map.keys $ satVariables satq

-- | Given a path to a cache and a 'SolverCacheKey', return a
-- 'SolverCacheValue' if the given key has been cached, or 'Nothing' otherwise.
-- Note that if we encounter an 'IOException', we simply return 'Nothing',
-- meaning we fall back to calling the solver backend. The idea is that solver
-- result caching is an optional step, so if we fail during a read from the disk
-- we don't want execution to stop, we just want to not use caching.
readCacheEntryFromDisk :: FilePath -> SolverCacheKey -> IO (Maybe SolverCacheValue)
readCacheEntryFromDisk path k =
  catch (readMaybe . last . lines <$> readFile (path </> solverCacheKeyToHex k))
        (\(_ :: IOException) -> return Nothing)

-- | Given a path to a cache and a 'SolverCacheKey'/'SolverCacheValue' pair,
-- add an approriate entry to the cache on disk. Note that if we encounter an
-- 'IOException, we simply do nothing, meaning we do not cache this result. The
-- idea is that solver result caching is an optional step, so if we fail during
-- a write to the disk we don't want execution to stop, we just want to not use
-- caching.
writeCacheEntryToDisk :: FilePath -> (SolverCacheKey, SolverCacheValue) -> IO ()
writeCacheEntryToDisk path (k, v) =
  catch (createDirectoryIfMissing False path >>
         writeFile (path </> solverCacheKeyToHex k)
                   (unlines $ solverCacheKeyBackendVersions k ++ [show v]))
        (\(_ :: IOException) -> return ())


-- The Solver Cache ------------------------------------------------------------

-- | A set of cached solver results as well as a 'FilePath' indicating where
-- new additions to the cache should be saved
data SolverCache =
  SolverCache
  { solverCacheMap  :: HashMap SolverCacheKey SolverCacheValue
  , solverCachePath :: Maybe FilePath
  , solverCacheHits :: (Integer, Integer)
  }

-- | An empty 'SolverCache' with no associated 'FilePath'
emptySolverCache :: SolverCache
emptySolverCache = SolverCache HM.empty Nothing (0,0)

-- | A stateful operation on a 'SolverCache', returning a value of the given type
type SolverCacheOp a = Options -> SolverCache -> IO (a, SolverCache)

-- | Lookup a 'SolverCacheKey' in the solver result cache
lookupInSolverCache :: SolverCacheKey -> SolverCacheOp (Maybe SolverCacheValue)
lookupInSolverCache k opts cache =
  case (HM.lookup k (solverCacheMap cache), solverCachePath cache) of
    (Just v, _) -> do
      printOutLn opts Info ("Using cached result from memory: " ++ show k)
      return (Just v, cache { solverCacheHits = first (+1) (solverCacheHits cache) })
    (_, Just path) -> readCacheEntryFromDisk path k >>= \case
      Just v -> do
          printOutLn opts Info ("Using cached result from disk: " ++ show k)
          return (Just v, cache { solverCacheMap = HM.insert k v (solverCacheMap cache)
                                , solverCacheHits = second (+1) (solverCacheHits cache) })
      Nothing -> return (Nothing, cache)
    _ -> return (Nothing, cache)

-- | Add a 'SolverCacheValue' to the solver result cache
insertInSolverCache :: SolverCacheKey -> SolverCacheValue -> SolverCacheOp ()
insertInSolverCache k v opts cache = do
  printOutLn opts Info ("Caching result: " ++ show k)
  case solverCachePath cache of
    Just path -> writeCacheEntryToDisk path (k, v)
    _ -> return ()
  return ((), cache { solverCacheMap = HM.insert k v (solverCacheMap cache) })

-- | Set the 'FilePath' of the solver result cache, erroring if it is already
-- set, and save all results cached so far
setSolverCachePath :: FilePath -> SolverCacheOp ()
setSolverCachePath path opts cache =
  makeAbsolute path >>= \pathAbs ->
  case solverCachePath cache of
    Just path' -> fail $ "Solver cache already has a set path: " ++ path'
    _ | HM.null (solverCacheMap cache) -> return ((), cache { solverCachePath = Just pathAbs })
    _ -> let to_save = HM.toList $ solverCacheMap cache in
         let (s0, s1) = (show (length to_save), if length to_save > 1 then "s" else "") in
         printOutLn opts Info ("Saving " ++ s0 ++ " cached result" ++ s1 ++ " to disk") >>
         mapM_ (writeCacheEntryToDisk path) to_save >>
         return ((), cache { solverCachePath = Just pathAbs })

-- | Print out statistics about how the solver cache was used
printSolverCacheStats :: SolverCacheOp ()
printSolverCacheStats opts cache = do
  let memSize = HM.size $ solverCacheMap cache
  let (memHits, diskHits) = solverCacheHits cache
  printOutLn opts Info ("== Solver result cache statistics ==")
  case solverCachePath cache of
    Just path -> do
      diskSize <- length <$> listDirectory path
      printOutLn opts Info ("- " ++ show diskSize ++ " results cached on disk "
                                 ++ "(" ++ path ++ ")")
      printOutLn opts Info ("- " ++ show memSize ++ " results cached in memory "
                                 ++ "(" ++ show (100*memSize `div` diskSize)
                                 ++ "% of total cache)")
      let totalHits = max 1 (memHits+diskHits)
      printOutLn opts Info ("- " ++ show diskHits ++ " cache hits from disk "
                                 ++ "(" ++ show (100*diskHits `div` totalHits)
                                 ++ "% of total hits)")
      printOutLn opts Info ("- " ++ show memHits ++ " cache hits from memory "
                                 ++ "(" ++ show (100*memHits `div` totalHits)
                                 ++ "% of total hits)")
    Nothing -> do
      printOutLn opts Info ("- " ++ show memSize ++ " results cached in memory")
      printOutLn opts Info ("- " ++ show memHits ++ " cache hits")
  return ((), cache)
