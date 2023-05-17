{- |
Module      : SAWScript.SolverCache
Description : Caching SMT solver results for SAWScript
License     : BSD3
Maintainer  : m-yac
Stability   : provisional
-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module SAWScript.SolverCache where

import System.Directory
import System.FilePath ((</>))
import Text.Read (readMaybe)

import Data.Tuple.Extra (first, second, firstM)
import Data.List (elemIndex)
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

-- | The key type for 'SolverCache': SHA256 hashes
newtype SolverCacheKey = SolverCacheKey ByteString deriving Eq

-- | Truncate a 'SolverCacheKey' (i.e. a SHA256 hash) to an 'Int', used to give
-- the type a fast 'Hashable' instance
solverCacheKeyInt :: SolverCacheKey -> Int
solverCacheKeyInt (SolverCacheKey bs) =
  BS.foldl' (\a b -> a `shiftL` 8 .|. fromIntegral b) 0 (BS.take 8 bs)

instance Hashable SolverCacheKey where
  hash = solverCacheKeyInt
  hashWithSalt s = hashWithSalt s . solverCacheKeyInt

-- | Convert a 'SolverCacheKey' to a hexadecimal 'String'
solverCacheKeyToHex :: SolverCacheKey -> String
solverCacheKeyToHex (SolverCacheKey bs) = T.unpack $ encodeHex bs

-- | Convert a hexadecimal 'String' to a 'SolverCacheKey'
solverCacheKeyFromHex :: String -> Maybe SolverCacheKey
solverCacheKeyFromHex x = fmap SolverCacheKey $ decodeHex $ T.pack x

-- | Hash using SHA256 a 'String' representation of a 'SATQuery' to get a
-- 'SolverCacheKey'
satQueryToSolverCacheKey :: SharedContext -> SATQuery -> IO SolverCacheKey
satQueryToSolverCacheKey sc satq = do
  body <- satQueryAsPropTerm sc satq
  let ecs = Map.keys (satVariables satq) ++
            filter (\ec -> ecVarIndex ec `elem` satUninterp satq)
                   (getAllExts body)
  tm <- scGeneralizeExts sc ecs body
  let str_to_hash = show (Map.size (satVariables satq)) ++ " " ++
                    show (length (satUninterp satq)) ++ "\n" ++
                    anonLocalNames (scWriteExternal tm)
  return $ SolverCacheKey $ SHA256.hash $ encodeUtf8 $ T.pack $ str_to_hash
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
-- 'SolverCacheValue' if the given key has been cached, or 'Nothing' otherwise
readCacheEntryFromDisk :: FilePath -> SolverCacheKey -> IO (Maybe SolverCacheValue)
readCacheEntryFromDisk path k = do
  ex <- doesFileExist (path </> solverCacheKeyToHex k)
  if not ex then return Nothing
  else readMaybe <$> readFile (path </> solverCacheKeyToHex k)

-- | Given a path to a cache and a 'SolverCacheKey'/'SolverCacheValue' pair,
-- add an approriate entry to the cache on disk
writeCacheEntryToDisk :: FilePath -> (SolverCacheKey, SolverCacheValue) -> IO ()
writeCacheEntryToDisk path (k, v) = 
  createDirectoryIfMissing False path >>
  writeFile (path </> solverCacheKeyToHex k) (show v)


-- The Solver Cache ------------------------------------------------------------

-- | A set of cached solver results as well as a 'FilePath' indicating where
-- new additions to the cache should be saved
data SolverCache =
  SolverCache
  { solverCacheMap :: HashMap SolverCacheKey SolverCacheValue
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
      printOutLn opts Info ("Using cached result from memory (" ++ solverCacheKeyToHex k ++ ")")
      return (Just v, cache { solverCacheHits = first (+1) (solverCacheHits cache) })
    (_, Just path) -> readCacheEntryFromDisk path k >>= \case
      Just v -> do
          printOutLn opts Info ("Using cached result from disk (" ++ solverCacheKeyToHex k ++ ")")
          return (Just v, cache { solverCacheMap = HM.insert k v (solverCacheMap cache)
                                , solverCacheHits = second (+1) (solverCacheHits cache) })
      Nothing -> return (Nothing, cache)
    _ -> return (Nothing, cache)

-- | Add a 'SolverCacheValue' to the solver result cache
insertInSolverCache :: SolverCacheKey -> SolverCacheValue -> SolverCacheOp ()
insertInSolverCache k v opts cache = do
  printOutLn opts Info ("Caching result (" ++ solverCacheKeyToHex k ++ ")")
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
