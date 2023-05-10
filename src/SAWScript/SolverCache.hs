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

import Control.Monad (forM_)
import Control.Exception (try, SomeException)
import Data.List (sortOn)
import System.Directory (makeAbsolute, doesFileExist, createDirectoryIfMissing)
import System.FilePath ((</>))
import Text.Read (readMaybe)

import Data.Hashable
import Data.Bits (shiftL, (.|.))

import qualified Data.HashMap.Strict as HM
import Data.HashMap.Strict (HashMap)

import qualified Data.Text as T
import Data.Text.Encoding
import Text.Hex

import qualified Data.ByteString as BS

import qualified Crypto.Hash.SHA256 as SHA256

import Verifier.SAW.ExternalFormat
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

import SAWScript.Options
import SAWScript.Proof
import SAWScript.Prover.SolverStats


-- Helper Functions ------------------------------------------------------------

-- | Generalize over the all external constants in a given term by
-- wrapping the term with foralls and replacing the external constant
-- occurrences with the appropriate local variables.
-- FIXME: Move to SharedTerm.hs
scGeneralizeAllExts :: SharedContext -> Term -> IO Term
scGeneralizeAllExts sc tm =
  let allexts = sortOn (toShortName . ecName) $ getAllExts tm
   in scGeneralizeExts sc allexts tm


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

-- | Hash the 'String' representation ('scWriteExternal') of a 'Sequent' using
-- SHA256 to get a 'SolverCacheKey'
propToSolverCacheKey :: SharedContext -> Sequent -> IO (Maybe SolverCacheKey)
propToSolverCacheKey sc sq = do
  try (sequentToProp sc sq) >>= \case
    Right p -> Just . SolverCacheKey . SHA256.hash .
               encodeUtf8 . T.pack . scWriteExternal <$>
               scGeneralizeAllExts sc (unProp p)
    Left (_ :: SomeException) -> return Nothing


-- The Solver Cache ------------------------------------------------------------

type SolverCacheValue = (Maybe CEX, SolverStats)

-- | A set of cached solver results as well as a 'FilePath' indicating where
-- new additions to the cache should be saved
data SolverCache =
  SolverCache
  { solverCacheMap :: HashMap SolverCacheKey SolverCacheValue
  , solverCachePath :: Maybe FilePath
  }

-- | An empty 'SolverCache' with no associated 'FilePath'
emptySolverCache :: SolverCache
emptySolverCache = SolverCache HM.empty Nothing

-- | A stateful operation on a 'SolverCache', returning a value of the given type
type SolverCacheOp a = Options -> SolverCache -> IO (a, SolverCache)

-- | Lookup a 'SolverCacheKey' in the solver result cache
lookupInSolverCache :: SolverCacheKey -> SolverCacheOp (Maybe SolverCacheValue)
lookupInSolverCache k opts cache =
  case (HM.lookup k (solverCacheMap cache), solverCachePath cache) of
    (Just v, _) -> do
      printOutLn opts Info ("Using cached result from memory (" ++ solverCacheKeyToHex k ++ ")")
      return (Just v, cache)
    (_, Just path) -> do
      ex <- doesFileExist (path </> solverCacheKeyToHex k)
      if not ex then return (Nothing, cache)
      else readMaybe <$> readFile (path </> solverCacheKeyToHex k) >>= \case
        Just (sz, ss) -> do
          let v = (Nothing, SolverStats ss sz)
          printOutLn opts Info ("Using cached result from disk (" ++ solverCacheKeyToHex k ++ ")")
          return (Just v, cache { solverCacheMap = HM.insert k v (solverCacheMap cache) })
        Nothing -> return (Nothing, cache)
    _ -> return (Nothing, cache)

-- | Add a 'SolverCacheValue' to the solver result cache
insertInSolverCache :: SolverCacheKey -> SolverCacheValue -> SolverCacheOp ()
insertInSolverCache k v@(Nothing, SolverStats ss sz) opts cache = do
  printOutLn opts Info ("Caching result (" ++ solverCacheKeyToHex k ++ ")")
  case solverCachePath cache of
    Just path -> createDirectoryIfMissing False path >>
                 writeFile (path </> solverCacheKeyToHex k) (show (sz, ss))
    _ -> return ()
  return ((), cache { solverCacheMap = HM.insert k v (solverCacheMap cache) })
insertInSolverCache _ _ _ cache = return ((), cache)

-- | Set the 'FilePath' of the solver result cache, erroring if it is already
-- set, and save all results cached so far
setSolverCachePath :: FilePath -> SolverCacheOp ()
setSolverCachePath path opts cache =
  makeAbsolute path >>= \pathAbs ->
  case solverCachePath cache of
    Just path' -> fail $ "Solver cache already has a set path: " ++ path'
    _ | HM.null (solverCacheMap cache) -> return ((), cache { solverCachePath = Just pathAbs })
    _ -> let to_save = HM.toList $ solverCacheMap cache in
         createDirectoryIfMissing False pathAbs >>
         let (s0, s1) = (show (length to_save), if length to_save > 1 then "s" else "") in
         printOutLn opts Info ("Saving " ++ s0 ++ " cached result" ++ s1 ++ " to disk") >>
         forM_ to_save (\(k,(_, SolverStats ss sz)) ->
           writeFile (pathAbs </> solverCacheKeyToHex k) (show (sz, ss))) >>
         return ((), cache { solverCachePath = Just pathAbs })
