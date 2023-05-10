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

module SAWScript.SolverCache where

import Control.Monad (unless, when)
import Control.Exception (try, SomeException)
import Data.List (sortOn)
import Data.Maybe (catMaybes)
import System.Directory (doesDirectoryExist, listDirectory, createDirectory)
import System.FilePath ((</>))
import Text.Read (readMaybe)

import Data.Hashable
import Data.Bits (shiftL, (.|.))

import qualified Data.HashMap.Strict as HM
import Data.HashMap.Strict (HashMap)

import qualified Data.HashSet as HS
import Data.HashSet (HashSet)

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
  { solverCachePath :: FilePath
  , solverCacheMap :: HashMap SolverCacheKey SolverCacheValue
  , solverCacheUnsaved :: Maybe (HashSet SolverCacheKey)
  }

-- | Load a solver result cache from a file, or if no such file exists,
-- construct an empty 'SolverCache' with its path set to the given value
loadSolverCache :: Options -> FilePath -> IO SolverCache
loadSolverCache opts path = do
  ex <- doesDirectoryExist path
  mbs <- if ex then listDirectory path >>= mapM processFile
               else return []
  when ex $ printOutLn opts Info ("Loaded solver result cache with " ++ show (length mbs) ++ " entries")
  return $ SolverCache path (HM.fromList $ catMaybes mbs) Nothing
  where processFile :: FilePath -> IO (Maybe (SolverCacheKey, SolverCacheValue))
        processFile f = case solverCacheKeyFromHex f of
          Just k -> fmap (\(sz,ss) -> (k, (Nothing, SolverStats ss sz))) <$>
                    readMaybe <$> readFile (path </> f)
          _ -> return Nothing

-- | A stateful operation on a 'SolverCache', returning a value of the given type
type SolverCacheOp a = Options -> SolverCache -> IO (a, SolverCache)

-- | Lookup a 'SolverCacheKey' in the solver result cache
lookupInSolverCache :: SolverCacheKey -> SolverCacheOp (Maybe SolverCacheValue)
lookupInSolverCache k opts cache =
  case HM.lookup k (solverCacheMap cache) of
    Just v -> printOutLn opts Info ("Using cached result (" ++ solverCacheKeyToHex k ++ ")" ++ show (solverCacheKeyInt k)) >>
              return (Just v, cache)
    _ -> return (Nothing, cache)

-- | Add a 'SolverCacheValue' to the solver result cache
insertInSolverCache :: SolverCacheKey -> SolverCacheValue -> SolverCacheOp ()
insertInSolverCache k v@(Nothing, _) opts cache =
  printOutLn opts Info ("Adding cached result (" ++ solverCacheKeyToHex k ++ ")" ++ show (solverCacheKeyInt k)) >>
  return ((), cache { solverCacheMap = HM.insert k v (solverCacheMap cache)
                    , solverCacheUnsaved = HS.insert k <$> solverCacheUnsaved cache })
insertInSolverCache _ _ _ cache = return ((), cache)

-- | Save the current solver result cache to a file, tracking unsaved results
-- from now on iff the given flag is 'True'
saveSolverCache :: Bool -> SolverCacheOp ()
saveSolverCache trackUnsaved _ cache = do
  ex <- doesDirectoryExist (solverCachePath cache)
  unless ex $ createDirectory (solverCachePath cache)
  mapM_ (\(k,v) -> writeFile (solverCachePath cache </> solverCacheKeyToHex k)
                             (showValue v))
        (maybe (HM.toList $ solverCacheMap cache)
               (map (\k -> (k, (solverCacheMap cache) HM.! k)) . HS.toList)
               (solverCacheUnsaved cache))
  return ((), cache { solverCacheUnsaved = if trackUnsaved then Just HS.empty else Nothing })
  where showValue (_, SolverStats ss sz) = show (sz, ss)
