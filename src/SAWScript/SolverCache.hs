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

import Control.Monad (unless)
import Control.Monad.State (get, modify)
import Control.Exception (try, SomeException)
import Data.List (sortOn)
import Data.Maybe (catMaybes)
import System.Directory (doesDirectoryExist, listDirectory, createDirectory)
import System.FilePath ((</>))
import Text.Read (readMaybe)

import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet        as HS
import qualified Data.ByteString     as BS
import qualified Data.Text           as T
import Data.Text.Encoding
import Text.Hex

import Crypto.Hash.SHA256 as SHA256

import Verifier.SAW.ExternalFormat
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

import SAWScript.Options
import SAWScript.Value
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


-- Conversions -----------------------------------------------------------------

-- | Convert a 'SolverCacheKey' to a hexadecimal 'String'
solverCacheKeyToHex :: SolverCacheKey -> String
solverCacheKeyToHex = T.unpack . encodeHex

-- | Convert a hexadecimal 'String' to a 'SolverCacheKey'
solverCacheKeyFromHex :: String -> Maybe SolverCacheKey
solverCacheKeyFromHex = decodeHex . T.pack

-- | Convert a 'Sequent' to a 'SolverCacheKey'
propToSolverCacheKey :: Sequent -> TopLevel (Maybe SolverCacheKey)
propToSolverCacheKey sq = getSharedContext >>= \sc -> io $ do
  try (sequentToProp sc sq) >>= \case
    Right p -> Just . SHA256.hash . encodeUtf8 . T.pack . scWriteExternal <$>
               scGeneralizeAllExts sc (unProp p)
    Left (_ :: SomeException) -> return Nothing


-- Modifying the SolverCache ---------------------------------------------------

-- | Lookup a 'SolverCacheKey' in the solver result cache
lookupInSolverCache :: SolverCacheKey -> TopLevel (Maybe SolverCacheValue)
lookupInSolverCache k =
  rwSolverCache <$> get >>= \case
    Just cache | Just v <- HM.lookup k (solverCacheMap cache) -> do
      printOutLnTop Info $ "Using cached result (" ++ solverCacheKeyToHex k ++ ")"
      return $ Just v
    _ -> return Nothing

-- | Add a 'SolverCacheValue' to the solver result cache
insertInSolverCache :: SolverCacheKey -> SolverCacheValue -> TopLevel ()
insertInSolverCache k v@(Nothing, _) =
  rwSolverCache <$> get >>= \case
    Just cache -> do
      printOutLnTop Info $ "Adding cached result (" ++ solverCacheKeyToHex k ++ ")"
      let cache' = cache { solverCacheMap = HM.insert k v (solverCacheMap cache)
                         , solverCacheUnsaved = HS.insert k <$> solverCacheUnsaved cache }
      modify (\rw -> rw { rwSolverCache = Just cache' })
    Nothing -> return ()
insertInSolverCache _ _ = return ()

-- | Load a solver result cache from a file
loadSolverCache :: FilePath -> TopLevel ()
loadSolverCache path =
  do cache <- io $ loadSolverCacheH path
     modify (\rw -> rw { rwSolverCache = cache })

-- | Construct a solver result cache from a file
loadSolverCacheH :: FilePath -> IO (Maybe SolverCache)
loadSolverCacheH path =
  doesDirectoryExist path >>= \case
    True -> do files <- listDirectory path
               cache <- catMaybes <$> mapM processFile files
               return $ Just $ SolverCache path (HM.fromList cache) Nothing
    False -> return $ Just $ SolverCache path HM.empty Nothing
  where processFile :: FilePath -> IO (Maybe (SolverCacheKey, SolverCacheValue))
        processFile f = case solverCacheKeyFromHex f of
          Just k | BS.length k == 32 ->
            fmap (\(sz,ss) -> (k, (Nothing, SolverStats ss sz))) <$>
            readMaybe <$> readFile (path </> f)
          _ -> return Nothing

-- | Save the current solver result cache to a file, tracking unsaved results
-- from now on iff the given flag is 'True'
saveSolverCache :: Bool -> TopLevel ()
saveSolverCache trackUnsaved =
  rwSolverCache <$> getTopLevelRW >>= \case
    Just cache -> do
      ex <- io $ doesDirectoryExist (solverCachePath cache)
      unless ex $ io $ createDirectory (solverCachePath cache)
      mapM_ (\(k,v) -> io $ writeFile (solverCachePath cache </> solverCacheKeyToHex k)
                                      (showValue v))
            (maybe (HM.toList $ solverCacheMap cache)
                   (map (\k -> (k, (solverCacheMap cache) HM.! k)) . HS.toList)
                   (solverCacheUnsaved cache))
      let cache' = cache { solverCacheUnsaved = if trackUnsaved then Just HS.empty else Nothing }
      modify (\rw -> rw { rwSolverCache = Just cache' })
    Nothing -> return ()
  where showValue (_, SolverStats ss sz) = show (sz, ss)