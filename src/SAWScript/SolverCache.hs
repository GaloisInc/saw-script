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
2. The 'SolverCache' contains a map from these hashes to previously obtained
   results ('solverCacheMap'). If the hash corresponding to the 'SATQuery' and
   'SolverBackendVersion's can be found in the map, then the corresponding
   result is used.
3. Otherwise, if the 'SolverCache' was given a path to a directory
   ('solverCachePath') and a file whose name is the hash can be found in that
   directory, the file's contents are 'read' and used as the result.
4. Otherwise, the 'SATQuery' is dispatched to the requested backend and a
   result is obtained. Then:
   - This result is added to the 'SolverCache' map using the hash of the
     'SATQuery' and 'SolverBackendVersion's as the key.
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
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module SAWScript.SolverCache
  ( Solver(..)
  , SolverBackend(..)
  , W4Backend(..)
  , w4Backends
  , baseBackends
  , SolverBackendVersion(..)
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
  , cleanSolverCache
  , printSolverCacheStats
  ) where

import System.Directory
import Control.Exception
import GHC.Generics (Generic)

import Control.Monad (forM_)
import Data.Tuple.Extra (first, firstM)
import Data.List (isPrefixOf, elemIndex, intercalate)
import Data.Hashable (Hashable(..))
import Data.Bits (shiftL, (.|.))
import Data.Maybe (fromMaybe, isJust)
import Data.Functor ((<&>))

import qualified Data.Set as Set
import Data.Set (Set)

import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HM
import Data.HashMap.Strict (HashMap)

import qualified Data.Text as T
import Data.Text.Encoding
import Text.Hex

import qualified Data.ByteString as BS

import qualified Crypto.Hash.SHA256 as SHA256

import qualified Database.LMDB.Simple as LMDB
import qualified Database.LMDB.Simple.Extra as LMDB
import Codec.Serialise

import Data.SBV.Dynamic (Solver(..))

import Verifier.SAW.FiniteValue
import Verifier.SAW.SATQuery
import Verifier.SAW.ExternalFormat
import Verifier.SAW.SharedTerm

import SAWScript.Options
import SAWScript.Proof


-- Solver Backends -------------------------------------------------------------

deriving instance Eq Solver
deriving instance Ord Solver
deriving instance Read Solver

-- | A datatype representing one of the ways the what4 backend can be used in
-- SAW - i.e. directly ('W4_Base'), with a tactic ('W4_Tactic'), by converting
-- to SMTLib2 then calling ABC ('W4_SMTLib2'), by converting to Verilog then
-- calling ABC ('W4_Verilog'), or by converting to AIGER then calling ABC
-- ('W4_AIGER')
data W4Backend = W4_Base
               | W4_Tactic String
               | W4_SMTLib2
               | W4_Verilog
               | W4_AIGER
               deriving (Eq, Ord, Read, Show)

-- | A datatype representing one of the solver backends available in SAW. Note
-- that for 'SBV' and 'W4', multiple backends will be used (e.g. 'SBV' with
-- @Solver Z3@ or @W4 W4_AIGER@ with 'AIG' and @Solver ABC@), though not all
-- comtinations of backends are valid (e.g. @W4 W4_SMTLib2@ with anything but
-- @Solver Z3@)
data SolverBackend = Solver Solver
                   | W4 W4Backend
                   | SBV
                   | AIG
                   | RME
                   deriving (Eq, Ord, Read, Show)

instance Serialise SolverBackend where
  encode (Solver s) = encode (1 :: Int, show s)
  encode (W4 w)     = encode (2 :: Int, show w)
  encode backend    = encode (0 :: Int, show backend)
  decode = decode <&> \case (1 :: Int, s) -> Solver (read s)
                            (2 :: Int, s) -> W4 (read s)
                            (_ :: Int, s) -> read s

-- | Given a 'W4Backend' and a 'Solver', return the list of 'SolverBackend's
-- used. In particular, this includes 'AIG' for 'W4_AIGER'.
w4Backends :: W4Backend -> Solver -> [SolverBackend]
w4Backends w s | W4_AIGER <- w = [W4 w, AIG, Solver s]
               | otherwise     = [W4 w, Solver s]

-- | Convert a 'SolverBackend' into its base form, namely replace any 'W4'
-- backend with @W4 W4_Base@.
baseBackend :: SolverBackend -> SolverBackend
baseBackend (W4 _) = W4 W4_Base
baseBackend backend = backend

-- | The finite list of all base 'SolverBackend's (as per 'baseBackend')
baseBackends :: [SolverBackend]
baseBackends = (Solver <$> enumFrom minBound) ++
               [W4 W4_Base, SBV, AIG, RME]

-- | A 'SolverBackend' and its version 'String', if one could be obtained
data SolverBackendVersion =
  SolverBackendVersion 
  { solverBackend :: SolverBackend 
  , solverVersion :: Maybe String
  } deriving (Eq, Ord, Generic)

instance Serialise SolverBackendVersion -- automatically derived

instance Show SolverBackendVersion where
  show (SolverBackendVersion backend mb_v) = case backend of
    Solver s | show s `isPrefixOf` v_str -> v_str
             | otherwise                 -> show s ++ " " ++ v_str
    W4 W4_Base       -> unwords ["what4", v_str]
    W4 (W4_Tactic t) -> unwords ["what4", v_str, "using", t]
    W4 W4_SMTLib2    -> unwords ["what4", v_str, "to", "SMTLib2"]
    W4 W4_Verilog    -> unwords ["what4", v_str, "to", "Verilog"]
    W4 W4_AIGER      -> unwords ["what4", v_str, "to", "AIGER"]
    SBV              -> unwords ["SBV", v_str]
    AIG              -> unwords ["AIG", v_str]
    RME              -> unwords ["RME", v_str]
    where v_str = fromMaybe "[unknown version]" mb_v

-- | Convert the 'SolverBackend' of a 'SolverBackendVersion' into its base
-- form using 'baseBackend'
baseBackendVersion :: SolverBackendVersion -> SolverBackendVersion
baseBackendVersion (SolverBackendVersion backend v) =
  SolverBackendVersion (baseBackend backend) v


-- Solver Cache Keys -----------------------------------------------------------

-- | The key type for 'SolverCache'. Each is a SHA256 hashes of 'SATQuery' and
-- a 'Set' of 'SolverBackendVersion's - see 'mkSolverCacheKey'
data SolverCacheKey =
  SolverCacheKey 
  { solverCacheKeyVersions :: Set SolverBackendVersion
  , solverCacheKeyHash     :: ByteString
  }

instance Eq SolverCacheKey where
  (SolverCacheKey _ bs1) == (SolverCacheKey _ bs2) = bs1 == bs2

instance Serialise SolverCacheKey where
  encode (SolverCacheKey _ bs) = encode bs
  decode = SolverCacheKey Set.empty <$> decode

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
                                if Set.null vs then ""
                                else " (" ++ intercalate ", " vstrs ++ ")"
    where vstrs = show <$> Set.elems vs

-- | Convert a 'SolverCacheKey' to a hexadecimal 'String'
solverCacheKeyToHex :: SolverCacheKey -> String
solverCacheKeyToHex (SolverCacheKey _ bs) = T.unpack $ encodeHex bs

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
mkSolverCacheKey :: SharedContext -> Set SolverBackendVersion -> SATQuery ->
                    IO SolverCacheKey
mkSolverCacheKey sc vs satq = do
  body <- satQueryAsPropTerm sc satq
  let ecs = Map.keys (satVariables satq) ++
            filter (\ec -> ecVarIndex ec `elem` satUninterp satq)
                   (getAllExts body)
  tm <- scGeneralizeExts sc ecs body
  let str_prefix = map show (Set.elems vs) ++
                   [ "satVariables " ++ show (Map.size (satVariables satq))
                   , "satUninterp "  ++ show (length   (satUninterp  satq)) ]
      str_to_hash = unlines str_prefix ++ anonLocalNames (scWriteExternal tm)
  return $ SolverCacheKey vs $ SHA256.hash $ encodeUtf8 $ T.pack $ str_to_hash
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
  { solverCacheValueVersions   :: Set SolverBackendVersion
  , solverCacheValueSolverName :: String
  , solverCacheValueCEXs       :: Maybe [(Int, FirstOrderValue)]
  } deriving (Eq, Generic)

instance Serialise SolverCacheValue -- automatically derived

instance Semigroup SolverCacheValue where
  (SolverCacheValue vs1 nm1 cs1) <> (SolverCacheValue vs2 nm2 cs2) =
    SolverCacheValue (vs1 <> vs2) (nm1 <> nm2) (cs1 <> cs2)

instance Monoid SolverCacheValue where
  mempty = SolverCacheValue mempty mempty mempty

-- | Convert the result of a solver call on the given 'SATQuery' to a
-- 'SolverCacheValue'
toSolverCacheValue :: Set SolverBackendVersion -> SATQuery ->
                      (Maybe CEX, String) -> Maybe SolverCacheValue
toSolverCacheValue vs satq (cexs, solver_name) =
  fmap (SolverCacheValue vs solver_name)
       (mapM (mapM (firstM (`elemIndex` ecs))) cexs)
  where ecs = Map.keys $ satVariables satq

-- | Convert a 'SolverCacheValue' to something which has the same form as the
-- result of a solver call on the given 'SATQuery'
fromSolverCacheValue :: SATQuery -> SolverCacheValue -> (Maybe CEX, String)
fromSolverCacheValue satq (SolverCacheValue _ solver_name cexs) =
  (fmap (fmap (first (ecs !!))) cexs, solver_name)
  where ecs = Map.keys $ satVariables satq


-- The Database Behind the Solver Cache ----------------------------------------

-- | The database behind the 'SolverCache' - either a 'HashMap' or a
-- 'LMDB.Database' from 'SolverCacheKey's to 'SolverCacheValue's. We refer to
-- the former as "in memory" and the latter as "on disk". For the latter, we
-- also save the 'FilePath' of the LMDB database as well as the
-- 'LMDB.Environment'.
data SolverCacheDB
  = SolverCacheMem (HashMap SolverCacheKey SolverCacheValue)
  | SolverCacheDisk FilePath (LMDB.Environment LMDB.ReadWrite)
                             (LMDB.Database SolverCacheKey SolverCacheValue)

-- | An empty 'SolverCacheDB' in memory
emptyDB :: SolverCacheDB
emptyDB = SolverCacheMem HM.empty

-- | Get the 'FilePath' of the 'SolverCacheDB's on-disk database, if it exists
getDBPath :: SolverCacheDB -> Maybe FilePath
getDBPath (SolverCacheMem _ ) = Nothing
getDBPath (SolverCacheDisk path _ _) = Just path

-- | If the 'SolverCacheDB' does not currently have an associated on-disk
-- database, create one at the associated 'FilePath' and copy all entries in
-- memory on to disk
setPathDB :: FilePath -> SolverCacheDB -> IO SolverCacheDB
setPathDB path (SolverCacheMem hm) = do
  createDirectoryIfMissing False path
  let limits = LMDB.defaultLimits { LMDB.mapSize = 2 ^ (32 :: Int) }
  env <- LMDB.openReadWriteEnvironment path limits
  LMDB.readWriteTransaction env $ do
    db <- LMDB.getDatabase Nothing
    forM_ (HM.toList hm) $ \(k,v) -> LMDB.put db k (Just v)
    return $ SolverCacheDisk path env db
setPathDB _ (SolverCacheDisk path _ _) =
  fail $ "Solver cache already has a set path: " ++ path

-- | A general function for querying a 'SolverCacheDB'
askDB :: (HashMap SolverCacheKey SolverCacheValue -> a) ->
         (LMDB.Database SolverCacheKey SolverCacheValue ->
          LMDB.Transaction LMDB.ReadOnly a) ->
         a -> SolverCacheDB -> IO a
askDB f _ _ (SolverCacheMem hm) = return $ f hm
askDB _ g dflt (SolverCacheDisk _ env db) =
  catch (LMDB.readOnlyTransaction env $ g db)
        (\(_ :: IOException) -> return dflt)

-- | Get the size of a 'SolverCacheDB'
sizeDB :: SolverCacheDB -> IO Int
sizeDB = askDB (HM.size) (LMDB.size) 0

-- | Check whether a 'SolverCacheKey' is in a 'SolverCacheDB'
lookupInDB :: SolverCacheKey -> SolverCacheDB -> IO (Maybe SolverCacheValue)
lookupInDB k = askDB (HM.lookup k) (LMDB.lookup k) Nothing

-- | A general function for modifying a 'SolverCacheDB'
onDB :: (HashMap SolverCacheKey SolverCacheValue ->
         HashMap SolverCacheKey SolverCacheValue) ->
        (LMDB.Database SolverCacheKey SolverCacheValue ->
         LMDB.Transaction LMDB.ReadWrite ()) ->
        SolverCacheDB -> IO SolverCacheDB
onDB f _ (SolverCacheMem hm) = return $ SolverCacheMem $ f hm
onDB _ g c@(SolverCacheDisk _ env db) =
  catch (LMDB.transaction env $ g db >>= \r -> return $ r `seq` c)
        (\(_ :: IOException) -> return c)

-- | Insert a 'SolverCacheValue' at the given 'SolverCacheKey' into a
-- 'SolverCacheDB'
insertInDB :: SolverCacheKey -> SolverCacheValue -> SolverCacheDB ->
              IO SolverCacheDB
insertInDB k v = onDB (HM.insert k v) (LMDB.insert k v)

-- | Filter the entries in a 'SolverCacheDB'
filterDB :: (SolverCacheValue -> Bool) -> SolverCacheDB ->
            IO SolverCacheDB
filterDB f = onDB (HM.filter f) $ \db -> do
  kvs <- LMDB.toList db
  forM_ kvs $ \(k,v) -> if f v then return False else LMDB.delete k db


-- The Solver Cache ------------------------------------------------------------

-- | A 'SolverCacheDB' of cached solver results as well as counters for how
-- many cache hits and how many new entry creations have occurred
data SolverCache =
  SolverCache
  { solverCacheDB      :: SolverCacheDB
  , solverCacheHits    :: Integer
  , solverCacheCreated :: Integer
  }

-- | An empty 'SolverCache' with no associated 'FilePath'
emptySolverCache :: SolverCache
emptySolverCache = SolverCache emptyDB 0 0

-- | A stateful operation on a 'SolverCache', returning a value of the given type
type SolverCacheOp a = Options -> SolverCache -> IO (a, SolverCache)

-- | Lookup a 'SolverCacheKey' in the solver result cache
lookupInSolverCache :: SolverCacheKey -> SolverCacheOp (Maybe SolverCacheValue)
lookupInSolverCache k opts cache =
  lookupInDB k (solverCacheDB cache) >>= \case
    Just v -> do
      printOutLn opts Info ("Using cached result: " ++ show k)
      return (Just v, cache { solverCacheHits = solverCacheHits cache + 1 })
    Nothing -> return (Nothing, cache)

-- | Add a 'SolverCacheValue' to the solver result cache
insertInSolverCache :: SolverCacheKey -> SolverCacheValue -> SolverCacheOp ()
insertInSolverCache k v opts cache = do
  printOutLn opts Info ("Caching result: " ++ show k)
  db' <- insertInDB k v (solverCacheDB cache)
  return ((), cache { solverCacheDB = db'
                    , solverCacheCreated = solverCacheCreated cache + 1 })

-- | Set the 'FilePath' of the solver result cache, erroring if it is already
-- set, and save all results cached so far
setSolverCachePath :: FilePath -> SolverCacheOp ()
setSolverCachePath path opts cache = do
  pathAbs <- makeAbsolute path
  sz <- sizeDB (solverCacheDB cache)
  let (s0, s1) = (show sz, if sz == 1 then "" else "s")
  db' <- setPathDB pathAbs (solverCacheDB cache)
  if sz == 0 then return ()
  else printOutLn opts Info ("Saved " ++ s0 ++ " cached result" ++ s1 ++ " to disk")
  return ((), cache { solverCacheDB = db' })

-- | Remove all entries in the solver result cache which have version(s) that
-- do not match the current version(s).
cleanSolverCache :: Set SolverBackendVersion -> SolverCacheOp ()
cleanSolverCache current_base_vs opts cache = do
  sz0 <- sizeDB (solverCacheDB cache)
  db' <- filterDB (f . solverCacheValueVersions) (solverCacheDB cache)
  sz1 <- sizeDB (solverCacheDB cache)
  let s = if (sz0 - sz1) == 1 then "" else "s"
  printOutLn opts Info ("Removed " ++ show (sz0 - sz1) ++
                        " cached result" ++ s ++ " with mismatched version" ++ s)
  return ((), cache { solverCacheDB = db' })
  where f vs = Set.isSubsetOf (Set.filter (\v -> solverBackend v `Set.member` currently_known_backends)
                                          (Set.map baseBackendVersion vs))
                              current_base_vs
        currently_known_backends = Set.map solverBackend (Set.filter (isJust . solverVersion)
                                                                     current_base_vs)

-- | Print out statistics about how the solver cache was used
printSolverCacheStats :: SolverCacheOp ()
printSolverCacheStats opts cache = do
  printOutLn opts Info ("== Solver result cache statistics ==")
  sz <- sizeDB (solverCacheDB cache)
  let sz_s = if sz == 1 then "" else "s"
  case getDBPath (solverCacheDB cache) of
    Nothing ->
      printOutLn opts Info ("- " ++ show sz ++ " result" ++ sz_s ++ " cached in memory")
    Just path -> do
      printOutLn opts Info ("- " ++ show sz ++ " result" ++ sz_s ++ " cached on disk "
                                            ++ "(" ++ path ++ ")")
      let created = solverCacheCreated cache
          created_s = if created == 1 then "y" else "ies"
      printOutLn opts Info ("- " ++ show created ++ " cache entr" ++ created_s ++ " created this run")
  let hits = solverCacheHits cache
      (hits_s1, hits_s2) = if hits == 1 then (" a"," was") else ("s","s were")
  printOutLn opts Info ("- " ++ show hits ++ " time" ++ hits_s1 ++ " cached result" ++ hits_s2 ++ " used this run")
  return ((), cache)
