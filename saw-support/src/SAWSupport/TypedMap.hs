{- |
Module      : SAWSupport.TypedMap
Copyright   : Galois, Inc. 2012-2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

Map with heterogenous codomain.
-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module SAWSupport.TypedMap
  ( TypedMap
  , empty
  , insert
  , lookup
  , alter
  , delete
  , elems
  , toMap
  , toIntMap
  , toList
  ) where

import Prelude hiding (lookup)
import Data.Functor.Identity (Identity(..))
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Map (Map)
import qualified Data.Map as Map
import Type.Reflection
import Data.Type.Equality

import Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF

-- | Internal wrapper for 'TypeRep' that we provide an 'MapF.OrdF'
--   instance for.
newtype TypeRep' a = TypeRep' (TypeRep a)
  deriving (TestEquality)

instance MapF.OrdF TypeRep' where
  compareF (TypeRep' tr1) (TypeRep' tr2) =
    case testEquality tr1 tr2 of
      Just Refl -> MapF.EQF
      Nothing -> case compare (SomeTypeRep tr1) (SomeTypeRep tr2) of
        LT -> MapF.LTF
        GT -> MapF.GTF
        EQ -> error "inconsistent TypeRep equality"

-- | Simple wrapper to intelligently use IntMap if the keys
--   are 'Int'.
data MapPI k v where
  MapP :: Ord k => Map k v -> MapPI k v
  MapI :: IntMap v -> MapPI Int v

lookupMapPI :: k -> MapPI k v -> Maybe v
lookupMapPI k = \case
  MapP m -> Map.lookup k m
  MapI m -> IntMap.lookup k m

emptyMapPI :: forall k v. (Ord k, Typeable k) => MapPI k v
emptyMapPI = case testEquality (TypeRep @Int) (TypeRep @k) of
  Just Refl -> MapI IntMap.empty
  Nothing -> MapP Map.empty

alterMapPI :: (Maybe v -> Maybe v) -> k -> MapPI k v -> MapPI k v
alterMapPI f k = \case
  MapP m -> MapP (Map.alter f k m)
  MapI m -> MapI (IntMap.alter f k m)

-- | A map that associates keys of type 'k' with values of any
--   'Typeable' type. Each stored type is treated as a distinct map:
--   adding/modifying/deleting entries for a given key and type will
--   not affect entries of other types.
data TypedMap k = (Ord k, Typeable k) =>
  TypedMap (MapF TypeRep' (MapPI k))

-- | An empty 'TypedMap'. Uses 'Typeable' keys to pick the
--   underlying storage datatype based on the type of 'k'.
empty :: forall k. (Ord k, Typeable k) => TypedMap k
empty = TypedMap MapF.empty

-- | Lookup the value of type 'a' associated with the given key.
lookup :: forall a k. Typeable a => k -> TypedMap k -> Maybe a
lookup k (TypedMap tm) = do
  m <- MapF.lookup (TypeRep' typeRep) tm
  lookupMapPI k m

-- | Alter the data of type 'a' associated with this key, inserting or
--   deleting based on the result of 'f'. Values of types other than
--   'a' associated with this key are unmodified.
alter :: forall a k.
  Typeable a =>
  (Maybe a -> Maybe a) ->
  k ->
  TypedMap k ->
  TypedMap k
alter f k (TypedMap tm) = TypedMap (MapF.updatedValue tm')
    where
      rep = TypeRep' (TypeRep @a)

      go :: MapPI k a -> Identity (MapF.UpdateRequest (MapPI k a))
      go m = pure $ MapF.Set (alterMapPI f k m)

      tm' = runIdentity $
        MapF.updateAtKey rep (pure $ Just emptyMapPI) go tm


-- | Insert a value of type 'a' at the given key.
insert :: forall a k. Typeable a => k -> a -> TypedMap k -> TypedMap k
insert k a = alter (\_ -> Just a) k

-- | Delete the value of type 'a' for the given key, if it exists.
delete :: forall a k. Typeable a => k -> TypedMap k -> TypedMap k
delete k tm = alter @a (\_ -> Nothing) k tm

lookup' :: forall a k. Typeable a => TypedMap k -> MapPI k a
lookup' (TypedMap tm) = case MapF.lookup rep tm of
  Just m -> m
  Nothing -> emptyMapPI
  where
    rep = TypeRep' (TypeRep @a)

elems :: forall a k. Typeable a => TypedMap k -> [a]
elems tm = case lookup' tm of
  MapP m -> Map.elems m
  MapI m -> IntMap.elems m

toMap :: forall a k. Typeable a => TypedMap k -> Map k a
toMap tm = case lookup' tm of
  MapP m -> m
  MapI m -> Map.fromAscList $ IntMap.toAscList m

toIntMap :: forall a. Typeable a => TypedMap Int -> IntMap a
toIntMap tm = case lookup' @a @Int tm of
  MapP m -> IntMap.fromAscList $ Map.toAscList m
  MapI m -> m

toList :: forall a k. Typeable a => TypedMap k -> [(k, a)]
toList tm = case lookup' tm of
  MapP m -> Map.toList m
  MapI m -> IntMap.toList m