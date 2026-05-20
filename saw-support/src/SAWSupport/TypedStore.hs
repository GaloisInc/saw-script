{- |
Module      : SAWSupport.TypedMap
Copyright   : Galois, Inc. 2012-2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

A store of arbitrary data, indexed by type.
-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}

module SAWSupport.TypedStore
  ( TypedStore
  , empty
  , insert
  , singleton
  , size
  , lookup
  , alter
  , delete
  , map
  , traverse
  , toList
  , merge
  , union
  , intersection
  ) where

import Prelude hiding (lookup, map, traverse)
import qualified Data.List as List
import Data.Functor.Identity (Identity(..))
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

newtype Wrapped t = Wrapped { unwrap :: t }

-- | A store of arbitrary 'Typeable' data, indexed by type.
newtype TypedStore = TypedStore (MapF TypeRep' Wrapped)

-- | An empty 'TypedStore'.
empty :: TypedStore
empty = TypedStore MapF.empty

-- | Lookup the value of type 'a' from the store.
lookup :: forall a. Typeable a => TypedStore -> Maybe a
lookup (TypedStore tm) = fmap unwrap $ MapF.lookup (TypeRep' typeRep) tm

-- | Alter the data of type 'a' in the store, inserting or
--   deleting based on the result of 'f'.
alter :: forall a.
  Typeable a =>
  (Maybe a -> Maybe a) ->
  TypedStore ->
  TypedStore
alter f (TypedStore tm) = TypedStore (MapF.updatedValue tm')
  where
    rep = TypeRep' (TypeRep @a)

    go :: Wrapped a -> Identity (MapF.UpdateRequest (Wrapped a))
    go (Wrapped a) = case f (Just a) of
      Nothing -> pure $ MapF.Delete
      Just a' -> pure $ MapF.Set (Wrapped a')

    tm' = runIdentity $
      MapF.updateAtKey rep (pure $ fmap Wrapped $ f Nothing) go tm


-- | Insert a value of type 'a' in the store, overwriting existing
--   data.
insert :: forall a. Typeable a => a -> TypedStore -> TypedStore
insert a = alter (\_ -> Just a)

singleton :: Typeable a => a -> TypedStore
singleton a = TypedStore (MapF.singleton (TypeRep' typeRep) (Wrapped a))

size :: TypedStore -> Int
size (TypedStore ts) = MapF.size ts

-- | Delete the value of type 'a' from the store.
delete :: forall a. Typeable a => TypedStore -> TypedStore
delete tm = alter @a (\_ -> Nothing) tm

map :: (forall a. Typeable a => a -> a) -> TypedStore -> TypedStore
map f (TypedStore ts) = TypedStore $ 
  MapF.mapWithKey (\(TypeRep' TypeRep) (Wrapped x) -> Wrapped (f x)) ts

traverse :: 
  Applicative m => 
  (forall a. Typeable a => a -> m a) -> 
  TypedStore -> 
  m TypedStore
traverse f (TypedStore ts) = TypedStore <$>
  MapF.traverseWithKey (\(TypeRep' TypeRep) (Wrapped x) -> Wrapped <$> f x) ts

liftWrap2 :: 
  (Typeable a => a -> a -> Maybe a) ->
  TypeRep' a -> Wrapped a -> Wrapped a -> Maybe (Wrapped a)
liftWrap2 f (TypeRep' TypeRep) (Wrapped l) (Wrapped r) =
  case f l r of
    Just a -> Just (Wrapped a)
    Nothing -> Nothing

merge :: 
  -- keys in both
  (forall a. Typeable a => a -> a -> Maybe a) ->
  -- keys only in left
  (forall a. Typeable a => a -> Maybe a) ->
  -- keys only in right
  (forall a. Typeable a => a -> Maybe a) ->
  TypedStore ->
  TypedStore ->
  TypedStore
merge f g1 g2 (TypedStore ts1) (TypedStore ts2) =
  TypedStore (MapF.mergeWithKey (liftWrap2 f) (do_filter g1) (do_filter g2) ts1 ts2)
    where
      do_filter :: 
        (forall a. Typeable a => a -> Maybe a) -> 
        MapF TypeRep' Wrapped -> 
        MapF TypeRep' Wrapped
      do_filter g = MapF.mapMaybeWithKey $ 
        \(TypeRep' TypeRep) (Wrapped a) ->
          case g a of
            Just b -> Just (Wrapped b)
            Nothing -> Nothing

-- | Combine two 'TypedStore's, using the given function to merge
--   entries of the same type.
union :: 
  (forall a. Typeable a => a -> a -> Maybe a) ->
  TypedStore ->
  TypedStore ->
  TypedStore
union f (TypedStore ts1) (TypedStore ts2) =
  TypedStore (MapF.mergeWithKey (liftWrap2 f) id id ts1 ts2)

-- | Intersect two 'TypedStore's, using the given function to merge
--   entries of the same type, and discarding types which only are
--   only present in one store.
intersection :: 
  (forall a. Typeable a => a -> a -> Maybe a) ->
  TypedStore ->
  TypedStore ->
  TypedStore
intersection f (TypedStore ts1) (TypedStore ts2) =
  TypedStore (MapF.mergeWithKey (liftWrap2 f) (const MapF.empty) (const MapF.empty) ts1 ts2)

toList :: (forall a. Typeable a => a -> b) -> TypedStore -> [b]
toList f (TypedStore ts) = 
  List.map (\(MapF.Pair (TypeRep' TypeRep) (Wrapped x)) -> f x) $ MapF.toList ts