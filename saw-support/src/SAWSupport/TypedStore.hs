{- |
Module      : SAWSupport.TypedStore
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
  , alterM
  , delete
  , map
  , traverse
  , traverse_
  , toList
  , merge
  , mergeM
  , union
  , intersection
  ) where

import Prelude hiding (lookup, map, traverse)
import Data.Coerce
import qualified Data.List as List
import Data.Functor.Identity (Identity(..))

import Type.Reflection
import Data.Type.Equality

import Data.Parameterized.Classes
import Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import Data.Parameterized.Pair

import Data.Parameterized.TraversableF

-- | Internal wrapper for 'TypeRep' that we provide an 'OrdF'
--   instance for.
newtype TypeRep' a = TypeRep' (TypeRep a)
  deriving (TestEquality, Show)

instance OrdF TypeRep' where
  compareF (TypeRep' tr1) (TypeRep' tr2) =
    case testEquality tr1 tr2 of
      Just Refl -> EQF
      Nothing -> case compare (SomeTypeRep tr1) (SomeTypeRep tr2) of
        LT -> LTF
        GT -> GTF
        EQ -> error "inconsistent TypeRep equality"

instance ShowF TypeRep'

withRep :: forall a b. TypeRep' a -> (Typeable a => b) -> b
withRep (TypeRep' tr) f = withTypeable tr f

-- | A store of arbitrary 'Typeable' data, indexed by type.
newtype TypedStore f = TypedStore (MapF TypeRep' f)

-- | An empty 'TypedStore'.
empty :: TypedStore f
empty = TypedStore MapF.empty

-- | Lookup the value of type 'f a' from the store.
lookup :: forall a f. Typeable a => TypedStore f -> Maybe (f a)
lookup (TypedStore tm) = MapF.lookup rep tm
  where
    rep = TypeRep' @a TypeRep

-- | Alter the data of type 'f a' in the store, inserting or
--   deleting based on the result of 'g'.
alter :: forall a f.
  Typeable a =>
  (Maybe (f a) -> Maybe (f a)) ->
  TypedStore f ->
  TypedStore f
alter g ts = runIdentity $ alterM (\ma -> Identity (g ma)) ts

-- | Alter the data of type 'f a' in the store, inserting or deleting
-- based on the result of the monadic action 'g'.
alterM :: forall a f m.
  Typeable a =>
  Monad m =>
  (Maybe (f a) -> m (Maybe (f a))) ->
  TypedStore f ->
  m (TypedStore f)
alterM g (TypedStore tm) = 
  (TypedStore . MapF.updatedValue) <$> tm'
  where
    rep = TypeRep' @a TypeRep

    go :: f a -> m (MapF.UpdateRequest (f a))
    go a = g (Just a) >>= \case
      Nothing -> pure $ MapF.Delete
      Just a' -> pure $ MapF.Set a'

    tm' = MapF.updateAtKey rep (g Nothing) go tm

-- | Insert a value of type 'f a' in the store, overwriting existing
--   data.
insert :: forall a f. Typeable a => f a -> TypedStore f -> TypedStore f
insert a = alter (\_ -> Just a)

-- | Create a 'TypedStore' with a single entry of type 'f a'.
singleton :: forall a f. (Typeable f, Typeable a) => f a -> TypedStore f
singleton a = TypedStore (MapF.singleton rep a)
  where
    rep = TypeRep' @a TypeRep

size :: TypedStore f -> Int
size (TypedStore ts) = MapF.size ts

-- | Delete the value of type 'f a' from the store, if present.
delete :: forall a f proxy. Typeable a => proxy a -> TypedStore f -> TypedStore f
delete _ tm = alter @a (\_ -> Nothing) tm

map :: forall f g.
  (forall a. (Typeable a) => f a -> g a) -> 
  TypedStore f -> 
  TypedStore g
map f (TypedStore ts) = TypedStore $ 
  MapF.mapWithKey (\rep x -> withRep rep $ f x) ts

traverse :: forall f g m.
  Applicative m => 
  (forall a. (Typeable a) => f a -> m (g a)) -> 
  TypedStore f -> 
  m (TypedStore g)
traverse f (TypedStore ts) = TypedStore <$>
  MapF.traverseWithKey (\rep x -> withRep rep $ f x) ts

traverse_ :: forall f m.
  Applicative m => 
  (forall a. (Typeable a) => f a -> m ()) -> 
  TypedStore f -> 
  m ()
traverse_ f (TypedStore ts) =
  MapF.traverseWithKey_ (\rep x -> withRep rep $ f x) ts

merge :: forall f g h.
  -- keys in both
  (forall a. (Typeable a) => f a -> g a -> Maybe (h a)) ->
  -- keys only in left
  (forall a. (Typeable a) => f a -> Maybe (h a)) ->
  -- keys only in right
  (forall a. (Typeable a) => g a -> Maybe (h a)) ->
  TypedStore f ->
  TypedStore g ->
  TypedStore h
merge f g1 g2 (TypedStore ts1) (TypedStore ts2) =
  TypedStore $ MapF.mergeWithKey 
    (\rep x y -> withRep rep $ f x y)
    (MapF.mapMaybeWithKey (\rep x -> withRep rep $ g1 x))
    (MapF.mapMaybeWithKey (\rep x -> withRep rep $ g2 x))
    ts1 ts2

mergeM :: forall f g h m.
  Applicative m =>
  -- keys in both
  (forall a. (Typeable a) => f a -> g a -> m (Maybe (h a))) ->
  -- keys only in left
  (forall a. (Typeable a) => f a -> m (Maybe (h a))) ->
  -- keys only in right
  (forall a. (Typeable a) => g a -> m (Maybe (h a))) ->
  TypedStore f ->
  TypedStore g ->
  m (TypedStore h)
mergeM f g1 g2 (TypedStore ts1) (TypedStore ts2) =
  TypedStore <$> MapF.mergeWithKeyM 
    (\rep x y -> withRep rep $ f x y)
    (MapF.traverseMaybeWithKey (\rep x -> withRep rep $ g1 x))
    (MapF.traverseMaybeWithKey (\rep x -> withRep rep $ g2 x))
    ts1 ts2

-- | Combine two 'TypedStore's, using the given function to merge
--   entries of the same type.
union :: forall f.
  (forall a. (Typeable a) => f a -> f a -> Maybe (f a)) ->
  TypedStore f ->
  TypedStore f ->
  TypedStore f
union f (TypedStore ts1) (TypedStore ts2) = TypedStore $
  MapF.mergeWithKey (\rep x y -> withRep rep $ f x y) id id ts1 ts2

-- | Intersect two 'TypedStore's, using the given function to merge
--   entries of the same type, and discarding types which only are
--   only present in one store.
intersection :: forall f.
  (forall a. (Typeable a) => f a -> f a -> Maybe (f a)) ->
  TypedStore f ->
  TypedStore f ->
  TypedStore f
intersection f (TypedStore ts1) (TypedStore ts2) = TypedStore $
  MapF.mergeWithKey (\rep x y -> withRep rep $ f x y) 
    (const MapF.empty) (const MapF.empty) ts1 ts2

toList :: forall f b.
  (forall a. (Typeable a) => f a -> b) -> TypedStore f -> [b]
toList f (TypedStore ts) = 
  List.map (\(Pair rep x) -> withRep rep $ f x) $ MapF.toList ts

instance FunctorF TypedStore where
  fmapF = map

instance FoldableF TypedStore where
  foldrF f z (TypedStore ts) = foldrF f z ts

instance TraversableF TypedStore where
  traverseF = traverse

instance EqF f => Eq (TypedStore f) where
  (TypedStore ts1) == (TypedStore ts2) = ts1 == ts2

newtype Pair' f g = Pair' (Pair f g)
  deriving (Eq)

instance (EqF g, OrdF f, OrdF g) => Ord (Pair' f g) where
  compare (Pair' (Pair f1 g1)) (Pair' (Pair f2 g2)) =
    toOrdering (compareF f1 f2) <> toOrdering (compareF g1 g2)

instance (EqF f, OrdF f) => Ord (TypedStore f) where
  compare (TypedStore ts1) (TypedStore ts2) = 
    compare 
      (coerce (MapF.toList ts1) :: [Pair' TypeRep' f]) 
      (coerce (MapF.toList ts2) :: [Pair' TypeRep' f])

instance (EqF f, HashableF f) => Hashable (TypedStore f) where
  hashWithSalt i = foldrF (\x y -> hashWithSaltF y x) i

instance ShowF f => Show (TypedStore f) where
  show (TypedStore ts) = show ts