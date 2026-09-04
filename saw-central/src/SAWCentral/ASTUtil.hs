{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module SAWCentral.ASTUtil (
    namedTyVars,
    SubstituteTyVars(..),
    SubstituteTyVars'(..),
    isDeprecated
 ) where

import qualified Data.Text as Text
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

import qualified SAWSupport.ScopedMap as ScopedMap
import SAWSupport.ScopedMap (ScopedMap)

import SAWCentral.Panic
import SAWCentral.Position
import SAWCentral.AST


------------------------------------------------------------
-- NamedTyVars

-- | namedTyVars is a type-class-polymorphic function for extracting named
-- type variables from a type or type schema. It returns a set of Name
-- (Name is just Text) manifested as a map from those Names to their
-- originating positions.
--
-- We take the first position we see. The calls to `Map.union` are
-- organized accordingly (it favors its left argument).
--
-- When we find a `TyVar`, we extract the position from the provenance
-- with `getPos`. This is not sensible in general; however, we are
-- called only from the typechecker's @generalize@ operation, which
-- collects names from the bodies of polymorphic functions.
--
-- Those names can have two origins: they can be user-written names,
-- in which case their provenance is `TypeExplicit` and the position
-- is meaningful; or they can be the the results of running
-- @generalize@. While we never run @generalize@ directly on the same
-- function body more than once, we do (must) rescan the bodies of
-- nested functions for occurrences of type variables properly
-- belonging to the enclosing function. That can turn up generalized
-- type variables that belong to the nested function.
--
-- We don't attempt to avoid extracting the positions from those type
-- variables. However, we discard the results in the `Schema`
-- instance: anything forall-bound within the schema is contained
-- within it and shouldn't escape. So it doesn't matter if the
-- positions we extract from those type variables are meaningful.
-- However, it does mean extracting them shouldn't crash.
--
-- If things change such that extracting those variables is a problem
-- we can, at the cost of a bunch of complexity, carry the
-- forall-bound variables from the `Schema` into the code for `Type`
-- and skip them when they appear.
--
-- FUTURE: given that we're now specific to being called from the
-- typechecker, maybe this should get moved back to Typechecker.hs.
--
class NamedTyVars t where
  namedTyVars :: t -> Map Name Pos

instance (Ord k, NamedTyVars a) => NamedTyVars (Map k a) where
  namedTyVars = namedTyVars . Map.elems

instance (NamedTyVars a) => NamedTyVars [a] where
  namedTyVars ts = Map.unions $ map namedTyVars ts

instance (NamedTyVars a) => NamedTyVars (Pos, a) where
  namedTyVars (_pos, x) = namedTyVars x

instance NamedTyVars Type where
  namedTyVars t = case t of
    TyCon _ _ ts      -> namedTyVars ts
    TyFunc _ _ params namedParams ret ->
        let paramVars = namedTyVars params
            namedParamVars = namedTyVars namedParams
            retVars = namedTyVars ret
        in
        Map.unions [paramVars, namedParamVars, retVars]
    TyRecord _ tm     -> namedTyVars tm
    TyVar prov n      -> Map.singleton n (getPos prov)
    TyUnifyVar _ _    -> Map.empty

instance NamedTyVars Schema where
  namedTyVars (Forall ns t) = namedTyVars t Map.\\ Map.fromList ns'
    where ns' = map (\(pos, n) -> (n, pos)) ns


------------------------------------------------------------
-- SubstituteTyVars

--
-- substituteTyVars is a typeclass-polymorphic function for
-- substituting named type variables (such as those declared with
-- typedef) in a Type.
--
-- Panics if we try to substitute a definition that isn't visible.
--
-- Note: substituteTyVars is reused by the interpreter as part of its
-- handling of typedefs during execution as well as by the
-- typechecker.
--
-- XXX: it's not clear that the instances for Maybe and List warrant
-- setting up the typeclass.
--

class SubstituteTyVars t where
  -- | @substituteTyVars m x@ applies the (scoped) map @m@ to type variables in @x@.
  substituteTyVars ::
      Set PrimitiveLifecycle ->
      ScopedMap Name (PrimitiveLifecycle, NamedType) ->
      t -> t

instance (SubstituteTyVars a) => SubstituteTyVars (Maybe a) where
  substituteTyVars avail tyenv = fmap (substituteTyVars avail tyenv)

instance (SubstituteTyVars a) => SubstituteTyVars [a] where
  substituteTyVars avail tyenv = map (substituteTyVars avail tyenv)

instance (SubstituteTyVars a) => SubstituteTyVars (Map k a) where
  substituteTyVars avail tyenv m = Map.map (substituteTyVars avail tyenv) m

instance (SubstituteTyVars a) => SubstituteTyVars (pos, a) where
  substituteTyVars avail tyenv (pos, x) = (pos, substituteTyVars avail tyenv x)

instance SubstituteTyVars Type where
  substituteTyVars avail tyenv ty = case ty of
    TyCon pos tc ts     -> TyCon pos tc (substituteTyVars avail tyenv ts)
    TyFunc pos nameinfo params namedParams ret ->
        let params' = substituteTyVars avail tyenv params
            namedParams' = substituteTyVars avail tyenv namedParams
            ret' = substituteTyVars avail tyenv ret
        in
        TyFunc pos nameinfo params' namedParams' ret'
    TyRecord pos fs     -> TyRecord pos (fmap (substituteTyVars avail tyenv) fs)
    TyUnifyVar _ _      -> ty
    TyVar _ n           ->
        case ScopedMap.lookup n tyenv of
            Nothing -> ty
            Just (lc, expansion) ->
                if not (Set.member lc avail) then
                    panic "substituteTyVars" [
                        "Found reference to non-visible typedef: " <> n,
                        "Lifecycle setting: " <> Text.pack (show lc)
                    ]
                else case expansion of
                    AbstractType _kind  -> ty
                    ConcreteType ty' -> ty'

--
-- The prime version uses an ordinary map.
--
-- This is used by the typechecker for the time being until the
-- typechecker gets taught to use ScopedMap.
--

class SubstituteTyVars' t where
  -- | @substituteTyVars' m x@ applies the (ordinary) map @m@ to type variables in @x@.
  substituteTyVars' ::
      Set PrimitiveLifecycle ->
      Map Name (PrimitiveLifecycle, NamedType) ->
      t -> t

instance (SubstituteTyVars' a) => SubstituteTyVars' (Maybe a) where
  substituteTyVars' avail tyenv = fmap (substituteTyVars' avail tyenv)

instance (SubstituteTyVars' a) => SubstituteTyVars' [a] where
  substituteTyVars' avail tyenv = map (substituteTyVars' avail tyenv)

instance (SubstituteTyVars' a) => SubstituteTyVars' (Map k a) where
  substituteTyVars' avail tyenv m = Map.map (substituteTyVars' avail tyenv) m

instance (SubstituteTyVars' a) => SubstituteTyVars' (pos, a) where
  substituteTyVars' avail tyenv (pos, x) = (pos, substituteTyVars' avail tyenv x)

instance SubstituteTyVars' Type where
  substituteTyVars' avail tyenv ty = case ty of
    TyCon pos tc ts     -> TyCon pos tc (substituteTyVars' avail tyenv ts)
    TyFunc pos nameinfo params namedParams ret ->
        let params' = substituteTyVars' avail tyenv params
            namedParams' = substituteTyVars' avail tyenv namedParams
            ret' = substituteTyVars' avail tyenv ret
        in
        TyFunc pos nameinfo params' namedParams' ret'
    TyRecord pos fs     -> TyRecord pos (fmap (substituteTyVars' avail tyenv) fs)
    TyUnifyVar _ _      -> ty
    TyVar _ n           ->
        case Map.lookup n tyenv of
            Nothing -> ty
            Just (lc, expansion) ->
                if not (Set.member lc avail) then
                    panic "substituteTyVars'" [
                        "Found reference to non-visible typedef: " <> n,
                        "Lifecycle setting: " <> Text.pack (show lc)
                    ]
                else case expansion of
                    AbstractType _kind -> ty
                    ConcreteType ty' -> ty'


------------------------------------------------------------
-- Deprecation

isDeprecated :: PrimitiveLifecycle -> Bool
isDeprecated lc = case lc of
    Current -> False
    WarnDeprecated -> True
    HideDeprecated -> True
    Experimental -> False
