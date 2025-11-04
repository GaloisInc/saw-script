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
-- NamedTyVars {{{

--
-- namedTyVars is a type-class-polymorphic function for extracting named
-- type variables from a type or type schema. It returns a set of Name
-- (Name is just Text) manifested as a map from those Names to their
-- positions/provenance.
--

class NamedTyVars t where
  namedTyVars :: t -> Map Name Pos

instance (Ord k, NamedTyVars a) => NamedTyVars (Map k a) where
  namedTyVars = namedTyVars . Map.elems

instance (NamedTyVars a) => NamedTyVars [a] where
  namedTyVars = Map.unionsWith choosePos . map namedTyVars

instance NamedTyVars Type where
  namedTyVars t = case t of
    TyCon _ _ ts      -> namedTyVars ts
    TyRecord _ tm     -> namedTyVars tm
    TyVar pos n       -> Map.singleton n pos
    TyUnifyVar _ _    -> Map.empty

instance NamedTyVars Schema where
  namedTyVars (Forall ns t) = namedTyVars t Map.\\ Map.fromList ns'
    where ns' = map (\(pos, n) -> (n, pos)) ns


------------------------------------------------------------
-- SubstituteTyVars {{{

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

instance SubstituteTyVars Type where
  substituteTyVars avail tyenv ty = case ty of
    TyCon pos tc ts     -> TyCon pos tc (substituteTyVars avail tyenv ts)
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

instance SubstituteTyVars' Type where
  substituteTyVars' avail tyenv ty = case ty of
    TyCon pos tc ts     -> TyCon pos tc (substituteTyVars' avail tyenv ts)
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

-- }}}


------------------------------------------------------------
-- Deprecation {{{

isDeprecated :: PrimitiveLifecycle -> Bool
isDeprecated lc = case lc of
    Current -> False
    WarnDeprecated -> True
    HideDeprecated -> True
    Experimental -> False


-- }}}
