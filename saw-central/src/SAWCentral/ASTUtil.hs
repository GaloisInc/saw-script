module SAWCentral.ASTUtil (
    namedTyVars,
    SubstituteTyVars(..)
 ) where

import Data.Map (Map)
import qualified Data.Map as M

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
  namedTyVars = namedTyVars . M.elems

instance (NamedTyVars a) => NamedTyVars [a] where
  namedTyVars = M.unionsWith choosePos . map namedTyVars

instance NamedTyVars Type where
  namedTyVars t = case t of
    TyCon _ _ ts      -> namedTyVars ts
    TyRecord _ tm     -> namedTyVars tm
    TyVar pos n       -> M.singleton n pos
    TyUnifyVar _ _    -> M.empty

instance NamedTyVars Schema where
  namedTyVars (Forall ns t) = namedTyVars t M.\\ M.fromList ns'
    where ns' = map (\(pos, n) -> (n, pos)) ns


------------------------------------------------------------
-- SubstituteTyVars {{{

--
-- substituteTyVars is a typeclass-polymorphic function for
-- substituting named type variables (such as those declared with
-- typedef) in a Type.
--
-- Note: substituteTyVars is exposed from this module and reused by
-- the interpreter as part of its handling of typedefs during
-- execution.
--

class SubstituteTyVars t where
  -- | @substituteTyVars m x@ applies the map @m@ to type variables in @x@.
  substituteTyVars :: Map Name NamedType -> t -> t

instance (SubstituteTyVars a) => SubstituteTyVars (Maybe a) where
  substituteTyVars tyenv = fmap (substituteTyVars tyenv)

instance (SubstituteTyVars a) => SubstituteTyVars [a] where
  substituteTyVars tyenv = map (substituteTyVars tyenv)

instance SubstituteTyVars Type where
  substituteTyVars tyenv ty = case ty of
    TyCon pos tc ts     -> TyCon pos tc (substituteTyVars tyenv ts)
    TyRecord pos fs     -> TyRecord pos (fmap (substituteTyVars tyenv) fs)
    TyUnifyVar _ _      -> ty
    TyVar _ n           ->
        case M.lookup n tyenv of
            Nothing -> ty
            Just AbstractType -> ty
            Just (ConcreteType ty') -> ty'

-- }}}
