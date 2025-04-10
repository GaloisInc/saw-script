module SAWScript.ASTUtil (
    namedTyVars
 ) where

import Data.Map (Map)
import qualified Data.Map as M

import SAWScript.Position
import SAWScript.AST

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

