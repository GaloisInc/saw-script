module SAWScript.ASTUtil (
    namedVars
 ) where

import Data.Map (Map)
import qualified Data.Map as M

import SAWScript.Position
import SAWScript.AST

--
-- namedVars is a type-class-polymorphic function for extracting named
-- type variables from a type or type schema. It returns a set of Name
-- (Name is just Text) manifested as a map from those Names to their
-- positions/provenance.
--

class NamedVars t where
  namedVars :: t -> Map Name Pos

instance (Ord k, NamedVars a) => NamedVars (Map k a) where
  namedVars = namedVars . M.elems

instance (NamedVars a) => NamedVars [a] where
  namedVars = M.unionsWith choosePos . map namedVars

instance NamedVars Type where
  namedVars t = case t of
    TyCon _ _ ts      -> namedVars ts
    TyRecord _ tm     -> namedVars tm
    TyVar pos n       -> M.singleton n pos
    TyUnifyVar _ _    -> M.empty

instance NamedVars Schema where
  namedVars (Forall ns t) = namedVars t M.\\ M.fromList ns'
    where ns' = map (\(pos, n) -> (n, pos)) ns

