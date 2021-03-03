module Verifier.SAW.SATQuery where

import Control.Monad (foldM)
import Data.Map (Map)
import Data.Set (Set)

import Verifier.SAW.Name
import Verifier.SAW.FiniteValue
import Verifier.SAW.SharedTerm

data SATQuery =
  SATQuery
  { satVariables :: Map (ExtCns Term) FirstOrderType
  , satUninterp  :: Set VarIndex
  , satAsserts   :: [Term]
  }

data SATResult
  = Unsatisfiable
  | Satisfiable (ExtCns Term -> IO FirstOrderValue)
  | Unknown

satQueryAsTerm :: SharedContext -> SATQuery -> IO Term
satQueryAsTerm sc satq =
  case satAsserts satq of
         [] -> scBool sc True
         (x:xs) -> foldM (scAnd sc) x xs
