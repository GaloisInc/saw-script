module Verifier.SAW.SATQuery
( SATQuery(..)
, SATResult(..)
, satQueryAsTerm
) where

import Control.Monad (foldM)
import Data.Map (Map)
import Data.Set (Set)

import Verifier.SAW.Name
import Verifier.SAW.FiniteValue
import Verifier.SAW.SharedTerm

-- | This datatype represents a satisfiability query that might
--   be dispatched to a solver.  It carries a series of assertions
--   to be made to a solver, together with a collection of
--   variables we expect the solver to report models over,
--   and a collection of @VarIndex@ values identifying
--   subterms that should be considered uninterpreted.
--
--   All the @ExtCns@ values in the query should
--   appear either in @satVariables@ or @satUninterp@.
--   Constant values for which definitions are provided
--   may also appear in @satUninterp@, in which case
--   they will be treated as uninterpreted.  Otherwise,
--   their definitions will be unfolded.
--
--   Solve solvers do not support uninterpreted values
--   and will fail if presented a query that requests them.
data SATQuery =
  SATQuery
  { satVariables :: Map (ExtCns Term) FirstOrderType
      -- ^ The variables in the query, for which we
      --   expect the solver to find values in satisfiable
      --   cases.  INVARIANT: The type of the @ExtCns@ keys
      --   should correspond to the @FirstOrderType@ values.

  , satUninterp  :: Set VarIndex
      -- ^ A set indicating which variables and constant
      --   values should be considered uninterpreted by
      --   the solver. Models will not report values
      --   for uninterpreted values.

  , satAsserts   :: [Term]
      -- ^ A collection of assertions.  These should
      --   all be terms of type @Bool@.  The overall
      --   query should be understood as the conjunction
      --   of these terms.
  }
-- TODO, allow first-order propositions in addition to Boolean terms.

-- | The result of a sat query.  In the event a model is found,
--   return a mapping from the @ExtCns@ variables to values.
data SATResult
  = Unsatisfiable
  | Satisfiable (ExtCns Term -> IO FirstOrderValue)
  | Unknown

-- | Compute the conjunction of all the assertions
--   in this SAT query as a single term of type Bool.
satQueryAsTerm :: SharedContext -> SATQuery -> IO Term
satQueryAsTerm sc satq =
  case satAsserts satq of
         [] -> scBool sc True
         (x:xs) -> foldM (scAnd sc) x xs
-- TODO, we may have to rethink this function
--  once we allow first-order statements.
