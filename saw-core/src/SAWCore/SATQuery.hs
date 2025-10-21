module SAWCore.SATQuery
( SATQuery(..)
, SATResult(..)
, SATAssert(..)
, satQueryAsTerm
, satQueryAsPropTerm
) where

import Data.Map (Map)
import Data.Set (Set)
import Data.Foldable (foldrM)

import SAWCore.Name
import SAWCore.FiniteValue
import SAWCore.SharedTerm

-- | This datatype represents a satisfiability query that might
--   be dispatched to a solver.  It carries a series of assertions
--   to be made to a solver, together with a collection of
--   variables we expect the solver to report models over,
--   and a collection of @VarIndex@ values identifying
--   subterms that should be considered uninterpreted.
--
--   All the free variables in the query should
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
  { satVariables :: Map VarName FirstOrderType
      -- ^ The variables in the query, for which we
      --   expect the solver to find values in satisfiable
      --   cases.

  , satUninterp  :: Set VarIndex
      -- ^ A set indicating which variables and constant
      --   values should be considered uninterpreted by
      --   the solver. Models will not report values
      --   for uninterpreted values.

  , satAsserts   :: [SATAssert]
      -- ^ A collection of assertions. The overall
      --   query should be understood as the conjunction
      --   of these terms.
  }

-- | The type of assertions we can make to a solver. These
--   are either boolean terms, or universally-quantified
--   statements. At present, only the What4 backends can
--   handle universally quantified statments, and only
--   some of the solvers will accept them without errors.
data SATAssert
   = BoolAssert Term -- ^ A boolean term to be asserted
   | UniversalAssert [(VarName, FirstOrderType)] [Term] Term
          -- ^ A universally-quantified assertion, consisting of a
          --   collection of first-order variables, a sequence
          --   of boolean hypotheses, and a boolean conclusion

-- | The result of a sat query. In the event a model is found,
--   return a mapping from variable names to values.
data SATResult
  = Unsatisfiable
  | Satisfiable (VarName -> IO FirstOrderValue)
  | Unknown

-- | Compute the conjunction of all the assertions
--   in this SAT query as a single term of type Bool.
--
--   This method of reducing a sat query to a boolean
--   cannot be used for universally-quantified assertions,
--   and will raise an error if it encounters one.
satQueryAsTerm :: SharedContext -> SATQuery -> IO Term
satQueryAsTerm sc satq =
  case satAsserts satq of
         [] -> scBool sc True
         (BoolAssert x:xs) -> loop x xs
         (UniversalAssert{} : _) -> univFail
 where
   univFail = fail "satQueryAsTerm : Solver backend cannot handle universally-quantified assertions"

   loop x [] = return x
   loop x (BoolAssert y:xs) =
     do x' <- scAnd sc x y
        loop x' xs
   loop _ (UniversalAssert{} : _) = univFail

-- | Compute the conjunction of all the assertions
--   in this SAT query as a single term of type Prop.
satQueryAsPropTerm :: SharedContext -> SATQuery -> IO Term
satQueryAsPropTerm sc satq =
  scTupleType sc =<< mapM assertAsPropTerm (satAsserts satq)
  where assertAsPropTerm (BoolAssert b) = scEqTrue sc b
        assertAsPropTerm (UniversalAssert vars hs g) =
          do vars' <- traverse (traverse (scFirstOrderType sc)) vars
             scPiList sc vars' =<<
               scEqTrue sc =<< foldrM (scImplies sc) g hs
