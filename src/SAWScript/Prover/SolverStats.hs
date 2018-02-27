{- |
Module      : SAWScript.Prover.SolverStats
Description : Represents information about solved goals.
Maintainer  : atomb
Stability   : provisional
-}

module SAWScript.Prover.SolverStats where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (intercalate)

-- | Data structure for recording useful information about
--   verification runs on goals.
data SolverStats
 = SolverStats
   { -- | The names of the solvers that proved this goal.  If verification was
     --   skipped for some reason, this should be the empty list.
     solverStatsSolvers :: Set String
     -- | The size of the term(s) that represent the proof obligations
     --   involved in this verification goal.  Usually, this is the size
     --   of the SAWCore term representing the goal, but it might also
     --   be the size of an AIG network, etc.
   , solverStatsGoalSize :: Integer
   }
 deriving (Show)

solverStats :: String -> Integer -> SolverStats
solverStats nm sz = SolverStats (Set.singleton nm) sz

instance Monoid SolverStats where
  mempty = SolverStats mempty 0
  mappend (SolverStats xs n) (SolverStats ys m) = SolverStats (mappend xs ys) (n+m)


ppStats :: SolverStats -> String
ppStats x = "Goal size " ++ show (solverStatsGoalSize x) ++
            ". Provers used: " ++
            intercalate "," (Set.toList (solverStatsSolvers x))

