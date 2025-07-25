{- |
Module      : SAWCentral.Prover.SolverStats
Description : Represents information about solved goals.
Maintainer  : atomb
Stability   : provisional
-}
{-# LANGUAGE OverloadedStrings #-}

module SAWCentral.Prover.SolverStats where

import Data.Semigroup
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Set (Set)
import qualified Data.Set as Set

import Prelude


-- | Data structure for recording useful information about
--   verification runs on goals.
data SolverStats
 = SolverStats
   { -- | The names of the solvers that proved this goal.  If verification was
     --   skipped for some reason, this should be the empty set.
     solverStatsSolvers :: Set Text
     -- | The size of the term(s) that represent the proof obligations
     --   involved in this verification goal.  Usually, this is the size
     --   of the SAWCore term representing the goal, but it might also
     --   be the size of an AIG network, etc.
   , solverStatsGoalSize :: Integer
   }
 deriving (Show)

solverStats :: Text -> Integer -> SolverStats
solverStats nm sz = SolverStats (Set.singleton nm) sz

instance Semigroup SolverStats where
  SolverStats xs n <> SolverStats ys m = SolverStats (mappend xs ys) (n+m)

instance Monoid SolverStats where
  mempty = SolverStats mempty 0
  mappend = (<>)


ppStats :: SolverStats -> Text
ppStats x = "Goal size " <> Text.pack (show $ solverStatsGoalSize x) <>
            ". Provers used: " <>
            Text.intercalate "," (Set.toList (solverStatsSolvers x))

