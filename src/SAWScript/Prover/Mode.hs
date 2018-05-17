module SAWScript.Prover.Mode where

data ProverMode = Prove    -- ^ Look for counter example (negates goal)
                | CheckSat -- ^ Look for a satisfiable assignment.
  deriving (Show,Eq)

