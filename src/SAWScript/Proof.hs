{- |
Module      : SAWScript.Proof
Description : Representations of SAW-Script proof states.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
module SAWScript.Proof where

import Verifier.SAW.SharedTerm
import SAWScript.Prover.SolverStats

-- | A theorem must contain a boolean term, possibly surrounded by one
-- or more lambdas which are interpreted as universal quantifiers.
data Theorem = Theorem { thmTerm :: Term }

data Quantification = Existential | Universal
  deriving Eq

-- | A ProofGoal is a term of type Bool, or a function of any arity
-- with a boolean result type. The abstracted arguments are treated as
-- either existentially or universally quantified, according to the
-- indicated quantification.
data ProofGoal =
  ProofGoal
  { goalQuant :: Quantification
  , goalNum  :: Int
  , goalType :: String
  , goalName :: String
  , goalTerm :: Term
  }

-- | A ProofState represents a sequent, where the collection of goals
-- implies the conclusion.
data ProofState =
  ProofState
  { psGoals :: [ProofGoal]
  , psConcl :: ProofGoal
  , psStats :: SolverStats
  }

startProof :: ProofGoal -> ProofState
startProof g = ProofState [g] g mempty

finishProof :: ProofState -> (SolverStats, Maybe Theorem)
finishProof (ProofState gs concl stats) =
  case gs of
    []    -> (stats, Just (Theorem (goalTerm concl)))
    _ : _ -> (stats, Nothing)
