{- |
Module           : $Header$
Description      :
License          : BSD3
Stability        : provisional
Point-of-contact : huffman
-}
module SAWScript.Proof where

import Verifier.SAW.SharedTerm

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
  , goalName :: String
  , goalTerm :: Term
  }

-- | A ProofState represents a sequent, where the collection of goals
-- implies the conclusion.
data ProofState =
  ProofState
  { psGoals :: [ProofGoal]
  , psConcl :: ProofGoal
  }

startProof :: ProofGoal -> ProofState
startProof g = ProofState [g] g

finishProof :: ProofState -> Maybe Theorem
finishProof (ProofState gs concl) =
  case gs of
    [] -> Just (Theorem (goalTerm concl))
    _ : _ -> Nothing
