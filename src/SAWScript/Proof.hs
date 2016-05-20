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
data Theorem s = Theorem { thmTerm :: SharedTerm s }

data Quantification = Existential | Universal
  deriving Eq

-- | A ProofGoal is a term of type Bool, or a function of any arity
-- with a boolean result type. The abstracted arguments are treated as
-- either existentially or universally quantified, according to the
-- indicated quantification.
data ProofGoal s =
  ProofGoal
  { goalQuant :: Quantification
  , goalName :: String
  , goalTerm :: SharedTerm s
  }

-- | A ProofState represents a sequent, where the collection of goals
-- implies the conclusion.
data ProofState s =
  ProofState
  { psGoals :: [ProofGoal s]
  , psConcl :: ProofGoal s
  }

startProof :: ProofGoal s -> ProofState s
startProof g = ProofState [g] g

finishProof :: ProofState s -> Maybe (Theorem s)
finishProof (ProofState gs concl) =
  case gs of
    [] -> Just (Theorem (goalTerm concl))
    _ : _ -> Nothing
