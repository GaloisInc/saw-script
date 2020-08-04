{- |
Module      : SAWScript.Proof
Description : Representations of SAW-Script proof states.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
module SAWScript.Proof where

import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm
import SAWScript.Prover.SolverStats

-- | A proposition is a saw-core type (i.e. a term of type @sort n@
-- for some @n@). In particular, this includes any pi type whose
-- result type is a proposition. The argument of a pi type represents
-- a universally quantified variable.
newtype Prop = Prop { unProp :: Term }

-- | A theorem is a proposition which has been wrapped in a
-- constructor indicating that it has already been proved.
data Theorem = Theorem { thmProp :: Prop }

-- | A @ProofGoal@ contains a proposition to be proved, along with
-- some metadata.
data ProofGoal =
  ProofGoal
  { goalNum  :: Int
  , goalType :: String
  , goalName :: String
  , goalProp :: Prop
  }

data Quantification = Existential | Universal
  deriving Eq

-- | Construct a 'ProofGoal' from a term of type @Bool@, or a function
-- of any arity with a boolean result type. Any function arguments are
-- treated as quantified variables. If the 'Quantification' argument
-- is 'Existential', then the predicate is negated and turned into a
-- universally-quantified goal.
makeProofGoal ::
  SharedContext ->
  Quantification ->
  Int    {- goal number    -} ->
  String {- goal type      -} ->
  String {- goal name      -} ->
  Term   {- goal predicate -} ->
  IO ProofGoal
makeProofGoal sc quant gnum gtype gname t =
  do t' <- predicateToProp sc quant [] t
     return (ProofGoal gnum gtype gname t')

-- | Convert a term with a function type of any arity into a pi type.
-- Negate the term if the result type is @Bool@ and the quantification
-- is 'Existential'.
predicateToProp :: SharedContext -> Quantification -> [Term] -> Term -> IO Prop
predicateToProp sc quant env t =
  case asLambda t of
    Just (x, ty, body) ->
      do Prop body' <- predicateToProp sc quant (ty : env) body
         Prop <$> scPi sc x ty body'
    Nothing ->
      do (argTs, resT) <- asPiList <$> scTypeOf' sc env t
         let toPi [] t0 =
               case asBoolType resT of
                 Nothing -> return t0 -- TODO: check quantification
                 Just () ->
                   case quant of
                     Universal -> scEqTrue sc t0
                     Existential -> scEqTrue sc =<< scNot sc t0
             toPi ((x, xT) : tys) t0 =
               do t1 <- incVars sc 0 1 t0
                  t2 <- scApply sc t1 =<< scLocalVar sc 0
                  t3 <- toPi tys t2
                  scPi sc x xT t3
         Prop <$> toPi argTs t

-- | Turn a pi type with an @EqTrue@ result into a lambda term with a
-- boolean result type. This function exists to interface the new
-- pi-type proof goals with older proof tactic implementations that
-- expect the old lambda-term representation.
propToPredicate :: SharedContext -> Prop -> IO Term
propToPredicate sc (Prop goal) =
  do let (args, t1) = asPiList goal
     case asEqTrue t1 of
       Just t2 -> scLambdaList sc args t2
       Nothing -> fail $ "propToPredicate: expected EqTrue, actual " ++ show t1

-- | A ProofState represents a sequent, where the collection of goals
-- implies the conclusion.
data ProofState =
  ProofState
  { psGoals :: [ProofGoal]
  , psConcl :: ProofGoal
  , psStats :: SolverStats
  , psTimeout :: Maybe Integer
  }

startProof :: ProofGoal -> ProofState
startProof g = ProofState [g] g mempty Nothing

finishProof :: ProofState -> (SolverStats, Maybe Theorem)
finishProof (ProofState gs concl stats _) =
  case gs of
    []    -> (stats, Just (Theorem (goalProp concl)))
    _ : _ -> (stats, Nothing)
