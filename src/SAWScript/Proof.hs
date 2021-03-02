{- |
Module      : SAWScript.Proof
Description : Representations of SAW-Script proof states.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

module SAWScript.Proof
  ( Prop
  , splitProp
  , unfoldProp
  , simplifyProp
  , evalProp
  , betaReduceProp
  , falseProp
  , termToProp
  , propToTerm
  , propToRewriteRule
  , propIsTrivial
  , propSize
  , prettyProp
  , ppProp

  , Theorem(..)

  , ProofGoal(..)
  , goalApply
  , goalIntro
  , goalAssume
  , goalInsert

  , Quantification(..)
  , makeProofGoal
  , predicateToProp
  , propToPredicate
  , ProofState(..)
  , startProof
  , finishProof
  ) where

import           Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import           Data.Set (Set)
import           Data.Text (Text)
import qualified Data.Text as Text

import Verifier.SAW.Prelude (scApplyPrelude_False)
import Verifier.SAW.Recognizer
import Verifier.SAW.Rewriter
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST
import Verifier.SAW.TypedTerm
import Verifier.SAW.Term.Pretty (SawDoc)

import SAWScript.Prover.SolverStats
import SAWScript.Crucible.Common as Common
import qualified Verifier.SAW.Simulator.What4 as W4Sim
import qualified Verifier.SAW.Simulator.What4.ReturnTrip as W4Sim

-- | A proposition is a saw-core type (i.e. a term of type @sort n@
-- for some @n@). In particular, this includes any pi type whose
-- result type is a proposition. The argument of a pi type represents
-- a universally quantified variable.
newtype Prop = Prop Term

unProp :: Prop -> Term
unProp (Prop tm) = tm

-- TODO, check that the given term has a type that is a sort
termToProp :: SharedContext -> Term -> IO Prop
termToProp _sc tm = pure (Prop tm)

propToTerm :: SharedContext -> Prop -> IO Term
propToTerm _sc (Prop tm) = pure tm

propToRewriteRule :: SharedContext -> Prop -> IO (Maybe (RewriteRule))
propToRewriteRule _sc (Prop tm) =
  case ruleOfProp tm of
    Nothing -> pure Nothing
    Just r  -> pure (Just r)

splitProp :: SharedContext -> Prop -> IO (Maybe (Prop, Prop))
splitProp sc (Prop p) =
  do let (vars, body) = asPiList p
     case (isGlobalDef "Prelude.and" <@> return <@> return) =<< asEqTrue body of
       Nothing -> pure Nothing
       Just (_ :*: p1 :*: p2) ->
         do t1 <- scPiList sc vars =<< scEqTrue sc p1
            t2 <- scPiList sc vars =<< scEqTrue sc p2
            return (Just (Prop t1,Prop t2))

unfoldProp :: SharedContext -> Set VarIndex -> Prop -> IO Prop
unfoldProp sc unints (Prop tm) =
  do tm' <- scUnfoldConstantSet sc True unints tm
     return (Prop tm')

simplifyProp :: SharedContext -> Simpset -> Prop -> IO Prop
simplifyProp sc ss (Prop tm) =
  do tm' <- rewriteSharedTerm sc ss tm
     return (Prop tm')

evalProp :: SharedContext -> Set VarIndex -> Prop -> IO Prop
evalProp sc unints (Prop p) =
  do let (args, body) = asPiList p

     body' <-
       case asEqTrue body of
         Just t -> pure t
         Nothing -> fail "goal_eval: expected EqTrue"

     ecs <- traverse (\(nm, ty) -> scFreshEC sc (Text.unpack nm) ty) args
     vars <- traverse (scExtCns sc) ecs
     t0 <- instantiateVarList sc 0 (reverse vars) body'

     sym <- Common.newSAWCoreBackend sc
     st <- Common.sawCoreState sym
     (_names, (_mlabels, p')) <- W4Sim.w4Eval sym st sc mempty unints t0
     t1 <- W4Sim.toSC sym st p'

     t2 <- scEqTrue sc t1
     -- turn the free variables we generated back into pi-bound variables
     t3 <- scGeneralizeExts sc ecs t2
     return (Prop t3)

betaReduceProp :: SharedContext -> Prop -> IO Prop
betaReduceProp sc (Prop tm) =
  do tm' <- betaNormalize sc tm
     return (Prop tm')

falseProp :: SharedContext -> IO Prop
falseProp sc = Prop <$> (scEqTrue sc =<< scApplyPrelude_False sc)

propSize :: Prop -> Integer
propSize (Prop tm) = scSharedSize tm

propIsTrivial :: Prop -> Bool
propIsTrivial (Prop tm) = checkTrue tm
  where
    checkTrue :: Term -> Bool
    checkTrue (asPiList -> (_, asEqTrue -> Just (asBool -> Just True))) = True
    checkTrue _ = False

prettyProp :: PPOpts -> Prop -> String
prettyProp opts (Prop tm) = scPrettyTerm opts tm

ppProp :: PPOpts -> Prop -> SawDoc
ppProp opts (Prop tm) = ppTerm opts tm

-- | A theorem is a proposition which has been wrapped in a
-- constructor indicating that it has already been proved.
data Theorem =
  Theorem
  { thmProp :: Prop
  , thmStats :: SolverStats
  }

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
    []    -> (stats, Just (Theorem (goalProp concl) stats))
    _ : _ -> (stats, Nothing)

{-
propToSATQuery :: SharedContext -> Prop -> IO SATQuery
propToSATQuery sc (Prop goal) =
  do let (args, t1) = asPiList goal
     case asEqTrue t1 of
       Nothing -> fail $ "propToSATQuery: expected EqTrue, actual " ++ show t1
       Just t2 ->
-}


-- TODO: unsound?
goalAssume :: ProofGoal -> IO (Maybe (Theorem, ProofGoal))
goalAssume goal =
  case asPi (unProp (goalProp goal)) of
    Just (_nm, tp, body)
      | looseVars body == emptyBitSet ->
          let goal' = goal{ goalProp = Prop body }
           in return (Just (Theorem (Prop tp) mempty, goal'))

    _ -> return Nothing

goalInsert :: SharedContext -> Theorem -> ProofGoal -> IO ProofGoal
goalInsert sc (Theorem t _stats) goal =
  do body' <- scFun sc (unProp t) (unProp (goalProp goal))
     let goal' = goal{ goalProp = Prop body' }
     return goal'

goalIntro :: SharedContext -> String -> ProofGoal -> IO (Maybe (TypedTerm, ProofGoal))
goalIntro sc s goal =
  case asPi (unProp (goalProp goal)) of
    Nothing -> pure Nothing
    Just (nm, tp, body) ->
      do let name = if null s then Text.unpack nm else s
         x <- scFreshGlobal sc name tp
         tt <- mkTypedTerm sc x
         body' <- instantiateVar sc 0 x body
         let goal' = goal { goalProp = Prop body' }
         return (Just (tt, goal'))

goalApply :: SharedContext -> Theorem -> ProofGoal -> IO (Maybe [ProofGoal])
goalApply sc (Theorem rule _stats) goal = applyFirst (asPiLists (unProp rule))
  where
    applyFirst [] = pure Nothing
    applyFirst ((ruleArgs, ruleConcl) : rest) =
      do result <- scMatch sc ruleConcl (unProp (goalProp goal))
         case result of
           Nothing -> applyFirst rest
           Just inst ->
             do let inst' = [ Map.lookup i inst | i <- take (length ruleArgs) [0..] ]
                dummy <- scUnitType sc
                let mkNewGoals (Nothing : mts) ((_, prop) : args) =
                      do c0 <- instantiateVarList sc 0 (map (fromMaybe dummy) mts) prop
                         cs <- mkNewGoals mts args
                         return (Prop c0 : cs)
                    mkNewGoals (Just _ : mts) (_ : args) =
                      mkNewGoals mts args
                    mkNewGoals _ _ = return []
                newgoalterms <- mkNewGoals inst' (reverse ruleArgs)
                let newgoals = reverse [ goal { goalProp = t } | t <- newgoalterms ]
                return (Just newgoals)

    asPiLists :: Term -> [([(Text, Term)], Term)]
    asPiLists t =
      case asPi t of
        Nothing -> [([], t)]
        Just (nm, tp, body) ->
          [ ((nm, tp) : args, concl) | (args, concl) <- asPiLists body ] ++ [([], t)]
