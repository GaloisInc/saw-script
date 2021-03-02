{- |
Module      : SAWScript.Proof
Description : Representations of SAW-Script proof states.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}

{-# LANGUAGE LambdaCase #-}
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

  , Theorem
  , admitTheorem
  , solverTheorem
  , proofByTerm
  , thmProp
  , thmStats
  , thmEvidence
  , validateTheorem

  , Evidence(..)
  , checkEvidence

  , impossibleEvidence
  , splitEvidence
  , passthroughEvidence
  , forallEvidence
  , assumeEvidence
  , cutEvidence
  , unfoldEvidence
  , evalEvidence
  , rewriteEvidence
  , leafEvidence

  , ProofGoal(..)
  , withFirstGoal

  , Tactic
  , tacticIntro
  , tacticCut
  , tacticAssume
  , tacticApply
  , tacticSplit
  , tacticTrivial
  , tacticId

  , Quantification(..)
  , makeProofGoal
  , predicateToProp
  , propToPredicate

  , ProofState
  , psTimeout
  , psGoals
  , setProofTimeout
  , startProof
  , finishProof
  ) where

import qualified Control.Monad.Fail as F
import           Control.Monad.State
import           Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text

import Verifier.SAW.Prelude (scApplyPrelude_False)
import Verifier.SAW.Recognizer
import Verifier.SAW.Rewriter
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST
import Verifier.SAW.TypedTerm
import Verifier.SAW.Term.Pretty (SawDoc)
import Verifier.SAW.SCTypeCheck (scTypeCheckError)

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
  { _thmProp :: Prop
  , _thmStats :: SolverStats
  , _thmEvidence :: Evidence
  }
  | LocalAssumption Prop

validateTheorem :: SharedContext -> Theorem -> IO ()
validateTheorem _sc (LocalAssumption p) =
   fail $ unlines
     [ "Illegal use of unbound local hypothesis"
     , showTerm (unProp p)
     ]
validateTheorem sc Theorem{ _thmProp = p, _thmEvidence = e } =
   checkEvidence sc e p

data Evidence
  = ProofTerm Term
  | LocalAssumptionEvidence Prop
  | SolverEvidence SolverStats Prop
  | Admitted Prop
  | QuickcheckEvidence Integer Prop
  | TrivialEvidence
  | SplitEvidence Evidence Evidence
  | ApplyEvidence Theorem [Evidence]
  | AssumeEvidence Prop Evidence
  | ForallEvidence TypedTerm Evidence
  | CutEvidence Theorem Evidence
  | RewriteEvidence Simpset Evidence
  | UnfoldEvidence (Set VarIndex) Evidence
  | EvalEvidence (Set VarIndex) Evidence

thmProp :: Theorem -> Prop
thmProp (LocalAssumption p) = p
thmProp Theorem{ _thmProp = p } = p

thmStats :: Theorem -> SolverStats
thmStats (LocalAssumption _) = mempty
thmStats Theorem{ _thmStats = stats } = stats

thmEvidence :: Theorem -> Evidence
thmEvidence (LocalAssumption p) = LocalAssumptionEvidence p
thmEvidence Theorem{ _thmEvidence = e } = e

impossibleEvidence :: [Evidence] -> IO Evidence
impossibleEvidence _ = fail "impossibleEvidence: attempted to check an impossible proof!"

splitEvidence :: [Evidence] -> IO Evidence
splitEvidence [e1,e2] = pure (SplitEvidence e1 e2)
splitEvidence _ = fail "splitEvidence: expected two evidence values"

assumeEvidence :: Prop -> [Evidence] -> IO Evidence
assumeEvidence p [e] = pure (AssumeEvidence p e)
assumeEvidence _ _ = fail "assumeEvidence: expected one evidence value"

forallEvidence :: TypedTerm -> [Evidence] -> IO Evidence
forallEvidence tt [e] = pure (ForallEvidence tt e)
forallEvidence _ _ = fail "forallEvidence: expected one evidence value"

cutEvidence :: Theorem -> [Evidence] -> IO Evidence
cutEvidence thm [e] = pure (CutEvidence thm e)
cutEvidence _ _ = fail "cutEvidence: expected one evidence value"

proofByTerm :: SharedContext -> Term -> IO Theorem
proofByTerm sc prf =
  do ty <- scTypeOf sc prf
     p  <- termToProp sc ty
     return
       Theorem
       { _thmProp      = p
       , _thmStats     = mempty
       , _thmEvidence  = ProofTerm prf
       }

admitTheorem :: Prop -> Theorem
admitTheorem p =
  Theorem
  { _thmProp      = p
  , _thmStats     = solverStats "ADMITTED" (propSize p)
  , _thmEvidence  = Admitted p
  }

solverTheorem :: Prop -> SolverStats -> Theorem
solverTheorem p stats =
  Theorem
  { _thmProp      = p
  , _thmStats     = stats
  , _thmEvidence  = SolverEvidence stats p
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
  { _psGoals :: [ProofGoal]
  , _psConcl :: Prop
  , _psStats :: SolverStats
  , _psTimeout :: Maybe Integer
  , _psEvidence :: [Evidence] -> IO Evidence
  }

psTimeout :: ProofState -> Maybe Integer
psTimeout = _psTimeout

psGoals :: ProofState -> [ProofGoal]
psGoals = _psGoals

-- | Verify that the given evidence in fact supports
--   the given proposition.
checkEvidence :: SharedContext -> Evidence -> Prop -> IO ()
checkEvidence sc = check mempty
  where
    checkApply _hyps (Prop p) [] = return p
    checkApply hyps (Prop p) (e:es)
      | Just (_lnm, tp, body) <- asPi p
      , looseVars body == emptyBitSet
      = do check hyps e (Prop tp) -- TODO, check that tp is a prop
           checkApply hyps (Prop body) es
      | otherwise = fail $ unlines
           [ "Apply evidence mismatch: non-function or dependent function"
           , showTerm p
           ]

    checkTheorem :: Set Term -> Theorem -> IO ()
    checkTheorem hyps (LocalAssumption p) =
       unless (Set.member (unProp p) hyps) $ fail $ unlines
          [ "Attempt to reference a local hypothesis that is not in scope"
          , showTerm (unProp p)
          ]
    checkTheorem _hyps Theorem{} = return ()

    check :: Set Term -> Evidence -> Prop -> IO ()
    check hyps e p@(Prop ptm) = case e of
      ProofTerm tm ->
        do ty <- scTypeCheckError sc tm
           ok <- scConvertible sc False ptm ty
           unless ok $ fail $ unlines
               [ "Proof term does not prove the required proposition"
               , showTerm ptm
               , showTerm tm
               ]

      LocalAssumptionEvidence (Prop l) ->
        unless (Set.member l hyps) $ fail $ unlines
             [ "Illegal use of local hypothesis"
             , showTerm l
             ]

      SolverEvidence _stats (Prop p') ->
        do ok <- scConvertible sc False ptm p'
           unless ok $ fail $ unlines
               [ "Solver proof does not prove the required proposition"
               , showTerm ptm
               , showTerm p'
               ]

      Admitted (Prop p') ->
        do ok <- scConvertible sc False ptm p'
           unless ok $ fail $ unlines
               [ "Admitted proof does not match the required proposition"
               , showTerm ptm
               , showTerm p'
               ]

      QuickcheckEvidence _n (Prop p') ->
        do ok <- scConvertible sc False ptm p'
           unless ok $ fail $ unlines
               [ "Quickcheck evidence does not match the required proposition"
               , showTerm ptm
               , showTerm p'
               ]

      TrivialEvidence ->
        unless (propIsTrivial p) $ fail $ unlines
            [ "Proposition is not trivial"
            , showTerm ptm
            ]

      SplitEvidence e1 e2 ->
        splitProp sc p >>= \case
          Nothing -> fail $ unlines
                       [ "Split evidence does not apply to non-conjunction prop"
                       , showTerm ptm
                       ]
          Just (p1,p2) ->
            do check hyps e1 p1
               check hyps e2 p2

      ApplyEvidence thm es ->
        do checkTheorem hyps thm
           p' <- checkApply hyps (thmProp thm) es
           ok <- scConvertible sc False ptm p'
           unless ok $ fail $ unlines
               [ "Apply evidence does not match the required proposition"
               , showTerm ptm
               , showTerm p'
               ]

      CutEvidence thm e' ->
        do checkTheorem hyps thm
           p' <- scFun sc (unProp (thmProp thm)) ptm
           check hyps e' (Prop p')

      UnfoldEvidence vars e' ->
        do p' <- unfoldProp sc vars p
           check hyps e' p'

      RewriteEvidence ss e' ->
        do p' <- simplifyProp sc ss p
           check hyps e' p'

      EvalEvidence vars e' ->
        do p' <- evalProp sc vars p
           check hyps e' p'

      AssumeEvidence (Prop p') e' ->
        case asPi ptm of
          Nothing -> fail $ unlines ["Assume evidence expected function prop", showTerm ptm]
          Just (_lnm, ty, body) ->
            do ok <- scConvertible sc False ty p'
               unless ok $ fail $ unlines
                   [ "Assume evidence types do not match"
                   , showTerm ty
                   , showTerm p'
                   ]
               unless (looseVars body == emptyBitSet) $ fail $ unlines
                   [ "Assume evidence cannot be used on a dependent propsition"
                   , showTerm ptm
                   ]
               check (Set.insert p' hyps) e' (Prop body)

      ForallEvidence tt e' ->
        case asPi ptm of
          Nothing -> fail $ unlines ["Assume evidence expected function prop", showTerm ptm]
          Just (_lnm, ty, body) ->
            do ty' <- scTypeOf sc (ttTerm tt)
               ok <- scConvertible sc False ty ty'
               unless ok $ fail $ unlines
                 ["Forall evidence types do not match"
                 , showTerm (ttTerm tt)
                 , showTerm ty
                 ]
               body' <- instantiateVar sc 0 (ttTerm tt) body
               check hyps e' (Prop body')

rewriteEvidence :: Simpset -> [Evidence] -> IO Evidence
rewriteEvidence ss [e] = pure (RewriteEvidence ss e)
rewriteEvidence _ _ = fail "rewriteEvidence: incorrect arity"

unfoldEvidence :: Set VarIndex -> [Evidence] -> IO Evidence
unfoldEvidence vs [e] = pure (UnfoldEvidence vs e)
unfoldEvidence _ _ = fail "unfoldEvidence: incorrect arity"

evalEvidence :: Set VarIndex -> [Evidence] -> IO Evidence
evalEvidence vs [e] = pure (EvalEvidence vs e)
evalEvidence _ _ = fail "evalEvidence: incorrect arity"

passthroughEvidence :: [Evidence] -> IO Evidence
passthroughEvidence [e] = pure e
passthroughEvidence _   = fail "passthroughEvidence: incorrect arity"

leafEvidence :: Evidence -> [Evidence] -> IO Evidence
leafEvidence e [] = pure e
leafEvidence _ _  = fail "leafEvidence: incorrect arity"

setProofTimeout :: Integer -> ProofState -> ProofState
setProofTimeout to ps = ps { _psTimeout = Just to }

startProof :: ProofGoal -> ProofState
startProof g = ProofState [g] (goalProp g) mempty Nothing passthroughEvidence

finishProof :: SharedContext -> ProofState -> IO (SolverStats, Maybe Theorem)
finishProof sc (ProofState gs concl stats _ checkEv) =
  case gs of
    [] ->
      do e <- checkEv []
         checkEvidence sc e concl
         let thm = Theorem
                   { _thmProp = concl
                   , _thmStats = stats
                   , _thmEvidence = e
                   }
         pure (stats, Just thm)
    _ : _ ->
         pure (stats, Nothing)

type Tactic m a = ProofGoal -> m (a, SolverStats, [ProofGoal], [Evidence] -> IO Evidence)

withFirstGoal :: F.MonadFail m => Tactic m a -> StateT ProofState m a
withFirstGoal f =
  StateT $ \(ProofState goals concl stats timeout ev) ->
  case goals of
    [] -> fail "ProofScript failed: no subgoal"
    g : gs -> do
      (x, stats', gs', ev') <- f g
      let ev'' es = do let (es1, es2) = splitAt (length gs') es
                       e <- ev' es1
                       ev (e:es2)
      return (x, ProofState (gs' <> gs) concl (stats <> stats') timeout ev'')

{-
propToSATQuery :: SharedContext -> Prop -> IO SATQuery
propToSATQuery sc (Prop goal) =
  do let (args, t1) = asPiList goal
     case asEqTrue t1 of
       Nothing -> fail $ "propToSATQuery: expected EqTrue, actual " ++ show t1
       Just t2 ->
-}


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
goalApply sc thm goal = applyFirst (asPiLists (unProp rule))
  where
    rule = thmProp thm

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


tacticIntro :: (F.MonadFail m, MonadIO m) => SharedContext -> String -> Tactic m TypedTerm
tacticIntro sc nm goal =
  liftIO (goalIntro sc nm goal) >>= \case
    Nothing -> fail "intro tactic failed: no a pi type"
    Just (tt, goal') -> return (tt, mempty, [goal'], forallEvidence tt)

tacticAssume :: (F.MonadFail m, MonadIO m) => SharedContext -> Tactic m Theorem
tacticAssume _sc goal =
  case asPi (unProp (goalProp goal)) of
    Just (_nm, tp, body)
      | looseVars body == emptyBitSet ->
          do let goal' = goal{ goalProp = Prop body }
             let p     = Prop tp
             let thm'  = LocalAssumption p
             return (thm', mempty, [goal'], assumeEvidence p)

    _ -> fail "assume tactic failed: not a function, or a dependent function"

tacticCut :: (F.MonadFail m, MonadIO m) => SharedContext -> Theorem -> Tactic m ()
tacticCut sc thm goal =
  do body' <- liftIO (scFun sc (unProp (thmProp thm)) (unProp (goalProp goal)))
     let goal' = goal{ goalProp = Prop body' }
     return ((), mempty, [goal'], cutEvidence thm)

tacticApply :: (F.MonadFail m, MonadIO m) => SharedContext -> Theorem -> Tactic m ()
tacticApply sc thm goal =
  liftIO (goalApply sc thm goal) >>= \case
    Nothing -> fail "apply tactic failed: no match"
    Just newgoals ->
      return ((), mempty, newgoals, pure . ApplyEvidence thm)

tacticSplit :: (F.MonadFail m, MonadIO m) => SharedContext -> Tactic m ()
tacticSplit sc (ProofGoal num ty name prop) =
  liftIO (splitProp sc prop) >>= \case
    Nothing -> fail "split tactic failed: goal not a conjunction"
    Just (p1,p2) ->
      do let g1 = ProofGoal num (ty ++ ".left")  name p1
         let g2 = ProofGoal num (ty ++ ".right") name p2
         return ((), mempty, [g1,g2], splitEvidence)

tacticTrivial :: (F.MonadFail m, MonadIO m) => SharedContext -> Tactic m ()
tacticTrivial _sc goal =
  if (propIsTrivial (goalProp goal)) then
    return ((), mempty, [], leafEvidence TrivialEvidence)
  else
    fail "trivial tactic: not a trivial goal"

tacticId :: Monad m => Tactic m ()
tacticId goal = return ((), mempty, [goal], passthroughEvidence)
