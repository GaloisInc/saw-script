{- |
Module      : SAWScript.Proof
Description : Representations of SAW-Script proof states.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}

{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

module SAWScript.Proof
  ( Prop
  , splitProp
  , unfoldProp
  , simplifyProp
  , hoistIfsInGoal
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
  , propToSATQuery

  , TheoremDB
  , newTheoremDB
  , reachableTheorems

  , Theorem
  , thmProp
  , thmStats
  , thmEvidence
  , thmLocation
  , thmProgramLoc
  , thmReason
  , thmNonce
  , thmDepends
  , thmElapsedTime
  , thmSummary
  , TheoremNonce
  , TheoremSummary(..)

  , admitTheorem
  , solverTheorem
  , proofByTerm
  , constructTheorem
  , validateTheorem

  , Evidence(..)
  , checkEvidence

  , Tactic
  , withFirstGoal
  , tacticIntro
  , tacticCut
  , tacticAssume
  , tacticApply
  , tacticSplit
  , tacticTrivial
  , tacticId
  , tacticChange
  , tacticSolve

  , Quantification(..)
  , predicateToProp
  , boolToProp

  , ProofState
  , psTimeout
  , psGoals
  , psStats
  , setProofTimeout
  , ProofGoal(..)
  , startProof
  , finishProof

  , CEX
  , ProofResult(..)
  , SolveResult(..)

  , predicateToSATQuery
  ) where

import qualified Control.Monad.Fail as F
import           Control.Monad.Except
import           Data.IORef
import           Data.Maybe (fromMaybe)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Time.Clock

import Data.Parameterized.Nonce

import Verifier.SAW.Prelude (scApplyPrelude_False)
import Verifier.SAW.Recognizer
import Verifier.SAW.Rewriter
import Verifier.SAW.SATQuery
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST
import Verifier.SAW.TypedTerm
import Verifier.SAW.FiniteValue (FirstOrderValue)
import Verifier.SAW.Term.Pretty (SawDoc)
import Verifier.SAW.SCTypeCheck (scTypeCheckError)

import Verifier.SAW.Simulator.Concrete (evalSharedTerm)
import Verifier.SAW.Simulator.Value (asFirstOrderTypeValue, Value(..), TValue(..))

import What4.ProgramLoc (ProgramLoc)

import SAWScript.Position
import SAWScript.Prover.SolverStats
import SAWScript.Crucible.Common as Common
import qualified Verifier.SAW.Simulator.What4 as W4Sim
import qualified Verifier.SAW.Simulator.What4.ReturnTrip as W4Sim
import SAWScript.Panic(panic)

-- | A proposition is a saw-core type of type `Prop`.
-- In particular, this includes any pi type whose result
-- type is a proposition. The argument of a pi type represents
-- a universally quantified variable.
newtype Prop = Prop Term
  -- INVARIANT: The type of the given term is `Prop`

unProp :: Prop -> Term
unProp (Prop tm) = tm

-- | Turn a saw-core term into a proposition under the type-as-propositions
--   regime.  The given term must be a type, which means that its own type
--   is a sort.
termToProp :: SharedContext -> Term -> IO Prop
termToProp sc tm =
   do mmap <- scGetModuleMap sc
      ty <- scTypeOf sc tm
      case evalSharedTerm mmap mempty mempty ty of
        TValue (VSort s) | s == propSort -> return (Prop tm)
        _ -> fail $ unlines [ "termToProp: Term is not a proposition", showTerm tm, showTerm ty ]


-- | Turn a boolean-valued saw-core term into a proposition by asserting
--   that it is equal to the true boolean value.  Generalize the proposition
--   by universally quantifing over the variables given in the list.
boolToProp :: SharedContext -> [ExtCns Term] -> Term -> IO Prop
boolToProp sc vars tm =
  do mmap <- scGetModuleMap sc
     ty <- scTypeOf sc tm
     case evalSharedTerm mmap mempty mempty ty of
       TValue VBoolType ->
         do p0 <- scEqTrue sc tm
            Prop <$> scGeneralizeExts sc vars p0
       _ -> fail $ unlines [ "boolToProp: Term is not a boolean", showTerm tm, showTerm ty ]

-- | Return the saw-core term that represents this proposition.
propToTerm :: SharedContext -> Prop -> IO Term
propToTerm _sc (Prop tm) = pure tm

-- | Attempt to interpret a proposition as a rewrite rule.
propToRewriteRule :: SharedContext -> Prop -> Maybe a -> IO (Maybe (RewriteRule a))
propToRewriteRule _sc (Prop tm) ann =
  case ruleOfProp tm ann of
    Nothing -> pure Nothing
    Just r  -> pure (Just r)

-- | Attempt to split a conjunctive proposition into two propositions,
--   such that a proof of both return propositions is equivalent to
--   a proof of the original.
splitProp :: SharedContext -> Prop -> IO (Maybe (Prop, Prop))
splitProp sc (Prop p) =
  do let (vars, body) = asPiList p
     case (isGlobalDef "Prelude.and" <@> return <@> return) =<< asEqTrue body of
       Nothing -> pure Nothing
       Just (_ :*: p1 :*: p2) ->
         do t1 <- scPiList sc vars =<< scEqTrue sc p1
            t2 <- scPiList sc vars =<< scEqTrue sc p2
            return (Just (Prop t1,Prop t2))

-- | Unfold all the constants appearing in the proposition
--   whose VarIndex is found in the given set.
unfoldProp :: SharedContext -> Set VarIndex -> Prop -> IO Prop
unfoldProp sc unints (Prop tm) =
  do tm' <- scUnfoldConstantSet sc True unints tm
     return (Prop tm')

-- | Rewrite the proposition using the provided Simpset
simplifyProp :: Ord a => SharedContext -> Simpset a -> Prop -> IO (Set a, Prop)
simplifyProp sc ss (Prop tm) =
  do (a, tm') <- rewriteSharedTerm sc ss tm
     return (a, Prop tm')

hoistIfsInGoal :: SharedContext -> Prop -> IO Prop
hoistIfsInGoal sc (Prop p) = do
  let (args, body) = asPiList p
  body' <-
    case asEqTrue body of
      Just t -> pure t
      Nothing -> fail "hoistIfsInGoal: expected EqTrue"
  ecs <- traverse (\(nm, ty) -> scFreshEC sc nm ty) args
  vars <- traverse (scExtCns sc) ecs
  t0 <- instantiateVarList sc 0 (reverse vars) body'
  t1 <- hoistIfs sc t0
  t2 <- scEqTrue sc t1
  t3 <- scGeneralizeExts sc ecs t2
  return (Prop t3)

-- | Evaluate the given proposition by round-tripping
--   through the What4 formula representation.  This will
--   perform a variety of simplifications and rewrites.
evalProp :: SharedContext -> Set VarIndex -> Prop -> IO Prop
evalProp sc unints (Prop p) =
  do let (args, body) = asPiList p

     body' <-
       case asEqTrue body of
         Just t -> pure t
         Nothing -> fail "goal_eval: expected EqTrue"

     ecs <- traverse (\(nm, ty) -> scFreshEC sc nm ty) args
     vars <- traverse (scExtCns sc) ecs
     t0 <- instantiateVarList sc 0 (reverse vars) body'

     sym <- Common.newSAWCoreExprBuilder sc
     st <- Common.sawCoreState sym
     (_names, (_mlabels, p')) <- W4Sim.w4Eval sym st sc mempty unints t0
     t1 <- W4Sim.toSC sym st p'

     t2 <- scEqTrue sc t1
     -- turn the free variables we generated back into pi-bound variables
     t3 <- scGeneralizeExts sc ecs t2
     return (Prop t3)

-- | Perform beta normalization on the given proposition.
betaReduceProp :: SharedContext -> Prop -> IO Prop
betaReduceProp sc (Prop tm) =
  do tm' <- betaNormalize sc tm
     return (Prop tm')

-- | Return the contant false proposition.
falseProp :: SharedContext -> IO Prop
falseProp sc = Prop <$> (scEqTrue sc =<< scApplyPrelude_False sc)

-- | Compute the shared-term size of the proposition.
propSize :: Prop -> Integer
propSize (Prop tm) = scSharedSize tm

-- | Test if the given proposition is trivially true.  This holds
--   just when the proposition is a (possibly empty) sequence of
--   Pi-types followed by an @EqTrue@ proposition for a
--   concretely-true boolean value.
propIsTrivial :: Prop -> Bool
propIsTrivial (Prop tm) = checkTrue tm
  where
    checkTrue :: Term -> Bool
    checkTrue (asPiList -> (_, asEqTrue -> Just (asBool -> Just True))) = True
    checkTrue _ = False

-- | Pretty print the given proposition as a string.
prettyProp :: PPOpts -> Prop -> String
prettyProp opts (Prop tm) = scPrettyTerm opts tm

-- | Pretty print the given proposition as a @SawDoc@.
ppProp :: PPOpts -> Prop -> SawDoc
ppProp opts (Prop tm) = ppTerm opts tm

type TheoremNonce = Nonce GlobalNonceGenerator Theorem

-- | A theorem is a proposition which has been wrapped in a
--   constructor indicating that it has already been proved,
--   and contains @Evidence@ for its truth.
data Theorem =
  Theorem
  { _thmProp :: Prop
  , _thmStats :: SolverStats
  , _thmEvidence :: Evidence
  , _thmLocation :: Pos
  , _thmProgramLoc :: Maybe ProgramLoc
  , _thmReason   :: Text
  , _thmNonce    :: TheoremNonce
  , _thmDepends  :: Set TheoremNonce
  , _thmElapsedTime :: NominalDiffTime
  , _thmSummary :: TheoremSummary
  } -- INVARIANT: the provided evidence is valid for the included proposition

  | LocalAssumption Prop Pos TheoremNonce
      -- This constructor is used to construct "hypothetical" theorems that
      -- are intended to be used in local scopes when proving implications.

data TheoremDB =
  TheoremDB
  -- TODO, maybe this should be a summary or something simpler?
  { theoremMap :: IORef (Map.Map TheoremNonce Theorem)
  }

newTheoremDB :: IO TheoremDB
newTheoremDB = TheoremDB <$> newIORef mempty

recordTheorem :: TheoremDB -> Theorem -> IO Theorem
recordTheorem _ (LocalAssumption _ pos _) =
  panic "recordTheorem" ["Tried to record a local assumption as a top-level", show pos]
recordTheorem db thm@Theorem{ _thmNonce = n } =
  do modifyIORef (theoremMap db) (Map.insert n thm)
     return thm

reachableTheorems :: TheoremDB -> Set TheoremNonce -> IO (Map TheoremNonce Theorem)
reachableTheorems db roots =
  do m <- readIORef (theoremMap db)
     pure $! Set.foldl' (loop m) mempty roots

 where
   loop m visited curr
     | Just _ <- Map.lookup curr visited = visited

     | Just thm <- Map.lookup curr m =
         Set.foldl' (loop m)
            (Map.insert curr thm visited)
            (thmDepends thm)

     | otherwise =
         panic "reachableTheorems" ["Could not find theorem with identifier", show (indexValue curr)]

-- | Check that the purported theorem is valid.
--
--   This checks that the given theorem object does not correspond
--   to a local assumption that has been leaked from its scope,
--   and validates that the included evidence actually supports
--   the proposition.  Note, however, this validation procedure
--   does not totally guarantee the theorem is true, as it does
--   not rerun any solver-provided proofs, and it accepts admitted
--   propositions and quickchecked propositions as valid.
validateTheorem :: SharedContext -> TheoremDB -> Theorem -> IO ()

validateTheorem _ _ (LocalAssumption p loc _n) =
   fail $ unlines
     [ "Illegal use of unbound local hypothesis generated at " ++ show loc
     , showTerm (unProp p)
     ]

validateTheorem sc db Theorem{ _thmProp = p, _thmEvidence = e, _thmDepends = thmDep } =
   do (deps,_) <- checkEvidence sc db e p
      unless (Set.isSubsetOf deps thmDep)
             (fail $ unlines ["Theorem failed to declare its depencences correctly"
                             , show deps, show thmDep ])

data TheoremSummary
  = AdmittedTheorem Text
  | TestedTheorem Integer
  | ProvedTheorem SolverStats

instance Monoid TheoremSummary where
  mempty = ProvedTheorem mempty

instance Semigroup TheoremSummary where
  AdmittedTheorem msg <> _ = AdmittedTheorem msg
  _ <> AdmittedTheorem msg = AdmittedTheorem msg
  TestedTheorem x <> TestedTheorem y = TestedTheorem (min x y)
  TestedTheorem x <> _ = TestedTheorem x
  _ <> TestedTheorem y = TestedTheorem y
  ProvedTheorem s1 <> ProvedTheorem s2 = ProvedTheorem (s1<>s2)


-- | This datatype records evidence for the truth of a proposition.
data Evidence
  = -- | The given term provides a direct programs-as-proofs witness
    --   for the truth of its type (qua proposition).
    ProofTerm Term

    -- | This type of evidence refers to a local assumption that
    --   must have been introduced by a surrounding @AssumeEvidence@
    --   constructor.
  | LocalAssumptionEvidence Prop TheoremNonce

    -- | This type of evidence is produced when the given proposition
    --   has been dispatched to a solver which has indicated that it
    --   was able to prove the proposition.  The included @SolverStats@
    --   give some details about the solver run.
  | SolverEvidence SolverStats Prop

    -- | This type of evidence is produced when the given proposition
    --   has been randomly tested against input vectors in the style
    --   of quickcheck.  The included number is the number of successfully
    --   passed test vectors.
  | QuickcheckEvidence Integer Prop

    -- | This type of evidence is produced when the given proposition
    --   has been explicitly assumed without other evidence at the
    --   user's direction.
  | Admitted Text Pos Prop

    -- | This type of evidence is produced when a given proposition is trivially
    --   true.
  | TrivialEvidence

    -- | This type of evidence is produced when a proposition can be deconstructed
    --   along a conjunction into two subgoals, each of which is supported by
    --   the included evidence.
  | SplitEvidence Evidence Evidence

    -- | This type of evidence is produced when a previously-proved theorem is
    --   applied via backward reasoning to prove a goal.  Some of the hypotheses
    --   of the theorem may be discharged via the included list of evidence, and
    --   then the proposition must match the conclusion of the theorem.
  | ApplyEvidence Theorem [Evidence]

    -- | This type of evidence is used to prove an implication.  The included
    --   proposition must match the hypothesis of the goal, and the included
    --   evidence must match the conclusion of the goal.  The proposition is
    --   allowed to appear inside the evidence as a local assumption.
  | AssumeEvidence TheoremNonce Prop Evidence

    -- | This type of evidence is used to prove a universally-quantified statement.
  | ForallEvidence (ExtCns Term) Evidence

    -- | This type of evidence is used to weaken a goal by adding a hypothesis,
    --   where the hypothesis is proved by the given theorem.
  | CutEvidence Theorem Evidence

    -- | This type of evidence is used to modify a goal to prove via rewriting.
    --   The goal to prove is rewritten by the given simpset; then the provided
    --   evidence is used to check the modified goal.
  | RewriteEvidence (Simpset TheoremNonce) Evidence

    -- | This type of evidence is used to modify a goal to prove via unfolding
    --   constant definitions.  The goal to prove is modified by unfolding
    --   constants identified via the given set of @VarIndex@; then the provided
    --   evidence is used to check the modified goal.
  | UnfoldEvidence (Set VarIndex) Evidence

    -- | This type of evidence is used to modify a goal to prove via evaluation
    --   into the the What4 formula representation. During evaluation, the
    --   constants identified by the given set of @VarIndex@ are held
    --   uninterpreted (i.e., will not be unfolded).  Then, the provided
    --   evidence is use to check the modified goal.
  | EvalEvidence (Set VarIndex) Evidence

    -- | This type of evidence is used to modify a goal to prove by applying
    -- 'hoistIfsInGoal'.
  | HoistIfsEvidence Evidence

-- | The the proposition proved by a given theorem.
thmProp :: Theorem -> Prop
thmProp (LocalAssumption p _loc _n) = p
thmProp Theorem{ _thmProp = p } = p

-- | Retrieve any solver stats from the proved theorem.
thmStats :: Theorem -> SolverStats
thmStats (LocalAssumption _ _ _) = mempty
thmStats Theorem{ _thmStats = stats } = stats

-- | Retrive the evidence associated with this theorem.
thmEvidence :: Theorem -> Evidence
thmEvidence (LocalAssumption p _ n) = LocalAssumptionEvidence p n
thmEvidence Theorem{ _thmEvidence = e } = e

-- | The SAW source location that generated this theorem
thmLocation :: Theorem -> Pos
thmLocation (LocalAssumption _p loc _) = loc
thmLocation Theorem{ _thmLocation = loc } = loc

-- | The program location (if any) of the program under
--   verification giving rise to this theorem
thmProgramLoc :: Theorem -> Maybe ProgramLoc
thmProgramLoc (LocalAssumption{}) = Nothing
thmProgramLoc Theorem{ _thmProgramLoc = ploc } = ploc

-- | Describes the reason this theorem was generated
thmReason :: Theorem -> Text
thmReason (LocalAssumption _ _ _) = "local assumption"
thmReason Theorem{ _thmReason = r } = r

-- | Returns a unique identifier for this theorem
thmNonce :: Theorem -> TheoremNonce
thmNonce (LocalAssumption _ _ n) = n
thmNonce Theorem{ _thmNonce = n } = n

-- | Returns the set of theorem identifiers that this theorem depends on
thmDepends :: Theorem -> Set TheoremNonce
thmDepends LocalAssumption{} = mempty
thmDepends Theorem { _thmDepends = s } = s

-- | Returns the amount of time elapsed during the proof of this theorem
thmElapsedTime :: Theorem -> NominalDiffTime
thmElapsedTime LocalAssumption{} = 0
thmElapsedTime Theorem{ _thmElapsedTime = tm } = tm

thmSummary :: Theorem -> TheoremSummary
thmSummary LocalAssumption{} = mempty
thmSummary Theorem { _thmSummary = sy } = sy

splitEvidence :: [Evidence] -> IO Evidence
splitEvidence [e1,e2] = pure (SplitEvidence e1 e2)
splitEvidence _ = fail "splitEvidence: expected two evidence values"

assumeEvidence :: TheoremNonce -> Prop -> [Evidence] -> IO Evidence
assumeEvidence n p [e] = pure (AssumeEvidence n p e)
assumeEvidence _ _ _ = fail "assumeEvidence: expected one evidence value"

forallEvidence :: ExtCns Term -> [Evidence] -> IO Evidence
forallEvidence x [e] = pure (ForallEvidence x e)
forallEvidence _ _ = fail "forallEvidence: expected one evidence value"

cutEvidence :: Theorem -> [Evidence] -> IO Evidence
cutEvidence thm [e] = pure (CutEvidence thm e)
cutEvidence _ _ = fail "cutEvidence: expected one evidence value"

-- | Construct a theorem directly via a proof term.
proofByTerm :: SharedContext -> TheoremDB -> Term -> Pos -> Text -> IO Theorem
proofByTerm sc db prf loc rsn =
  do ty <- scTypeOf sc prf
     p  <- termToProp sc ty
     n  <- freshNonce globalNonceGenerator
     recordTheorem db
       Theorem
       { _thmProp      = p
       , _thmStats     = mempty
       , _thmEvidence  = ProofTerm prf
       , _thmLocation  = loc
       , _thmProgramLoc = Nothing
       , _thmReason    = rsn
       , _thmNonce     = n
       , _thmDepends   = mempty
       , _thmElapsedTime = 0
       , _thmSummary = ProvedTheorem mempty
       }

-- | Construct a theorem directly from a proposition and evidence
--   for that proposition.  The evidence will be validated to
--   check that it supports the given proposition; if not, an
--   error will be raised.
constructTheorem ::
  SharedContext ->
  TheoremDB ->
  Prop ->
  Evidence ->
  Pos ->
  Maybe ProgramLoc ->
  Text ->
  NominalDiffTime ->
  IO Theorem
constructTheorem sc db p e loc ploc rsn elapsed =
  do (deps,sy) <- checkEvidence sc db e p
     n  <- freshNonce globalNonceGenerator
     recordTheorem db
       Theorem
       { _thmProp  = p
       , _thmStats = mempty
       , _thmEvidence = e
       , _thmLocation = loc
       , _thmProgramLoc = ploc
       , _thmReason   = rsn
       , _thmNonce    = n
       , _thmDepends  = deps
       , _thmElapsedTime = elapsed
       , _thmSummary  = sy
       }

-- | Admit the given theorem without evidence.
--   The provided message allows the user to
--   explain why this proposition is being admitted.
admitTheorem ::
  TheoremDB ->
  Text ->
  Prop ->
  Pos ->
  Text ->
  IO Theorem
admitTheorem db msg p loc rsn =
  do n  <- freshNonce globalNonceGenerator
     recordTheorem db
       Theorem
       { _thmProp        = p
       , _thmStats       = solverStats "ADMITTED" (propSize p)
       , _thmEvidence    = Admitted msg loc p
       , _thmLocation    = loc
       , _thmProgramLoc  = Nothing
       , _thmReason      = rsn
       , _thmNonce       = n
       , _thmDepends     = mempty
       , _thmElapsedTime = 0
       , _thmSummary     = AdmittedTheorem msg
       }

-- | Construct a theorem that an external solver has proved.
solverTheorem ::
  TheoremDB ->
  Prop ->
  SolverStats ->
  Pos ->
  Text ->
  NominalDiffTime ->
  IO Theorem
solverTheorem db p stats loc rsn elapsed =
  do n  <- freshNonce globalNonceGenerator
     recordTheorem db
       Theorem
       { _thmProp      = p
       , _thmStats     = stats
       , _thmEvidence  = SolverEvidence stats p
       , _thmLocation  = loc
       , _thmReason    = rsn
       , _thmProgramLoc = Nothing
       , _thmNonce     = n
       , _thmDepends   = mempty
       , _thmElapsedTime = elapsed
       , _thmSummary = ProvedTheorem stats
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


-- | Convert a term with a function type of any arity into a pi type.
-- Negate the term if the result type is @Bool@ and the quantification
-- is 'Existential'.
predicateToProp :: SharedContext -> Quantification -> Term -> IO Prop
predicateToProp sc quant = loop []
  where
  loop env t =
    case asLambda t of
      Just (x, ty, body) ->
        do Prop body' <- loop (ty : env) body
           Prop <$> scPi sc x ty body'
      Nothing ->
        do (argTs, resT) <- asPiList <$> scTypeOf' sc env t
           let toPi [] t0 =
                 case asBoolType resT of
                   Nothing -> fail $ unlines ["predicateToProp : Expected boolean result type but got", showTerm resT]
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


-- | A ProofState represents a sequent, where the collection of goals
-- implies the conclusion.
data ProofState =
  ProofState
  { _psGoals :: [ProofGoal]
  , _psConcl :: (Prop,Pos,Maybe ProgramLoc,Text)
  , _psStats :: SolverStats
  , _psTimeout :: Maybe Integer
  , _psEvidence :: [Evidence] -> IO Evidence
  , _psStartTime :: UTCTime
  }

psTimeout :: ProofState -> Maybe Integer
psTimeout = _psTimeout

psGoals :: ProofState -> [ProofGoal]
psGoals = _psGoals

psStats :: ProofState -> SolverStats
psStats = _psStats

-- | Verify that the given evidence in fact supports the given proposition.
--   Returns the identifers of all the theorems depened on while checking evidence.
checkEvidence :: SharedContext -> TheoremDB -> Evidence -> Prop -> IO (Set TheoremNonce, TheoremSummary)
checkEvidence sc db = \e p -> do hyps <- Map.keysSet <$> readIORef (theoremMap db)
                                 check hyps e p

  where
    checkApply _hyps (Prop p) [] = return (mempty, mempty, p)
    checkApply hyps (Prop p) (e:es)
      | Just (_lnm, tp, body) <- asPi p
      , looseVars body == emptyBitSet
      = do (d1,sy1) <- check hyps e =<< termToProp sc tp
           (d2,sy2,p') <- checkApply hyps (Prop body) es
           return (Set.union d1 d2, sy1 <> sy2, p')
      | otherwise = fail $ unlines
           [ "Apply evidence mismatch: non-function or dependent function"
           , showTerm p
           ]

    checkTheorem :: Set TheoremNonce -> Theorem -> IO ()
    checkTheorem hyps (LocalAssumption p loc n) =
       unless (Set.member n hyps) $ fail $ unlines
          [ "Attempt to reference a local hypothesis that is not in scope"
          , "Generated at " ++ show loc
          , showTerm (unProp p)
          ]
    checkTheorem _hyps Theorem{} = return ()

    check ::
      Set TheoremNonce ->
      Evidence ->
      Prop ->
      IO (Set TheoremNonce, TheoremSummary)
    check hyps e p@(Prop ptm) = case e of
      ProofTerm tm ->
        do ty <- scTypeCheckError sc tm
           ok <- scConvertible sc False ptm ty
           unless ok $ fail $ unlines
               [ "Proof term does not prove the required proposition"
               , showTerm ptm
               , showTerm tm
               ]
           return (mempty, ProvedTheorem mempty)

      LocalAssumptionEvidence (Prop l) n ->
        do unless (Set.member n hyps) $ fail $ unlines
             [ "Illegal use of local hypothesis"
             , showTerm l
             ]
           return (Set.singleton n, ProvedTheorem mempty)

      SolverEvidence stats (Prop p') ->
        do ok <- scConvertible sc False ptm p'
           unless ok $ fail $ unlines
               [ "Solver proof does not prove the required proposition"
               , showTerm ptm
               , showTerm p'
               ]
           return (mempty, ProvedTheorem stats)

      Admitted msg pos (Prop p') ->
        do ok <- scConvertible sc False ptm p'
           unless ok $ fail $ unlines
               [ "Admitted proof does not match the required proposition " ++ show pos
               , Text.unpack msg
               , showTerm ptm
               , showTerm p'
               ]
           return (mempty, AdmittedTheorem msg)

      QuickcheckEvidence n (Prop p') ->
        do ok <- scConvertible sc False ptm p'
           unless ok $ fail $ unlines
               [ "Quickcheck evidence does not match the required proposition"
               , showTerm ptm
               , showTerm p'
               ]
           return (mempty, TestedTheorem n)

      TrivialEvidence ->
        do unless (propIsTrivial p) $ fail $ unlines
             [ "Proposition is not trivial"
             , showTerm ptm
             ]
           return mempty

      SplitEvidence e1 e2 ->
        splitProp sc p >>= \case
          Nothing -> fail $ unlines
                       [ "Split evidence does not apply to non-conjunction prop"
                       , showTerm ptm
                       ]
          Just (p1,p2) ->
            do d1 <- check hyps e1 p1
               d2 <- check hyps e2 p2
               return (d1 <> d2)

      ApplyEvidence thm es ->
        do checkTheorem hyps thm
           (d,sy,p') <- checkApply hyps (thmProp thm) es
           ok <- scConvertible sc False ptm p'
           unless ok $ fail $ unlines
               [ "Apply evidence does not match the required proposition"
               , showTerm ptm
               , showTerm p'
               ]
           return (Set.insert (thmNonce thm) d, sy)

      CutEvidence thm e' ->
        do checkTheorem hyps thm
           p' <- scFun sc (unProp (thmProp thm)) ptm
           (d,sy) <- check hyps e' (Prop p')
           return (Set.insert (thmNonce thm) d, sy)

      UnfoldEvidence vars e' ->
        do p' <- unfoldProp sc vars p
           check hyps e' p'

      RewriteEvidence ss e' ->
        do (d1,p') <- simplifyProp sc ss p
           unless (Set.isSubsetOf d1 hyps) $ fail $ unlines
             [ "Rewrite step used theorem not in hypothesis database"
             , show (Set.difference d1 hyps)
             ]
           (d2,sy) <- check hyps e' p'
           return (Set.union d1 d2, sy)

      HoistIfsEvidence e' ->
        do p' <- hoistIfsInGoal sc p
           check hyps e' p'

      EvalEvidence vars e' ->
        do p' <- evalProp sc vars p
           check hyps e' p'

      AssumeEvidence n (Prop p') e' ->
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
                   [ "Assume evidence cannot be used on a dependent proposition"
                   , showTerm ptm
                   ]
               (d,sy) <- check (Set.insert n hyps) e' (Prop body)
               return (Set.delete n d, sy)

      ForallEvidence x e' ->
        case asPi ptm of
          Nothing -> fail $ unlines ["Assume evidence expected function prop", showTerm ptm]
          Just (_lnm, ty, body) ->
            do let ty' = ecType x
               ok <- scConvertible sc False ty ty'
               unless ok $ fail $ unlines
                 ["Forall evidence types do not match"
                 , showTerm ty'
                 , showTerm ty
                 ]
               x' <- scExtCns sc x
               body' <- instantiateVar sc 0 x' body
               check hyps e' (Prop body')

passthroughEvidence :: [Evidence] -> IO Evidence
passthroughEvidence [e] = pure e
passthroughEvidence _   = fail "passthroughEvidence: incorrect arity"

updateEvidence :: (Evidence -> Evidence) -> [Evidence] -> IO Evidence
updateEvidence f [e] = pure (f e)
updateEvidence _ _ = fail "updateEvidence: incorrect arity"

leafEvidence :: Evidence -> [Evidence] -> IO Evidence
leafEvidence e [] = pure e
leafEvidence _ _  = fail "leafEvidence: incorrect arity"

setProofTimeout :: Integer -> ProofState -> ProofState
setProofTimeout to ps = ps { _psTimeout = Just to }

-- | Initialize a proof state with a single goal to prove.
startProof :: ProofGoal -> Pos -> Maybe ProgramLoc -> Text -> IO ProofState
startProof g pos ploc rsn =
  do start <- getCurrentTime
     pure (ProofState [g] (goalProp g,pos,ploc,rsn) mempty Nothing passthroughEvidence start)

-- | Attempt to complete a proof by checking that all subgoals have been discharged,
--   and validate the computed evidence to ensure that it supports the original
--   proposition.  If successful, return the completed @Theorem@ and a summary
--   of solver resources used in the proof.
finishProof :: SharedContext -> TheoremDB -> ProofState -> IO ProofResult
finishProof sc db ps@(ProofState gs (concl,loc,ploc,rsn) stats _ checkEv start) =
  case gs of
    [] ->
      do e <- checkEv []
         (deps,sy) <- checkEvidence sc db e concl
         n <- freshNonce globalNonceGenerator
         end <- getCurrentTime
         thm <- recordTheorem db
                   Theorem
                   { _thmProp = concl
                   , _thmStats = stats
                   , _thmEvidence = e
                   , _thmLocation = loc
                   , _thmProgramLoc = ploc
                   , _thmReason = rsn
                   , _thmNonce = n
                   , _thmDepends = deps
                   , _thmElapsedTime = diffUTCTime end start
                   , _thmSummary = sy
                   }
         pure (ValidProof stats thm)
    _ : _ ->
         pure (UnfinishedProof ps)

-- | A type describing counterexamples.
type CEX = [(ExtCns Term, FirstOrderValue)]

-- | The results that can occur after a proof attempt.
data ProofResult
  = -- | The proof was completed and results in a theorem
    ValidProof SolverStats Theorem
    -- | The proof failed, and we found a counterexample to
    --   one of the proof's subgoals.
  | InvalidProof SolverStats CEX ProofState
    -- | The proof was not completed, but we did not find
    --   a counterexample.
  | UnfinishedProof ProofState

-- | A @Tactic@ is a computation that examines, simplifies
--   and/or solves a proof goal.  Given a goal, it does some
--   work and returns 0 or more subgoals which, if they are all proved,
--   imply the original goal.  Moreover, it returns a way to compute
--   evidence for the original goal when given evidence for the generated
--   subgoal.  An important special case is a tactic that returns 0 subgoals,
--   and therefore completely solves the goal.
newtype Tactic m a =
  Tactic (ProofGoal -> ExceptT (SolverStats, CEX) m (a, SolverStats, [ProofGoal], [Evidence] -> IO Evidence))

-- | Choose the first subgoal in the current proof state and apply the given
--   proof tactic.
withFirstGoal :: F.MonadFail m => Tactic m a -> ProofState -> m (Either (SolverStats, CEX) (a, ProofState))
withFirstGoal (Tactic f) (ProofState goals concl stats timeout evidenceCont start) =
     case goals of
       [] -> fail "ProofScript failed: no subgoal"
       g : gs -> runExceptT (f g) >>= \case
         Left cex -> return (Left cex)
         Right (x, stats', gs', buildTacticEvidence) ->
           do let evidenceCont' es =
                      do let (es1, es2) = splitAt (length gs') es
                         e <- buildTacticEvidence es1
                         evidenceCont (e:es2)
              return (Right (x, ProofState (gs' <> gs) concl (stats <> stats') timeout evidenceCont' start))

predicateToSATQuery :: SharedContext -> Set VarIndex -> Term -> IO SATQuery
predicateToSATQuery sc unintSet tm0 =
    do mmap <- scGetModuleMap sc
       (initVars, abstractVars) <- filterFirstOrderVars mmap mempty mempty (getAllExts tm0)
       (finalVars, tm') <- processTerm mmap initVars tm0
       return SATQuery
              { satVariables = finalVars
              , satUninterp  = Set.union unintSet abstractVars
              , satAsserts   = [tm']
              }
  where
    evalFOT mmap t =
      asFirstOrderTypeValue (evalSharedTerm mmap mempty mempty t)

    filterFirstOrderVars _ fovars absvars [] = pure (fovars, absvars)
    filterFirstOrderVars mmap fovars absvars (e:es) =
      case evalFOT mmap (ecType e) of
        Nothing  -> filterFirstOrderVars mmap fovars (Set.insert (ecVarIndex e) absvars) es
        Just fot -> filterFirstOrderVars mmap (Map.insert e fot fovars) absvars es

    processTerm mmap vars tm =
      case asLambda tm of
        Just (lnm,tp,body) ->
          case evalFOT mmap tp of
            Nothing -> fail ("predicateToSATQuery: expected first order type: " ++ showTerm tp)
            Just fot ->
              do ec  <- scFreshEC sc lnm tp
                 etm <- scExtCns sc ec
                 body' <- instantiateVar sc 0 etm body
                 processTerm mmap (Map.insert ec fot vars) body'

          -- TODO: check that the type is a boolean
        Nothing ->
          do ty <- scTypeOf sc tm
             ok <- scConvertible sc True ty =<< scBoolType sc
             unless ok $ fail $ unlines
               [ "predicateToSATQuery: expected boolean result but got:"
               , showTerm ty
               , showTerm tm0
               ]
             return (vars, tm)

-- | Given a proposition, compute a SAT query which will prove the proposition
--   iff the SAT query is unsatisfiable.
propToSATQuery :: SharedContext -> Set VarIndex -> Prop -> IO SATQuery
propToSATQuery sc unintSet prop =
    do mmap <- scGetModuleMap sc
       tm <- propToTerm sc prop
       (initVars, abstractVars) <- filterFirstOrderVars mmap mempty mempty (getAllExts tm)
       (finalVars, asserts)     <- processTerm mmap initVars [] tm
       return SATQuery
              { satVariables = finalVars
              , satUninterp  = Set.union unintSet abstractVars
              , satAsserts   = asserts
              }

  where
    evalFOT mmap t =
      asFirstOrderTypeValue (evalSharedTerm mmap mempty mempty t)

    filterFirstOrderVars _ fovars absvars [] = pure (fovars, absvars)
    filterFirstOrderVars mmap fovars absvars (e:es) =
      case evalFOT mmap (ecType e) of
         Nothing  -> filterFirstOrderVars mmap fovars (Set.insert (ecVarIndex e) absvars) es
         Just fot -> filterFirstOrderVars mmap (Map.insert e fot fovars) absvars es

    processTerm mmap vars xs tm =
      case asPi tm of
        Just (lnm, tp, body)
          | Just x <- asEqTrue tp
          , looseVars body == emptyBitSet ->
              do processTerm mmap vars (x:xs) body

            -- TODO? Allow universal hypotheses...

          | otherwise ->
              case evalFOT mmap tp of
                Nothing -> fail ("propToSATQuery: expected first order type: " ++ showTerm tp)
                Just fot ->
                  do ec  <- scFreshEC sc lnm tp
                     etm <- scExtCns sc ec
                     body' <- instantiateVar sc 0 etm body
                     processTerm mmap (Map.insert ec fot vars) xs body'

        Nothing ->
          case asEqTrue tm of
            Nothing  -> fail $ "propToSATQuery: expected EqTrue, actual " ++ showTerm tm
            Just tmBool ->
              do tmNeg <- scNot sc tmBool
                 return (vars, reverse (tmNeg:xs))

-- | Given a goal to prove, attempt to apply the given proposition, producing
--   new subgoals for any necessary hypotheses of the proposition.  Returns
--   @Nothing@ if the given proposition does not apply to the goal.
goalApply :: SharedContext -> Prop-> ProofGoal -> IO (Maybe [ProofGoal])
goalApply sc rule goal = applyFirst (asPiLists (unProp rule))
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
                -- TODO, change the "ty" field to list the hypotheses?
                let newgoals = reverse [ goal { goalProp = t } | t <- newgoalterms ]
                return (Just newgoals)

    asPiLists :: Term -> [([(Text, Term)], Term)]
    asPiLists t =
      case asPi t of
        Nothing -> [([], t)]
        Just (nm, tp, body) ->
          [ ((nm, tp) : args, concl) | (args, concl) <- asPiLists body ] ++ [([], t)]


-- | Attempt to prove a universally quantified goal by introducing a fresh variable
--   for the binder.  Return the generated fresh term.
tacticIntro :: (F.MonadFail m, MonadIO m) =>
  SharedContext ->
  Text {- ^ Name to give to the variable.  If empty, will be chosen automatically from the goal. -} ->
  Tactic m TypedTerm
tacticIntro sc usernm = Tactic \goal ->
  case asPi (unProp (goalProp goal)) of
    Just (nm, tp, body) ->
      do let name = if Text.null usernm then nm else usernm
         xv <- liftIO $ scFreshEC sc name tp
         x  <- liftIO $ scExtCns sc xv
         tt <- liftIO $ mkTypedTerm sc x
         body' <- liftIO $ instantiateVar sc 0 x body
         let goal' = goal { goalProp = Prop body' }
         return (tt, mempty, [goal'], forallEvidence xv)

    _ -> fail "intro tactic failed: not a function"

-- | Attempt to prove an implication goal by introducing a local assumption for
--   hypothesis.  Return a @Theorem@ representing this local assumption.
--   This hypothesis should only be used for proving subgoals arising
--   from this call to @tacticAssume@ or evidence verification will later fail.
tacticAssume :: (F.MonadFail m, MonadIO m) => SharedContext -> Pos -> Tactic m Theorem
tacticAssume _sc loc = Tactic \goal ->
  case asPi (unProp (goalProp goal)) of
    Just (_nm, tp, body)
      | looseVars body == emptyBitSet ->
          do let goal' = goal{ goalProp = Prop body }
             let p     = Prop tp
             n <- liftIO (freshNonce globalNonceGenerator)
             let thm'  = LocalAssumption p loc n
             return (thm', mempty, [goal'], assumeEvidence n p)

    _ -> fail "assume tactic failed: not a function, or a dependent function"

-- | Attempt to prove a goal by weakening it with a new hypothesis, which is
--   justified by the given theorem.
tacticCut :: (F.MonadFail m, MonadIO m) => SharedContext -> Theorem -> Tactic m ()
tacticCut sc thm = Tactic \goal ->
  do body' <- liftIO (scFun sc (unProp (thmProp thm)) (unProp (goalProp goal)))
     let goal' = goal{ goalProp = Prop body' }
     return ((), mempty, [goal'], cutEvidence thm)

-- | Attempt to prove a goal by applying the given theorem.  Any hypotheses of
--   the theorem will generate additional subgoals.
tacticApply :: (F.MonadFail m, MonadIO m) => SharedContext -> Theorem -> Tactic m ()
tacticApply sc thm = Tactic \goal ->
  liftIO (goalApply sc (thmProp thm) goal) >>= \case
    Nothing -> fail "apply tactic failed: no match"
    Just newgoals ->
      return ((), mempty, newgoals, pure . ApplyEvidence thm)

-- | Attempt to simplify a goal by splitting it along conjunctions.  If successful,
--   two subgoals will be produced, representing the two conjuncts to be proved.
tacticSplit :: (F.MonadFail m, MonadIO m) => SharedContext -> Tactic m ()
tacticSplit sc = Tactic \(ProofGoal num ty name prop) ->
  liftIO (splitProp sc prop) >>= \case
    Nothing -> fail "split tactic failed: goal not a conjunction"
    Just (p1,p2) ->
      do let g1 = ProofGoal num (ty ++ ".left")  name p1
         let g2 = ProofGoal num (ty ++ ".right") name p2
         return ((), mempty, [g1,g2], splitEvidence)

-- | Attempt to solve a goal by recognizing it as a trivially true proposition.
tacticTrivial :: (F.MonadFail m, MonadIO m) => SharedContext -> Tactic m ()
tacticTrivial _sc = Tactic \goal ->
  if (propIsTrivial (goalProp goal)) then
    return ((), mempty, [], leafEvidence TrivialEvidence)
  else
    fail "trivial tactic: not a trivial goal"

-- | Examine the given proof goal and potentially do some work with it,
--   but do not alter the proof state.
tacticId :: Monad m => (ProofGoal -> m ()) -> Tactic m ()
tacticId f = Tactic \gl ->
  do lift (f gl)
     return ((), mempty, [gl], passthroughEvidence)

data SolveResult
  = SolveSuccess Evidence
  | SolveCounterexample CEX
  | SolveUnknown

-- | Attempt to solve the given goal, usually via an automatic solver.
--   If the goal is discharged, return evidence for the goal.  If there
--   is a counterexample for the goal, the counterexample will be used
--   to indicate the goal is unsolvable. Otherwise, the goal will remain unchanged.
tacticSolve :: Monad m => (ProofGoal -> m (SolverStats, SolveResult)) -> Tactic m ()
tacticSolve f = Tactic \gl ->
  do (stats, sres) <- lift (f gl)
     case sres of
       SolveSuccess e -> return ((), stats, [], leafEvidence e)
       SolveUnknown   -> return ((), stats, [gl], passthroughEvidence)
       SolveCounterexample cex -> throwError (stats, cex)

-- | Attempt to simplify a proof goal via computation, rewriting or similar.
--   The tactic should return a new proposition to prove and a method for
--   transferring evidence for the modified proposition into a evidence for
--   the original goal.
tacticChange :: Monad m => (ProofGoal -> m (Prop, Evidence -> Evidence)) -> Tactic m ()
tacticChange f = Tactic \gl ->
  do (p, ef) <- lift (f gl)
     return ((), mempty, [ gl{ goalProp = p } ], updateEvidence ef)
