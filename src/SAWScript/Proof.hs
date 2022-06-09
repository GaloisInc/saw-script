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
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

module SAWScript.Proof
  ( Prop
  , splitConj
  , splitDisj
  , unfoldProp
  , simplifyProp
  , hoistIfsInGoal
  , evalProp
  , betaReduceProp
  , falseProp
  , termToProp
  , termToMaybeProp
  , propToTerm
  , propToRewriteRule
  , propSize
  , prettyProp
  , ppProp
  , propToSATQuery
  , normalizeProp
  , checkProp

  , Sequent
  , SequentState(..)
  , sequentToProp
  , sequentToSATQuery
  , sequentSharedSize
  , sequentTreeSize
  , prettySequent
  , ppSequent
  , propToSequent
  , traverseSequent
  , traverseSequentWithFocus
  , checkSequent
  , sequentConstantSet
  , booleansToSequent
  , unfocusSequent
  , focusOnGoal
  , focusOnHyp
  , normalizeSequent
  , filterHyps
  , filterGoals

  , CofinSet(..)
  , cofinSetMember

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
  , specializeTheorem

  , Evidence(..)
  , checkEvidence
  , structuralEvidence

  , Tactic
  , withFirstGoal
  , tacticIntro
--  , tacticCut
--  , tacticAssume
  , tacticApply
  , tacticSplit
  , tacticCut
  , tacticTrivial
  , tacticId
  , tacticChange
  , tacticSolve
  , tacticExact

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
import qualified Data.Foldable as Fold
import           Data.List
import           Data.Maybe (fromMaybe)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Time.Clock

import Prettyprinter

import Data.Parameterized.Nonce

import Verifier.SAW.Prelude (scApplyPrelude_False)
import Verifier.SAW.Recognizer
import Verifier.SAW.Rewriter
import Verifier.SAW.SATQuery
import Verifier.SAW.Name (SAWNamingEnv)
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST
import Verifier.SAW.TypedTerm
import Verifier.SAW.FiniteValue (FirstOrderValue)
import Verifier.SAW.Term.Pretty
  (SawDoc, renderSawDoc, ppTermWithNames, ppTermContainerWithNames)
import qualified Verifier.SAW.SCTypeCheck as TC

import Verifier.SAW.Simulator.Concrete (evalSharedTerm)
import Verifier.SAW.Simulator.Value (asFirstOrderTypeValue, Value(..), TValue(..))

import What4.ProgramLoc (ProgramLoc)

import SAWScript.Position
import SAWScript.Prover.SolverStats
import SAWScript.Crucible.Common as Common
import qualified Verifier.SAW.Simulator.TermModel as TM
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
   do ty <- scWhnf sc =<< scTypeOf sc tm
      case asSort ty of
        Just s | s == propSort -> return (Prop tm)
        _ ->
          case asLambda tm of
            Just _ ->
              fail $ unlines [ "termToProp: Term is not a proposition."
                             , "Note: the given term is a lambda; try using Pi terms instead."
                             , showTerm tm, showTerm ty
                             ]
            Nothing ->
              fail $ unlines [ "termToProp: Term is not a proposition", showTerm tm, showTerm ty ]

-- | Turn a saw-core term into a proposition under the type-as-propositions
--   regime.  The given term must be a type, which means that its own type
--   is a sort.  If it is not, return @Nothing@.
termToMaybeProp :: SharedContext -> Term -> IO (Maybe Prop)
termToMaybeProp sc tm =
   do ty <- scWhnf sc =<< scTypeOf sc tm
      case asSort ty of
        Just s | s == propSort -> return (Just (Prop tm))
        _ -> return Nothing

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

-- | Attempt to split a conjunctive proposition into two propositions.
splitConj :: SharedContext -> Prop -> IO (Maybe (Prop, Prop))
splitConj sc (Prop p) =
  do let (vars, body) = asPiList p
     case (isGlobalDef "Prelude.and" <@> return <@> return) =<< asEqTrue body of
       Nothing -> pure Nothing
       Just (_ :*: p1 :*: p2) ->
         do t1 <- scPiList sc vars =<< scEqTrue sc p1
            t2 <- scPiList sc vars =<< scEqTrue sc p2
            return (Just (Prop t1,Prop t2))

-- | Attempt to split a disjunctive proposition into two propositions.
splitDisj :: SharedContext -> Prop -> IO (Maybe (Prop, Prop))
splitDisj sc (Prop p) =
  do let (vars, body) = asPiList p
     case (isGlobalDef "Prelude.or" <@> return <@> return) =<< asEqTrue body of
       Nothing -> pure Nothing
       Just (_ :*: p1 :*: p2) ->
         do t1 <- scPiList sc vars =<< scEqTrue sc p1
            t2 <- scPiList sc vars =<< scEqTrue sc p2
            return (Just (Prop t1,Prop t2))


splitSequent :: SharedContext -> Sequent -> IO (Maybe (Sequent, Sequent))
splitSequent sc sqt =
  case sequentState sqt of
    GoalFocus g mkSqt ->
      splitConj sc g >>= \case
        Nothing -> return Nothing
        Just (x, y) -> return (Just (mkSqt x, mkSqt y))
    HypFocus h mkSqt ->
      splitDisj sc h >>= \case
        Nothing -> return Nothing
        Just (x, y) -> return (Just (mkSqt x, mkSqt y))
    Unfocused -> fail "split tactic: focus required"

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

-- | Rewrite the propositions using the provided Simpset
simplifyProps :: Ord a => SharedContext -> Simpset a -> [Prop] -> IO (Set a, [Prop])
simplifyProps _sc _ss [] = return (mempty, [])
simplifyProps sc ss (p:ps) =
  do (a, p')  <- simplifyProp sc ss p
     (b, ps') <- simplifyProps sc ss ps
     return (Set.union a b, p' : ps')

-- | Rewrite in the sequent using the provided Simpset
simplifySequent :: Ord a => SharedContext -> Simpset a -> Sequent -> IO (Set a, Sequent)
simplifySequent sc ss (UnfocusedSequent hs gs) =
  do (a, hs') <- simplifyProps sc ss hs
     (b, gs') <- simplifyProps sc ss gs
     return (Set.union a b, UnfocusedSequent hs' gs')
simplifySequent sc ss (GoalFocusedSequent hs (gs1,g,gs2)) =
  do (a, g') <- simplifyProp sc ss g
     return (a, GoalFocusedSequent hs (gs1, g', gs2))
simplifySequent sc ss (HypFocusedSequent (hs1, h, hs2) gs) =
  do (a, h') <- simplifyProp sc ss h
     return (a, HypFocusedSequent (hs1, h', hs2) gs)


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
         Nothing -> fail ("goal_eval: expected EqTrue\n" ++ scPrettyTerm defaultPPOpts p)

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

trivialProofTerm :: SharedContext -> Prop -> IO (Either String Term)
trivialProofTerm sc (Prop p) = runExceptT (loop =<< lift (scWhnf sc p))
  where
    loop (asPi -> Just (nm, tp, tm)) =
      do pf <- loop =<< lift (scWhnf sc tm)
         lift $ scLambda sc nm tp pf

    loop (asEq -> Just (tp, x, _y)) =
      lift $ scCtorApp sc "Prelude.Refl" [tp, x]

    loop _ = throwError $ unlines
               [ "The trivial tactic can only prove quantified equalities, but"
               , "the given goal is not in the correct form."
               , showTerm p
               ]

normalizeProp :: SharedContext -> ModuleMap -> Set VarIndex -> Prop -> IO Prop
normalizeProp sc modmap opaqueSet (Prop tm) =
  do tm' <- TM.normalizeSharedTerm sc modmap mempty mempty opaqueSet tm
     termToProp sc tm'

-- | Pretty print the given proposition as a string.
prettyProp :: PPOpts -> SAWNamingEnv -> Prop -> String
prettyProp opts nenv p = renderSawDoc opts (ppProp opts nenv p)

-- | Pretty print the given proposition as a @SawDoc@.
ppProp :: PPOpts -> SAWNamingEnv -> Prop -> SawDoc
ppProp opts nenv (Prop tm) = ppTermWithNames opts nenv tm

-- TODO, I'd like to add metadata here
type SequentBranch = Prop

data Sequent
  = UnfocusedSequent   [SequentBranch] [SequentBranch]
  | GoalFocusedSequent [SequentBranch] ([SequentBranch], SequentBranch, [SequentBranch])
  | HypFocusedSequent ([SequentBranch], SequentBranch, [SequentBranch]) [SequentBranch]

unfocus :: Sequent -> ([SequentBranch],[SequentBranch])
unfocus (UnfocusedSequent hs gs) = (hs,gs)
unfocus (GoalFocusedSequent hs (gs1,g,gs2)) = (hs, gs1 ++ g : gs2)
unfocus (HypFocusedSequent (hs1,h,hs2) gs)  = (hs1 ++ h : hs2,  gs)

unfocusSequent :: Sequent -> Sequent
unfocusSequent sqt = UnfocusedSequent hs gs
  where (hs,gs) = unfocus sqt

focusOnGoal :: Integer -> Sequent -> Maybe Sequent
focusOnGoal i sqt =
    let (hs,gs) = unfocus sqt in
    case genericDrop i gs of
      (g:gs2) -> Just (GoalFocusedSequent hs (genericTake i gs, g, gs2))
      []      -> Nothing

focusOnHyp :: Integer -> Sequent -> Maybe Sequent
focusOnHyp i sqt =
    let (hs,gs) = unfocus sqt in
    case genericDrop i hs of
      (h:hs2) -> Just (HypFocusedSequent (genericTake i hs, h, hs2) gs)
      []      -> Nothing

sequentToRawSequent :: Sequent -> RawSequent Prop
sequentToRawSequent sqt =
   case sqt of
     UnfocusedSequent   hs gs            -> RawSequent hs gs
     GoalFocusedSequent hs (gs1, g, gs2) -> RawSequent hs (gs1 ++ g : gs2)
     HypFocusedSequent  (hs1, h, hs2) gs -> RawSequent (hs1 ++ h : hs2) gs


sequentConstantSet :: Sequent -> Map VarIndex (NameInfo, Term, Maybe Term)
sequentConstantSet sqt = foldr (\p m -> Map.union (getConstantSet (unProp p)) m) mempty (hs++gs)
  where
    RawSequent hs gs = sequentToRawSequent sqt

data RawSequent a = RawSequent [a] [a]

instance Functor RawSequent where
  fmap f (RawSequent hs gs) = RawSequent (fmap f hs) (fmap f gs)
instance Foldable RawSequent where
  foldMap f (RawSequent hs gs) = Fold.foldMap f (hs ++ gs)
instance Traversable RawSequent where
  traverse f (RawSequent hs gs) = RawSequent <$> traverse f hs <*> traverse f gs


convertibleProps :: SharedContext -> [Prop] -> [Prop] -> IO Bool
convertibleProps _sc [] [] = return True
convertibleProps sc (p1:ps1) (p2:ps2) =
  do ok1 <- scConvertible sc True (unProp p1) (unProp p2)
     ok2 <- convertibleProps sc ps1 ps2
     return (ok1 && ok2)
convertibleProps _sc _ _ = return False

convertibleSequents :: SharedContext -> Sequent -> Sequent -> IO Bool
convertibleSequents sc sqt1 sqt2 =
  do ok1 <- convertibleProps sc hs1 hs2
     ok2 <- convertibleProps sc gs1 gs2
     return (ok1 && ok2)
  where
    RawSequent hs1 gs1 = sequentToRawSequent sqt1
    RawSequent hs2 gs2 = sequentToRawSequent sqt2



data SequentState
  = Unfocused
  | GoalFocus Prop (Prop -> Sequent)
  | HypFocus Prop (Prop -> Sequent)

propToSequent :: Prop -> Sequent
propToSequent p = GoalFocusedSequent [] ([], p, [])

booleansToSequent :: SharedContext -> [Term] -> [Term] -> IO Sequent
booleansToSequent sc hs gs =
  do hs' <- mapM (boolToProp sc []) hs
     gs' <- mapM (boolToProp sc []) gs
     case gs' of
       [g] -> return (GoalFocusedSequent hs' ([],g,[]))
       _   -> return (UnfocusedSequent hs' gs')

sequentToProp :: SharedContext -> Sequent -> IO Prop
sequentToProp sc sqt =
  do let RawSequent hs gs = sequentToRawSequent sqt
     case gs of
       []  -> do g <- boolToProp sc [] =<< scBool sc False
                 loop hs g
       [g] -> loop hs g
              -- TODO, we should add a prop-level disjunction to the SAWCore prelude
       _   -> fail "seqentToProp: cannot handle multi-conclusion sequents"

 where
   loop [] g = return g
   loop (h:hs) g =
     do g' <- loop hs g
        Prop <$> scFun sc (unProp h) (unProp g')

-- | Pretty print the given proposition as a string.
prettySequent :: PPOpts -> SAWNamingEnv -> Sequent -> String
prettySequent opts nenv sqt = renderSawDoc opts (ppSequent opts nenv sqt)

-- | Pretty print the given proposition as a @SawDoc@.
ppSequent :: PPOpts -> SAWNamingEnv -> Sequent -> SawDoc
ppSequent opts nenv sqt =
  ppTermContainerWithNames
    (ppRawSequent sqt)
    opts
    nenv
    (fmap unProp (sequentToRawSequent sqt))

ppRawSequent :: Sequent -> RawSequent SawDoc -> SawDoc
ppRawSequent _sqt (RawSequent [] [g]) = g
ppRawSequent sqt (RawSequent hs gs)  =
  align (vcat (map ppHyp (zip [0..] hs) ++ turnstile ++ map ppGoal (zip [0..] gs)))
 where
  turnstile  = [ pretty (take 40 (repeat '=')) ]
  focused doc = "<<" <> doc <> ">>"
  ppHyp (i, tm)
    | HypFocusedSequent (hs1,_h,_hs2) _gs <- sqt
    , length hs1 == i
    = focused ("H" <> pretty i) <+> tm

    | otherwise
    = "H" <> pretty i <> ":" <+> tm

  ppGoal (i, tm)
    | GoalFocusedSequent _hs (gs1,_g,_gs2) <- sqt
    , length gs1 == i
    = focused ("G" <> pretty i) <+> tm

    | otherwise
    = "G" <> pretty i <> ":" <+> tm


data CofinSet a
  = WhiteList (Set a)
  | BlackList (Set a)

cofinSetMember :: Ord a => a -> CofinSet a -> Bool
cofinSetMember a (WhiteList xs) = Set.member a xs
cofinSetMember a (BlackList xs)  = not (Set.member a xs)

filterPosList :: CofinSet Integer -> [a] -> [a]
filterPosList pss xs = map snd $ filter f $ zip [0..] xs
  where
    f (i,_) = cofinSetMember i pss

filterFocusedList :: CofinSet Integer -> ([a],a,[a]) -> Either [a] ([a],a,[a])
filterFocusedList pss (xs1,x,xs2) =
   if cofinSetMember idx pss then
     Right (xs1',x,xs2')
   else
     Left (xs1' ++ xs2')
  where
    f (i,_) = cofinSetMember i pss
    idx  = genericLength xs1
    xs1' = map snd $ filter f $ zip [0..] xs1
    xs2' = map snd $ filter f $ zip [idx+1..] xs2

filterHyps :: CofinSet Integer -> Sequent -> Sequent
filterHyps pss (UnfocusedSequent hs gs) =
  UnfocusedSequent (filterPosList pss hs) gs
filterHyps pss (GoalFocusedSequent hs gs) =
  GoalFocusedSequent (filterPosList pss hs) gs
filterHyps pss (HypFocusedSequent hs gs) =
  case filterFocusedList pss hs of
    Left hs'  -> UnfocusedSequent hs' gs
    Right hs' -> HypFocusedSequent hs' gs

filterGoals :: CofinSet Integer -> Sequent -> Sequent
filterGoals pss (UnfocusedSequent hs gs) =
  UnfocusedSequent hs (filterPosList pss gs)
filterGoals pss (HypFocusedSequent hs gs) =
  HypFocusedSequent hs (filterPosList pss gs)
filterGoals pss (GoalFocusedSequent hs gs) =
  case filterFocusedList pss gs of
    Left gs'  -> UnfocusedSequent hs gs'
    Right gs' -> GoalFocusedSequent hs gs'

addHypothesis :: Prop -> Sequent -> Sequent
addHypothesis p (UnfocusedSequent hs gs)   = UnfocusedSequent (hs ++ [p]) gs
addHypothesis p (GoalFocusedSequent hs gs) = GoalFocusedSequent (hs ++ [p]) gs
addHypothesis p (HypFocusedSequent (hs1,h,hs2) gs) = HypFocusedSequent (hs1,h,hs2++[p]) gs

addNewFocusedGoal :: Prop -> Sequent -> Sequent
addNewFocusedGoal p sqt =
  let RawSequent hs gs = sequentToRawSequent sqt
   in GoalFocusedSequent hs (gs,p,[])

sequentState :: Sequent -> SequentState
sequentState (UnfocusedSequent _ _) = Unfocused
sequentState (GoalFocusedSequent hs (gs1,g,gs2)) =
  GoalFocus g (\g' -> GoalFocusedSequent hs (gs1,g',gs2))
sequentState (HypFocusedSequent (hs1,h,hs2) gs) =
  HypFocus h (\h' -> HypFocusedSequent (hs1,h',hs2) gs)

sequentSharedSize :: Sequent -> Integer
sequentSharedSize sqt = scSharedSizeMany (map unProp (hs ++ gs))
  where
   RawSequent hs gs = sequentToRawSequent sqt

sequentTreeSize :: Sequent -> Integer
sequentTreeSize sqt = scTreeSizeMany (map unProp (hs ++ gs))
  where
   RawSequent hs gs = sequentToRawSequent sqt

traverseSequentWithFocus :: Applicative m => (Prop -> m Prop) -> Sequent -> m Sequent
traverseSequentWithFocus f (UnfocusedSequent hs gs) =
  UnfocusedSequent <$> traverse f hs <*> traverse f gs
traverseSequentWithFocus f (GoalFocusedSequent hs (gs1, g, gs2)) =
  (\g' -> GoalFocusedSequent hs (gs1, g', gs2)) <$> f g
traverseSequentWithFocus f (HypFocusedSequent (hs1, h, hs2) gs) =
  (\h' -> HypFocusedSequent (hs1, h', hs2) gs) <$> f h

traverseSequent :: Applicative m => (Prop -> m Prop) -> Sequent -> m Sequent
traverseSequent f (UnfocusedSequent hs gs) =
  UnfocusedSequent <$> traverse f hs <*> traverse f gs
traverseSequent f (GoalFocusedSequent hs (gs1, g, gs2)) =
  GoalFocusedSequent <$>
    (traverse f hs) <*>
    ( (,,) <$> traverse f gs1 <*> f g <*> traverse f gs2)

traverseSequent f (HypFocusedSequent (hs1, h, hs2) gs) =
  HypFocusedSequent <$>
    ( (,,) <$> traverse f hs1 <*> f h <*> traverse f hs2) <*>
    (traverse f gs)

checkSequent :: SharedContext -> PPOpts -> Sequent -> IO ()
checkSequent sc ppOpts (UnfocusedSequent hs gs) =
  do forM_ hs (checkProp sc ppOpts)
     forM_ gs (checkProp sc ppOpts)
checkSequent sc ppOpts (GoalFocusedSequent hs (gs1,g,gs2)) =
  do forM_ hs (checkProp sc ppOpts)
     forM_ gs1 (checkProp sc ppOpts)
     checkProp sc ppOpts g
     forM_ gs2 (checkProp sc ppOpts)
checkSequent sc ppOpts (HypFocusedSequent (hs1,h,hs2) gs) =
  do forM_ hs1 (checkProp sc ppOpts)
     checkProp sc ppOpts h
     forM_ hs2 (checkProp sc ppOpts)
     forM_ gs  (checkProp sc ppOpts)

checkProp :: SharedContext -> PPOpts -> Prop -> IO ()
checkProp sc ppOpts (Prop t) =
  do ty <- TC.scTypeCheckError sc t
     case asSort ty of
        Just s | s == propSort -> return ()
        _ -> fail $ unlines ["Term is not a prop!", scPrettyTerm ppOpts t, scPrettyTerm ppOpts ty]

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
  | SolverEvidence SolverStats Sequent

    -- | This type of evidence is produced when the given proposition
    --   has been randomly tested against input vectors in the style
    --   of quickcheck.  The included number is the number of successfully
    --   passed test vectors.
  | QuickcheckEvidence Integer Sequent

    -- | This type of evidence is produced when the given proposition
    --   has been explicitly assumed without other evidence at the
    --   user's direction.
  | Admitted Text Pos Sequent

    -- | This type of evidence is produced when a proposition can be deconstructed
    --   along a conjunction into two subgoals, each of which is supported by
    --   the included evidence.
  | SplitEvidence Evidence Evidence

    -- | This type of evidence is produced when a previously-proved theorem is
    --   applied via backward reasoning to prove a goal.  Pi-quantified variables
    --   of the theorem may be specialized either by giving an explicit @Term@ to
    --   instantiate the variable, or by giving @Evidence@ for @Prop@ hypotheses.
    --   After specializing the given @Theorem@ the result must match the
    --   current goal.
  | ApplyEvidence Theorem [Either Term Evidence]

    -- | This type of evidence is used to prove an implication.  The included
    --   proposition must match the hypothesis of the goal, and the included
    --   evidence must match the conclusion of the goal.  The proposition is
    --   allowed to appear inside the evidence as a local assumption.
--  | AssumeEvidence TheoremNonce Prop Evidence

    -- | This type of evidence is used to prove a universally-quantified statement.
  | IntroEvidence (ExtCns Term) Evidence

    -- | This type of evidence is used to apply the "cut rule" of sequent calculus.
    --   The given proposition is added to the hypothesis list in the first
    --   deriviation, and into the conclusion list in the second, where it is focused.
  | CutEvidence Prop Evidence Evidence

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

    -- | This type of evidence is used to modify a focused part of the goal.
    --   The modified goal should be equivalent up to conversion.
  | ConversionEvidence Sequent Evidence

    -- | This type of evidence is used to modify a goal to prove by applying
    -- 'hoistIfsInGoal'.
  | HoistIfsEvidence Evidence

    -- | Change the state of the sequent in some "structural" way. This
    --   can involve changing focus, reordering or applying weakening rules.
  | StructuralEvidence Sequent Evidence

    -- | Change the state of the sequent in some way that is governed by
    --   the "reversable" L/R rules of the sequent calculus, e.g.,
    --   conjunctions in hypotheses can be split into multiple hypotheses,
    --   negated conclusions become positive hypotheses, etc.
  | NormalizeSequentEvidence Sequent Evidence

    -- | Change the sate of th sequent by invoking the term evaluator
    --   on the focused sequent branch (or all branches, if unfocused).
    --   Treat the given variable indexes as opaque.
  | NormalizePropEvidence (Set VarIndex) Evidence

    -- | This type of evidence is used when the current sequent, after
    --   applying structural rules, is an instance of the basic
    --   sequent calculus axiom, which connects a hypothesis to a goal.
  | AxiomEvidence

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

{-
assumeEvidence :: TheoremNonce -> Prop -> [Evidence] -> IO Evidence
assumeEvidence n p [e] = pure (AssumeEvidence n p e)
assumeEvidence _ _ _ = fail "assumeEvidence: expected one evidence value"
-}

introEvidence :: ExtCns Term -> [Evidence] -> IO Evidence
introEvidence x [e] = pure (IntroEvidence x e)
introEvidence _ _ = fail "introEvidence: expected one evidence value"

cutEvidence :: Prop -> [Evidence] -> IO Evidence
cutEvidence p [e1,e2] = pure (CutEvidence p e1 e2)
cutEvidence _ _ = fail "cutEvidence: expected two evidence values"

structuralEvidence :: Sequent -> Evidence -> Evidence
structuralEvidence _sqt (StructuralEvidence sqt' e) = StructuralEvidence sqt' e
structuralEvidence sqt e = StructuralEvidence sqt e

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


-- | Given a theorem with quantified variables, build a new theorem that
--   specializes the leading quantifiers with the given terms.
--   This will fail if the given terms to not match the quantifier structure
--   of the given theorem.
specializeTheorem :: SharedContext -> TheoremDB -> Pos -> Text -> Theorem -> [Term] -> IO Theorem
specializeTheorem _sc _db _loc _rsn thm [] = return thm
specializeTheorem sc db loc rsn thm ts0 =
  do let p0 = unProp (_thmProp thm)
     res <- TC.runTCM (loop p0 ts0) sc Nothing []
     case res of
       Left err -> fail (unlines (["specialize_theorem: failed to specialize"] ++ TC.prettyTCError err))
       Right p' ->
         constructTheorem sc db (Prop p') (ApplyEvidence thm (map Left ts0)) loc Nothing rsn 0

 where
  loop p [] = return p
  loop p (t:ts) =
    do prop <- liftIO (scSort sc propSort)
       t' <- TC.typeInferComplete t
       p' <- TC.applyPiTyped (TC.NotFuncTypeInApp (TC.TypedTerm p prop) t') p t'
       loop p' ts

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
       , _thmEvidence    = Admitted msg loc (propToSequent p)
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
       , _thmEvidence  = SolverEvidence stats (propToSequent p)
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
  , goalLoc  :: String
  , goalDesc :: String
  , goalTags :: Set String
  , goalSequent :: Sequent
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
  , _psConcl :: (Sequent,Pos,Maybe ProgramLoc,Text)
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

-- forall x in ps1, exists y in ps2 where x == y
propsSubset :: SharedContext -> [Prop] -> [Prop] -> IO Bool
propsSubset sc ps1 ps2 =
  and <$> sequence [ propsElem sc x ps2 | x <- ps1 ]

-- exists y in ps where x == y
propsElem :: SharedContext -> Prop -> [Prop] -> IO Bool
propsElem sc x ps =
  or <$> sequence [ scConvertible sc True (unProp x) (unProp y) | y <- ps ]

sequentIsAxiom :: SharedContext -> Sequent -> IO Bool
sequentIsAxiom sc sqt =
  do let RawSequent hs gs = sequentToRawSequent sqt
     or <$> sequence [ scConvertible sc True (unProp x) (unProp y) | x <- hs, y <- gs ]

-- | Test if the first given sequent subsumes the
--   second given sequent. This is a shallow syntactic
--   check that is sufficent to show that a proof
--   of the first sequent is sufficent to prove the second
sequentSubsumes :: SharedContext -> Sequent -> Sequent -> IO Bool
sequentSubsumes sc sqt1 sqt2 =
  do let RawSequent hs1 gs1 = sequentToRawSequent sqt1
     let RawSequent hs2 gs2 = sequentToRawSequent sqt2
     hypsOK  <- propsSubset sc hs1 hs2
     conclOK <- propsSubset sc gs1 gs2
     return (hypsOK && conclOK)

-- | Test if the first given sequent subsumes the
--   second given sequent. This is a shallow syntactic
--   check that is sufficent to show that a proof
--   of the first sequent is sufficent to prove the second
normalizeSequentSubsumes :: SharedContext -> Sequent -> Sequent -> IO Bool
normalizeSequentSubsumes sc sqt1 sqt2 =
  do RawSequent hs1 gs1 <- normalizeRawSequent sc (sequentToRawSequent sqt1)
     RawSequent hs2 gs2 <- normalizeRawSequent sc (sequentToRawSequent sqt2)
     hypsOK  <- propsSubset sc hs1 hs2
     conclOK <- propsSubset sc gs1 gs2
     return (hypsOK && conclOK)

normalizeSequent :: SharedContext -> Sequent -> IO Sequent
normalizeSequent sc sqt =
  -- TODO, if/when we add metadata to sequent branches, this will need to change
  do RawSequent hs gs <- normalizeRawSequent sc (sequentToRawSequent sqt)
     return (UnfocusedSequent hs gs)

normalizeRawSequent :: SharedContext -> RawSequent Prop -> IO (RawSequent Prop)
normalizeRawSequent sc (RawSequent hs gs) =
  do hs' <- mapM (normalizeHyp sc) hs
     gs' <- mapM (normalizeGoal sc) gs
     return (joinSequents (hs' ++ gs'))

joinSequent :: RawSequent Prop -> RawSequent Prop -> RawSequent Prop
joinSequent (RawSequent hs1 gs1) (RawSequent hs2 gs2) = RawSequent (hs1 ++ hs2) (gs1 ++ gs2)

joinSequents :: [RawSequent Prop] -> RawSequent Prop
joinSequents = foldl joinSequent (RawSequent [] [])


normalizeHyp :: SharedContext -> Prop -> IO (RawSequent Prop)
normalizeHyp sc p =
  do t <- scWhnf sc (unProp p)
     case asEqTrue t of
       Just b -> normalizeHypBool sc b >>= \case
                   Just sqt -> return sqt
                   Nothing  -> return (RawSequent [p] [])
       _      -> return (RawSequent [p] [])

normalizeGoal :: SharedContext -> Prop -> IO (RawSequent Prop)
normalizeGoal sc p =
  do t <- scWhnf sc (unProp p)
     case asEqTrue t of
       Just b -> normalizeGoalBool sc b >>= \case
                   Just sqt -> return sqt
                   Nothing  -> return (RawSequent [] [p])
       _      -> return (RawSequent [] [p])

normalizeHypBool :: SharedContext -> Term -> IO (Maybe (RawSequent Prop))
normalizeHypBool sc b =
  do body <- scWhnf sc b
     case () of
       _ | Just (_ :*: p1) <- (isGlobalDef "Prelude.not" <@> return) body
         -> Just <$> normalizeGoalBoolCommit sc p1

         | Just (_ :*: p1 :*: p2) <- (isGlobalDef "Prelude.and" <@> return <@> return) body
         -> Just <$> (joinSequent <$> normalizeHypBoolCommit sc p1 <*> normalizeHypBoolCommit sc p2)

         | otherwise
         -> return Nothing

normalizeHypBoolCommit :: SharedContext -> Term -> IO (RawSequent Prop)
normalizeHypBoolCommit sc b =
  normalizeHypBool sc b >>= \case
    Just sqt -> return sqt
    Nothing  -> do p <- boolToProp sc [] b
                   return (RawSequent [p] [])

normalizeGoalBool :: SharedContext -> Term -> IO (Maybe (RawSequent Prop))
normalizeGoalBool sc b =
  do body <- scWhnf sc b
     case () of
       _ | Just (_ :*: p1) <- (isGlobalDef "Prelude.not" <@> return) body
         -> Just <$> normalizeHypBoolCommit sc p1

         | Just (_ :*: p1 :*: p2) <- (isGlobalDef "Prelude.or" <@> return <@> return) body
         -> Just <$> (joinSequent <$> normalizeGoalBoolCommit sc p1 <*> normalizeGoalBoolCommit sc p2)

         | otherwise
         -> return Nothing

normalizeGoalBoolCommit :: SharedContext -> Term -> IO (RawSequent Prop)
normalizeGoalBoolCommit sc b =
  normalizeGoalBool sc b >>= \case
    Just sqt -> return sqt
    Nothing  -> do p <- boolToProp sc [] b
                   return (RawSequent [] [p])


-- | Verify that the given evidence in fact supports the given proposition.
--   Returns the identifers of all the theorems depended on while checking evidence.
checkEvidence :: SharedContext -> TheoremDB -> Evidence -> Prop -> IO (Set TheoremNonce, TheoremSummary)
checkEvidence sc db = \e p -> do hyps <- Map.keysSet <$> readIORef (theoremMap db)
                                 nenv <- scGetNamingEnv sc
                                 check nenv hyps e (propToSequent p)

  where
    checkApply _nenv _hyps _mkSqt (Prop p) [] = return (mempty, mempty, p)

    -- Check a theorem applied to "Evidence".
    -- The given prop must be an implication
    -- (i.e., nondependent Pi quantifying over a Prop)
    -- and the given evidence must match the expected prop.
    checkApply nenv hyps mkSqt (Prop p) (Right e:es)
      | Just (_lnm, tp, body) <- asPi p
      , looseVars body == emptyBitSet
      = do (d1,sy1) <- check nenv hyps e . mkSqt =<< termToProp sc tp
           (d2,sy2,p') <- checkApply nenv hyps mkSqt (Prop body) es
           return (Set.union d1 d2, sy1 <> sy2, p')
      | otherwise = fail $ unlines
           [ "Apply evidence mismatch: non-function or dependent function"
           , showTerm p
           ]

    -- Check a theorem applied to a term. This explicity instantiates
    -- a Pi binder with the given term.
    checkApply nenv hyps mkSqt (Prop p) (Left tm:es) =
      do propTerm <- scSort sc propSort
         let m = do tm' <- TC.typeInferComplete tm
                    let err = TC.NotFuncTypeInApp (TC.TypedTerm p propTerm) tm'
                    TC.applyPiTyped err p tm'
         res <- TC.runTCM m sc Nothing []
         case res of
           Left msg -> fail (unlines (TC.prettyTCError msg))
           Right p' -> checkApply nenv hyps mkSqt (Prop p') es

    checkTheorem :: Set TheoremNonce -> Theorem -> IO ()
    checkTheorem hyps (LocalAssumption p loc n) =
       unless (Set.member n hyps) $ fail $ unlines
          [ "Attempt to reference a local hypothesis that is not in scope"
          , "Generated at " ++ show loc
          , showTerm (unProp p)
          ]
    checkTheorem _hyps Theorem{} = return ()

    check ::
      SAWNamingEnv ->
      Set TheoremNonce ->
      Evidence ->
      Sequent ->
      IO (Set TheoremNonce, TheoremSummary)
    check nenv hyps e sqt = case e of
      ProofTerm tm ->
        case sequentState sqt of
          GoalFocus (Prop ptm) _ ->
            do ty <- TC.scTypeCheckError sc tm
               ok <- scConvertible sc True ptm ty
               unless ok $ fail $ unlines
                   [ "Proof term does not prove the required proposition"
                   , showTerm ptm
                   , showTerm tm
                   ]
               return (mempty, ProvedTheorem mempty)
          _ -> fail "Sequent must be goal-focused for proof term evidence"


      LocalAssumptionEvidence (Prop l) n ->
        do unless (Set.member n hyps) $ fail $ unlines
             [ "Illegal use of local hypothesis"
             , showTerm l
             ]
           return (Set.singleton n, ProvedTheorem mempty)

      SolverEvidence stats sqt' ->
        do ok <- sequentSubsumes sc sqt' sqt
           unless ok $ fail $ unlines
               [ "Solver proof does not prove the required sequent"
               , prettySequent defaultPPOpts nenv sqt
               , prettySequent defaultPPOpts nenv sqt'
               ]
           return (mempty, ProvedTheorem stats)

      Admitted msg pos sqt' ->
        do ok <- sequentSubsumes sc sqt' sqt
           unless ok $ fail $ unlines
               [ "Admitted proof does not match the required sequent " ++ show pos
               , Text.unpack msg
               , prettySequent defaultPPOpts nenv sqt
               , prettySequent defaultPPOpts nenv sqt'
               ]
           return (mempty, AdmittedTheorem msg)

      QuickcheckEvidence n sqt' ->
        do ok <- sequentSubsumes sc sqt' sqt
           unless ok $ fail $ unlines
               [ "Quickcheck evidence does not match the required sequent"
               , prettySequent defaultPPOpts nenv sqt
               , prettySequent defaultPPOpts nenv sqt'
               ]
           return (mempty, TestedTheorem n)

      SplitEvidence e1 e2 ->
        splitSequent sc sqt >>= \case
          Nothing -> fail $ unlines
                       [ "Split evidence does not apply"
                       , prettySequent defaultPPOpts nenv sqt
                       ]
          Just (sqt1,sqt2) ->
            do d1 <- check nenv hyps e1 sqt1
               d2 <- check nenv hyps e2 sqt2
               return (d1 <> d2)

      ApplyEvidence thm es ->
        case sequentState sqt of
          GoalFocus p mkSqt ->
            do checkTheorem hyps thm
               (d,sy,p') <- checkApply nenv hyps mkSqt (thmProp thm) es
               ok <- scConvertible sc False (unProp p) p'
               unless ok $ fail $ unlines
                   [ "Apply evidence does not match the required proposition"
                   , showTerm (unProp p)
                   , showTerm p'
                   ]
               return (Set.insert (thmNonce thm) d, sy)
          _ -> fail $ unlines $
                    [ "Apply evidence requires a goal-focused sequent"
                    , prettySequent defaultPPOpts nenv sqt
                    ]

      UnfoldEvidence vars e' ->
        do sqt' <- traverseSequentWithFocus (unfoldProp sc vars) sqt
           check nenv hyps e' sqt'

      NormalizePropEvidence opqueSet e' ->
        do modmap <- scGetModuleMap sc
           sqt' <- traverseSequentWithFocus (normalizeProp sc modmap opqueSet) sqt
           check nenv hyps e' sqt'

      RewriteEvidence ss e' ->
        do (d1,sqt') <- simplifySequent sc ss sqt
           unless (Set.isSubsetOf d1 hyps) $ fail $ unlines
             [ "Rewrite step used theorem not in hypothesis database"
             , show (Set.difference d1 hyps)
             ]
           (d2,sy) <- check nenv hyps e' sqt'
           return (Set.union d1 d2, sy)

      HoistIfsEvidence e' ->
        do sqt' <- traverseSequentWithFocus (hoistIfsInGoal sc) sqt
           check nenv hyps e' sqt'

      EvalEvidence vars e' ->
        do sqt' <- traverseSequentWithFocus (evalProp sc vars) sqt
           check nenv hyps e' sqt'

      ConversionEvidence sqt' e' ->
        do ok <- convertibleSequents sc sqt sqt'
           unless ok $ fail $ unlines
             [ "Converted sequent does not match goal"
             , prettySequent defaultPPOpts nenv sqt
             , prettySequent defaultPPOpts nenv sqt'
             ]
           check nenv hyps e' sqt'

      NormalizeSequentEvidence sqt' e' ->
        do ok <- normalizeSequentSubsumes sc sqt' sqt
           unless ok $ fail $ unlines
             [ "Normalized sequent does not subsume goal"
             , prettySequent defaultPPOpts nenv sqt
             , prettySequent defaultPPOpts nenv sqt'
             ]
           check nenv hyps e' sqt'

      StructuralEvidence sqt' e' ->
        do ok <- sequentSubsumes sc sqt' sqt
           unless ok $ fail $ unlines
             [ "Sequent does not subsume goal"
             , prettySequent defaultPPOpts nenv sqt
             , prettySequent defaultPPOpts nenv sqt'
             ]
           check nenv hyps e' sqt'

{-
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
-}

      AxiomEvidence ->
        do ok <- sequentIsAxiom sc sqt
           unless ok $ fail $ unlines
             [ "Sequent is not an instance of the sequent calculus axiom"
             , prettySequent defaultPPOpts nenv sqt
             ]
           return (mempty, ProvedTheorem mempty)

      CutEvidence p ehyp egl ->
        do d1 <- check nenv hyps ehyp (addHypothesis p sqt)
           d2 <- check nenv hyps egl  (addNewFocusedGoal p sqt)
           return (d1 <> d2)

      IntroEvidence x e' ->
        -- TODO! Check that the given ExtCns is fresh for the sequent
        case sequentState sqt of
          Unfocused -> fail "Intro evidence requires a focused sequent"
          HypFocus _ _ -> fail "Intro evidence apply in hypothesis: TODO: apply to existentials"
          GoalFocus (Prop ptm) mkSqt ->
            case asPi ptm of
              Nothing -> fail $ unlines ["Intro evidence expected function prop", showTerm ptm]
              Just (_lnm, ty, body) ->
                do let ty' = ecType x
                   ok <- scConvertible sc False ty ty'
                   unless ok $ fail $ unlines
                     ["Intro evidence types do not match"
                     , showTerm ty'
                     , showTerm ty
                     ]
                   x' <- scExtCns sc x
                   body' <- instantiateVar sc 0 x' body
                   check nenv hyps e' (mkSqt (Prop body'))

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
     pure (ProofState [g] (goalSequent g,pos,ploc,rsn) mempty Nothing passthroughEvidence start)

-- | Attempt to complete a proof by checking that all subgoals have been discharged,
--   and validate the computed evidence to ensure that it supports the original
--   proposition.  If successful, return the completed @Theorem@ and a summary
--   of solver resources used in the proof.
finishProof :: SharedContext -> TheoremDB -> Prop -> ProofState -> IO ProofResult
finishProof sc db conclProp ps@(ProofState gs (concl,loc,ploc,rsn) stats _ checkEv start) =
  case gs of
    [] ->
      do e <- checkEv []
         let e' = NormalizeSequentEvidence concl e
         (deps,sy) <- checkEvidence sc db e' conclProp
         n <- freshNonce globalNonceGenerator
         end <- getCurrentTime
         thm <- recordTheorem db
                   Theorem
                   { _thmProp = conclProp
                   , _thmStats = stats
                   , _thmEvidence = e'
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
propToSATQuery sc unintSet prop = sequentToSATQuery sc unintSet (propToSequent prop)

-- | Given a proposition, compute a SAT query which will prove the proposition
--   iff the SAT query is unsatisfiable.
sequentToSATQuery :: SharedContext -> Set VarIndex -> Sequent -> IO SATQuery
sequentToSATQuery sc unintSet sqt =
    do let RawSequent hs gs = sequentToRawSequent sqt
       mmap <- scGetModuleMap sc
       let exts = foldMap getAllExtSet (map unProp (hs ++ gs))
       (initVars, abstractVars) <- filterFirstOrderVars mmap mempty mempty (Set.toList exts)
       -- NB, the following reversals make the order of assertions more closely match the input sequent,
       -- but should otherwise not be semantically relevant
       hypAsserts <- mapM processHyp (reverse (map unProp hs))
       (finalVars, asserts) <- foldM (processGoal mmap) (initVars, hypAsserts) (map unProp gs)
       return SATQuery
              { satVariables = finalVars
              , satUninterp  = Set.union unintSet abstractVars
              , satAsserts   = reverse asserts
              }

  where
    evalFOT mmap t =
      asFirstOrderTypeValue (evalSharedTerm mmap mempty mempty t)

    filterFirstOrderVars _ fovars absvars [] = pure (fovars, absvars)
    filterFirstOrderVars mmap fovars absvars (e:es) =
      case evalFOT mmap (ecType e) of
         Nothing  -> filterFirstOrderVars mmap fovars (Set.insert (ecVarIndex e) absvars) es
         Just fot -> filterFirstOrderVars mmap (Map.insert e fot fovars) absvars es

    processHyp tm =
      do -- TODO: I would like to WHNF here, but that evalutes too aggressively
         -- because scWhnf evaluates strictly through the `Eq` datatype former.
         -- This breaks some proof examples by unfolding things that need to
         -- be uninterpreted.
         -- tm' <- scWhnf sc tm
         let tm' = tm

         -- TODO? Allow universal hypotheses...
         case asEqTrue tm' of
           Nothing -> fail $ "sequentToSATQuery : expected EqTrue in hypothesis, actual " ++ showTerm tm'
           Just tmBool -> return tmBool

    processGoal mmap (vars,xs) tm =
      do -- TODO: I would like to WHNF here, but that evalutes too aggressively
         -- because scWhnf evaluates strictly through the `Eq` datatype former.
         -- This breaks some proof examples by unfolding things that need to
         -- be uninterpreted.
         -- tm' <- scWhnf sc tm
         let tm' = tm

         case asPi tm' of
           Just (lnm, tp, body) ->
             do -- same issue with WHNF
                -- tp' <- scWhnf sc tp
                let tp' = tp
                case asEqTrue tp' of
                  Just x | looseVars body == emptyBitSet ->
                    processGoal mmap (vars, x:xs) body

                    -- TODO? Allow universal hypotheses...

                  _ ->
                    case evalFOT mmap tp' of
                      Nothing -> fail ("propToSATQuery: expected first order type: " ++ showTerm tp')
                      Just fot ->
                        do ec  <- scFreshEC sc lnm tp'
                           etm <- scExtCns sc ec
                           body' <- instantiateVar sc 0 etm body
                           processGoal mmap (Map.insert ec fot vars, xs) body'

           Nothing ->
             case asEqTrue tm' of
               Nothing -> fail $ "propToSATQuery: expected EqTrue, actual " ++ showTerm tm'
               Just tmBool ->
                 do tmNeg <- scNot sc tmBool
                    return (vars, tmNeg:xs)

-- | Given a goal to prove, attempt to apply the given proposition, producing
--   new subgoals for any necessary hypotheses of the proposition.  Returns
--   @Nothing@ if the given proposition does not apply to the goal.
goalApply :: SharedContext -> Prop -> Prop -> IO (Maybe [Either Term Prop])
goalApply sc rule goal = applyFirst (asPiLists (unProp rule))
  where

    applyFirst [] = pure Nothing
    applyFirst ((ruleArgs, ruleConcl) : rest) =
      do result <- scMatch sc ruleConcl (unProp goal)
         case result of
           Nothing -> applyFirst rest
           Just inst ->
             do let inst' = [ Map.lookup i inst | i <- take (length ruleArgs) [0..] ]
                dummy <- scUnitType sc
                let mkNewGoals (Nothing : mts) ((nm, prop) : args) =
                      do c0 <- instantiateVarList sc 0 (map (fromMaybe dummy) mts) prop
                         mp <- termToMaybeProp sc c0
                         case mp of
                           Nothing ->
                             fail ("goal_apply: could not find instantiation for " ++ show nm)
                           Just p ->
                             do cs <- mkNewGoals mts args
                                return (Right p : cs)
                    mkNewGoals (Just tm : mts) (_ : args) =
                      do cs <- mkNewGoals mts args
                         return (Left tm : cs)
                    mkNewGoals _ _ = return []

                newgoalterms <- mkNewGoals inst' (reverse ruleArgs)
                return (Just (reverse newgoalterms))

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
  case sequentState (goalSequent goal) of
    GoalFocus p mkSqt ->
      case asPi (unProp p) of
        Just (nm, tp, body) ->
          do let name = if Text.null usernm then nm else usernm
             xv <- liftIO $ scFreshEC sc name tp
             x  <- liftIO $ scExtCns sc xv
             tt <- liftIO $ mkTypedTerm sc x
             body' <- liftIO $ instantiateVar sc 0 x body
             let goal' = goal { goalSequent = mkSqt (Prop body') }
             return (tt, mempty, [goal'], introEvidence xv)

        _ -> fail "intro tactic failed: not a function"

    HypFocus _ _ -> fail "TODO: implement intro on hyps"
    Unfocused -> fail "intro tactic: focus required"

{-
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

-}

-- | Attempt to prove a goal by applying the given theorem.  Any hypotheses of
--   the theorem will generate additional subgoals.
tacticApply :: (F.MonadFail m, MonadIO m) => SharedContext -> Theorem -> Tactic m ()
tacticApply sc thm = Tactic \goal ->
  case sequentState (goalSequent goal) of
    Unfocused -> fail "apply tactic: focus required"
    HypFocus _ _ -> fail "apply tactic: cannot apply in a hypothesis"
    GoalFocus gl mkSqt ->
      liftIO (goalApply sc (thmProp thm) gl) >>= \case
        Nothing -> fail "apply tactic failed: no match"
        Just newterms ->
          let newgoals =
                [ goal{ goalSequent = mkSqt p, goalType = goalType goal ++ ".subgoal" ++ show i }
                | Right p <- newterms
                | i <- [0::Integer ..]
                ] in
          return ((), mempty, newgoals, \es -> ApplyEvidence thm <$> processEvidence newterms es)

 where
   processEvidence :: [Either Term Prop] -> [Evidence] -> IO [Either Term Evidence]
   processEvidence (Left tm : xs) es     = (Left tm :) <$> processEvidence xs es
   processEvidence (Right _ : xs) (e:es) = (Right e :) <$> processEvidence xs es
   processEvidence []             []     = pure []
   processEvidence _ _ = fail "apply tactic failed: evidence mismatch"

-- | Attempt to simplify a goal by splitting it along conjunctions.  If successful,
--   two subgoals will be produced, representing the two conjuncts to be proved.
tacticSplit :: (F.MonadFail m, MonadIO m) => SharedContext -> Tactic m ()
tacticSplit sc = Tactic \gl ->
  case sequentState (goalSequent gl) of
    Unfocused -> fail "split tactic: focus required"
    HypFocus h mkSqt ->
      liftIO (splitDisj sc h) >>= \case
        Nothing -> fail "split tactic failed: hypothesis not a disjunction"
        Just (p1,p2) ->
          do let g1 = gl{ goalType = goalType gl ++ ".left", goalSequent = mkSqt p1 }
             let g2 = gl{ goalType = goalType gl ++ ".right", goalSequent = mkSqt p2 }
             return ((), mempty, [g1,g2], splitEvidence)
    GoalFocus g mkSqt ->
      liftIO (splitConj sc g) >>= \case
        Nothing -> fail "split tactic failed: goal not a conjunction"
        Just (p1,p2) ->
          do let g1 = gl{ goalType = goalType gl ++ ".left", goalSequent = mkSqt p1 }
             let g2 = gl{ goalType = goalType gl ++ ".right", goalSequent = mkSqt p2 }
             return ((), mempty, [g1,g2], splitEvidence)

tacticCut :: (F.MonadFail m, MonadIO m) => SharedContext -> Prop -> Tactic m ()
tacticCut _sc p = Tactic \gl ->
  let sqt1 = addHypothesis p (goalSequent gl)
      sqt2 = addNewFocusedGoal p (goalSequent gl)
      g1 = gl{ goalType = goalType gl ++ ".cutH", goalSequent = sqt1 }
      g2 = gl{ goalType = goalType gl ++ ".cutG", goalSequent = sqt2 }
   in return ((), mempty, [g1, g2], cutEvidence p)

-- | Attempt to solve a goal by recognizing it as a trivially true proposition.
tacticTrivial :: (F.MonadFail m, MonadIO m) => SharedContext -> Tactic m ()
tacticTrivial sc = Tactic \goal ->
  case sequentState (goalSequent goal) of
    Unfocused -> fail "trivial tactic: focus required"
    HypFocus _ _ -> fail "trivial tactic: cannot apply trivial in a hypothesis"
    GoalFocus g _ ->
      liftIO (trivialProofTerm sc g) >>= \case
        Left err -> fail err
        Right pf ->
           do let gp = unProp g
              ty <- liftIO $ TC.scTypeCheckError sc pf
              ok <- liftIO $ scConvertible sc True gp ty
              unless ok $ fail $ unlines
                [ "The trivial tactic cannot prove this equality"
                , showTerm gp
                ]
              return ((), mempty, [], leafEvidence (ProofTerm pf))

tacticExact :: (F.MonadFail m, MonadIO m) => SharedContext -> Term -> Tactic m ()
tacticExact sc tm = Tactic \goal ->
  case sequentState (goalSequent goal) of
    Unfocused -> fail "tactic exact: focus required"
    HypFocus _ _ -> fail "tactic exact: cannot apply exact in a hypothesis"
    GoalFocus g _ ->
      do let gp = unProp g
         ty <- liftIO $ TC.scTypeCheckError sc tm
         ok <- liftIO $ scConvertible sc True gp ty
         unless ok $ fail $ unlines
             [ "Proof term does not prove the required proposition"
             , showTerm gp
             , showTerm tm
             ]
         return ((), mempty, [], leafEvidence (ProofTerm tm))


-- | Examine the given proof goal and potentially do some work with it,
--   but do not alter the proof state.
tacticId :: Monad m => (ProofGoal -> m a) -> Tactic m a
tacticId f = Tactic \gl ->
  do x <- lift (f gl)
     return (x, mempty, [gl], passthroughEvidence)

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
tacticChange :: Monad m => (ProofGoal -> m (Sequent, Evidence -> Evidence)) -> Tactic m ()
tacticChange f = Tactic \gl ->
  do (sqt, ef) <- lift (f gl)
     return ((), mempty, [ gl{ goalSequent = sqt } ], updateEvidence ef)
