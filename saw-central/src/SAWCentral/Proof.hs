{- |
Module      : SAWCentral.Proof
Description : Representations of SAW-Script proof states.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}

{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp #-}

module SAWCentral.Proof
  ( Prop
  , splitConj
  , splitDisj
  , unfoldProp
  , unfoldFixOnceProp
  , simplifyProp
  , hoistIfsInProp
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
  , unProp

  , Sequent
  , sequentToProp
  , sequentToSATQuery
  , sequentSharedSize
  , sequentTreeSize
  , ppSequent
  , propToSequent
  , traverseSequentWithFocus
  , checkSequent
  , sequentConstantSet

  , CofinSet(..)
  , cofinSetMember

  , TheoremDB
  , emptyTheoremDB
  , reachableTheorems

  , Theorem
  , thmProp
  , thmHyps
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
  , TheoremAnnotation(..)
  , prettyTheorem

  , admitTheorem
  , solverTheorem
  , proofByTerm
  , constructTheorem
  , validateTheorem
  , specializeTheorem

  , Evidence(..)
  , checkEvidence
  , leafEvidence

  , Tactic(..)
  , withFirstGoal
  , tacticIntro
  , tacticApply
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
  , subProof

  , CEX
  , ProofResult(..)
  , prettyProofResult, ppProofResult
  , SolveResult(..)

  , predicateToSATQuery
  ) where

import           Control.Lens ( (^.) )
import           Control.Monad (foldM, forM_, unless)
import qualified Control.Monad.Fail as F
import           Control.Monad.IO.Class (MonadIO(..))
import           Control.Monad.Except (ExceptT, MonadError(..), runExceptT)
import           Control.Monad.State (MonadState(..))
import           Control.Monad.Trans.Class (MonadTrans(..))
import qualified Data.Foldable as Fold
import           Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Time.Clock

-- XXX: hunt down the unqualified uses sometime
import Prettyprinter
import qualified Prettyprinter as PP

import Data.Parameterized.Nonce

import qualified What4.Expr.Builder as W4
import What4.ProgramLoc (ProgramLoc)

import qualified SAWSupport.Pretty as PPS (Doc, Opts, render, renderText)
import SAWSupport.Position

import SAWCore.Recognizer
import SAWCore.Rewriter
import SAWCore.SATQuery
import SAWCore.Name (DisplayNameEnv, Name(..), VarName(..))
import SAWCore.SharedTerm
import SAWCore.Term.Functor
import SAWCore.FiniteValue (FirstOrderValue, prettyFirstOrderValue)
import qualified SAWCore.Term.Certified as TC
import SAWCore.Term.Pretty (prettyTermWithEnv, prettyTermContainerWithEnv)

import SAWCore.Simulator.Concrete (evalSharedTerm)
import SAWCore.Simulator.Value (asFirstOrderTypeValue, Value(..), TValue(..))

import CryptolSAWCore.TypedTerm

import SAWCentral.Position
import SAWCentral.Prover.SolverStats
import qualified SAWCoreWhat4.What4 as W4Sim
import qualified SAWCoreWhat4.ReturnTrip as W4Sim
import SAWCentral.Panic (panic)

-- | A proposition is a saw-core type of type `Prop`.
-- In particular, this includes any pi type whose result
-- type is a proposition. The argument of a pi type represents
-- a universally quantified variable.
newtype Prop = Prop Term
  -- INVARIANT: The type of the given term is `Prop`

unProp :: Prop -> Term
unProp (Prop tm) = tm

-- | Turn a SAWCore term into a proposition.
-- If it already has type @Prop@, then it is returned as is.
-- If it has a function type of any arity with a return type of
-- @Bool@, then convert the function arguments to universal
-- quantifiers.
termToProp :: SharedContext -> Term -> IO Prop
termToProp sc tm =
  do ty <- scWhnf sc =<< scTypeOf sc tm
     case asSort ty of
       Just s | s == propSort -> pure (Prop tm)
       -- If the term is not a Prop, then we check whether it is a
       -- function that returns a Bool.
       _ ->
         case asBoolType (snd (asPiList ty)) of
           Nothing ->
             do ty' <- ppTerm sc ty
                fail $ unlines $
                  [ "Expected type Prop or function type returning Bool."
                  , "Found type: " ++ ty'
                  ]
           Just () ->
             predicateToProp sc Universal tm

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
--   by universally quantifying over the variables given in the list.
boolToProp :: SharedContext -> [(VarName, Term)] -> Term -> IO Prop
boolToProp sc vars tm =
  do mmap <- scGetModuleMap sc
     ty <- scTypeOf sc tm
     case evalSharedTerm mmap mempty mempty ty of
       TValue VBoolType ->
         do p0 <- scEqTrue sc tm
            Prop <$> scPiList sc vars p0
       _ -> do
           tm' <- ppTerm sc tm
           ty' <- ppTerm sc ty
           fail $ unlines [ "boolToProp: Term is not a boolean", tm', ty' ]

-- | Return the saw-core term that represents this proposition.
propToTerm :: SharedContext -> Prop -> IO Term
propToTerm _sc (Prop tm) = pure tm

-- | Attempt to interpret a proposition as a rewrite rule.
propToRewriteRule :: SharedContext -> Prop -> Maybe a -> IO (Maybe (RewriteRule a))
propToRewriteRule sc (Prop tm) = ruleOfProp sc tm

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

-- | Unfold all the constants appearing in the proposition
--   whose VarIndex is found in the given set.
unfoldProp :: SharedContext -> Set VarIndex -> Prop -> IO Prop
unfoldProp sc unints (Prop tm) =
  do let unfold nm = Set.member (nameIndex nm) unints
     tm' <- scUnfoldConstants sc unfold tm
     return (Prop tm')

-- | Unfold one time all the fixpoint constants appearing in the proposition
-- whose VarIndex is found in the given set.
unfoldFixOnceProp :: SharedContext -> Set VarIndex -> Prop -> IO Prop
unfoldFixOnceProp sc unints (Prop tm) =
  do tm' <- scUnfoldOnceFixConstantSet sc True unints tm
     return (Prop tm')

-- | Rewrite the proposition using the provided Simpset
simplifyProp :: Monoid a => SharedContext -> Simpset a -> Prop -> IO (a, Prop)
simplifyProp sc ss (Prop tm) =
  do (a, tm') <- rewriteSharedTerm sc ss tm
     return (a, Prop tm')

-- | Rewrite the propositions using the provided Simpset
simplifyProps :: Monoid a => SharedContext -> Simpset a -> [Prop] -> IO (a, [Prop])
simplifyProps _sc _ss [] = return (mempty, [])
simplifyProps sc ss (p:ps) =
  do (a, p')  <- simplifyProp sc ss p
     (b, ps') <- simplifyProps sc ss ps
     return (a <> b, p' : ps')

-- | Add hypotheses from the given sequent as rewrite rules
--   to the given simpset.
localHypSimpset :: SharedContext -> Sequent -> [Integer] -> Simpset a -> IO (Simpset a)
localHypSimpset sc sqt hs ss0 = Fold.foldlM processHyp ss0 nhyps

  where
    processHyp ss (n,h) =
      ruleOfProp sc (unProp h) Nothing >>= \case
        Nothing -> fail $ "Hypothesis " ++ show n ++ "cannot be used as a rewrite rule."
        Just r  -> return (addRule r ss)

    nhyps = [ (n,h)
            | (n,h) <- zip [0..] hyps
            , Set.member n hset
            ]
    RawSequent hyps _ = sequentToRawSequent sqt
    hset = Set.fromList hs

-- | Rewrite in the sequent using the provided Simpset
simplifySequent :: Monoid a => SharedContext -> Simpset a -> Sequent -> IO (a, Sequent)
simplifySequent sc ss (UnfocusedSequent hs gs) =
  do (a, hs') <- simplifyProps sc ss hs
     (b, gs') <- simplifyProps sc ss gs
     return (a <> b, UnfocusedSequent hs' gs')
simplifySequent sc ss (ConclFocusedSequent hs (FB gs1 g gs2)) =
  do (a, g') <- simplifyProp sc ss g
     return (a, ConclFocusedSequent hs (FB gs1 g' gs2))
simplifySequent sc ss (HypFocusedSequent (FB hs1 h hs2) gs) =
  do (a, h') <- simplifyProp sc ss h
     return (a, HypFocusedSequent (FB hs1 h' hs2) gs)


hoistIfsInProp :: SharedContext -> Prop -> IO Prop
hoistIfsInProp sc (Prop p) = do
  let (vars, body) = asPiList p
  body' <-
    case asEqTrue body of
      Just t -> pure t
      Nothing -> fail "hoistIfsInProp: expected EqTrue"
  t1 <- hoistIfs sc body'
  t2 <- scEqTrue sc t1
  t3 <- scPiList sc vars t2
  return (Prop t3)

-- | Evaluate the given proposition by round-tripping
--   through the What4 formula representation.  This will
--   perform a variety of simplifications and rewrites.
evalProp :: SharedContext -> Bool -> Set VarIndex -> Prop -> IO Prop
evalProp sc what4PushMuxOps unints p =
  do let (vars, body) = asPiList (unProp p)
     body' <-
       case asEqTrue body of
         Just t -> pure t
         Nothing -> do
           p' <- ppTerm sc (unProp p)
           fail $ "goal_eval: expected EqTrue\n" ++ p'

     eb <- W4Sim.newSAWCoreExprBuilder sc what4PushMuxOps
     let st = eb ^. W4.userState
     (_names, (_mlabels, p')) <- W4Sim.w4Eval eb st sc mempty unints body'
     t1 <- W4Sim.toSC eb st p'
     t2 <- scEqTrue sc t1
     -- turn the free variables we generated back into pi-bound variables
     t3 <- scPiList sc vars t2
     return (Prop t3)

-- | Perform beta normalization on the given proposition.
betaReduceProp :: SharedContext -> Prop -> IO Prop
betaReduceProp sc (Prop tm) =
  do tm' <- betaNormalize sc tm
     return (Prop tm')

-- | Return the contant false proposition.
falseProp :: SharedContext -> IO Prop
falseProp sc = Prop <$> (scEqTrue sc =<< scBool sc False)

-- | Compute the shared-term size of the proposition.
propSize :: Prop -> Integer
propSize (Prop tm) = scSharedSize tm

trivialProofTerm :: SharedContext -> Prop -> IO (Either String Term)
trivialProofTerm sc (Prop p) = runExceptT (loop =<< lift (scWhnf sc p))
  where
    loop t =
      case asPi t of
        Just (nm, tp, body) ->
          do pf <- loop =<< lift (scWhnf sc body)
             lift $ scLambda sc nm tp pf
        Nothing ->
          case asEq t of
            Just (tp, x, _y) ->
              -- NB, we don't check if x is convertable to y here, as that will
              -- be done later in @tacticTrivial@ during the type-checking step
              lift $ scGlobalApply sc "Prelude.Refl" [tp, x]
            Nothing -> do
              p' <- lift $ ppTerm sc p
              throwError $ unlines
                [ "The trivial tactic can only prove quantified equalities, but"
                , "the given goal is not in the correct form."
                , p'
                ]

normalizeProp :: SharedContext -> Set VarIndex -> Prop -> IO Prop
normalizeProp sc opaqueSet (Prop tm) =
  do let unfold nm = Set.notMember (nameIndex nm) opaqueSet
     tm' <- scNormalize sc unfold tm
     termToProp sc tm'

-- | Pretty print the given proposition as a string.
ppProp :: PPS.Opts -> DisplayNameEnv -> Prop -> String
ppProp opts nenv p = PPS.render opts (prettyProp opts nenv p)

-- | Pretty print the given proposition as a @PPS.Doc@.
prettyProp :: PPS.Opts -> DisplayNameEnv -> Prop -> PPS.Doc
prettyProp opts nenv (Prop tm) = prettyTermWithEnv opts nenv tm

-- | Pretty print the given theorem as a @PPS.Doc@.
prettyTheorem :: PPS.Opts -> DisplayNameEnv -> Theorem -> PPS.Doc
prettyTheorem opts nenv thm
  | HashSet.null (thmHyps thm) = prettyProp opts nenv (thmProp thm)
  | otherwise =
    group $ vsep $
    [ group $
      encloseSep (flatAlt "{ " "{") (flatAlt " }" "}") ", " $
      map (prettyTermWithEnv opts nenv) (HashSet.toList (thmHyps thm))
    , "|-" <+> prettyProp opts nenv (thmProp thm)
    ]

-- TODO, I'd like to add metadata here
type SequentBranch = Prop

-- | The representation of either hypotheses or conclusions with a focus
--   point. A @FB xs y zs@ represents a collection of propositions
--   where @xs@ come before the focus point @y@, and @zs@ is the
--   collection of propositions following the focus point.
data FocusedBranch = FB ![SequentBranch] !SequentBranch ![SequentBranch]

-- | This datatype represents sequents in the style of Gentzen.  Sequents
--   are used to represent the intermediate states of a proof, and are the
--   primary objects manipulated by the proof tactic system.
--
--   A sequent essentially represents a logical claim which is in the process
--   of being proved.  A sequent has some (possibly 0) number of
--   "hypotheses" and some number (possibly 0) of "conclusions". In mathematical
--   notation, the hypotheses are separated from the conclusions by a turnstile
--   character, and the individual hypotheses and conclusions are separated from
--   each other by a comma. So, a typical sequent may look like:
--
--      H1, H2, H3, |- C1, C2
--
--   The logical meaning of a sequent is that the conjunction of all the hypotheses
--   implies the disjunction of the conclusions. The multi-conclusion form
--   of sequent (as is presented here) is typical of a classical logic.
--
--   In a Gentzen-style proof system (such as the sequent calculus), the method by
--   which proof proceeds is to apply inference rules. Each rule applies to a goal
--   sequent (the thing to be proved) and has 0 or more subgoals that must be proved
--   to apply the rule. Part of a proof is completed when a rule is applied which has 0
--   subgoals. When doing proofs in SAW using the tactic system, there is a stack of
--   currently outstanding proof goals (each in the form of a sequent to be proved).
--   Executing a tactic will modify or apply a proof rule to the top goal on the stack;
--   if that subgoal is finished, then the next subgoal becomes active.
--   If applying a rule causes more than one subgoal to be generated, the remaining
--   ones are pushed onto the stack of goals to be proved. An entire proof is completed
--   when the stack of outstanding goals to prove is empty.
--
--   This particular presentation of sequents is a "focused" sequent calculus.
--   This means that a sequent may optionally have a focus on a particular
--   hypothesis or conclusion. Some manipulations of sequents require a focus
--   point to indicate where some manipulation should be carried out, and others
--   will apply in both focused or unfocused states.
data Sequent
  = -- | A sequent in the unfocused state
    UnfocusedSequent   ![SequentBranch] ![SequentBranch]
    -- | A sequent focused on a particular conclusion
  | ConclFocusedSequent ![SequentBranch] !FocusedBranch
    -- | A sequent focused on a particular hypothesis
  | HypFocusedSequent  !FocusedBranch   ![SequentBranch]

-- | A RawSequent is a data-structure representing a sequent, but without
--   the ability to focus on a particular hypothesis or conclusion.
--
--   This data-structure is parametric in the type of propositions,
--   which enables some convenient patterns using traversals, etc.
data RawSequent a = RawSequent [a] [a]

instance Functor RawSequent where
  fmap f (RawSequent hs gs) = RawSequent (fmap f hs) (fmap f gs)
instance Foldable RawSequent where
  foldMap f (RawSequent hs gs) = Fold.foldMap f (hs ++ gs)
instance Traversable RawSequent where
  traverse f (RawSequent hs gs) = RawSequent <$> traverse f hs <*> traverse f gs

sequentToRawSequent :: Sequent -> RawSequent Prop
sequentToRawSequent sqt =
   case sqt of
     UnfocusedSequent   hs gs              -> RawSequent hs gs
     ConclFocusedSequent hs (FB gs1 g gs2) -> RawSequent hs (gs1 ++ g : gs2)
     HypFocusedSequent  (FB hs1 h hs2) gs  -> RawSequent (hs1 ++ h : hs2) gs

sequentConstantSet :: Sequent -> Map VarIndex NameInfo
sequentConstantSet sqt = foldr (\p m -> Map.union (getConstantSet (unProp p)) m) mempty (hs++gs)
  where
    RawSequent hs gs = sequentToRawSequent sqt

convertibleProps :: SharedContext -> [Prop] -> [Prop] -> IO Bool
convertibleProps _sc [] [] = return True
convertibleProps sc (p1:ps1) (p2:ps2) =
  do ok1 <- scConvertible sc (unProp p1) (unProp p2)
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


-- | A helper data structure for working with sequents when a focus
--   point is expected. When a conclusion or hypothesis is focused,
--   return the focused proposition; and return a function which
--   allows building a new sequent by replacing the proposition under
--   focus.
data SequentState
  = Unfocused
  | ConclFocus Prop (Prop -> Sequent)
  | HypFocus   Prop (Prop -> Sequent)

-- | Build a sequent with the given proposition as the
--   only conclusion, and place it under focus.
propToSequent :: Prop -> Sequent
propToSequent p = ConclFocusedSequent [] (FB [] p [])

-- | Given a sequent, render its semantics as a proposition.
--
--   Currently this can only handle sequents with 0 or 1 conclusion
--   (this is not a fundamental limitation, but we need a Prop-level disjunction
--   in SAWCore to fix this).
--
--   Given a sequent like @H1, H2 ..., Hn |- C@, this will build a corresponding
--   proposition @H1 -> H2 -> ... Hn -> C@. If the list of conclusions is empty,
--   the proposition will be @H1 -> H2 -> ... Hn -> False@.
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
ppSequent :: PPS.Opts -> DisplayNameEnv -> Sequent -> String
ppSequent opts nenv sqt = PPS.render opts (prettySequent opts nenv sqt)

-- | Pretty print the given proposition as a @PPS.Doc@.
prettySequent :: PPS.Opts -> DisplayNameEnv -> Sequent -> PPS.Doc
prettySequent opts nenv sqt =
  prettyTermContainerWithEnv
    (prettyRawSequent sqt)
    opts
    nenv
    (fmap unProp (sequentToRawSequent sqt))

prettyRawSequent :: Sequent -> RawSequent PPS.Doc -> PPS.Doc
prettyRawSequent _sqt (RawSequent [] [g]) = g
prettyRawSequent sqt (RawSequent hs gs)  =
  align (vcat (map ppHyp (zip [0..] hs) ++ turnstile ++ map ppConcl (zip [0..] gs)))
 where
  turnstile  = [ pretty (take 40 (repeat '=')) ]
  focused doc = "<<" <> doc <> ">>"
  ppHyp (i, tm)
    | HypFocusedSequent (FB hs1 _h _hs2) _gs <- sqt
    , length hs1 == i
    = focused ("H" <> pretty i) <+> tm

    | otherwise
    = "H" <> pretty i <> ":" <+> tm

  ppConcl (i, tm)
    | ConclFocusedSequent _hs (FB gs1 _g _gs2) <- sqt
    , length gs1 == i
    = focused ("C" <> pretty i) <+> tm

    | otherwise
    = "C" <> pretty i <> ":" <+> tm


-- | A datatype for representing finte or cofinite sets.
data CofinSet a
  = -- | A whitelist represents exactly the values in the given set
    WhiteList (Set a)
    -- | A blacklist represents all the values NOT found in the given set.
  | BlackList (Set a)

-- | Test for membership in a finite/cofinite set
cofinSetMember :: Ord a => a -> CofinSet a -> Bool
cofinSetMember a (WhiteList xs) = Set.member a xs
cofinSetMember a (BlackList xs) = not (Set.member a xs)

sequentState :: Sequent -> SequentState
sequentState (UnfocusedSequent _ _) = Unfocused
sequentState (ConclFocusedSequent hs (FB gs1 g gs2)) =
  ConclFocus g (\g' -> ConclFocusedSequent hs (FB gs1 g' gs2))
sequentState (HypFocusedSequent (FB hs1 h hs2) gs) =
  HypFocus h (\h' -> HypFocusedSequent (FB hs1 h' hs2) gs)

sequentSharedSize :: Sequent -> Integer
sequentSharedSize sqt = scSharedSizeMany (map unProp (hs ++ gs))
  where
   RawSequent hs gs = sequentToRawSequent sqt

sequentTreeSize :: Sequent -> Integer
sequentTreeSize sqt = scTreeSizeMany (map unProp (hs ++ gs))
  where
   RawSequent hs gs = sequentToRawSequent sqt

-- | Given an operation on propositions, apply the operation to the sequent.
--   If the sequent is focused, apply the operation just to the focused
--   hypothesis or conclusion. If the sequent is unfocused, apply the operation
--   to all the hypotheses and conclusions in the sequent.
traverseSequentWithFocus :: Applicative m => (Prop -> m Prop) -> Sequent -> m Sequent
traverseSequentWithFocus f (UnfocusedSequent hs gs) =
  UnfocusedSequent <$> traverse f hs <*> traverse f gs
traverseSequentWithFocus f (ConclFocusedSequent hs (FB gs1 g gs2)) =
  (\g' -> ConclFocusedSequent hs (FB gs1 g' gs2)) <$> f g
traverseSequentWithFocus f (HypFocusedSequent (FB hs1 h hs2) gs) =
  (\h' -> HypFocusedSequent (FB hs1 h' hs2) gs) <$> f h

-- | Typecheck a sequent.  This will typecheck all the terms
--   appearing in the sequent to ensure that they are propositions.
--   This check should always succeed, unless some programming
--   mistake has allowed us to build an ill-typed sequent.
checkSequent :: SharedContext -> Sequent -> IO ()
checkSequent sc (UnfocusedSequent hs gs) =
  do forM_ hs (checkProp sc)
     forM_ gs (checkProp sc)
checkSequent sc (ConclFocusedSequent hs (FB gs1 g gs2)) =
  do forM_ hs (checkProp sc)
     forM_ gs1 (checkProp sc)
     checkProp sc g
     forM_ gs2 (checkProp sc)
checkSequent sc (HypFocusedSequent (FB hs1 h hs2) gs) =
  do forM_ hs1 (checkProp sc)
     checkProp sc h
     forM_ hs2 (checkProp sc)
     forM_ gs  (checkProp sc)

-- | Check that a @Prop@ value is actually a proposition.
--   This check should always succeed, unless some programming
--   mistake has allowed us to build an ill-typed Prop.
checkProp :: SharedContext -> Prop -> IO ()
checkProp sc (Prop t) =
  do ty <- scTypeOf sc t
     case asSort ty of
        Just s | s == propSort -> return ()
        _ -> do
          t' <- ppTerm sc t
          ty' <- ppTerm sc ty
          fail $ unlines ["Term is not a prop!", t', ty']

-- | Type 'Hypotheses' represents a side condition on a theorem:
-- It is a set of types that are all assumed to be inhabited.
type Hypotheses = HashSet Term

termHypotheses :: Term -> Hypotheses
termHypotheses t = HashSet.fromList (IntMap.elems (varTypes t))

propHypotheses :: Prop -> Hypotheses
propHypotheses p = termHypotheses (unProp p)

rawSequentHypotheses :: RawSequent Prop -> Hypotheses
rawSequentHypotheses (RawSequent hs gs) =
  Fold.foldMap propHypotheses (hs ++ gs)

sequentHypotheses :: Sequent -> Hypotheses
sequentHypotheses sqt = rawSequentHypotheses (sequentToRawSequent sqt)

type TheoremNonce = Nonce GlobalNonceGenerator Theorem

-- | A theorem is a proposition which has been wrapped in a
--   constructor indicating that it has already been proved,
--   and contains @Evidence@ for its truth.
data Theorem =
  Theorem
  { _thmProp :: Prop
  , _thmHyps :: Hypotheses -- ^ Types assumed to be inhabited.
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

-- | A theorem database is intended to track theorems that may be used
--   in the proof of later theorems or verification conditions. This is
--   ultimately used to produce verification summaries, which capture
--   the dependency graph between theorems and verifications.
data TheoremDB =
  TheoremDB
  -- TODO, maybe this should be a summary or something simpler?
  { theoremMap :: Map TheoremNonce Theorem
  }

emptyTheoremDB :: TheoremDB
emptyTheoremDB = TheoremDB mempty

recordTheorem :: TheoremDB -> Theorem -> TheoremDB
recordTheorem db thm@Theorem{ _thmNonce = n } = TheoremDB (Map.insert n thm (theoremMap db))

-- | Given a set of root values, find all the theorems in this database
--   that are transitively used in the proofs of those theorems.
--   This function will panic if any of the roots or reachable theorems
--   are not found in the database.
reachableTheorems :: TheoremDB -> Set TheoremNonce -> Map TheoremNonce Theorem
reachableTheorems db roots = Set.foldl' (loop (theoremMap db)) mempty roots

 where
   loop m visited curr
     | Just _ <- Map.lookup curr visited = visited

     | Just thm <- Map.lookup curr m =
         Set.foldl' (loop m)
            (Map.insert curr thm visited)
            (thmDepends thm)

     | otherwise =
         let curr' = Text.pack (show (indexValue curr))
             m' = map (\(k, _v) -> Text.pack (show k)) $ Map.toList m
         in
         panic "reachableTheorems" [
             "Could not find theorem with identifier: " <> curr',
             "Theorems in database: " <> Text.intercalate " " m'
         ]


-- | Check that the purported theorem is valid.
--
--   This validates that the included evidence actually supports
--   the proposition.  Note, however, this validation procedure
--   does not totally guarantee the theorem is true, as it does
--   not verify any solver-provided proofs, and it accepts admitted
--   propositions and quickchecked propositions as valid.
validateTheorem :: SharedContext -> Bool -> TheoremDB -> Theorem -> IO ()

validateTheorem sc what4PushMuxOps db Theorem{ _thmProp = p, _thmEvidence = e, _thmDepends = thmDep } =
   do let knownThms = Map.keysSet (theoremMap db)
      (deps, _, hyps) <- checkEvidence sc what4PushMuxOps e p
      unless (Set.isSubsetOf deps thmDep && Set.isSubsetOf thmDep knownThms)
             (fail $ unlines ["Theorem failed to declare its dependencies correctly"
                             , show deps, show thmDep ])
      ppHyps <- traverse (ppTerm sc) (HashSet.toList hyps)
      unless (HashSet.null hyps) $
        fail $ unlines $ ["Theorem depends on undischarged hypotheses:"] ++ ppHyps

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

-- | When a 'Theorem' is converted to a rewrite rule, it is tagged
-- with a 'TheoremAnnotation' that records dependencies that will be
-- collected and combined as rewrite rules are applied.
data TheoremAnnotation =
  TheoremAnnotation (Set TheoremNonce) Hypotheses TheoremSummary

instance Semigroup TheoremAnnotation where
  TheoremAnnotation d1 h1 s1 <> TheoremAnnotation d2 h2 s2 =
    TheoremAnnotation (d1 <> d2) (h1 <> h2) (s1 <> s2)

instance Monoid TheoremAnnotation where
  mempty = TheoremAnnotation mempty mempty mempty

-- | This datatype records evidence for the truth of a proposition.
data Evidence
  = -- | The given term provides a direct programs-as-proofs witness
    --   for the truth of its type (qua proposition). This will
    --   succeed when applied to sequent with a conclusion focus whose
    --   statement matches the type of the given term.
    ProofTerm !Term

    -- | This type of evidence is produced when the given sequent
    --   has been dispatched to a solver which has indicated that it
    --   was able to prove the sequent. The included @SolverStats@
    --   give some details about the solver run.
  | SolverEvidence !SolverStats !Sequent

    -- | This type of evidence is produced when the given sequent
    --   has been randomly tested against input vectors in the style
    --   of quickcheck. The included number is the number of successfully
    --   passed test vectors.
  | QuickcheckEvidence !Integer !Sequent

    -- | This type of evidence is produced when the given sequent
    --   has been explicitly assumed without other evidence, at the
    --   user's direction.
  | Admitted !Text !Pos !Sequent

    -- | This type of evidence is produced when a previously-proved
    --   theorem is applied via backward reasoning to prove a focused
    --   conclusion.  Pi-quantified variables of the theorem may be
    --   specialized either by giving an explicit @Term@ to
    --   instantiate the variable, or by giving @Evidence@ for @Prop@
    --   hypotheses. After specializing the given @Theorem@ the
    --   result must match the current focued conclusion.
  | ApplyEvidence !Theorem ![Either Term Evidence]

    -- | This type of evidence is used to prove a universally-quantified conclusion.
    --   The included 'VarName' should be a fresh variable used to instantiate the
    --   quantified proposition.
  | IntroEvidence !VarName !Term !Evidence

    -- | This type of evidence is used to modify a sequent to prove via
    --   rewriting. The sequent is rewritten by the given
    --   simpset; then the provided evidence is used to check the
    --   modified sequent. The list of integers indicate local
    --   hypotheses that should also be treated as rewrite rules.
  | RewriteEvidence ![Integer] !(Simpset TheoremAnnotation) !Evidence

    -- | This type of evidence is used to modify a sequent via unfolding
    --   constant definitions.  The sequent is modified by unfolding
    --   constants identified via the given set of @VarIndex@; then the provided
    --   evidence is used to check the modified sequent.
  | UnfoldEvidence !(Set VarIndex) !Evidence

    -- | This type of evidence is used to modify a sequent via unfolding fixpoint
    --   constant definitions once.  The sequent is modified by unfolding
    --   constants identified via the given set of @VarIndex@; then the provided
    --   evidence is used to check the modified sequent.
  | UnfoldFixOnceEvidence !(Set VarIndex) !Evidence

    -- | This type of evidence is used to modify a sequent via evaluation
    --   into the the What4 formula representation. During evaluation, the
    --   constants identified by the given set of @VarIndex@ are held
    --   uninterpreted (i.e., will not be unfolded).  Then, the provided
    --   evidence is use to check the modified sequent.
  | EvalEvidence !(Set VarIndex) !Evidence

    -- | This type of evidence is used to modify a focused part of the sequent.
    --   The modified sequent should be equivalent up to conversion.
  | ConversionEvidence !Sequent !Evidence

    -- | This type of evidence is used to modify a goal to prove by applying
    --   'hoistIfsInProp'.
  | HoistIfsEvidence !Evidence

    -- | Change the state of the sequent by invoking the term evaluator
    --   on the focused sequent branch (or all branches, if unfocused).
    --   Treat the given variable indexes as opaque.
  | NormalizePropEvidence !(Set VarIndex) !Evidence

-- | The the proposition proved by a given theorem.
thmProp :: Theorem -> Prop
thmProp Theorem{ _thmProp = p } = p

-- | The hypotheses assumed by a given theorem.
thmHyps :: Theorem -> Hypotheses
thmHyps Theorem{ _thmHyps = hyps } = hyps

-- | Retrieve any solver stats from the proved theorem.
thmStats :: Theorem -> SolverStats
thmStats Theorem{ _thmStats = stats } = stats

-- | Retrive the evidence associated with this theorem.
thmEvidence :: Theorem -> Evidence
thmEvidence Theorem{ _thmEvidence = e } = e

-- | The SAW source location that generated this theorem
thmLocation :: Theorem -> Pos
thmLocation Theorem{ _thmLocation = loc } = loc

-- | The program location (if any) of the program under
--   verification giving rise to this theorem
thmProgramLoc :: Theorem -> Maybe ProgramLoc
thmProgramLoc Theorem{ _thmProgramLoc = ploc } = ploc

-- | Describes the reason this theorem was generated
thmReason :: Theorem -> Text
thmReason Theorem{ _thmReason = r } = r

-- | Returns a unique identifier for this theorem
thmNonce :: Theorem -> TheoremNonce
thmNonce Theorem{ _thmNonce = n } = n

-- | Returns the set of theorem identifiers that this theorem depends on
thmDepends :: Theorem -> Set TheoremNonce
thmDepends Theorem { _thmDepends = s } = s

-- | Returns the amount of time elapsed during the proof of this theorem
thmElapsedTime :: Theorem -> NominalDiffTime
thmElapsedTime Theorem{ _thmElapsedTime = tm } = tm

thmSummary :: Theorem -> TheoremSummary
thmSummary Theorem { _thmSummary = sy } = sy

introEvidence :: VarName -> Term -> [Evidence] -> IO Evidence
introEvidence x t [e] = pure (IntroEvidence x t e)
introEvidence _ _ _ = fail "introEvidence: expected one evidence value"

-- | Construct a theorem directly via a proof term.
proofByTerm :: SharedContext -> TheoremDB -> Term -> Pos -> Text -> IO (Theorem, TheoremDB)
proofByTerm sc db prf loc rsn =
  do ty <- scTypeOf sc prf
     p  <- termToProp sc ty
     n  <- freshNonce globalNonceGenerator
     let thm =
          Theorem
          { _thmProp      = p
          , _thmHyps      = termHypotheses prf
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
     let db' = recordTheorem db thm
     pure (thm, db')

-- | Construct a theorem directly from a proposition and evidence
--   for that proposition.  The evidence will be validated to
--   check that it supports the given proposition; if not, an
--   error will be raised.
constructTheorem ::
  SharedContext ->
  Bool ->
  TheoremDB ->
  Prop ->
  Evidence ->
  Pos ->
  Maybe ProgramLoc ->
  Text ->
  NominalDiffTime ->
  IO (Theorem, TheoremDB)
constructTheorem sc what4PushMuxOps db p e loc ploc rsn elapsed =
  do (deps, sy, hyps) <- checkEvidence sc what4PushMuxOps e p
     n  <- freshNonce globalNonceGenerator
     let thm =
          Theorem
          { _thmProp  = p
          , _thmHyps = hyps
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
     let db' = recordTheorem db thm
     pure (thm, db')


-- | Given a theorem with quantified variables, build a new theorem that
--   specializes the leading quantifiers with the given terms.
--   This will fail if the given terms to not match the quantifier structure
--   of the given theorem.
specializeTheorem :: SharedContext -> Bool -> TheoremDB -> Pos -> Text -> Theorem -> [Term] -> IO (Theorem, TheoremDB)
specializeTheorem _sc _what4PushMuxOps db _loc _rsn thm [] = return (thm, db)
specializeTheorem sc what4PushMuxOps db loc rsn thm ts =
  do res <- specializeProp sc (_thmProp thm) ts
     case res of
       Left err -> do
         err' <- prettyTermError sc err
         ppopts <- scGetPPOpts sc
         fail $ PPS.render ppopts $ PP.vsep [
             "specialize_theorem: failed to specialize",
             err'
          ]
       Right p' ->
         constructTheorem sc what4PushMuxOps db p' (ApplyEvidence thm (map Left ts)) loc Nothing rsn 0

specializeProp :: SharedContext -> Prop -> [Term] -> IO (Either TC.TermError Prop)
specializeProp sc (Prop p0) ts0 =
  do x <- scFreshVarName sc "_"
     t0 <- scVariable sc x p0
     TC.runSCM sc (loop t0 ts0)
 where
  loop p [] = Prop <$> TC.scmTypeOf p
  loop p (t:ts) =
    do p' <- TC.scmApply p t
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
  IO (Theorem, TheoremDB)
admitTheorem db msg p loc rsn =
  do n  <- freshNonce globalNonceGenerator
     let thm =
          Theorem
          { _thmProp        = p
          , _thmHyps        = propHypotheses p
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
     let db' = recordTheorem db thm
     pure (thm, db')

-- | Construct a theorem that an external solver has proved.
solverTheorem ::
  TheoremDB ->
  Prop ->
  SolverStats ->
  Pos ->
  Text ->
  NominalDiffTime ->
  IO (Theorem, TheoremDB)
solverTheorem db p stats loc rsn elapsed =
  do n  <- freshNonce globalNonceGenerator
     let thm =
          Theorem
          { _thmProp      = p
          , _thmHyps      = propHypotheses p
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
     let db' = recordTheorem db thm
     pure (thm, db')

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
  , goalSequent :: !Sequent
  }


data Quantification = Existential | Universal
  deriving Eq


-- | Convert a term with a function type of any arity into a pi type.
-- Negate the term if the result type is @Bool@ and the quantification
-- is 'Existential'.
predicateToProp :: SharedContext -> Quantification -> Term -> IO Prop
predicateToProp sc quant = loop
  where
  loop t =
    case asLambda t of
      Just (x, ty, body) ->
        do Prop body' <- loop body
           Prop <$> scPi sc x ty body'
      Nothing ->
        do (argTs, resT) <- asPiList <$> scTypeOf sc t
           let toPi env [] t0 =
                 case asBoolType resT of
                   Nothing -> do
                       resT' <- ppTerm sc resT
                       fail $ unlines [
                           "predicateToProp : Expected boolean result type but got",
                           resT'
                        ]
                   Just () ->
                     case quant of
                       Universal -> scEqTrue sc =<< scInstantiate sc env t0
                       Existential -> scEqTrue sc =<< scNot sc =<< scInstantiate sc env t0
               toPi env ((x, xT) : tys) t1 =
                 do x' <- scFreshVarName sc (vnName x)
                    xT' <- scInstantiate sc env xT
                    v <- scVariable sc x' xT'
                    t2 <- scApply sc t1 v
                    t3 <- toPi (IntMap.insert (vnIndex x) v env) tys t2
                    scPi sc x' xT' t3
           Prop <$> toPi IntMap.empty argTs t


-- | A ProofState consists of a sequence of goals, each represented by a sequent.
--   If each subgoal is provable, that implies the ultimate conclusion.
data ProofState =
  ProofState
  { _psGoals :: ![ProofGoal]
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
  -- For each x, check if x exists in ps2 by checking term identity using stAppIndex
  -- If the check succeeds, return True. Otherwise use propsElem to do the more expensive
  -- convertibility check.
  and <$> sequence [ if idSubset (unProp x) then pure True else propsElem sc x ps2 | x <- ps1 ]
  where
    ps2Ids = foldr (\x ids -> Set.insert (termIndex (unProp x)) ids) Set.empty ps2
    idSubset t = Set.member (termIndex t) ps2Ids

-- exists y in ps where x == y
propsElem :: SharedContext -> Prop -> [Prop] -> IO Bool
propsElem sc x ps =
  or <$> sequence [ scConvertible sc (unProp x) (unProp y) | y <- ps ]

-- | Test if the first given sequent subsumes the
--   second given sequent. This is a shallow syntactic
--   check that is sufficient to show that a proof
--   of the first sequent is sufficient to prove the second
sequentSubsumes :: SharedContext -> Sequent -> Sequent -> IO Bool
sequentSubsumes sc sqt1 sqt2 =
  do let s1 = sequentToRawSequent sqt1
     let s2 = sequentToRawSequent sqt2
     rawSequentSubsumes sc s1 s2

-- | Tests that the first raw sequent subsumes the second.
-- This is a shallow syntactic check that is sufficient to show that a proof
-- of the first sequent is sufficient to prove the second
rawSequentSubsumes :: SharedContext -> RawSequent Prop -> RawSequent Prop -> IO Bool
rawSequentSubsumes sc (RawSequent hs1 gs1) (RawSequent hs2 gs2) =
  do hypsOK  <- propsSubset sc hs1 hs2 -- assumes no *more*
     conclOK <- propsSubset sc gs2 gs1 -- proves no *less*
     return (hypsOK && conclOK)

-- | Verify that the given evidence in fact supports the given proposition.
--   Returns the identifiers of all the theorems depended on while checking evidence
--   Also return the context of all types assumed to be inhabited.
checkEvidence ::
  SharedContext -> Bool -> Evidence -> Prop ->
  IO (Set TheoremNonce, TheoremSummary, Hypotheses)
checkEvidence sc what4PushMuxOps = \e p -> do
                              nenv <- scGetNamingEnv sc
                              check nenv e (propToSequent p)

  where
    checkApply _nenv _mkSqt (Prop p) [] = return (mempty, mempty, p, termHypotheses p)

    -- Check a theorem applied to "Evidence".
    -- The given prop must be an implication
    -- (i.e., nondependent Pi quantifying over a Prop)
    -- and the given evidence must match the expected prop.
    checkApply nenv mkSqt (Prop p) (Right e:es)
      | Just (lnm, tp, body) <- asPi p
      , IntSet.notMember (vnIndex lnm) (freeVars body)
      = do (d1, sy1, hyps1) <- check nenv e . mkSqt =<< termToProp sc tp
           (d2, sy2, p', hyps2) <- checkApply nenv mkSqt (Prop body) es
           return (Set.union d1 d2, sy1 <> sy2, p', hyps1 <> hyps2)
      | otherwise = do
           p' <- ppTerm sc p
           fail $ unlines [
               "Apply evidence mismatch: non-function or dependent function",
               p'
            ]

    -- Check a theorem applied to a term. This explicitly instantiates
    -- a Pi binder with the given term.
    checkApply nenv mkSqt (Prop p) (Left tm:es) =
      do p1 <- reducePi sc p tm
         (deps, sy, p2, hyps) <- checkApply nenv mkSqt (Prop p1) es
         pure (deps, sy, p2, hyps <> termHypotheses tm)

    check ::
      DisplayNameEnv ->
      Evidence ->
      Sequent ->
      IO (Set TheoremNonce, TheoremSummary, HashSet Term)
    check nenv e sqt = case e of
      ProofTerm tm ->
        case sequentState sqt of
          ConclFocus (Prop ptm) _ ->
            do ty <- scTypeOf sc tm
               ok <- scConvertible sc ptm ty
               unless ok $ do
                   ptm' <- ppTerm sc ptm
                   tm' <- ppTerm sc tm
                   fail $ unlines [
                       "Proof term does not prove the required proposition",
                       ptm',
                       tm'
                    ]
               return (mempty, ProvedTheorem mempty, termHypotheses tm)
          _ -> fail "Sequent must be conclusion-focused for proof term evidence"

      SolverEvidence stats sqt' ->
        do ok <- sequentSubsumes sc sqt' sqt
           unless ok $ do
             ppopts <- scGetPPOpts sc
             fail $ PPS.render ppopts $ PP.vsep
               [ "Solver proof does not prove the required sequent"
               , prettySequent ppopts nenv sqt
               , prettySequent ppopts nenv sqt'
               ]
           return (mempty, ProvedTheorem stats, sequentHypotheses sqt')

      Admitted msg pos sqt' ->
        do ok <- sequentSubsumes sc sqt' sqt
           unless ok $ do
             ppopts <- scGetPPOpts sc
             let pos' = prettyPosition pos
             fail $ PPS.render ppopts $ PP.vsep
               [ "Admitted proof does not match the required sequent" <+> pos'
               , pretty msg
               , prettySequent ppopts nenv sqt
               , prettySequent ppopts nenv sqt'
               ]
           return (mempty, AdmittedTheorem msg, sequentHypotheses sqt')

      QuickcheckEvidence n sqt' ->
        do ok <- sequentSubsumes sc sqt' sqt
           unless ok $ do
             ppopts <- scGetPPOpts sc
             fail $ PPS.render ppopts $ PP.vsep
               [ "Quickcheck evidence does not match the required sequent"
               , prettySequent ppopts nenv sqt
               , prettySequent ppopts nenv sqt'
               ]
           return (mempty, TestedTheorem n, sequentHypotheses sqt')

      ApplyEvidence thm es ->
        case sequentState sqt of
          ConclFocus p mkSqt ->
            do (d, sy, p', hyps) <- checkApply nenv mkSqt (thmProp thm) es
               ok <- scConvertible sc (unProp p) p'
               unless ok $ do
                   sp <- ppTerm sc (unProp p)
                   sp' <- ppTerm sc p'
                   fail $ unlines [
                       "Apply evidence does not match the required proposition",
                       sp,
                       sp'
                    ]
               return (Set.insert (thmNonce thm) d, sy, thmHyps thm <> hyps)
          _ -> do
              ppopts <- scGetPPOpts sc
              fail $ PPS.render ppopts $ PP.vsep
                    [ "Apply evidence requires a conclusion-focused sequent"
                    , prettySequent ppopts nenv sqt
                    ]

      UnfoldEvidence vars e' ->
        do sqt' <- traverseSequentWithFocus (unfoldProp sc vars) sqt
           check nenv e' sqt'

      UnfoldFixOnceEvidence vars e' ->
        do sqt' <- traverseSequentWithFocus (unfoldFixOnceProp sc vars) sqt
           check nenv e' sqt'

      NormalizePropEvidence opqueSet e' ->
        do sqt' <- traverseSequentWithFocus (normalizeProp sc opqueSet) sqt
           check nenv e' sqt'

      RewriteEvidence hs ss e' ->
        do ss' <- localHypSimpset sc sqt hs ss
           (TheoremAnnotation d1 h1 s1, sqt') <- simplifySequent sc ss' sqt
           (d2, s2, h2) <- check nenv e' sqt'
           return (d1 <> d2, s1 <> s2, h1 <> h2)

      HoistIfsEvidence e' ->
        do sqt' <- traverseSequentWithFocus (hoistIfsInProp sc) sqt
           check nenv e' sqt'

      EvalEvidence vars e' ->
        do sqt' <- traverseSequentWithFocus (evalProp sc what4PushMuxOps vars) sqt
           check nenv e' sqt'

      ConversionEvidence sqt' e' ->
        do ok <- convertibleSequents sc sqt sqt'
           unless ok $ do
               ppopts <- scGetPPOpts sc
               fail $ PPS.render ppopts $ PP.vsep [
                   "Converted sequent does not match goal",
                   prettySequent ppopts nenv sqt,
                   prettySequent ppopts nenv sqt'
                ]
           check nenv e' sqt'

      IntroEvidence x xty e' ->
        -- TODO! Check that the given VarName is fresh for the sequent.
        --
        --   On soundness: I am concerned that just checking that 'x' is fresh for 'sqt'
        --   isn't enough, as 'x' may nonetheless appear in other values in the ambient
        --   context, such as defined constants, or in the type of other things, etc.
        --
        --   The most reliable way to actually do this freshness check, then, is to produce
        --   a brand-new guaranteed fresh value (call it 'y') and replace 'x' with 'y'
        --   everywhere in the remaining evidence checking process. This is going to require
        --   quite a bit of additional infrastructure to do the necessary replacements, and we
        --   will need to be pretty careful if we want to avoid repeated traversals (which
        --   could cause substantial performance issues).
        case sequentState sqt of
          Unfocused -> fail "Intro evidence requires a focused sequent"
          HypFocus _ _ -> fail "Intro evidence apply in hypothesis"
          ConclFocus (Prop ptm) mkSqt ->
            case asPi ptm of
              Nothing -> do
                  ptm' <- ppTerm sc ptm
                  fail $ unlines ["Intro evidence expected function prop", ptm']
              Just (nm, ty, body) ->
                do ok <- scConvertible sc ty xty
                   unless ok $ do
                       xty' <- ppTerm sc xty
                       ty' <- ppTerm sc ty
                       fail $ unlines [
                           "Intro evidence types do not match",
                           xty',
                           ty'
                        ]
                   x' <- scVariable sc x xty
                   body' <- scInstantiate sc (IntMap.singleton (vnIndex nm) x') body
                   (deps, sy, hyps) <- check nenv e' (mkSqt (Prop body'))
                   let hyps' = HashSet.delete xty hyps
                   pure (deps, sy, hyps')

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
--
--   If first boolean argument is @False@, the resulting theorem will not be
--   recorded in the theorem database. This should only be done when you are
--   sure that the theorem will not be used as part of the proof of other theorems,
--   or later steps will fail. This is intended for proofs of verification conditions,
--   which are not exposed for reuse, and where it requires a significant memory
--   burden to record them. In particular commands like @llvm_verify@, @jvm_verify@, etc
--   that produce and verify verification conditions should set this argument to
--   @False@ to reduce memory pressure.
--
--   The final boolean argument indicates if the proof state needs a sequent normalization
--   step as the final step in its evidence chain to check.  This is useful for goals that
--   start with a nontrivial sequent (e.g., when enable_sequent_goals is turned on). For some
--   goals, this step is expensive, so we avoid it unless necessary.
finishProof ::
  SharedContext ->
  TheoremDB ->
  Prop ->
  ProofState ->
  Bool {- ^ should we record the theorem in the database? -} ->
  Bool {- ^ If 'True', push certain @ExprBuilder@ operations (e.g., @zext@) down
            to the branches of @ite@ expressions -} ->
  IO (ProofResult, TheoremDB)
finishProof sc db conclProp
    ps@(ProofState gs (_concl,loc,ploc,rsn) stats _ checkEv start)
    recordThm what4PushMuxOps =
  case gs of
    [] ->
      do e <- checkEv []
         (deps, sy, hyps) <- checkEvidence sc what4PushMuxOps e conclProp
         -- Fail if hyps includes any types that do not correspond to a
         -- free variable in the conclusion
         let extraHyps = HashSet.difference hyps (propHypotheses conclProp)
         ppHyps <- traverse (ppTerm sc) (HashSet.toList extraHyps)
         unless (HashSet.null extraHyps) $
           fail $ unlines $ ["Theorem depends on undischarged hypotheses:"] ++ ppHyps
         n <- freshNonce globalNonceGenerator
         end <- getCurrentTime
         let theorem =
                   Theorem
                   { _thmProp = conclProp
                   , _thmHyps = hyps
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
         let db' = if recordThm then recordTheorem db theorem else db
         pure (ValidProof stats theorem, db')
    _ : _ ->
         pure (UnfinishedProof ps, db)

-- | Run the given 'ProofScript' as a subproof starting from a proof
-- state where only the first subgoal is visible.
-- The inner proof script must discharge its goal, leaving no
-- remaining subgoals; otherwise the outer proof fails.
subProof :: (MonadFail m, MonadIO m, MonadState ProofState m) => m () -> m ()
subProof action =
  do ProofState goals concl stats timeout evidenceCont start <- get
     case goals of
       [] -> fail "subproof: No subgoals"
       g1 : gs ->
         do let substate = ProofState [g1] concl stats timeout passthroughEvidence start
            put substate
            action
            ProofState unfinishedGoals _ _ _ cont _ <- get
            unless (null unfinishedGoals) $
              fail $ "subproof: Unfinished: " ++ show (length unfinishedGoals) ++ " goals remaining"
            e <- liftIO $ cont []
            let evidenceCont' es = evidenceCont (e : es)
            put (ProofState gs concl stats timeout evidenceCont' start)

-- | A type describing counterexamples.
type CEX = [(VarName, FirstOrderValue)]

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

-- | Print a `CEX`
prettyCEX :: PPS.Opts -> CEX -> PPS.Doc
prettyCEX opts cex =
    let once (x, v) =
          let x' = PP.pretty $ vnName x
              v' = prettyFirstOrderValue opts v
          in
          PP.nest 2 (x' <+> "=" <> PP.group (PP.line <> v'))
    in
    PP.vsep $ map once cex

-- | Print a `ProofResult`
prettyProofResult :: PPS.Opts -> ProofResult -> PPS.Doc
prettyProofResult opts r = case r of
    ValidProof _ _ ->
        "Valid"
    InvalidProof _ ts _
        | null ts -> "Invalid: []"
        | otherwise ->
            let ts' = prettyCEX opts ts in
            PP.vsep ["Invalid: [", PP.indent 3 ts', "]"]
    UnfinishedProof st ->
        let n' = PP.viaShow (length $ psGoals st) in
        "Unfinished:" <+> n' <+> "goals remaining"

-- | Print a `ProofResult` as `Text`
ppProofResult :: PPS.Opts -> ProofResult -> Text
ppProofResult opts r =
    PPS.renderText opts $ prettyProofResult opts r

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
              let ps' = ProofState (gs' <> gs) concl (stats <> stats') timeout evidenceCont' start
              seq ps' (return (Right (x, ps')))

predicateToSATQuery :: SharedContext -> Set VarIndex -> Term -> IO SATQuery
predicateToSATQuery sc unintSet tm0 =
    do mmap <- scGetModuleMap sc
       (initVars, abstractVars) <- filterFirstOrderVars mmap mempty mempty (getAllVars tm0)
       (finalVars, tm') <- processTerm mmap initVars tm0
       return SATQuery
              { satVariables = finalVars
              , satUninterp  = Set.union unintSet abstractVars
              , satAsserts   = [BoolAssert tm']
              }
  where
    evalFOT mmap t =
      asFirstOrderTypeValue (evalSharedTerm mmap mempty mempty t)

    filterFirstOrderVars _ fovars absvars [] = pure (fovars, absvars)
    filterFirstOrderVars mmap fovars absvars ((x, t) : es) =
      case evalFOT mmap t of
        Nothing  -> filterFirstOrderVars mmap fovars (Set.insert (vnIndex x) absvars) es
        Just fot -> filterFirstOrderVars mmap (Map.insert x fot fovars) absvars es

    processTerm mmap vars tm =
      case asLambda tm of
        Just (nm, tp, body) ->
          case evalFOT mmap tp of
            Nothing -> do
              tp' <- ppTerm sc tp
              fail ("predicateToSATQuery: expected first order type: " ++ tp')
            Just fot ->
              processTerm mmap (Map.insert nm fot vars) body

          -- TODO: check that the type is a boolean
        Nothing ->
          do ty <- scTypeOf sc tm
             ok <- scConvertible sc ty =<< scBoolType sc
             unless ok $ do
               ty' <- ppTerm sc ty
               tm0' <- ppTerm sc tm0
               fail $ unlines [
                   "predicateToSATQuery: expected boolean result but got:",
                   ty',
                   tm0'
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
       let frees = foldMap getAllVarsMap (map unProp (hs ++ gs))
       (initVars, abstractVars) <- filterFirstOrderVars mmap mempty mempty (Map.toList frees)
       -- NB, the following reversals make the order of assertions more closely match the input sequent,
       -- but should otherwise not be semantically relevant
       hypAsserts <- mapM (processAssert mmap) (reverse (map unProp hs))
       (finalVars, asserts) <- foldM (processConcl mmap) (initVars, hypAsserts) (map unProp gs)
       return SATQuery
              { satVariables = finalVars
              , satUninterp  = Set.union unintSet abstractVars
              , satAsserts   = asserts
              }

  where
    evalFOT mmap t =
      asFirstOrderTypeValue (evalSharedTerm mmap mempty mempty t)

    filterFirstOrderVars _ fovars absvars [] = pure (fovars, absvars)
    filterFirstOrderVars mmap fovars absvars ((x, t) : es) =
      case evalFOT mmap t of
         Nothing  -> filterFirstOrderVars mmap fovars (Set.insert (vnIndex x) absvars) es
         Just fot -> filterFirstOrderVars mmap (Map.insert x fot fovars) absvars es

    processAssert mmap tp =
      case asEqTrue tp of
        Just x -> return (BoolAssert x)
        _ -> processUnivAssert mmap [] [] tp

    processUnivAssert mmap vars xs tm =
      do -- TODO: See related TODO in processConcl
         let tm' = tm

         case asPi tm' of
           Just (nm, tp, body) ->
             do -- TODO, same issue
                let tp' = tp
                case evalFOT mmap tp' of
                  Just fot ->
                    processUnivAssert mmap ((nm, fot) : vars) xs body
                  Nothing
                    | IntSet.null (foldr IntSet.delete (freeVars body) (map (vnIndex . fst) vars)) ->
                      case asEqTrue tp' of
                        Just x  -> processUnivAssert mmap vars (x:xs) body
                        Nothing -> do
                          tp'' <- ppTerm sc tp'
                          fail ("sequentToSATQuery: expected first order type or assertion:\n" ++ tp'')
                    | otherwise -> do
                        tp'' <- ppTerm sc tp'
                        fail ("sequentToSATQuery: expected first order type or assertion:\n" ++ tp'')

           Nothing ->
             case asEqTrue tm' of
               Nothing -> do
                 tm'' <- ppTerm sc tm'
                 fail $ "sequentToSATQuery: expected EqTrue, actual:\n" ++ tm''
               Just tmBool -> return (UniversalAssert (reverse vars) (reverse xs) tmBool)

    processConcl mmap (vars,xs) tm =
      do -- TODO: I would like to WHNF here, but that evaluates too aggressively
         -- because scWhnf evaluates strictly through the `Eq` datatype former.
         -- This breaks some proof examples by unfolding things that need to
         -- be uninterpreted.
         -- tm' <- scWhnf sc tm
         let tm' = tm

         case asPi tm' of
           Just (nm, tp, body) ->
             do -- same issue with WHNF
                -- tp' <- scWhnf sc tp
                let tp' = tp
                case evalFOT mmap tp' of
                  Just fot ->
                    processConcl mmap (Map.insert nm fot vars, xs) body
                  Nothing
                    | IntSet.null (foldr IntSet.delete (freeVars body) (map vnIndex (Map.keys vars))) ->
                        do asrt <- processAssert mmap tp
                           processConcl mmap (vars, asrt : xs) body
                    | otherwise -> do
                        tp'' <- ppTerm sc tp'
                        fail ("sequentToSATQuery: expected first order type or assertion:\n" ++ tp'')

           Nothing ->
             case asEqTrue tm' of
               Nothing -> do
                   tm'' <- ppTerm sc tm'
                   fail $ "sequentToSATQuery: expected EqTrue, actual:\n" ++ tm''
               Just tmBool ->
                 do tmNeg <- scNot sc tmBool
                    return (vars, reverse (BoolAssert tmNeg : xs))

-- | Given a prop to prove, attempt to apply another given proposition, producing
--   new subgoals for any necessary hypotheses of the proposition.  Returns
--   @Nothing@ if the given proposition does not apply to the goal.
propApply ::
  SharedContext ->
  Prop {- ^ propsition to apply (usually a quantified and/or implication term) -} ->
  Prop {- ^ goal to apply the proposition to -} ->
  IO (Maybe [Either Term Prop])
propApply sc rule goal = applyFirst (asPiLists (unProp rule))
  where
    applyFirst :: [([(VarName, Term)], Term)] -> IO (Maybe [Either Term Prop])
    applyFirst [] = pure Nothing
    applyFirst ((ruleArgs, ruleConcl) : rest) =
      do result <- scMatch sc ruleArgs ruleConcl (unProp goal)
         case result of
           Nothing -> applyFirst rest
           Just inst ->
             do let mkNewGoal :: (VarName, Term) -> IO (Either Term Prop)
                    mkNewGoal (vn, tp) =
                      case IntMap.lookup (vnIndex vn) inst of
                        Nothing ->
                          -- this argument not solved by unification, so make it a goal
                          do c0 <- scInstantiate sc inst tp
                             mp <- termToMaybeProp sc c0
                             let nm = vnName vn
                             case mp of
                               Nothing ->
                                 fail ("goal_apply: could not find instantiation for " ++ show nm)
                               Just p -> pure (Right p)
                        Just tm ->
                          pure (Left tm)
                Just <$> traverse mkNewGoal ruleArgs

    asPiLists :: Term -> [([(VarName, Term)], Term)]
    asPiLists t =
      case asPi t of
        Nothing -> [([], t)]
        Just (nm, tp, body) ->
          [ ((nm, tp) : args, concl) | (args, concl) <- asPiLists body ] ++ [([], t)]


-- | Attempt to prove a universally quantified goal by introducing a fresh variable
--   for the binder. Return the generated fresh term.
tacticIntro :: (F.MonadFail m, MonadIO m) =>
  SharedContext ->
  Text {- ^ Name to give to the variable.  If empty, will be chosen automatically from the goal. -} ->
  Tactic m TypedTerm
tacticIntro sc usernm = Tactic \goal ->
  case sequentState (goalSequent goal) of
    ConclFocus p mkSqt ->
      case asPi (unProp p) of
        Just (vn, tp, body) ->
          do let nm = vnName vn
             let name = if Text.null usernm then nm else usernm
             vn' <- liftIO $ scFreshVarName sc name
             x  <- liftIO $ scVariable sc vn' tp
             tt <- liftIO $ mkTypedTerm sc x
             body' <- liftIO $ scInstantiate sc (IntMap.singleton (vnIndex vn) x) body
             let goal' = goal { goalSequent = mkSqt (Prop body') }
             return (tt, mempty, [goal'], introEvidence vn' tp)

        _ -> fail "intro tactic failed: not a function"

    _ -> fail "intro tactic: conclusion focus required"

-- | Attempt to prove a goal by applying the given theorem.  Any hypotheses of
--   the theorem will generate additional subgoals.
tacticApply :: (F.MonadFail m, MonadIO m) => SharedContext -> Theorem -> Tactic m ()
tacticApply sc thm = Tactic \goal ->
  case sequentState (goalSequent goal) of
    Unfocused -> fail "apply tactic: focus required"
    HypFocus _ _ -> fail "apply tactic: cannot apply in a hypothesis"
    ConclFocus gl mkSqt ->
      liftIO (propApply sc (thmProp thm) gl) >>= \case
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

-- | Attempt to solve a goal by recognizing it as a trivially true proposition.
tacticTrivial :: (F.MonadFail m, MonadIO m) => SharedContext -> Tactic m ()
tacticTrivial sc = Tactic \goal ->
  case sequentState (goalSequent goal) of
    Unfocused -> fail "trivial tactic: focus required"
    HypFocus _ _ -> fail "trivial tactic: cannot apply trivial in a hypothesis"
    ConclFocus g _ ->
      liftIO (trivialProofTerm sc g) >>= \case
        Left err -> fail err
        Right pf ->
           do let gp = unProp g
              ty <- liftIO $ scTypeOf sc pf
              ok <- liftIO $ scConvertible sc gp ty
              unless ok $ do
                  gp' <- liftIO $ ppTerm sc gp
                  fail $ unlines [
                      "The trivial tactic cannot prove this equality",
                      gp'
                   ]
              return ((), mempty, [], leafEvidence (ProofTerm pf))

-- | Attempt to prove a goal by giving a direct proof term.
tacticExact :: (F.MonadFail m, MonadIO m) => SharedContext -> Term -> Tactic m ()
tacticExact sc tm = Tactic \goal ->
  case sequentState (goalSequent goal) of
    Unfocused -> fail "tactic exact: focus required"
    HypFocus _ _ -> fail "tactic exact: cannot apply exact in a hypothesis"
    ConclFocus g _ ->
      do let gp = unProp g
         ty <- liftIO $ scTypeOf sc tm
         ok <- liftIO $ scConvertible sc gp ty
         unless ok $ do
             gp' <- liftIO $ prettyTerm sc gp
             tm' <- liftIO $ prettyTerm sc tm
             ty' <- liftIO $ prettyTerm sc ty
             ppopts <- liftIO $ scGetPPOpts sc
             fail $ PPS.render ppopts $ PP.vsep [
                 "Proof term does not prove the required proposition:",
                 PP.indent 3 $ "Offered proof term:" <+> tm',
                 PP.indent 3 $ "Type of proof term:" <+> ty',
                 PP.indent 3 $ "Expected type:" <+> gp'
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
