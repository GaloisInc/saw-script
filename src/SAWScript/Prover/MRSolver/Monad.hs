{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}

{- |
Module      : SAWScript.Prover.MRSolver.Monad
Copyright   : Galois, Inc. 2022
License     : BSD3
Maintainer  : westbrook@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

This module defines the monad used by Mr. Solver ('MRM') as well as the core
monadic combinators for operating on terms.
-}

module SAWScript.Prover.MRSolver.Monad where

import Data.Maybe
import Data.List (find, findIndex, foldl')
import Data.IORef
import qualified Data.Text as T
import System.IO (hPutStrLn, stderr)
import Control.Monad (MonadPlus(..), foldM)
import Control.Monad.Catch (MonadThrow, MonadCatch)
import Control.Monad.Except (MonadError(..), ExceptT, runExceptT)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (MonadReader(..), ReaderT(..))
import Control.Monad.State (MonadState(..), StateT(..), modify)
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Trans.Maybe
import GHC.Generics

import Data.Map (Map)
import qualified Data.Map as Map

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap

import Data.Set (Set)
import qualified Data.Set as Set

import Prettyprinter

import Verifier.SAW.Utils (panic)
import Verifier.SAW.Term.Functor
import Verifier.SAW.Term.CtxTerm (MonadTerm(..))
import Verifier.SAW.Term.Pretty
import Verifier.SAW.SCTypeCheck
import Verifier.SAW.SharedTerm
import Verifier.SAW.Module (Def(..))
import Verifier.SAW.Recognizer
import Verifier.SAW.Cryptol.Monadify
import SAWScript.Prover.SolverStats
import SAWScript.Proof (Sequent, SolveResult)
import SAWScript.Value (TopLevel)

import SAWScript.Prover.MRSolver.Term
import SAWScript.Prover.MRSolver.Evidence


----------------------------------------------------------------------
-- * MR Solver Errors
----------------------------------------------------------------------

-- | The context in which a failure occurred
data FailCtx
  = FailCtxRefines NormComp NormComp
  | FailCtxCoIndHyp CoIndHyp
  | FailCtxMNF Term
  | FailCtxProveRel Term Term
  deriving Show

-- | That's MR. Failure to you
data MRFailure
  = TermsNotEq Term Term
  | TypesNotEq Type Type
  | TypesNotUnifiable Type Type
  | BindTypesNotUnifiable Type Type
  | ReturnTypesNotEq Type Type
  | FunNamesDoNotRefine FunName [Term] FunName [Term]
  | CompsDoNotRefine NormComp NormComp
  | ReturnNotError (Either Term Term) Term
  | FunsNotEq FunName FunName
  | CannotLookupFunDef FunName
  | RecursiveUnfold FunName
  | MalformedTpDescList Term
  | MalformedDefs Term
  | MalformedComp Term
  | NotCompFunType Term Term
  | AssertionNotProvable Term
  | AssumptionNotProvable Term
  | InvariantNotProvable FunName FunName Term
    -- | A local variable binding
  | MRFailureLocalVar LocalName MRFailure
    -- | Information about the context of the failure
  | MRFailureCtx FailCtx MRFailure
    -- | Records a disjunctive branch we took, where both cases failed
  | MRFailureDisj MRFailure MRFailure
  deriving Show

-- | Remove the context from a 'MRFailure', i.e. remove all applications of the
-- 'MRFailureLocalVar' and 'MRFailureCtx' constructors
mrFailureWithoutCtx :: MRFailure -> MRFailure
mrFailureWithoutCtx (MRFailureLocalVar x err) =
  MRFailureLocalVar x (mrFailureWithoutCtx err)
mrFailureWithoutCtx (MRFailureCtx _ err) = mrFailureWithoutCtx err
mrFailureWithoutCtx (MRFailureDisj err1 err2) =
  MRFailureDisj (mrFailureWithoutCtx err1) (mrFailureWithoutCtx err2)
mrFailureWithoutCtx err = err

-- | Pretty-print an object prefixed with a 'String' that describes it
prettyPrefix :: PrettyInCtx a => String -> a -> PPInCtxM SawDoc
prettyPrefix str a =
  (pretty str <>) <$> nest 2 <$> (line <>) <$> prettyInCtx a

-- | Pretty-print two objects, prefixed with a 'String' and with a separator
prettyPrefixSep :: (PrettyInCtx a, PrettyInCtx b) =>
                   String -> a -> String -> b -> PPInCtxM SawDoc
prettyPrefixSep d1 t2 d3 t4 =
  prettyInCtx t2 >>= \d2 -> prettyInCtx t4 >>= \d4 ->
  return $ group (pretty d1 <> nest 2 (line <> d2) <> line <>
                  pretty d3 <> nest 2 (line <> d4))

-- | Apply 'vsep' to a list of pretty-printing computations
vsepM :: [PPInCtxM SawDoc] -> PPInCtxM SawDoc
vsepM = fmap vsep . sequence

instance PrettyInCtx FailCtx where
  prettyInCtx (FailCtxRefines m1 m2) =
    group <$> nest 2 <$>
    prettyPrefixSep "When proving refinement:" m1 "|=" m2
  prettyInCtx (FailCtxCoIndHyp hyp) =
    group <$> nest 2 <$>
    prettyPrefix "When doing co-induction with hypothesis:" hyp
  prettyInCtx (FailCtxMNF t) =
    group <$> nest 2 <$> vsepM [return "When normalizing computation:",
                                prettyInCtx t]
  prettyInCtx (FailCtxProveRel t1 t2) =
    group <$> nest 2 <$> vsepM [return "When proving terms equal:",
                                prettyInCtx t1, prettyInCtx t2]

instance PrettyInCtx MRFailure where
  prettyInCtx (TermsNotEq t1 t2) =
    prettyPrefixSep "Could not prove terms equal:" t1 "and" t2
  prettyInCtx (TypesNotEq tp1 tp2) =
    prettyPrefixSep "Types not equal:" tp1 "and" tp2
  prettyInCtx (TypesNotUnifiable tp1 tp2) =
    prettyPrefixSep "Types cannot be unified:" tp1 "and" tp2
  prettyInCtx (BindTypesNotUnifiable tp1 tp2) =
    prettyPrefixSep "Could not start co-induction because bind types cannot be unified:" tp1 "and" tp2
  prettyInCtx (ReturnTypesNotEq tp1 tp2) =
    prettyPrefixSep "Could not form refinement because return types are not equal:" tp1 "and" tp2
  prettyInCtx (FunNamesDoNotRefine f1 args1 f2 args2) =
    snd (prettyInCtxFunBindH f1 args1) >>= \d1 ->
    snd (prettyInCtxFunBindH f2 args2) >>= \d2 ->
    let prefix = "Could not prove function refinement:" in
    let postfix = ["because:",
                   "- No matching assumptions could be found",
                   "- At least one side cannot be unfolded without fix"] in
    return $ group (prefix <> nest 2 (line <> d1) <> line <>
                    "|=" <> nest 2 (line <> d2) <> line <> vsep postfix)
  prettyInCtx (CompsDoNotRefine m1 m2) =
    prettyPrefixSep "Could not prove refinement: " m1 "|=" m2
  prettyInCtx (ReturnNotError eith_terr t) =
    let (lr_s, terr) = either ("left",) ("right",) eith_terr in
    prettyPrefixSep "errorS:" terr (" on the " ++ lr_s ++ " does not match retS:") t
  prettyInCtx (FunsNotEq nm1 nm2) =
    vsepM [return "Named functions not equal:",
           prettyInCtx nm1, prettyInCtx nm2]
  prettyInCtx (CannotLookupFunDef nm) =
    prettyPrefix "Could not find definition for function:" nm
  prettyInCtx (RecursiveUnfold nm) =
    prettyPrefix "Recursive unfolding of function inside its own body:" nm
  prettyInCtx (MalformedTpDescList t) =
    prettyPrefix "Not a list of type descriptions:" t
  prettyInCtx (MalformedDefs t) =
    prettyPrefix "Cannot handle multiFixS recursive definitions term:" t
  prettyInCtx (MalformedComp t) =
    prettyPrefix "Could not handle computation:" t
  prettyInCtx (NotCompFunType tp t) =
    prettyPrefixSep "Not a computation or computational function type:" tp
                    "for term:" t
  prettyInCtx (AssertionNotProvable cond) =
    prettyPrefix "Failed to prove assertion:" cond
  prettyInCtx (AssumptionNotProvable cond) =
    prettyPrefix "Failed to prove condition for `assuming`:" cond
  prettyInCtx (InvariantNotProvable f g pre) =
    prettyAppList [return "Could not prove loop invariant for functions",
                   prettyInCtx f, return "and", prettyInCtx g,
                   return ":", prettyInCtx pre]
  prettyInCtx (MRFailureLocalVar x err) =
    local (fmap (x:)) $ prettyInCtx err
  prettyInCtx (MRFailureCtx ctx err) =
    do pp1 <- prettyInCtx ctx
       pp2 <- prettyInCtx err
       return (pp1 <> line <> pp2)
  prettyInCtx (MRFailureDisj err1 err2) =
    prettyPrefixSep "Tried two comparisons:" err1 "Backtracking..." err2

-- | Render a 'MRFailure' to a 'String'
showMRFailure :: MREnv -> MRFailure -> String
showMRFailure env = showInCtx (mrePPOpts env) emptyMRVarCtx

-- | Render a 'MRFailure' to a 'String' without its context (see
-- 'mrFailureWithoutCtx')
showMRFailureNoCtx :: MREnv -> MRFailure -> String
showMRFailureNoCtx env = showMRFailure env . mrFailureWithoutCtx


----------------------------------------------------------------------
-- * MR Monad
----------------------------------------------------------------------

-- | Classification info for what sort of variable an 'MRVar' is
data MRVarInfo
     -- | An existential variable, that might be instantiated and that tracks
     -- how many uvars were in scope when it was created. An occurrence of an
     -- existential variable should always be applied to these uvars; this is
     -- ensured by only allowing evars to be created by 'mrFreshEVar'.
  = EVarInfo Int (Maybe Term)
    -- | A recursive function bound by @multiFixS@, with its body
  | CallVarInfo Term

instance PrettyInCtx MRVarInfo where
  prettyInCtx (EVarInfo _ maybe_t) =
    prettyAppList [ return "EVar", parens <$> prettyInCtx maybe_t]
  prettyInCtx (CallVarInfo t) =
    prettyAppList [ return "CallVar", parens <$> prettyInCtx t]

-- | A map from 'MRVar's to their info
type MRVarMap = Map MRVar MRVarInfo

-- | Test if a 'Term' is an application of an 'ExtCns' to some arguments
asExtCnsApp :: Recognizer Term (ExtCns Term, [Term])
asExtCnsApp (asApplyAll -> (asExtCns -> Just ec, args)) =
  return (ec, args)
asExtCnsApp _ = Nothing

-- | Recognize an evar applied to 0 or more arguments relative to a 'MRVarMap'
-- along with its uvar context length and its instantiation, if any
asEVarApp :: MRVarMap -> Recognizer Term (MRVar, Int, [Term], Maybe Term)
asEVarApp var_map (asExtCnsApp -> Just (ec, args))
  | Just (EVarInfo clen maybe_inst) <- Map.lookup (MRVar ec) var_map =
    Just (MRVar ec, clen, args, maybe_inst)
asEVarApp _ _ = Nothing

-- | A co-inductive hypothesis of the form:
--
-- > forall x1, ..., xn. F y1 ... ym |= G z1 ... zl
--
-- for some universal context @x1:T1, ..., xn:Tn@ and some lists of argument
-- expressions @y1, ..., ym@ and @z1, ..., zl@ over the universal context.
data CoIndHyp = CoIndHyp {
  -- | The uvars that were in scope when this assmption was created
  coIndHypCtx :: MRVarCtx,
  -- | The LHS function name
  coIndHypLHSFun :: FunName,
  -- | The RHS function name
  coIndHypRHSFun :: FunName,
  -- | The LHS argument expressions @y1, ..., ym@ over the 'coIndHypCtx' uvars
  coIndHypLHS :: [Term],
  -- | The RHS argument expressions @y1, ..., ym@ over the 'coIndHypCtx' uvars
  coIndHypRHS :: [Term],
  -- | The invariant for the left-hand arguments, as a closed function from
  -- the left-hand arguments to @Bool@
  coIndHypInvariantLHS :: Maybe Term,
  -- | The invariant for the right-hand arguments, as a closed function from
  -- the left-hand arguments to @Bool@
  coIndHypInvariantRHS :: Maybe Term
} deriving Show

-- | Extract the @i@th argument on either the left- or right-hand side of a
-- coinductive hypothesis
coIndHypArg :: CoIndHyp -> Either Int Int -> Term
coIndHypArg hyp (Left i) = (coIndHypLHS hyp) !! i
coIndHypArg hyp (Right i) = (coIndHypRHS hyp) !! i

-- | Set the @i@th argument on either the left- or right-hand side of a
-- coinductive hypothesis to the given value
coIndHypSetArg :: CoIndHyp -> Either Int Int -> Term -> CoIndHyp
coIndHypSetArg hyp@(CoIndHyp {..}) (Left i) x =
  hyp { coIndHypLHS = take i coIndHypLHS ++ x : drop (i+1) coIndHypLHS }
coIndHypSetArg hyp@(CoIndHyp {..}) (Right i) x =
  hyp { coIndHypRHS = take i coIndHypRHS ++ x : drop (i+1) coIndHypRHS }

-- | Add a variable to the context of a coinductive hypothesis, returning the
-- updated coinductive hypothesis and a 'Term' which is the new variable
coIndHypWithVar :: CoIndHyp -> LocalName -> Type -> MRM t (CoIndHyp, Term)
coIndHypWithVar (CoIndHyp ctx f1 f2 args1 args2 invar1 invar2) nm tp =
  do var <- liftSC1 scLocalVar 0
     let ctx' = mrVarCtxAppend (singletonMRVarCtx nm tp) ctx
     (args1', args2') <- liftTermLike 0 1 (args1, args2)
     return (CoIndHyp ctx' f1 f2 args1' args2' invar1 invar2, var)

-- | A map from pairs of function names to co-inductive hypotheses over those
-- names
type CoIndHyps = Map (FunName, FunName) CoIndHyp

instance PrettyInCtx CoIndHyp where
  prettyInCtx (CoIndHyp ctx f1 f2 args1 args2 invar1 invar2) =
    prettyWithCtx ctx $ -- ignore whatever context we're in and use `ctx` instead
    prettyAppList [prettyInCtx ctx, return ".",
                   (case invar1 of
                       Just f -> prettyTermApp f args1
                       Nothing -> return "True"), return "=>",
                   (case invar2 of
                       Just f -> prettyTermApp f args2
                       Nothing -> return "True"), return "=>",
                   prettyTermApp (funNameTerm f1) args1,
                   return "|=",
                   prettyTermApp (funNameTerm f2) args2]

-- | An assumption that something is equal to one of the constructors of a
-- datatype, e.g. equal to @Left@ of some 'Term' or @Right@ of some 'Term'
data DataTypeAssump
  = IsLeft Term | IsRight Term | IsNum Term | IsInf
  deriving (Generic, Show, TermLike)

instance PrettyInCtx DataTypeAssump where
  prettyInCtx (IsLeft  x) = prettyInCtx x >>= prettyPrefix "Left _ _"
  prettyInCtx (IsRight x) = prettyInCtx x >>= prettyPrefix "Right _ _"
  prettyInCtx (IsNum   x) = prettyInCtx x >>= prettyPrefix "TCNum"
  prettyInCtx IsInf = return "TCInf"

-- | A map from 'Term's to 'DataTypeAssump's over that term
type DataTypeAssumps = HashMap Term DataTypeAssump

-- | Parameters and locals for MR. Solver
data MRInfo t = MRInfo {
  -- | Global shared context for building terms, etc.
  mriSC :: SharedContext,
  -- | SMT timeout for SMT calls made by Mr. Solver
  mriSMTTimeout :: Maybe Integer,
  -- | The top-level Mr Solver environment
  mriEnv :: MREnv,
  -- | The function to be used as the SMT backend for Mr. Solver, taking a set
  -- of uninterpreted variables and a proposition to prove
  mriAskSMT :: Set VarIndex -> Sequent -> TopLevel (SolverStats, SolveResult),
  -- | The set of function refinements to assume
  mriRefnset :: Refnset t,
  -- | The current context of universal variables
  mriUVars :: MRVarCtx,
  -- | The current set of co-inductive hypotheses
  mriCoIndHyps :: CoIndHyps,
  -- | The current assumptions, which are conjoined into a single Boolean term;
  -- note that these have the current UVars free
  mriAssumptions :: Term,
  -- | The current set of 'DataTypeAssump's
  mriDataTypeAssumps :: DataTypeAssumps
}

-- | State maintained by MR. Solver
data MRState t = MRState {
  -- | Cumulative stats on all solver runs made so far
  mrsSolverStats :: SolverStats,
  -- | The evidence object, which includes information about which
  -- 'FunAssump's in 'mriRefnset' have been used so far
  mrsEvidence :: MREvidence t,
  -- | The existential and letrec-bound variables
  mrsVars :: MRVarMap
}

-- | The exception type for MR. Solver, which is either a 'MRFailure' or a
-- widening request
data MRExn = MRExnFailure MRFailure
             -- | A widening request gives two recursive function names whose
             -- coinductive assumption needs to be widened along with a list of
             -- indices into the argument lists for these functions (in either
             -- the arguments to the 'Left' or 'Right' function) that need to be
             -- generalized
           | MRExnWiden FunName FunName [Either Int Int]
           deriving Show

-- | Mr. Monad, the monad used by MR. Solver, which has 'MRInfo' as as a
-- shared environment, 'MRState' as state, and 'MRFailure' as an exception
-- type, all over an 'IO' monad
newtype MRM t a = MRM { unMRM :: ReaderT (MRInfo t) (StateT (MRState t)
                                                    (ExceptT MRExn TopLevel)) a }
                deriving newtype (Functor, Applicative, Monad, MonadIO,
                                  MonadReader (MRInfo t), MonadState (MRState t),
                                  MonadError MRExn, MonadThrow, MonadCatch)

instance MonadTerm (MRM t) where
  mkTermF = liftSC1 scTermF
  liftTerm = liftSC3 incVars
  whnfTerm = liftSC1 scWhnf
  substTerm = liftSC3 instantiateVarList

-- | Get the current value of 'mriSC'
mrSC :: MRM t SharedContext
mrSC = mriSC <$> ask

-- | Get the current value of 'mriSMTTimeout'
mrSMTTimeout :: MRM t (Maybe Integer)
mrSMTTimeout = mriSMTTimeout <$> ask

-- | Get the current value of 'mriUVars'
mrUVars :: MRM t MRVarCtx
mrUVars = mriUVars <$> ask

-- | Get the current function assumptions
mrRefnset :: MRM t (Refnset t)
mrRefnset = mriRefnset <$> ask

-- | Get the current value of 'mriCoIndHyps'
mrCoIndHyps :: MRM t CoIndHyps
mrCoIndHyps = mriCoIndHyps <$> ask

-- | Get the current value of 'mriAssumptions'
mrAssumptions :: MRM t Term
mrAssumptions = mriAssumptions <$> ask

-- | Get the current value of 'mriDataTypeAssumps'
mrDataTypeAssumps :: MRM t DataTypeAssumps
mrDataTypeAssumps = mriDataTypeAssumps <$> ask

-- | Call the SMT backend given by 'mriAskSMT' on a set of uninterpreted
-- variables and a proposition to prove
mrAskSMT :: Set VarIndex -> Sequent -> MRM t (SolverStats, SolveResult)
mrAskSMT unints goal = do
  askSMT <- mriAskSMT <$> ask
  MRM $ lift $ lift $ lift $ askSMT unints goal

-- | Get the current debug level
mrDebugLevel :: MRM t Int
mrDebugLevel = mreDebugLevel <$> mriEnv <$> ask

-- | Get the current pretty-printing options
mrPPOpts :: MRM t PPOpts
mrPPOpts = mrePPOpts <$> mriEnv <$> ask

-- | Get the current value of 'mriEnv'
mrEnv :: MRM t MREnv
mrEnv = mriEnv <$> ask

-- | Get the current value of 'mrsSolverStats'
mrSolverStats :: MRM t SolverStats
mrSolverStats = mrsSolverStats <$> get

-- | Get the current value of 'mrsEvidence'
mrEvidence :: MRM t (MREvidence t)
mrEvidence = mrsEvidence <$> get

-- | Get the current value of 'mrsVars'
mrVars :: MRM t MRVarMap
mrVars = mrsVars <$> get

-- | Run a 'PPInCtxM' computation in the current context and with the current
-- 'PPOpts'
mrPPInCtxM :: PPInCtxM a -> MRM t a
mrPPInCtxM m = mrPPOpts >>= \opts -> mrUVars >>= \ctx ->
  return $ runPPInCtxM m opts ctx

-- | Pretty-print an object in the current context and with the current 'PPOpts'
mrPPInCtx :: PrettyInCtx a => a -> MRM t SawDoc
mrPPInCtx a = mrPPOpts >>= \opts -> mrUVars >>= \ctx ->
  return $ ppInCtx opts ctx a

-- | Pretty-print an object in the current context and render to a 'String' with
-- the current 'PPOpts'
mrShowInCtx :: PrettyInCtx a => a -> MRM t String
mrShowInCtx a = mrPPOpts >>= \opts -> mrUVars >>= \ctx ->
  return $ showInCtx opts ctx a


-- | Run an 'MRM' computation and return a result or an error, including the
-- final state of 'mrsSolverStats' and 'mrsEvidence'
runMRM ::
  SharedContext ->
  MREnv {- ^ The Mr Solver environment -} ->
  Maybe Integer {- ^ Timeout in milliseconds for each SMT call -} ->
  (Set VarIndex -> Sequent -> TopLevel (SolverStats, SolveResult))
    {- ^ The callback to use for making SMT queries -} ->
  Refnset t {- ^ Any additional refinements to be assumed by Mr Solver -} ->
  MRM t a {- ^ The monadic computation to run -} ->
  TopLevel (Either MRFailure (a, (SolverStats, MREvidence t)))
runMRM sc env timeout askSMT rs m =
  do true_tm <- liftIO $ scBool sc True
     let init_info = MRInfo { mriSC = sc, mriSMTTimeout = timeout,
                              mriEnv = env, mriAskSMT = askSMT,
                              mriRefnset = rs,
                              mriUVars = emptyMRVarCtx,
                              mriCoIndHyps = Map.empty,
                              mriAssumptions = true_tm,
                              mriDataTypeAssumps = HashMap.empty }
     let init_st = MRState { mrsSolverStats = mempty, mrsEvidence = mempty,
                             mrsVars = Map.empty }
     res <- runExceptT $ flip runStateT init_st $
       flip runReaderT init_info $ unMRM m
     case res of
       Right (a, st) -> return $ Right (a, (mrsSolverStats st, mrsEvidence st))
       Left (MRExnFailure failure) -> return $ Left failure
       Left exn -> fail ("runMRM: unexpected internal exception: " ++ show exn)

-- | Run an 'MRM' computation and return a result or an error, discarding the
-- final state
evalMRM ::
  SharedContext ->
  MREnv {- ^ The Mr Solver environment -} ->
  Maybe Integer {- ^ Timeout in milliseconds for each SMT call -} ->
  (Set VarIndex -> Sequent -> TopLevel (SolverStats, SolveResult))
    {- ^ The callback to use for making SMT queries -} ->
  Refnset t {- ^ Any additional refinements to be assumed by Mr Solver -} ->
  MRM t a {- ^ The monadic computation to eval -} ->
  TopLevel (Either MRFailure a)
evalMRM sc env timeout askSMT rs =
  fmap (fmap fst) . runMRM sc env timeout askSMT rs

-- | Run an 'MRM' computation and return a final state or an error, discarding
-- the result
execMRM ::
  SharedContext ->
  MREnv {- ^ The Mr Solver environment -} ->
  Maybe Integer {- ^ Timeout in milliseconds for each SMT call -} ->
  (Set VarIndex -> Sequent -> TopLevel (SolverStats, SolveResult))
    {- ^ The callback to use for making SMT queries -} ->
  Refnset t {- ^ Any additional refinements to be assumed by Mr Solver -} ->
  MRM t a {- ^ The monadic computation to exec -} ->
  TopLevel (Either MRFailure (SolverStats, MREvidence t))
execMRM sc env timeout askSMT rs =
  fmap (fmap snd) . runMRM sc env timeout askSMT rs

-- | Throw an 'MRFailure'
throwMRFailure :: MRFailure -> MRM t a
throwMRFailure = throwError . MRExnFailure

-- | Apply a function to any failure thrown by an 'MRM' computation
mapMRFailure :: (MRFailure -> MRFailure) -> MRM t a -> MRM t a
mapMRFailure f m = catchError m $ \case
  MRExnFailure failure -> throwError $ MRExnFailure $ f failure
  e -> throwError e

-- | Catch any 'MRFailure' raised by a computation
catchFailure :: MRM t a -> (MRFailure -> MRM t a) -> MRM t a
catchFailure m f =
  m `catchError` \case
  MRExnFailure failure -> f failure
  e -> throwError e

-- | Try two different 'MRM' computations, combining their failures if needed.
-- Note that the 'MRState' will reset if the first computation fails.
mrOr :: MRM t a -> MRM t a -> MRM t a
mrOr m1 m2 =
  catchFailure m1 $ \err1 ->
  catchFailure m2 $ \err2 ->
  throwMRFailure $ MRFailureDisj err1 err2

-- | Run an 'MRM' computation in an extended failure context
withFailureCtx :: FailCtx -> MRM t a -> MRM t a
withFailureCtx ctx = mapMRFailure (MRFailureCtx ctx)

{-
-- | Catch any errors thrown by a computation and coerce them to a 'Left'
catchErrorEither :: MonadError e m => m a -> m (Either e a)
catchErrorEither m = catchError (Right <$> m) (return . Left)
-}

-- FIXME: replace these individual lifting functions with a more general
-- typeclass like LiftTCM

-- | Lift a nullary SharedTerm computation into 'MRM'
liftSC0 :: (SharedContext -> IO a) -> MRM t a
liftSC0 f = mrSC >>= \sc -> liftIO (f sc)

-- | Lift a unary SharedTerm computation into 'MRM'
liftSC1 :: (SharedContext -> a -> IO b) -> a -> MRM t b
liftSC1 f a = mrSC >>= \sc -> liftIO (f sc a)

-- | Lift a binary SharedTerm computation into 'MRM'
liftSC2 :: (SharedContext -> a -> b -> IO c) -> a -> b -> MRM t c
liftSC2 f a b = mrSC >>= \sc -> liftIO (f sc a b)

-- | Lift a ternary SharedTerm computation into 'MRM'
liftSC3 :: (SharedContext -> a -> b -> c -> IO d) -> a -> b -> c -> MRM t d
liftSC3 f a b c = mrSC >>= \sc -> liftIO (f sc a b c)

-- | Lift a quaternary SharedTerm computation into 'MRM'
liftSC4 :: (SharedContext -> a -> b -> c -> d -> IO e) -> a -> b -> c -> d ->
           MRM t e
liftSC4 f a b c d = mrSC >>= \sc -> liftIO (f sc a b c d)

-- | Lift a quinary SharedTerm computation into 'MRM'
liftSC5 :: (SharedContext -> a -> b -> c -> d -> e -> IO f) ->
           a -> b -> c -> d -> e -> MRM t f
liftSC5 f a b c d e = mrSC >>= \sc -> liftIO (f sc a b c d e)


----------------------------------------------------------------------
-- * Functions for Building Terms
----------------------------------------------------------------------

-- | Create a term representing an application of @Prelude.error@
mrErrorTerm :: Term -> T.Text -> MRM t Term
mrErrorTerm a str =
  do err_str <- liftSC1 scString str
     liftSC2 scGlobalApply "Prelude.error" [a, err_str]

-- | Create a term representing an application of @Prelude.genBVVecFromVec@,
-- where the default value argument is @Prelude.error@ of the given 'T.Text'
mrGenBVVecFromVec :: Term -> Term -> Term -> T.Text -> Term -> Term -> MRM t Term
mrGenBVVecFromVec m a v def_err_str n len =
  do err_tm <- mrErrorTerm a def_err_str
     liftSC2 scGlobalApply "Prelude.genBVVecFromVec" [m, a, v, err_tm, n, len]

-- | Create a term representing an application of @Prelude.genFromBVVec@,
-- where the default value argument is @Prelude.error@ of the given 'T.Text'
mrGenFromBVVec :: Term -> Term -> Term -> Term -> T.Text -> Term -> MRM t Term
mrGenFromBVVec n len a v def_err_str m =
  do err_tm <- mrErrorTerm a def_err_str
     liftSC2 scGlobalApply "Prelude.genFromBVVec" [n, len, a, v, err_tm, m]

-- | Match a lambda of the form @(\i _ -> f i)@ as @f@
asIndexWithProofFnTerm :: Recognizer Term (SharedContext -> IO Term)
asIndexWithProofFnTerm (asLambdaList -> ([(ix_nm, ix_tp), _], e))
  | not $ inBitSet 0 $ looseVars e
  = Just $ \sc ->
    do ix_var <- scLocalVar sc 0
       -- Substitute an error term for the proof variable and ix_var for ix in
       -- the body e of the lambda
       let s = [error "asGen(BV)VecTerm: unexpected var occurrence", ix_var]
       e' <- instantiateVarList sc 0 s e
       scLambda sc ix_nm ix_tp e'
asIndexWithProofFnTerm _ = Nothing

-- | Match a term of the form @gen n a f@ or @genWithProof n a (\i _ -> f i)@
asGenVecTerm :: Recognizer Term (Term, Term, SharedContext -> IO Term)
asGenVecTerm (asApplyAll -> (isGlobalDef "Prelude.gen" -> Just _,
                             [n, a, f]))
  = Just (n, a, const $ return f)
asGenVecTerm (asApplyAll -> (isGlobalDef "Prelude.genWithProof" -> Just _,
                             [n, a, asIndexWithProofFnTerm -> Just m_f]))
  = Just (n, a, m_f)
asGenVecTerm _ = Nothing

-- | Match a term of the form @genBVVecNoPf n len a f@ or
-- @genBVVec n len a (\i _ -> f i)@
asGenBVVecTerm :: Recognizer Term (Term, Term, Term, SharedContext -> IO Term)
asGenBVVecTerm (asApplyAll -> (isGlobalDef "Prelude.genBVVecNoPf" -> Just _,
                               [n, len, a, f]))
  = Just (n, len, a, const $ return f)
asGenBVVecTerm (asApplyAll -> (isGlobalDef "Prelude.genBVVec" -> Just _,
                               [n, len, a, asIndexWithProofFnTerm -> Just m_f]))
  = Just (n, len, a, m_f)
asGenBVVecTerm _ = Nothing

-- | Index into a vector using the @at@ accessor, taking in the same 'Term'
-- arguments as that function, but simplify when the vector is a term
-- constructed from @gen@ or @genWithProof@
mrAtVec :: Term -> Term -> Term -> Term -> MRM t Term
mrAtVec _ _ (asGenVecTerm -> Just (_, _, m_f)) ix =
  liftSC0 m_f >>= \f -> mrApply f ix
mrAtVec len a v ix =
  liftSC2 scGlobalApply "Prelude.at" [len, a, v, ix]

-- | Index into a vector using the @atBVVecNoPf@ accessor, taking in the same
-- 'Term' arguments as that function, but simplify when the vector is a term
-- constructed from @gen@ or @genWithProof@
mrAtBVVec :: Term -> Term -> Term -> Term -> Term -> MRM t Term
mrAtBVVec _ _ _ (asGenBVVecTerm -> Just (_, _, _, m_f)) ix =
  liftSC0 m_f >>= \f -> mrApply f ix
mrAtBVVec n len a v ix =
  liftSC2 scGlobalApply "Prelude.atBVVecNoPf" [n, len, a, v, ix]


----------------------------------------------------------------------
-- * Monadic Operations on Terms
----------------------------------------------------------------------

-- | Apply a 'TermProj' to perform a projection on a 'Term'
doTermProj :: Term -> TermProj -> MRM t Term
doTermProj (asPairValue -> Just (t, _)) TermProjLeft = return t
doTermProj (asPairValue -> Just (_, t)) TermProjRight = return t
doTermProj (asRecordValue -> Just t_map) (TermProjRecord fld)
  | Just t <- Map.lookup fld t_map = return t
doTermProj t TermProjLeft = liftSC1 scPairLeft t
doTermProj t TermProjRight = liftSC1 scPairRight t
doTermProj t (TermProjRecord fld) = liftSC2 scRecordSelect t fld

-- | Apply a 'TermProj' to a type to get the output type of the projection,
-- assuming that the type is already normalized
doTypeProj :: Term -> TermProj -> MRM t Term
doTypeProj (asPairType -> Just (tp1, _)) TermProjLeft = return tp1
doTypeProj (asPairType -> Just (_, tp2)) TermProjRight = return tp2
doTypeProj (asRecordType -> Just tp_map) (TermProjRecord fld)
  | Just tp <- Map.lookup fld tp_map
  = return tp
doTypeProj _ _ =
  -- FIXME: better error message? This is an error and not an MRFailure because
  -- we should only be projecting types for terms that we have already seen...
  error "doTypeProj"

-- | Get and normalize the type of a 'FunName'
funNameType :: FunName -> MRM t Term
funNameType (CallSName var) = liftSC1 scWhnf $ mrVarType var
funNameType (EVarFunName var) = liftSC1 scWhnf $ mrVarType var
funNameType (GlobalName gd projs) =
  liftSC1 scWhnf (globalDefType gd) >>= \gd_tp ->
  foldM doTypeProj gd_tp projs

-- | Apply a 'Term' to a list of arguments and beta-reduce in Mr. Monad
mrApplyAll :: Term -> [Term] -> MRM t Term
mrApplyAll f args = liftSC2 scApplyAllBeta f args

-- | Apply a 'Term' to a single argument and beta-reduce in Mr. Monad
mrApply :: Term -> Term -> MRM t Term
mrApply f arg = mrApplyAll f [arg]

-- | Substitue a list of @N@ arguments into the body of an @N@-ary pi type
mrPiApplyAll :: Term -> [Term] -> MRM t Term
mrPiApplyAll tp args
  | Just (_, body) <- asPiListN (length args) tp
  = substTermLike 0 args body
mrPiApplyAll _ _ = panic "mrPiApplyAll" ["Too many arguments for pi type"]

-- | Return the unit type as a 'Type'
mrUnitType :: MRM t Type
mrUnitType = Type <$> liftSC0 scUnitType

-- | Build a constructor application in Mr. Monad
mrCtorApp :: Ident -> [Term] -> MRM t Term
mrCtorApp = liftSC2 scCtorApp

-- | Build a 'Term' for a global in Mr. Monad
mrGlobalTerm :: Ident -> MRM t Term
mrGlobalTerm = liftSC1 scGlobalDef

-- | Build a 'Term' for a global and unfold the global
mrGlobalTermUnfold :: Ident -> MRM t Term
mrGlobalTermUnfold ident =
  (defBody <$> liftSC1 scRequireDef ident) >>= \case
  Just body -> return body
  Nothing -> panic "mrGlobalTermUnfold" ["Definition " ++ show ident ++
                                         " does not have a body"]

-- | Apply a named global to a list of arguments and beta-reduce in Mr. Monad
mrApplyGlobal :: Ident -> [Term] -> MRM t Term
mrApplyGlobal f args = mrGlobalTerm f >>= \t -> mrApplyAll t args

-- | Build an arrow type @a -> b@ using a return type @b@ that does not have an
-- additional free deBruijn index for the input
mrArrowType :: LocalName -> Term -> Term -> MRM t Term
mrArrowType n tp_in tp_out =
  liftSC3 scPi n tp_in =<< liftTermLike 0 1 tp_out

-- | Build the bitvector type @Vec n Bool@ from natural number term @n@
mrBvType :: Term -> MRM t Term
mrBvType n =
  do bool_tp <- liftSC0 scBoolType
     liftSC2 scVecType n bool_tp

-- | Build the equality proposition @Eq a t1 t2@
mrEqProp :: Term -> Term -> Term -> MRM t Term
mrEqProp tp t1 t2 = liftSC2 scDataTypeApp "Prelude.Eq" [tp,t1,t2]

-- | Like 'scBvConst', but if given a bitvector literal it is converted to a
-- natural number literal
mrBvToNat :: Term -> Term -> MRM t Term
mrBvToNat _ (asArrayValue -> Just (asBoolType -> Just _,
                                   mapM asBool -> Just bits)) =
  liftSC1 scNat $ foldl' (\n bit -> if bit then 2*n+1 else 2*n) 0 bits
mrBvToNat n len = liftSC2 scGlobalApply "Prelude.bvToNat" [n, len]

-- | Given a bit-width 'Term' and a natural number 'Term', return a bitvector
-- 'Term' of the given bit-width only if we can can do so without truncation
-- (i.e. only if we can ensure the given natural is in range)
mrBvNatInRange :: Term -> Term -> MRM t (Maybe Term)
mrBvNatInRange (asNat -> Just w) (asUnsignedConcreteBvToNat -> Just v)
  | v < 2 ^ w = Just <$> liftSC2 scBvLit w (toInteger v)
mrBvNatInRange w (asBvToNat -> Just (w', bv)) =
  mrBvCastInRange w w' bv
mrBvNatInRange w (asApplyAll -> (asGlobalDef -> Just "Prelude.intToNat",
                                 [i])) = case i of
  (asApplyAll -> (asGlobalDef -> Just "Prelude.natToInt", [v])) ->
    mrBvNatInRange w v
  (asApplyAll -> (asGlobalDef -> Just "Prelude.bvToInt", [w', bv])) ->
    mrBvCastInRange w w' bv
  _ -> return Nothing
mrBvNatInRange _ _ = return Nothing

-- | Given two bit-width 'Term's and a bitvector 'Term' of the second bit-width,
-- return a bitvector 'Term' of the first bit-width only if we can can do so
-- without truncation (i.e. only if we can ensure the given bitvector is in
-- range)
mrBvCastInRange :: Term -> Term -> Term -> MRM t (Maybe Term)
mrBvCastInRange w1_t w2_t bv =
  do w1_w2_cvt <- mrConvertible w1_t w2_t
     if w1_w2_cvt then return $ Just bv
     else case (asNat w1_t, asNat w1_t, asUnsignedConcreteBv bv) of
       (Just w1, _, Just v) | v < 2 ^ w1 ->
         Just <$> liftSC2 scBvLit w1 (toInteger v)
       (Just w1, Just w2, _) | w1 > w2 -> 
         do w1_sub_w2_t <- liftSC1 scNat (w1 - w2)
            Just <$> liftSC3 scBvUExt w2_t w1_sub_w2_t bv
       _ -> return Nothing

-- | Get the current context of uvars as a list of variable names and their
-- types as SAW core 'Term's, with the least recently bound uvar first, i.e., in
-- the order as seen \"from the outside\"
mrUVarsOuterToInner :: MRM t [(LocalName,Term)]
mrUVarsOuterToInner = mrVarCtxOuterToInner <$> mrUVars

-- | Get the current context of uvars as a list of variable names and their
-- types as SAW core 'Term's, with the most recently bound uvar first, i.e., in
-- the order as seen \"from the inside\"
mrUVarsInnerToOuter :: MRM t [(LocalName,Term)]
mrUVarsInnerToOuter = mrVarCtxInnerToOuter <$> mrUVars

-- | Get the type of a 'Term' in the current uvar context
mrTypeOf :: Term -> MRM t Term
mrTypeOf t =
  -- NOTE: scTypeOf' wants the type context in the most recently bound var first
  -- mrDebugPPPrefix 3 "mrTypeOf:" t >>
  mrUVarsInnerToOuter >>= \ctx -> liftSC2 scTypeOf' (map snd ctx) t

-- | Check if two 'Term's are convertible in the 'MRM' monad
mrConvertible :: Term -> Term -> MRM t Bool
mrConvertible = liftSC4 scConvertibleEval scTypeCheckWHNF True

-- | Take a 'FunName' @f@ for a monadic function of type @vars -> SpecM a@ and
-- compute the type @SpecM [args/vars]a@ of @f@ applied to @args@. Return the
-- type @[args/vars]a@ that @SpecM@ is applied to, along with its event type.
mrFunOutType :: FunName -> [Term] -> MRM t (EvTerm, Term)
mrFunOutType fname args =
  do app <- mrApplyAll (funNameTerm fname) args
     r_tp <- mrTypeOf app >>= liftSC1 scWhnf
     case asSpecM r_tp of
       Just (ev, tp) -> return (ev, tp)
       Nothing -> throwMRFailure (NotCompFunType r_tp app)

-- | Turn a 'LocalName' into one not in a list, adding a suffix if necessary
uniquifyName :: LocalName -> [LocalName] -> LocalName
uniquifyName nm nms | notElem nm nms = nm
uniquifyName nm nms =
  case find (flip notElem nms) $
       map (T.append nm . T.pack . show) [(0::Int) ..] of
    Just nm' -> nm'
    Nothing -> error "uniquifyName"

-- | Turn a list of 'LocalName's into one names not in a list, adding suffixes
-- if necessary
uniquifyNames :: [LocalName] -> [LocalName] -> [LocalName]
uniquifyNames [] _ = []
uniquifyNames (nm:nms) nms_other =
  let nm' = uniquifyName nm nms_other in
  nm' : uniquifyNames nms (nm' : nms_other)

-- | Build a lambda term with the lifting (in the sense of 'incVars') of an
-- MR Solver term
-- NOTE: The types in the given context can have earlier variables in the
-- context free. Thus, if passing a list of types all in the same context, later
-- types should be lifted.
mrLambdaLift :: TermLike tm => [(LocalName,Term)] -> tm ->
                ([Term] -> tm -> MRM t Term) -> MRM t Term
mrLambdaLift [] t f = f [] t
mrLambdaLift ctx t f =
  do -- uniquifyNames doesn't care about the order of the names in its second,
     -- argument, thus either inner-to-outer or outer-to-inner would work
     nms <- uniquifyNames (map fst ctx) <$> map fst <$> mrUVarsInnerToOuter
     let ctx' = zipWith (\nm (_,tp) -> (nm,tp)) nms ctx
     vars <- reverse <$> mapM (liftSC1 scLocalVar) [0 .. length ctx - 1]
     t' <- liftTermLike 0 (length ctx) t
     f vars t' >>= liftSC2 scLambdaList ctx'

-- Specialized versions of mrLambdaLift that expect a certain number of Term
-- arguments. As an alternative, we could change the type of mrLambdaLift to
-- take a length-indexed vector instead (thereby avoiding partial pattern
-- matches), but that is probably overkill for our needs.

-- | Call 'mrLambdaLift' with exactly one 'Term' argument.
mrLambdaLift1 :: TermLike tm => (LocalName,Term) -> tm ->
                 (Term -> tm -> MRM t Term) -> MRM t Term
mrLambdaLift1 (nm,tp) t f =
  mrLambdaLift [(nm,tp)] t $ \vars t' ->
    case vars of
      [v] -> f v t'
      _   -> panic "mrLambdaLift1" ["Expected exactly one Term argument"]

-- | Call 'mrLambdaLift' with exactly two 'Term' arguments which are both in the
-- same context. (To create two lambdas where the type of the second variable
-- depends on the value of the first, use 'mrLambdaLift' directly.)
mrLambdaLift2 :: TermLike tm => (LocalName,Term) -> (LocalName,Term) -> tm ->
                 (Term -> Term -> tm -> MRM t Term) -> MRM t Term
mrLambdaLift2 (nm1,tp1) (nm2,tp2) t f =
  liftTermLike 0 1 tp2 >>= \tp2' ->
  mrLambdaLift [(nm1,tp1), (nm2,tp2')] t $ \vars t' ->
    case vars of
      [v1, v2] -> f v1 v2 t'
      _        -> panic "mrLambdaLift2" ["Expected exactly two Term arguments"]

-- | Run a MR Solver computation in a context extended with a universal
-- variable, which is passed as a 'Term' to the sub-computation. Note that any
-- assumptions made in the sub-computation will be lost when it completes.
withUVar :: LocalName -> Type -> (Term -> MRM t a) -> MRM t a
withUVar nm tp m = withUVars (singletonMRVarCtx nm tp) $ \case
  [v] -> m v
  _   -> panic "withUVar" ["impossible"]

-- | Run a MR Solver computation in a context extended with a universal variable
-- and pass it the lifting (in the sense of 'incVars') of an MR Solver term
withUVarLift :: TermLike tm => LocalName -> Type -> tm ->
                (Term -> tm -> MRM t a) -> MRM t a
withUVarLift nm tp t m =
  withUVar nm tp (\x -> liftTermLike 0 1 t >>= m x)

-- | Run a MR Solver computation in a context extended with a list of universal
-- variables, passing 'Term's for those variables to the supplied computation.
withUVars :: MRVarCtx -> ([Term] -> MRM t a) -> MRM t a
withUVars (mrVarCtxLength -> 0) f = f []
withUVars ctx f =
  do -- for uniquifyNames, we want to consider the oldest names first, thus we
     -- must pass the first argument in outer-to-inner order. uniquifyNames
     -- doesn't care about the order of the names in its second, argument, thus
     -- either inner-to-outer or outer-to-inner would work
     let ctx_l = mrVarCtxOuterToInner ctx
     nms <- uniquifyNames (map fst ctx_l) <$> map fst <$> mrUVarsInnerToOuter
     let ctx_u = mrVarCtxFromOuterToInner $ zip nms $ map snd ctx_l
     -- lift all the variables in our assumptions by the number of new uvars
     -- we're adding (we do not have to lift the types in our uvar context
     -- itself, since each type is in the context of all older uvars - see the
     -- definition of MRVarCtx)
     assumps' <- mrAssumptions >>= liftTerm 0 (mrVarCtxLength ctx)
     dataTypeAssumps' <- mrDataTypeAssumps >>= mapM (liftTermLike 0 (mrVarCtxLength ctx))
     -- make terms for our new uvars, extend the context, and continue
     vars <- reverse <$> mapM (liftSC1 scLocalVar) [0 .. mrVarCtxLength ctx - 1]
     local (\info -> info { mriUVars = mrVarCtxAppend ctx_u (mriUVars info),
                            mriAssumptions = assumps',
                            mriDataTypeAssumps = dataTypeAssumps' }) $
       mapM (\t -> (t,) <$> mrTypeOf t) vars >>= \vars_with_types ->
       mrDebugPPPrefix 3 "withUVars:" vars_with_types >>
       foldr (\nm m -> mapMRFailure (MRFailureLocalVar nm) m) (f vars) nms

-- | Run a MR Solver in a top-level context, i.e., with no uvars or assumptions
withNoUVars :: MRM t a -> MRM t a
withNoUVars m =
  do true_tm <- liftSC1 scBool True
     local (\info -> info { mriUVars = emptyMRVarCtx, mriAssumptions = true_tm,
                            mriDataTypeAssumps = HashMap.empty }) m

-- | Run a MR Solver in a context of only the specified UVars, no others -
-- note that this also clears all assumptions
withOnlyUVars :: MRVarCtx -> MRM t a -> MRM t a
withOnlyUVars vars m = withNoUVars $ withUVars vars $ const m

-- | Build 'Term's for all the uvars currently in scope, ordered from least to
-- most recently bound
getAllUVarTerms :: MRM t [Term]
getAllUVarTerms =
  (mrVarCtxLength <$> mrUVars) >>= \len ->
  mapM (liftSC1 scLocalVar) [len-1, len-2 .. 0]

-- | Lambda-abstract all the current uvars out of a 'Term', with the least
-- recently bound variable being abstracted first
lambdaUVarsM :: Term -> MRM t Term
lambdaUVarsM t = mrUVarsOuterToInner >>= \ctx -> liftSC2 scLambdaList ctx t

-- | Pi-abstract all the current uvars out of a 'Term', with the least recently
-- bound variable being abstracted first
piUVarsM :: Term -> MRM t Term
piUVarsM t = mrUVarsOuterToInner >>= \ctx -> liftSC2 scPiList ctx t

-- | Instantiate all uvars in a term using the supplied function
instantiateUVarsM :: forall a t. TermLike a =>
                     (LocalName -> Term -> MRM t Term) -> a -> MRM t a
instantiateUVarsM f a =
  do ctx <- mrUVarsOuterToInner
     -- Remember: the uvar context is outermost to innermost, so we bind
     -- variables from left to right, substituting earlier ones into the types
     -- of later ones, but all substitutions are in reverse order, since
     -- substTerm and friends like innermost bindings first
     let helper :: [Term] -> [(LocalName,Term)] -> MRM t [Term]
         helper tms [] = return tms
         helper tms ((nm,tp):vars) =
           do tp' <- substTerm 0 tms tp
              tm <- f nm tp'
              helper (tm:tms) vars
     ecs <- helper [] ctx
     substTermLike 0 ecs a

-- | Convert an 'MRVar' to a 'Term', applying it to all the uvars in scope
mrVarTerm :: MRVar -> MRM t Term
mrVarTerm (MRVar ec) =
  do var_tm <- liftSC1 scExtCns ec
     vars <- getAllUVarTerms
     liftSC2 scApplyAll var_tm vars

-- | Create a dummy proof term of the specified type, which can be open but
-- should be of @Prop@ sort, by creating an 'ExtCns' axiom. This is sound as
-- long as we only use the resulting term in computation branches where we know
-- the proposition holds.
mrDummyProof :: Term -> MRM t Term
mrDummyProof tp = mrFreshVar "pf" tp >>= mrVarTerm

-- | Get the 'VarInfo' associated with a 'MRVar'
mrVarInfo :: MRVar -> MRM t (Maybe MRVarInfo)
mrVarInfo var = Map.lookup var <$> mrVars

-- | Convert an 'ExtCns' to a 'FunName'
extCnsToFunName :: ExtCns Term -> MRM t FunName
extCnsToFunName ec = let var = MRVar ec in mrVarInfo var >>= \case
  Just (EVarInfo _ _) -> return $ EVarFunName var
  Just (CallVarInfo _) -> return $ CallSName var
  Nothing
    | Just glob <- asTypedGlobalDef (Unshared $ FTermF $ ExtCns ec) ->
      return $ GlobalName glob []
  _ -> error "extCnsToFunName: unreachable"

-- | Get the 'FunName' of a global definition
mrGlobalDef :: Ident -> MRM t FunName
mrGlobalDef ident = asTypedGlobalDef <$> liftSC1 scGlobalDef ident >>= \case
  Just glob -> return $ GlobalName glob []
  _ -> error $ "mrGlobalDef: could not get GlobalDef of: " ++ show ident

-- | Get the body of a global definition, raising an 'error' if none is found
mrGlobalDefBody :: Ident -> MRM t Term
mrGlobalDefBody ident = asConstant <$> liftSC1 scGlobalDef ident >>= \case
  Just (_, Just body) -> return body
  _ -> error $ "mrGlobalDefBody: global has no definition: " ++ show ident

-- | Get the body of a function @f@ if it has one
mrFunNameBody :: FunName -> MRM t (Maybe Term)
mrFunNameBody (CallSName var) =
  mrVarInfo var >>= \case
  Just (CallVarInfo body) -> return $ Just body
  _ -> error "mrFunBody: unknown letrec var"
mrFunNameBody (GlobalName glob projs)
  | Just body <- globalDefBody glob
  = Just <$> foldM doTermProj body projs
mrFunNameBody (GlobalName _ _) = return Nothing
mrFunNameBody (EVarFunName _) = return Nothing

-- | Get the body of a function @f@ applied to some arguments, if possible
mrFunBody :: FunName -> [Term] -> MRM t (Maybe Term)
mrFunBody f args = mrFunNameBody f >>= \case
  Just body -> Just <$> mrApplyAll body args
  Nothing -> return Nothing

-- | Get the body of a function @f@ applied to some arguments, as per
-- 'mrFunBody', and also return whether its body recursively calls itself, as
-- per 'mrCallsFun'
mrFunBodyRecInfo :: FunName -> [Term] -> MRM t (Maybe (Term, Bool))
mrFunBodyRecInfo f args =
  mrFunNameBody f >>= \case
  Just body -> do
    body_applied <- mrApplyAll body args
    is_recursive <- mrCallsFun f body
    return $ Just (body_applied, is_recursive)
  Nothing -> return Nothing

-- | Test if a 'Term' contains, after possibly unfolding some functions, a call
-- to a given function @f@ again
mrCallsFun :: FunName -> Term -> MRM t Bool
mrCallsFun f = flip memoFixTermFunAccum Set.empty $ \recurse seen t ->
  let onFunName g = mrFunNameBody g >>= \case
        _ | f == g -> return True
        Just body | Set.notMember g seen -> recurse (Set.insert g seen) body
        _ -> return False
  in case t of
  (asExtCns -> Just ec) -> extCnsToFunName ec >>= onFunName
  (asGlobalFunName -> Just g) -> onFunName g
  (unwrapTermF -> tf) ->
    foldM (\b t' -> if b then return b else recurse seen t') False tf


----------------------------------------------------------------------
-- * Monadic Operations on Mr. Solver State
----------------------------------------------------------------------

-- | Make a fresh 'MRVar' of a given type, which must be closed, i.e., have no
-- free uvars
mrFreshVarCl :: LocalName -> Term -> MRM t MRVar
mrFreshVarCl nm tp = MRVar <$> liftSC2 scFreshEC nm tp

-- | Make a fresh 'MRVar' of type @(u1:tp1) -> ... (un:tpn) -> tp@, where the
-- @ui@ are all the current uvars
mrFreshVar :: LocalName -> Term -> MRM t MRVar
mrFreshVar nm tp = piUVarsM tp >>= mrFreshVarCl nm

-- | Set the info associated with an 'MRVar', assuming it has not been set
mrSetVarInfo :: MRVar -> MRVarInfo -> MRM t ()
mrSetVarInfo var info =
  mrDebugPPInCtxM 3 (prettyWithCtx emptyMRVarCtx $
                     prettyPrefixSep "mrSetVarInfo" var "=" info) >>
  (modify $ \st ->
   st { mrsVars =
          Map.alter (\case
                        Just _ -> error "mrSetVarInfo"
                        Nothing -> Just info)
          var (mrsVars st) })

-- | Make a fresh existential variable of the given type, abstracting out all
-- the current uvars and returning the new evar applied to all current uvars
mrFreshEVar :: LocalName -> Type -> MRM t Term
mrFreshEVar nm (Type tp) =
  do var <- mrFreshVar nm tp
     ctx_len <- mrVarCtxLength <$> mrUVars
     mrSetVarInfo var (EVarInfo ctx_len Nothing)
     mrVarTerm var

-- | Return a fresh sequence of existential variables from a 'MRVarCtx'.
-- Return the new evars all applied to the current uvars.
mrFreshEVars :: MRVarCtx -> MRM t [Term]
mrFreshEVars = helper [] . mrVarCtxOuterToInner where
  -- Return fresh evars for the suffix of a context of variable names and types,
  -- where the supplied Terms are evars that have already been generated for the
  -- earlier part of the context, and so must be substituted into the remaining
  -- types in the context. Since we want to make fresh evars for the oldest
  -- variables first, the second argument must be in outer-to-inner order.
  helper :: [Term] -> [(LocalName,Term)] -> MRM t [Term]
  helper evars [] = return evars
  helper evars ((nm,tp):ctx) =
    do evar <- substTerm 0 evars tp >>= mrFreshEVar nm . Type
       helper (evar:evars) ctx

-- | Set the value of an evar to a closed term
mrSetEVarClosed :: MRVar -> Term -> MRM t ()
mrSetEVarClosed var val =
  do val_tp <- mrTypeOf val
     -- NOTE: need to instantiate any evars in the type of var, to ensure the
     -- following subtyping check will succeed
     var_tp <- mrSubstEVars $ mrVarType var
     -- FIXME: catch subtyping errors and report them as being evar failures
     eith_err <-
       liftSC2 (runTCM $ checkSubtype (TypedTerm val val_tp) var_tp) Nothing []
     case eith_err of
       Left _ ->
         error ("mrSetEVarClosed: incorrect instantiation for evar " ++
                showMRVar var ++
                "\nexpected type:\n" ++ showTerm var_tp ++
                "\nactual type:\n" ++ showTerm val_tp)
       Right _ -> return ()
     modify $ \st ->
       st { mrsVars =
            Map.alter
            (\case
                Just (EVarInfo clen Nothing) -> Just $ EVarInfo clen (Just val)
                Just (EVarInfo _ (Just _)) ->
                  error "Setting existential variable: variable already set!"
                _ -> error "Setting existential variable: not an evar!")
            var (mrsVars st) }


-- | Try to set the value of the application @X e1 .. en@ of evar @X@ to an
-- expression @e@ by trying to set @X@ to @\ x1 ... xn -> e@. This only works if
-- each free uvar @xi@ in @e@ is one of the arguments @ej@ to @X@ (though it
-- need not be the case that @i=j@). Return whether this succeeded.
mrTrySetAppliedEVar :: MRVar -> [Term] -> Term -> MRM t Bool
mrTrySetAppliedEVar evar args t =
  -- Get the first N argument variables of the type of evar, where N is the
  -- length of args; note that evar can have more than N arguments if t is a
  -- higher-order term
  let (take (length args) -> evar_vars, _) = asPiList (mrVarType evar) in
  -- Get all the free variables of t
  let free_vars = bitSetElems (looseVars t) in
  -- For each free var of t, find an arg equal to it
  case mapM (\i -> findIndex (\case
                                 (asLocalVar -> Just j) -> i == j
                                 _ -> False) args) free_vars of
    Just fv_arg_ixs
      -- Check to make sure we have the right number of args
      | length args == length evar_vars -> do
          -- Build a list of the input vars x1 ... xn as terms, noting that the
          -- first variable is the least recently bound and so has the highest
          -- deBruijn index
          let arg_ixs = reverse [0 .. length args - 1]
          arg_vars <- mapM (liftSC1 scLocalVar) arg_ixs

          -- For each free variable of t, we substitute the corresponding
          -- variable xi, substituting error terms for the variables that are
          -- not free (since we have nothing else to substitute for them)
          let var_map = zip free_vars fv_arg_ixs
          let subst_vars = if free_vars == [] then [] else
                             [0 .. maximum free_vars]
          let subst = flip map subst_vars $ \i ->
                maybe (error
                       ("mrTrySetAppliedEVar: unexpected free variable "
                        ++ show i ++ " in term\n" ++ showTerm t))
                (arg_vars !!) (lookup i var_map)
          body <- substTerm 0 subst t

          -- Now instantiate evar to \x1 ... xn -> body
          evar_inst <- liftSC2 scLambdaList evar_vars body
          mrSetEVarClosed evar evar_inst
          return True

    _ -> return False


-- | Replace all evars in a 'Term' with their instantiations when they have one
mrSubstEVars :: Term -> MRM t Term
mrSubstEVars = memoFixTermFun $ \recurse t ->
  do var_map <- mrVars
     case t of
       -- If t is an instantiated evar, recurse on its instantiation
       (asEVarApp var_map -> Just (_, _, args, Just t')) ->
         mrApplyAll t' args >>= recurse
       -- If t is anything else, recurse on its immediate subterms
       _ -> traverseSubterms recurse t

-- | Replace all evars in a 'Term' with their instantiations when they have one
-- and \"lower\" those that do not. Lowering an evar in this context means
-- replacing each occurrence @X x1 .. xn@ of an evar @X@ applied to its context
-- of uvars with a fresh 'ExtCns' variable @Y@. This must be done after
-- 'instantiateUVarsM' has replaced all uvars with fresh 'ExtCns' variables,
-- which ensures that @X x1 .. xn@ is actually a closed, top-level term since
-- each @xi@ is now an 'ExtCns'. This is necessary so @X x1 .. xn@ can be
-- replaced by an 'ExtCns' @Y@, which is always closed. The idea of lowering is
-- that @X@ should always occur applied to these same values, so really we can
-- just treat the entire expression @X x1 .. xn@ as a single unknown value,
-- rather than worrying about how @X@ depends on its inputs.
mrSubstLowerEVars :: Term -> MRM t Term
mrSubstLowerEVars t_top =
  do var_map <- mrVars
     lower_map <- liftIO $ newIORef Map.empty
     flip memoFixTermFun t_top $ \recurse t ->
       case t of
         -- If t is an instantiated evar, recurse on its instantiation
         (asEVarApp var_map -> Just (_, _, args, Just t')) ->
           mrApplyAll t' args >>= recurse
         -- If t is an uninstantiated evar, look up or create its lowering as a
         -- variable, making sure it is applied to evars for its arguments
         (asEVarApp var_map -> Just (evar, clen, args, Nothing)) ->
           do let (cargs, args') = splitAt clen args
              let my_panic :: () -> a
                  my_panic () =
                    panic "mrSubstLowerEVars"
                    ["Unexpected evar application: " ++ show t]
              let cargs_ec = fromMaybe (my_panic ()) $ mapM asExtCns cargs
              t' <- (Map.lookup evar <$> liftIO (readIORef lower_map)) >>= \case
                Just (y, cargs_expected) ->
                  if cargs_ec == cargs_expected then return y else my_panic ()
                Nothing ->
                  do y_tp <- mrPiApplyAll (mrVarType evar) cargs
                     y <- liftSC2 scFreshGlobal (T.pack $ showMRVar evar) y_tp
                     liftIO $ modifyIORef' lower_map $
                       Map.insert evar (y,cargs_ec)
                     return y
              mrApplyAll t' args' >>= recurse
         -- If t is anything else, recurse on its immediate subterms
         _ -> traverseSubterms recurse t

-- | Replace all evars in a 'Term' with their instantiations, returning
-- 'Nothing' if we hit an uninstantiated evar
mrSubstEVarsStrict :: Term -> MRM t (Maybe Term)
mrSubstEVarsStrict top_t =
  runMaybeT $ flip memoFixTermFun top_t $ \recurse t ->
  do var_map <- lift mrVars
     case t of
       -- If t is an instantiated evar, recurse on its instantiation
       (asEVarApp var_map -> Just (_, _, args, Just t')) ->
         lift (mrApplyAll t' args) >>= recurse
       -- If t is an uninstantiated evar, return Nothing
       (asEVarApp var_map -> Just (_, _, _, Nothing)) ->
         mzero
       -- If t is anything else, recurse on its immediate subterms
       _ -> traverseSubterms recurse t

-- | Makes 'mrSubstEVarsStrict' be marked as used
_mrSubstEVarsStrict :: Term -> MRM t (Maybe Term)
_mrSubstEVarsStrict = mrSubstEVarsStrict

-- | Get the 'CoIndHyp' for a pair of 'FunName's, if there is one
mrGetCoIndHyp :: FunName -> FunName -> MRM t (Maybe CoIndHyp)
mrGetCoIndHyp nm1 nm2 = Map.lookup (nm1, nm2) <$> mrCoIndHyps

-- | Run a compuation under an additional co-inductive assumption
withCoIndHyp :: CoIndHyp -> MRM t a -> MRM t a
withCoIndHyp hyp m =
  do mrDebugPPInCtxM 2 (prettyWithCtx emptyMRVarCtx $
                        prettyPrefix "withCoIndHyp" hyp)
     hyps' <- Map.insert (coIndHypLHSFun hyp,
                          coIndHypRHSFun hyp) hyp <$> mrCoIndHyps
     local (\info -> info { mriCoIndHyps = hyps' }) m

-- | Generate fresh evars for the context of a 'CoIndHyp' and
-- substitute them into its arguments and right-hand side
instantiateCoIndHyp :: CoIndHyp -> MRM t ([Term], [Term])
instantiateCoIndHyp (CoIndHyp {..}) =
  do evars <- mrFreshEVars coIndHypCtx
     lhs <- substTermLike 0 evars coIndHypLHS
     rhs <- substTermLike 0 evars coIndHypRHS
     return (lhs, rhs)

-- | Apply the invariants of a 'CoIndHyp' to their respective arguments,
-- yielding @Bool@ conditions, using the constant @True@ value when an
-- invariant is absent
applyCoIndHypInvariants :: CoIndHyp -> MRM t (Term, Term)
applyCoIndHypInvariants hyp =
  let apply_invariant :: Maybe Term -> [Term] -> MRM t Term
      apply_invariant (Just (asLambdaList -> (vars, phi))) args
        | length vars == length args
          -- NOTE: applying to a list of arguments == substituting the reverse
          -- of that list, because the first argument corresponds to the
          -- greatest deBruijn index
        = substTerm 0 (reverse args) phi
      apply_invariant (Just _) _ =
        error "applyCoIndHypInvariants: wrong number of arguments for invariant!"
      apply_invariant Nothing _ = liftSC1 scBool True in
  do invar1 <- apply_invariant (coIndHypInvariantLHS hyp) (coIndHypLHS hyp)
     invar2 <- apply_invariant (coIndHypInvariantRHS hyp) (coIndHypRHS hyp)
     return (invar1, invar2)

-- | Look up the 'FunAssump' for a 'FunName', if there is one
mrGetFunAssump :: FunName -> MRM t (Maybe (FunAssump t))
mrGetFunAssump nm = lookupFunAssump nm <$> mrRefnset

-- | Run a computation under the additional assumption that a named function
-- applied to a list of arguments refines a given right-hand side, all of which
-- are 'Term's that can have the current uvars free
withFunAssump :: FunName -> [Term] -> Term -> MRM t a -> MRM t a
withFunAssump fname args rhs m =
  do k <- mkCompFunReturn <$> mrFunOutType fname args
     mrDebugPPPrefixSep 1 "withFunAssump" (FunBind fname args k)
                                     "|=" rhs
     ctx <- mrUVars
     rs <- mrRefnset
     let assump = FunAssump ctx fname args (RewriteFunAssump rhs) Nothing
     let rs' = addFunAssump assump rs
     local (\info -> info { mriRefnset = rs' }) m

-- | Get the invariant hint associated with a function name, by unfolding the
-- name and checking if its body has the form
--
-- > \ x1 ... xn -> invariantHint a phi m
--
-- If so, return @\ x1 ... xn -> phi@ as a term with the @xi@ variables free.
-- Otherwise, return 'Nothing'. Note that this function will also look past
-- any initial @bindS ... (assertFiniteS ...)@ applications.
mrGetInvariant :: FunName -> MRM t (Maybe Term)
mrGetInvariant nm =
  mrFunNameBody nm >>= \case
    Just body -> mrGetInvariantBody body
    _ -> return Nothing

-- | The main loop of 'mrGetInvariant', which operates on a function body
mrGetInvariantBody :: Term -> MRM t (Maybe Term)
mrGetInvariantBody tm = case asApplyAll tm of
  -- go inside any top-level lambdas
  (asLambda -> Just (nm, tp, body), []) ->
    do body' <- liftSC1 betaNormalize body
       mb_phi <- mrGetInvariantBody body'
       liftSC3 scLambda nm tp `mapM` mb_phi
  -- always beta-reduce
  (f@(asLambda -> Just _), args) ->
    do tm' <- mrApplyAll f args
       mrGetInvariantBody tm'
  -- go inside any top-level applications of of bindS ... (assertFiniteS ...)
  (isGlobalDef "SpecM.bindS" -> Just (),
   [_, _, _,
    (asApplyAll -> (isGlobalDef "CryptolM.assertFiniteS" -> Just (),
                    [_, (asCtor -> Just (primName -> "Cryptol.TCNum", _))])),
    k]) ->
    do pf <- liftSC1 scGlobalDef "Prelude.TrueI"
       body <- mrApplyAll k [pf]
       mrGetInvariantBody body
  -- otherwise, return Just iff there is a top-level invariant hint
  (isGlobalDef "SpecM.invariantHint" -> Just (),
   [_, phi, _]) -> return $ Just phi
  _ -> return Nothing

-- | Add an assumption of type @Bool@ to the current path condition while
-- executing a sub-computation
withAssumption :: Term -> MRM t a -> MRM t a
withAssumption phi m =
  do mrDebugPPPrefix 1 "withAssumption" phi
     assumps <- mrAssumptions
     assumps' <- liftSC2 scAnd phi assumps
     local (\info -> info { mriAssumptions = assumps' }) m

-- | Remove any existing assumptions and replace them with a Boolean term
withOnlyAssumption :: Term -> MRM t a -> MRM t a
withOnlyAssumption phi m =
  do mrDebugPPPrefix 1 "withOnlyAssumption" phi
     local (\info -> info { mriAssumptions = phi }) m

-- | Add a 'DataTypeAssump' to the current context while executing a
-- sub-computations
withDataTypeAssump :: Term -> DataTypeAssump -> MRM t a -> MRM t a
withDataTypeAssump x assump m =
  do mrDebugPPPrefixSep 1 "withDataTypeAssump" x "==" assump
     dataTypeAssumps' <- HashMap.insert x assump <$> mrDataTypeAssumps
     local (\info -> info { mriDataTypeAssumps = dataTypeAssumps' }) m

-- | Get the 'DataTypeAssump' associated to the given term, if one exists
mrGetDataTypeAssump :: Term -> MRM t (Maybe DataTypeAssump)
mrGetDataTypeAssump x = HashMap.lookup x <$> mrDataTypeAssumps

-- | Record a use of an SMT solver (for tracking 'SolverStats' and 'MRSolverEvidence')
recordUsedSolver :: SolverStats -> Term -> MRM t ()
recordUsedSolver stats prop =
  modify $ \st -> st { mrsSolverStats = stats <> mrsSolverStats st,
                       mrsEvidence = MREUsedSolver stats prop : mrsEvidence st }

-- | Record a use of a 'FunAssump' (for 'MRSolverEvidence')
recordUsedFunAssump :: FunAssump t -> MRM t ()
recordUsedFunAssump (fassumpAnnotation -> Just t) =
  modify $ \st -> st { mrsEvidence = MREUsedFunAssump t : mrsEvidence st }
recordUsedFunAssump _ = return ()


----------------------------------------------------------------------
-- * Functions for Debug Output
----------------------------------------------------------------------

-- | Print a 'String' to 'stderr' if the debug level is at least the supplied
-- 'Int'
mrDebugPrint :: Int -> String -> MRM t ()
mrDebugPrint i str =
  mrDebugLevel >>= \lvl ->
  if lvl >= i then liftIO (hPutStrLn stderr str) else return ()

-- | Print a document to 'stderr' if the debug level is at least the supplied
-- 'Int'
mrDebugPretty :: Int -> SawDoc -> MRM t ()
mrDebugPretty i pp =
  mrPPOpts >>= \opts ->
  mrDebugPrint i (renderSawDoc opts pp)

-- | Print to 'stderr' the result of running a 'PPInCtxM' computation in the
-- current context and with the current 'PPOpts' if the current debug level is
-- at least the supplied 'Int'
mrDebugPPInCtxM :: Int -> PPInCtxM SawDoc -> MRM t ()
mrDebugPPInCtxM i m = mrDebugPretty i =<< mrPPInCtxM m

-- | Pretty-print an object to 'stderr' in the current context and with the
-- current 'PPOpts' if the current debug level is at least the supplied 'Int'
mrDebugPPInCtx :: PrettyInCtx a => Int -> a -> MRM t ()
mrDebugPPInCtx i a = mrDebugPretty i =<< mrPPInCtx a

-- | Pretty-print the result of 'prettyPrefix' to 'stderr' in the
-- current context and with the current 'PPOpts' if the debug level is at least
-- the 'Int' provided
mrDebugPPPrefix :: PrettyInCtx a => Int -> String -> a -> MRM t ()
mrDebugPPPrefix i pre a =
  mrDebugPPInCtxM i $ group <$> nest 2 <$> prettyPrefix pre a

-- | Pretty-print the result of 'prettyPrefixSep' to 'stderr' in the current
-- context and with the current 'PPOpts' if the debug level is at least the
-- 'Int' provided
mrDebugPPPrefixSep :: (PrettyInCtx a, PrettyInCtx b) =>
                      Int -> String -> a -> String -> b -> MRM t ()
mrDebugPPPrefixSep i pre a1 sp a2 =
  mrDebugPPInCtxM i $ group <$> nest 2 <$> prettyPrefixSep pre a1 sp a2
