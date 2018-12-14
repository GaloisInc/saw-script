{-# LANGUAGE MultiParamTypeClasses #-}

module SAWScript.Prover.MRSolver
  (askMRSolver
  , SBV.SMTConfig
  , SBV.z3, SBV.cvc4, SBV.yices, SBV.mathSAT, SBV.boolector
  ) where

import Control.Monad.State
import Control.Monad.Trans.Except

import Verifier.SAW.SharedTerm
import Verifier.SAW.Recognizer

import qualified SAWScript.Prover.SBV as SBV

-- | Functions to be used in computations, which are either local, letrec-bound
-- names (represented with an 'ExtCns'), or global named constants
data CompFun = LocalFun (ExtCns Term) | GlobalFun String
             deriving Eq

-- | A pattern for matching the form of a computation
data CompPat
  = Return Term -- ^ Terminates with a return
  | Error -- ^ Raises an error
  | If Term CompTerm CompTerm -- ^ If-then-else that returns @CompM a@
  | FunBind CompFun [Term] CompFunTerm
    -- ^ Bind a monadic function with @N@ arguments in an @a -> CompM b@ term

-- | Term of type @CompM a@ for some @a@
newtype CompTerm = CompTerm Term

-- | Term of type @a -> CompM b@ for some @a@ and @b@
newtype CompFunTerm = CompFunTerm Term

-- | FIXME: make this have better error messages
data MRFailure
  = TermsNotEq Term Term
  | ReturnNotError Term
  | FunsNotEq CompFun CompFun

-- | State maintained by MR solver; that's MR. State to you
data MRState = MRState {
  mrSC :: SharedContext,
  mrSMTConfig :: SBV.SMTConfig,
  mrLocalFuns :: [(ExtCns Term, Term)],
  mrFunEqs :: [(CompFun, CompFun)],
  mrPathCondition :: Term
}

-- | Monad used by the MR solver
-- newtype MRM a = MRM { runMRM :: StateT MRState (ExceptT MRFailure IO) a }
type MRM = ExceptT MRFailure (StateT MRState IO)

liftSC1 :: (SharedContext -> a -> IO b) -> a -> MRM b
liftSC1 f a = (mrSC <$> get) >>= \sc -> liftIO (f sc a)

-- | Test if the types of two terms are equal
mrFunTypesEq :: CompFun -> CompFun -> MRM Bool
mrFunTypesEq = undefined

-- | Test if a Boolean term is satisfiable
mrSatisfiable :: Term -> MRM Bool
mrSatisfiable = undefined

-- | Test if two terms are equal using an SMT solver
mrTermsEq :: Term -> Term -> MRM Bool
mrTermsEq = undefined

-- | Test if a term is equal to a Boolean
mrTermEqBool :: Term -> Bool -> MRM Bool
mrTermEqBool t b = mrTermsEq t =<< liftSC1 scBool b

-- | Run an equality-testing computation under the assumption of an additional
-- path condition. If the condition is unsatisfiable, the test is vacuously
-- true, so need not be run.
withPathCondition :: Term -> MRM () -> MRM ()
withPathCondition cond m =
  do sat <- mrSatisfiable cond
     if sat then m else return ()

-- | Like 'withPathCondition' but for the negation of a condition
withNotPathCondition :: Term -> MRM () -> MRM ()
withNotPathCondition cond m =
  liftSC1 scNot cond >>= \cond' -> withPathCondition cond' m

-- | Convert a 'Term' to a computation pattern
matchCompTerm :: CompTerm -> MRM CompPat
matchCompTerm = undefined

-- | FIXME: documentation!
mrUnfoldFun :: CompFun -> [Term] -> CompFunTerm -> MRM CompPat
mrUnfoldFun = undefined

mrCanUnfold :: CompFun -> MRM Bool
mrCanUnfold = undefined

-- | Typeclass for proving that an @a@ and a @b@ represent equivalent
-- computations. The 'MRM' computation returns @()@ on success and throws an
-- 'MRFailure' on error.
class MRSolveEq a b where
  mrSolveEq :: a -> b -> MRM ()

instance MRSolveEq Term Term where
  mrSolveEq t1 t2 =
    do eq <- mrTermsEq t1 t2
       if eq then return () else throwE (TermsNotEq t1 t2)

instance MRSolveEq CompFun CompFun where
  mrSolveEq f1 f2 = undefined

instance MRSolveEq CompTerm CompTerm where
  mrSolveEq t1 t2 =
    do comp1 <- matchCompTerm t1
       comp2 <- matchCompTerm t2
       mrSolveEq comp1 comp2

instance MRSolveEq CompTerm CompPat where
  mrSolveEq t1 comp2 =
    do comp1 <- matchCompTerm t1
       mrSolveEq comp1 comp2

instance MRSolveEq CompPat CompTerm where
  mrSolveEq comp1 t2 =
    do comp2 <- matchCompTerm t2
       mrSolveEq comp1 comp2

instance MRSolveEq CompPat CompPat where
  mrSolveEq (Return t1) (Return t2) =
    -- Returns are equal iff their returned values are
    mrSolveEq t1 t2
  mrSolveEq (Return t1) Error =
    -- Return is never equal to error
    throwE (ReturnNotError t1)
  mrSolveEq Error (Return t2) =
    -- Return is never equal to error
    throwE (ReturnNotError t2)
  mrSolveEq Error Error =
    -- Error trivially equals itself
    return ()
  mrSolveEq (If cond1 then1 else1) comp2@(If cond2 then2 else2) =
    -- Special case if the two conditions are equal: assert the one condition to
    -- test the then branches and assert its negtion to test the elses
    do eq <- mrTermsEq cond1 cond2
       if eq then
         (withPathCondition cond1 $ mrSolveEq then1 then2) >>
         (withNotPathCondition cond1 $ mrSolveEq else1 else2)
         else
         -- Otherwise, compare the first then and else, under their respective
         -- path conditions, to the whole second computation
         (withPathCondition cond1 $ mrSolveEq then1 comp2) >>
         (withNotPathCondition cond1 $ mrSolveEq else1 comp2)
  mrSolveEq (If cond1 then1 else1) comp2 =
    -- To compare an if to anything else, compare the then and else, under their
    -- respective path conditions, to the other computation
    (withPathCondition cond1 $ mrSolveEq then1 comp2) >>
    (withNotPathCondition cond1 $ mrSolveEq else1 comp2)
  mrSolveEq comp1 (If cond2 then2 else2) =
    -- To compare an if to anything else, compare the then and else, under their
    -- respective path conditions, to the other computation
    (withPathCondition cond2 $ mrSolveEq comp1 then2) >>
    (withNotPathCondition cond2 $ mrSolveEq comp1 else2)
  mrSolveEq p1@(FunBind f1 args1 comp1) p2@(FunBind f2 args2 comp2) =
    -- If we have two function calls whose arguments are equal, then we guess
    -- that they are supposed to be equal
    do tps_eq <- mrFunTypesEq f1 f2
       test_res <-
         if tps_eq && length args1 == length args2 then
           Right <$> test_args args1 args2
         else return (Left ())
       case test_res of
         Right Nothing ->
           -- If all terms are equal, compare the functions
           mrSolveEq f1 f2
         Right bad_ts@(Just _) ->
           -- If not, that may be the failure, so pass it forwards
           unfoldFun bad_ts
         Left () ->
           -- If the funs are of different types, then they definitely cannot be
           -- equal, so pass Nothing forwards
           unfoldFun Nothing
    where
      -- Test if two lists of terms are equal; return the first failure if not
      test_args :: [Term] -> [Term] -> MRM (Maybe (Term,Term))
      test_args (a1:as1) (a2:as2) =
        do eq <- mrTermsEq a1 a2
           if eq then test_args as1 as2 else return (Just (a1,a2))
      test_args [] [] = return Nothing
      test_args _ _ = error "test_args"

      -- Unfold one of the functions, if possible, and continue
      unfoldFun :: Maybe (Term,Term) -> MRM ()
      unfoldFun term_neq =
        do can_unfold1 <- mrCanUnfold f1
           can_unfold2 <- mrCanUnfold f2
           case (can_unfold1, can_unfold2, term_neq) of
             (True, _, _) -> mrUnfoldFun f1 args1 comp1 >>= \c -> mrSolveEq c p2
             (_, True, _) -> mrUnfoldFun f2 args2 comp2 >>= \c -> mrSolveEq p1 c
             (_, _, Just (t1, t2)) -> throwE (TermsNotEq t1 t2)
             (_, _, Nothing) -> throwE (FunsNotEq f1 f2)

-- | Test two monadic, recursive terms for equivalence
askMRSolver ::
  SBV.SMTConfig {- ^ SBV configuration -} ->
  Maybe Integer {- ^ Timeout in milliseconds -} ->
  Term -> Term -> IO (Maybe MRFailure)

askMRSolver = undefined
