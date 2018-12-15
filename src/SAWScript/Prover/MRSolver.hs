{-# LANGUAGE MultiParamTypeClasses #-}

module SAWScript.Prover.MRSolver
  (askMRSolver
  , SBV.SMTConfig
  , SBV.z3, SBV.cvc4, SBV.yices, SBV.mathSAT, SBV.boolector
  ) where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

import Verifier.SAW.SharedTerm
import Verifier.SAW.Recognizer

import qualified SAWScript.Prover.SBV as SBV

newtype LocalFunName = LocalFunName (ExtCns Term) deriving Eq

-- | Names of functions to be used in computations, which are either local,
-- letrec-bound names (represented with an 'ExtCns'), or global named constants
data FunName = LocalFun LocalFunName | GlobalFun String
             deriving Eq

-- | A pattern for matching the form of a computation
data CompPat
  = Return Term -- ^ Terminates with a return
  | Error -- ^ Raises an error
  | If Term CompTerm CompTerm -- ^ If-then-else that returns @CompM a@
  | FunBind FunName [Term] CompFunTerm
    -- ^ Bind a monadic function with @N@ arguments in an @a -> CompM b@ term

-- | Term of type @CompM a@ for some @a@
newtype CompTerm = CompTerm Term

-- | Term of type @a -> CompM b@ for some @a@ and @b@
newtype CompFunTerm = CompFunTerm Term

-- | FIXME: make this have better error messages
data MRFailure
  = TermsNotEq Term Term
  | ReturnNotError Term
  | FunsNotEq FunName FunName
  | MRFailureCtx CompTerm CompTerm MRFailure
    -- ^ Records terms we were trying to compare when we got a failure
  | MRFailureDisj MRFailure MRFailure
    -- ^ Records a disjunctive branch we took, where both cases failed

data FunBody = FunBody { funTerm :: CompFunTerm,
                         funFreeVars :: [LocalFunName] }

-- | Environment maintained by MR solver; that's MR. Environment to you
data MREnv = MREnv {
  mrSC :: SharedContext,
  mrSMTConfig :: SBV.SMTConfig,
  mrLocalFuns :: [(LocalFunName, FunBody)],
  mrFunEqs :: [(FunName, FunName)],
  mrUnfoldedFuns :: [LocalFunName],
  mrPathCondition :: Term
}

data MRState = MRState {
  mrProvedFunEqs :: [(FunName, FunName)]
}

-- | Monad used by the MR solver
type MRM = ExceptT MRFailure (ReaderT MREnv (StateT MRState IO))

-- | Run an 'MRM' computation, and apply a function to any failure thrown
mapFailure :: (MRFailure -> MRFailure) -> MRM a -> MRM a
mapFailure f m = catchError m (throwError . f)

-- | Try two different 'MRM' computations, combining their failures if needed
mrOr :: MRM a -> MRM a -> MRM a
mrOr m1 m2 =
  catchError m1 $ \err1 ->
  catchError m2 $ \err2 ->
  throwError $ MRFailureDisj err1 err2

-- | Run an 'MRM' computation in an extended failure context
withFailureCtx :: CompTerm -> CompTerm -> MRM a -> MRM a
withFailureCtx t1 t2 = mapFailure (MRFailureCtx t1 t2)

catchErrorEither :: MonadError e m => m a -> m (Either e a)
catchErrorEither m = catchError (Right <$> m) (return . Left)

-- | Lift a unary SharedTerm computation into 'MRM'
liftSC1 :: (SharedContext -> a -> IO b) -> a -> MRM b
liftSC1 f a = (mrSC <$> ask) >>= \sc -> liftIO (f sc a)

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
mrUnfoldFunBind :: FunName -> [Term] -> CompFunTerm -> MRM CompPat
mrUnfoldFunBind = undefined

-- | Typeclass for proving that an @a@ and a @b@ represent equivalent
-- computations. The 'MRM' computation returns @()@ on success and throws an
-- 'MRFailure' on error.
class MRSolveEq a b where
  mrSolveEq :: a -> b -> MRM ()

instance MRSolveEq Term Term where
  mrSolveEq t1 t2 =
    do eq <- mrTermsEq t1 t2
       if eq then return () else throwError (TermsNotEq t1 t2)

instance MRSolveEq FunName FunName where
  mrSolveEq f1 f2 = undefined

instance MRSolveEq CompTerm CompTerm where
  mrSolveEq t1 t2 =
    do comp1 <- matchCompTerm t1
       comp2 <- matchCompTerm t2
       withFailureCtx t1 t2 (mrSolveEq comp1 comp2)

instance MRSolveEq CompFunTerm CompFunTerm where
  mrSolveEq t1 t2 = undefined

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
    throwError (ReturnNotError t1)
  mrSolveEq Error (Return t2) =
    -- Return is never equal to error
    throwError (ReturnNotError t2)
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
    -- To compare two computations (f1 args1 >>= comp1) and (f2 args2 >>= comp2)
    -- we first test if (f1 args1) and (f2 args2) are equal. If so, we recurse
    -- and compare comp1 and comp2; otherwise, we try unfolding one or the other
    -- of f1 and f2.
    catchErrorEither cmp_funs >>= \ cmp_fun_res ->
    case cmp_fun_res of
      Right () -> mrSolveEq comp1 comp2
      Left err ->
        mapFailure (MRFailureDisj err) $
        (mrUnfoldFunBind f1 args1 comp1 >>= \c -> mrSolveEq c p2)
        `mrOr`
        (mrUnfoldFunBind f2 args2 comp2 >>= \c -> mrSolveEq p1 c)
    where
      cmp_funs = mrSolveEq f1 f2 >> zipWithM_ mrSolveEq args1 args2
  mrSolveEq (FunBind f1 args1 comp1) p2 =
    -- This case compares a function call to a Return or Error; the only thing
    -- to do is unfold the function call and recurse
    mrUnfoldFunBind f1 args1 comp1 >>= \c -> mrSolveEq c p2
  mrSolveEq p1 (FunBind f2 args2 comp2) =
    -- This case compares a function call to a Return or Error; the only thing
    -- to do is unfold the function call and recurse
    mrUnfoldFunBind f2 args2 comp2 >>= \c -> mrSolveEq p1 c

-- | Test two monadic, recursive terms for equivalence
askMRSolver ::
  SBV.SMTConfig {- ^ SBV configuration -} ->
  Maybe Integer {- ^ Timeout in milliseconds -} ->
  Term -> Term -> IO (Maybe MRFailure)

askMRSolver = undefined
