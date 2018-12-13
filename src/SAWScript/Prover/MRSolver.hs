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

-- | Representation of monadic computations
data Comp
  = Return Term
  | Error
  | If Term Comp Comp
  | FunBind CompFun [Term] Comp

-- | FIXME: make this have better error messages
data MRFailure
  = TermsNotEq Term Term
  | ReturnNotError Term

-- | State maintained by MR solver; that's MR. State to you
data MRState = MRState {
  mrSC :: SharedContext,
  mrSMTConfig :: SBV.SMTConfig,
  mrLocalFuns :: [(ExtCns Term, Comp)],
  mrFunEqs :: [(CompFun, CompFun)],
  mrPathCondition :: Term
}

-- | Monad used by the MR solver
-- newtype MRM a = MRM { runMRM :: StateT MRState (ExceptT MRFailure IO) a }
type MRM = ExceptT MRFailure (StateT MRState IO)

liftSC1 :: (SharedContext -> a -> IO b) -> a -> MRM b
liftSC1 f a = (mrSC <$> get) >>= \sc -> liftIO (f sc a)

-- | Convert a SAW term of type @CompM a@ to a 'Comp'
sawToComp :: Term -> MRM Comp
sawToComp = undefined

-- | Test if two terms are equal using an SMT solver
mrTermsEq :: Term -> Term -> MRM Bool
mrTermsEq = undefined

-- | Assert that two terms are equal, failing if not
mrAssertEq :: Term -> Term -> MRM ()
mrAssertEq t1 t2 =
  do eq <- mrTermsEq t1 t2
     if eq then return () else throwE (TermsNotEq t1 t2)

-- | Test if a term is equal to a Boolean
mrTermEqBool :: Term -> Bool -> MRM Bool
mrTermEqBool t b = mrTermsEq t =<< liftSC1 scBool b

-- | Test if a Boolean term is satisfiable
mrSatisfiable :: Term -> MRM Bool
mrSatisfiable = undefined

-- | Run an equality-testing computation under the assumption of an additional
-- path condition. If the condition is unsatisfiable, the test is vacuously
-- true, so need not be run.
withPathCondition :: Term -> MRM () -> MRM ()
withPathCondition cond m =
  do sat <- mrSatisfiable cond
     if sat then m else return ()

withNotPathCondition :: Term -> MRM () -> MRM ()
withNotPathCondition cond m =
  liftSC1 scNot cond >>= \cond' -> withPathCondition cond' m

-- | Try to prove that two computations are equal. We assume that the current
-- path conditions are always satisfiable.
mrSolveComps :: Comp -> Comp -> MRM ()
mrSolveComps (Return t1) (Return t2) = mrAssertEq t1 t2
mrSolveComps (Return t1) Error = throwE (ReturnNotError t1)
mrSolveComps Error (Return t2) = throwE (ReturnNotError t2)
mrSolveComps Error Error = return ()
mrSolveComps (If cond1 then1 else1) comp2@(If cond2 then2 else2) =
  -- Special case if the two conditions are equal
  do eq <- mrTermsEq cond1 cond2
     if eq then
       (withPathCondition cond1 $ mrSolveComps then1 then2) >>
       (withNotPathCondition cond1 $ mrSolveComps else1 else2)
       else
       (withPathCondition cond1 $ mrSolveComps then1 comp2) >>
       (withNotPathCondition cond1 $ mrSolveComps else1 comp2)
mrSolveComps (If cond1 then1 else1) comp2 =
  (withPathCondition cond1 $ mrSolveComps then1 comp2) >>
  (withNotPathCondition cond1 $ mrSolveComps else1 comp2)
mrSolveComps comp1 (If cond2 then2 else2) =
  (withPathCondition cond2 $ mrSolveComps comp1 then2) >>
  (withNotPathCondition cond2 $ mrSolveComps comp1 else2)

-- | Test two monadic, recursive terms for equivalence
askMRSolver ::
  SBV.SMTConfig {- ^ SBV configuration -} ->
  Maybe Integer {- ^ Timeout in milliseconds -} ->
  Term -> Term -> IO (Maybe MRFailure)

askMRSolver = error "askMRSolver not yet written!"
