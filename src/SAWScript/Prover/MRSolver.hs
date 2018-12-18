{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

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
data FunName = LocalName LocalFunName | GlobalName Ident
             deriving Eq

-- | A "marking" consisting of a set of unfolded function names
newtype Mark = Mark [FunName] deriving (Semigroup, Monoid)

inMark :: FunName -> Mark -> Bool
inMark f (Mark fs) = elem f fs

singleMark :: FunName -> Mark
singleMark f = Mark [f]

-- | A computation in WHNF
data WHNFComp
  = Return Term -- ^ Terminates with a return
  | Error -- ^ Raises an error
  | If Term Comp Comp -- ^ If-then-else that returns @CompM a@
  | FunBind FunName [Term] Mark CompFun
    -- ^ Bind a monadic function with @N@ arguments in an @a -> CompM b@ term,
    -- marked with a set of function names

-- | A computation function of type @a -> CompM b@ for some @a@ and @b@
data CompFun
  = CompFunTerm Term
  | CompFunComp CompFun CompFun
    -- ^ The monadic composition @f >=> g@
  | CompFunMark CompFun Mark
    -- ^ A computation marked with function names

-- | A computation of type @CompM a@ for some @a@
data Comp = CompTerm Term | CompBind Comp CompFun | CompMark Comp Mark

-- | That's MR. Failure to you
data MRFailure
  = TermsNotEq Term Term
  | ReturnNotError Term
  | FunsNotEq FunName FunName
  | CannotLookupFunDef FunName
  | RecursiveUnfold FunName
  | MalformedComp Term
  | MRFailureCtx Comp Comp MRFailure
    -- ^ Records terms we were trying to compare when we got a failure
  | MRFailureDisj MRFailure MRFailure
    -- ^ Records a disjunctive branch we took, where both cases failed

-- | State maintained by MR. Solver
data MRState = MRState {
  mrSC :: SharedContext,
  -- ^ Global shared context for building terms, etc.
  mrSMTConfig :: SBV.SMTConfig,
  -- ^ Global SMT configuration for the duration of the MR. Solver call
  mrLocalFuns :: [(LocalFunName, Term)],
  -- ^ Letrec-bound function names with their definitions as lambda-terms
  mrFunEqs :: [((FunName, FunName), Bool)],
  -- ^ Cache of which named functions are equal
  mrPathCondition :: Term
  -- ^ The conjunction of all Boolean if conditions along the current path
}

-- | Monad used by the MR. Solver
type MRM = ExceptT MRFailure (StateT MRState IO)

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
withFailureCtx :: Comp -> Comp -> MRM a -> MRM a
withFailureCtx t1 t2 = mapFailure (MRFailureCtx t1 t2)

catchErrorEither :: MonadError e m => m a -> m (Either e a)
catchErrorEither m = catchError (Right <$> m) (return . Left)

-- | Lift a unary SharedTerm computation into 'MRM'
liftSC1 :: (SharedContext -> a -> IO b) -> a -> MRM b
liftSC1 f a = (mrSC <$> get) >>= \sc -> liftIO (f sc a)

-- | Lift a binary SharedTerm computation into 'MRM'
liftSC2 :: (SharedContext -> a -> b -> IO c) -> a -> b -> MRM c
liftSC2 f a b = (mrSC <$> get) >>= \sc -> liftIO (f sc a b)

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

-- | Get the input type of a computation function
compFunInputType :: CompFun -> MRM Term
compFunInputType = undefined

-- | Match a term as a function name
asFunName :: MonadPlus m => Recognizer m Term FunName
asFunName t =
  (LocalName <$> LocalFunName <$> asExtCns t)
  `mplus` (GlobalName <$> asGlobalDef t)

-- | Apply a computation function to a term argument to get a computation
applyCompFun :: CompFun -> Term -> MRM Comp
applyCompFun (CompFunComp f g) t =
  -- (f >=> g) t == f t >>= g
  do comp <- applyCompFun f t
     return $ CompBind comp g
applyCompFun (CompFunTerm f) t =
  CompTerm <$> liftSC2 scApply f t
applyCompFun (CompFunMark f mark) t =
  do comp <- applyCompFun f t
     return $ CompMark comp mark

-- | Take in an @InputOutputTypes@ list (as a SAW core term) and build a fresh
-- function variable for each pair of input and output types in it. Return the
-- list of these names along with a term of them tupled up together.
mkFunVarsForTps :: Term -> MRM ([LocalFunName], Term)
mkFunVarsForTps = undefined

-- | Normalize a computation to weak head normal form
whnfComp :: Comp -> MRM WHNFComp
whnfComp (CompBind m f) =
  do norm <- whnfComp m
     whnfBind norm f
whnfComp (CompMark m mark) =
  do norm <- whnfComp m
     whnfMark norm mark
whnfComp (CompTerm t) =
  do t' <- liftSC1 scWhnf t
     case asApplyAll t' of
       (isGlobalDef "Prelude.returnM" -> Just (), [_, x]) ->
         return $ Return x
       (isGlobalDef "Prelude.bindM" -> Just (), [_, _, m, f]) ->
         do norm <- whnfComp (CompTerm m)
            whnfBind norm (CompFunTerm f)
       (isGlobalDef "Prelude.errorM" -> Just (), [_]) ->
         return Error
       (isGlobalDef "Prelude.ite" -> Just (), [_, cond, then_tm, else_tm]) ->
         return $ If cond (CompTerm then_tm) (CompTerm else_tm)
       (isGlobalDef "Prelude.letRecM" -> Just (), [tps, _, defs_f, body_f]) ->
         do (funs, funs_tm) <- mkFunVarsForTps tps
            defs_tm <- liftSC2 scApply defs_f funs_tm >>= liftSC1 scWhnf
            defs <- case asTupleValue defs_tm of
              Just defs -> return defs
              Nothing -> throwError (MalformedComp t')
            modify $ \st ->
              st { mrLocalFuns = (zip funs defs) ++ mrLocalFuns st }
            body_tm <- liftSC2 scApply body_f funs_tm
            whnfComp (CompTerm body_tm)
       ((asFunName -> Just f), args) ->
         do comp_tp <- liftSC1 scTypeOf t >>= liftSC1 scWhnf
            tp <-
              case asApp comp_tp of
                Just (isGlobalDef "Prelude.CompM" -> Just (), tp) -> return tp
                _ -> error "Computation not of type CompM a for some a"
            ret_fun <- liftSC1 scGlobalDef "Prelude.returnM"
            g <- liftSC2 scApply ret_fun tp
            return $ FunBind f args mempty (CompFunTerm g)
       _ -> throwError (MalformedComp t')


-- | Bind a computation in whnf with a function, and normalize
whnfBind :: WHNFComp -> CompFun -> MRM WHNFComp
whnfBind (Return t) f = applyCompFun f t >>= whnfComp
whnfBind Error _ = return Error
whnfBind (If cond comp1 comp2) f =
  return $ If cond (CompBind comp1 f) (CompBind comp2 f)
whnfBind (FunBind f args mark g) h =
  return $ FunBind f args mark (CompFunComp g h)

-- | Mark a normalized computation
whnfMark :: WHNFComp -> Mark -> MRM WHNFComp
whnfMark (Return t) _ = return $ Return t
whnfMark Error _ = return Error
whnfMark (If cond comp1 comp2) mark =
  return $ If cond (CompMark comp1 mark) (CompMark comp2 mark)
whnfMark (FunBind f args mark1 g) mark2 =
  return $ FunBind f args (mark1 `mappend` mark2) (CompFunMark g mark2)

-- | Lookup the definition of a function or throw a 'CannotLookupFunDef' if this is
-- not allowed, either because it is a global function we are treating as opaque
-- or because it is a locally-bound function variable
mrLookupFunDef :: FunName -> MRM Term
mrLookupFunDef f@(GlobalName _) = throwError (CannotLookupFunDef f)
mrLookupFunDef f@(LocalName nm) =
  do fun_assoc <- mrLocalFuns <$> get
     case lookup nm fun_assoc of
       Just body -> return body
       Nothing -> throwError (CannotLookupFunDef f)

-- | Unfold a call to function @f@ in term @f args >>= g@
mrUnfoldFunBind :: FunName -> [Term] -> Mark -> CompFun -> MRM Comp
mrUnfoldFunBind f _ mark _ | inMark f mark = throwError (RecursiveUnfold f)
mrUnfoldFunBind f args mark g =
  do f_def <- mrLookupFunDef f
     CompBind <$>
       (CompMark <$> (CompTerm <$> liftSC2 scApplyAll f_def args)
        <*> (return $ singleMark f `mappend` mark))
       <*> return g

-- | Coinductively prove an equality between two named functions by assuming
-- the names are equal and proving their bodies equal
mrSolveCoInd :: FunName -> FunName -> MRM ()
mrSolveCoInd f1 f2 =
  do def1 <- mrLookupFunDef f1
     def2 <- mrLookupFunDef f2
     saved <- get
     put $ saved { mrFunEqs = ((f1,f2),True) : mrFunEqs saved }
     catchError (mrSolveEq (CompFunMark (CompFunTerm def1) (singleMark f1))
                 (CompFunMark (CompFunTerm def2) (singleMark f2))) $ \err ->
       -- NOTE: any equalities proved under the assumption that f1 == f2 are
       -- suspect, so we have to throw them out and revert to saved on error
       (put saved >> throwError err)


-- | Typeclass for proving that two (representations of) objects of the same SAW
-- core type @a@ are equivalent, where the notion of equivalent depends on the
-- type @a@. The 'MRM' computation returns @()@ on success and throws a
-- 'MRFailure' on error.
class MRSolveEq a b where
  mrSolveEq :: a -> b -> MRM ()

-- NOTE: this instance is specifically for terms of non-computation type
instance MRSolveEq Term Term where
  mrSolveEq t1 t2 =
    do eq <- mrTermsEq t1 t2
       if eq then return () else throwError (TermsNotEq t1 t2)

instance MRSolveEq FunName FunName where
  mrSolveEq f1 f2 | f1 == f2 = return ()
  mrSolveEq f1 f2 =
    do eqs <- mrFunEqs <$> get
       case lookup (f1,f2) eqs of
         Just True -> return ()
         Just False -> throwError (FunsNotEq f1 f2)
         Nothing -> mrSolveCoInd f1 f2

instance MRSolveEq Comp Comp where
  mrSolveEq comp1 comp2 =
    withFailureCtx comp1 comp2 $
    do norm1 <- whnfComp comp1
       norm2 <- whnfComp comp2
       mrSolveEq norm1 norm2

instance MRSolveEq CompFun CompFun where
  mrSolveEq f1 f2 =
    do tp <- compFunInputType f1
       var <- liftSC2 scFreshGlobal "x" tp
       comp1 <- applyCompFun f1 var
       comp2 <- applyCompFun f2 var
       mrSolveEq comp1 comp2

instance MRSolveEq Comp WHNFComp where
  mrSolveEq comp1 norm2 =
    do norm1 <- whnfComp comp1
       mrSolveEq norm1 norm2

instance MRSolveEq WHNFComp Comp where
  mrSolveEq norm1 comp2 =
    do norm2 <- whnfComp comp2
       mrSolveEq norm1 norm2

instance MRSolveEq WHNFComp WHNFComp where
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
  mrSolveEq (If cond1 then1 else1) norm2@(If cond2 then2 else2) =
    -- Special case if the two conditions are equal: assert the one condition to
    -- test the then branches and assert its negtion to test the elses
    do eq <- mrTermsEq cond1 cond2
       if eq then
         (withPathCondition cond1 $ mrSolveEq then1 then2) >>
         (withNotPathCondition cond1 $ mrSolveEq else1 else2)
         else
         -- Otherwise, compare the first then and else, under their respective
         -- path conditions, to the whole second computation
         (withPathCondition cond1 $ mrSolveEq then1 norm2) >>
         (withNotPathCondition cond1 $ mrSolveEq else1 norm2)
  mrSolveEq (If cond1 then1 else1) norm2 =
    -- To compare an if to anything else, compare the then and else, under their
    -- respective path conditions, to the other computation
    (withPathCondition cond1 $ mrSolveEq then1 norm2) >>
    (withNotPathCondition cond1 $ mrSolveEq else1 norm2)
  mrSolveEq norm1 (If cond2 then2 else2) =
    -- To compare an if to anything else, compare the then and else, under their
    -- respective path conditions, to the other computation
    (withPathCondition cond2 $ mrSolveEq norm1 then2) >>
    (withNotPathCondition cond2 $ mrSolveEq norm1 else2)
  mrSolveEq comp1@(FunBind f1 args1 mark1 norm1) comp2@(FunBind f2 args2 mark2 norm2) =
    -- To compare two computations (f1 args1 >>= norm1) and (f2 args2 >>= norm2)
    -- we first test if (f1 args1) and (f2 args2) are equal. If so, we recurse
    -- and compare norm1 and norm2; otherwise, we try unfolding one or the other
    -- of f1 and f2.
    catchErrorEither cmp_funs >>= \ cmp_fun_res ->
    case cmp_fun_res of
      Right () -> mrSolveEq norm1 norm2
      Left err ->
        mapFailure (MRFailureDisj err) $
        (mrUnfoldFunBind f1 args1 mark1 norm1 >>= \c -> mrSolveEq c comp2)
        `mrOr`
        (mrUnfoldFunBind f2 args2 mark2 norm2 >>= \c -> mrSolveEq comp1 c)
    where
      cmp_funs = mrSolveEq f1 f2 >> zipWithM_ mrSolveEq args1 args2
  mrSolveEq (FunBind f1 args1 mark1 norm1) comp2 =
    -- This case compares a function call to a Return or Error; the only thing
    -- to do is unfold the function call and recurse
    mrUnfoldFunBind f1 args1 mark1 norm1 >>= \c -> mrSolveEq c comp2
  mrSolveEq comp1 (FunBind f2 args2 mark2 norm2) =
    -- This case compares a function call to a Return or Error; the only thing
    -- to do is unfold the function call and recurse
    mrUnfoldFunBind f2 args2 mark2 norm2 >>= \c -> mrSolveEq comp1 c

-- | Test two monadic, recursive terms for equivalence
askMRSolver ::
  SBV.SMTConfig {- ^ SBV configuration -} ->
  Maybe Integer {- ^ Timeout in milliseconds -} ->
  Term -> Term -> IO (Maybe MRFailure)

askMRSolver = undefined
