{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : SAWScript.Prover.MRSolver.Solver
Copyright   : Galois, Inc. 2022
License     : BSD3
Maintainer  : westbrook@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

This module implements a monadic-recursive solver, for proving that one monadic
term refines another. The algorithm works on the "monadic normal form" of
computations, which uses the following laws to simplify binds in computations,
where either is the sum elimination function defined in the SAW core prelude:

returnM x >>= k               = k x
errorM str >>= k              = errorM
(m >>= k1) >>= k2             = m >>= \x -> k1 x >>= k2
(existsM f) >>= k             = existsM (\x -> f x >>= k)
(forallM f) >>= k             = forallM (\x -> f x >>= k)
(orM m1 m2) >>= k             = orM (m1 >>= k) (m2 >>= k)
(if b then m1 else m2) >>= k  = if b then m1 >>= k else m2 >>1 k
(either f1 f2 e) >>= k        = either (\x -> f1 x >= k) (\x -> f2 x >= k) e
(letrecM funs body) >>= k     = letrecM funs (\F1 ... Fn -> body F1 ... Fn >>= k)

The resulting computations of one of the following forms:

returnM e  |  errorM str  |  existsM f  |  forallM f  |  orM m1 m2  |
if b then m1 else m2  |  either f1 f2 e  |  F e1 ... en  |  F e1 ... en >>= k  |
letrecM lrts B (\F1 ... Fn -> (f1, ..., fn)) (\F1 ... Fn -> m)

The form F e1 ... en refers to a recursively-defined function or a function
variable that has been locally bound by a letrecM. Either way, monadic
normalization does not attempt to normalize these functions.

The algorithm maintains a context of three sorts of variables: letrec-bound
variables, existential variables, and universal variables. Universal variables
are represented as free SAW core variables, while the other two forms of
variable are represented as SAW core 'ExtCns's terms, which are essentially
axioms that have been generated internally. These 'ExtCns's are Skolemized,
meaning that they take in as arguments all universal variables that were in
scope when they were created. The context also maintains a partial substitution
for the existential variables, as they become instantiated with values, and it
additionally remembers the bodies / unfoldings of the letrec-bound variables.

The goal of the solver at any point is of the form C |- m1 |= m2, meaning that
we are trying to prove m1 refines m2 in context C. This proceed by cases:

C |- returnM e1 |= returnM e2: prove C |- e1 = e2

C |- errorM str1 |= errorM str2: vacuously true

C |- if b then m1' else m1'' |= m2: prove C,b=true |- m1' |= m2 and
C,b=false |- m1'' |= m2, skipping either case where C,b=X is unsatisfiable;

C |- m1 |= if b then m2' else m2'': similar to the above

C |- either T U (CompM V) f1 f2 e |= m: prove C,x:T,e=inl x |- f1 x |= m and
C,y:U,e=inl y |- f2 y |= m, again skippping any case with unsatisfiable context;

C |- m |= either T U (CompM V) f1 f2 e: similar to previous

C |- m |= forallM f: make a new universal variable x and recurse

C |- existsM f |= m: make a new universal variable x and recurse (existential
elimination uses universal variables and vice-versa)

C |- m |= existsM f: make a new existential variable x and recurse

C |- forall f |= m: make a new existential variable x and recurse

C |- m |= orM m1 m2: try to prove C |- m |= m1, and if that fails, backtrack and
prove C |- m |= m2

C |- orM m1 m2 |= m: prove both C |- m1 |= m and C |- m2 |= m

C |- letrec (\F1 ... Fn -> (f1, ..., fn)) (\F1 ... Fn -> body) |= m: create
letrec-bound variables F1 through Fn in the context bound to their unfoldings f1
through fn, respectively, and recurse on body |= m

C |- m |= letrec (\F1 ... Fn -> (f1, ..., fn)) (\F1 ... Fn -> body): similar to
previous case

C |- F e1 ... en >>= k |= F e1' ... en' >>= k': prove C |- ei = ei' for each i
and then prove k x |= k' x for new universal variable x

C |- F e1 ... en >>= k |= F' e1' ... em' >>= k':

* If we have an assumption that forall x1 ... xj, F a1 ... an |= F' a1' .. am',
  prove ei = ai and ei' = ai' and then that C |- k x |= k' x for fresh uvar x

* If we have an assumption that forall x1, ..., xn, F e1'' ... en'' |= m' for
  some ei'' and m', match the ei'' against the ei by instantiating the xj with
  fresh evars, and if this succeeds then recursively prove C |- m' >>= k |= RHS

(We don't do this one right now)
* If we have an assumption that forall x1', ..., xn', m |= F e1'' ... en'' for
  some ei'' and m', match the ei'' against the ei by instantiating the xj with
  fresh evars, and if this succeeds then recursively prove C |- LHS |= m' >>= k'

* If either side is a definition whose unfolding does not contain letrecM, fixM,
  or any related operations, unfold it

* If F and F' have the same return type, add an assumption forall uvars in scope
  that F e1 ... en |= F' e1' ... em' and unfold both sides, recursively proving
  that F_body e1 ... en |= F_body' e1' ... em'. Then also prove k x |= k' x for
  fresh uvar x.

* Otherwise we don't know to "split" one of the sides into a bind whose
  components relate to the two components on the other side, so just fail
-}

module SAWScript.Prover.MRSolver.Solver where

import Data.Maybe
import Data.Either
import Data.List (findIndices, intercalate)
import Control.Monad.Except

import Prettyprinter

import Verifier.SAW.Term.Functor
import Verifier.SAW.SharedTerm
import Verifier.SAW.Recognizer

import SAWScript.Prover.MRSolver.Term
import SAWScript.Prover.MRSolver.Monad
import SAWScript.Prover.MRSolver.SMT


----------------------------------------------------------------------
-- * Normalizing and Matching on Terms
----------------------------------------------------------------------

-- | Pattern-match on a @LetRecTypes@ list in normal form and return a list of
-- the types it specifies, each in normal form and with uvars abstracted out
asLRTList :: Term -> MRM [Term]
asLRTList (asCtor -> Just (primName -> "Prelude.LRT_Nil", [])) =
  return []
asLRTList (asCtor -> Just (primName -> "Prelude.LRT_Cons", [lrt, lrts])) =
  do tp <- liftSC2 scGlobalApply "Prelude.lrtToType" [lrt]
     tp_norm_closed <- liftSC1 scWhnf tp >>= piUVarsM
     (tp_norm_closed :) <$> asLRTList lrts
asLRTList t = throwMRFailure (MalformedLetRecTypes t)

-- | Match a right-nested series of pairs. This is similar to 'asTupleValue'
-- except that it expects a unit value to always be at the end.
asNestedPairs :: Recognizer Term [Term]
asNestedPairs (asPairValue -> Just (x, asNestedPairs -> Just xs)) = Just (x:xs)
asNestedPairs (asFTermF -> Just UnitValue) = Just []
asNestedPairs _ = Nothing

-- | Syntactically project then @i@th element of the body of a lambda. That is,
-- assuming the input 'Term' has the form
--
-- > \ (x1:T1) ... (xn:Tn) -> (e1, (e2, ... (en, ())))
--
-- return the bindings @x1:T1,...,xn:Tn@ and @ei@
synProjFunBody :: Int -> Term -> Maybe ([(LocalName, Term)], Term)
synProjFunBody i (asLambdaList -> (vars, asTupleValue -> Just es)) =
  -- NOTE: we are doing 1-based indexing instead of 0-based, thus the -1
  Just $ (vars, es !! (i-1))
synProjFunBody _ _ = Nothing

-- | Bind fresh function variables for a @letRecM@ or @multiFixM@ with the given
-- @LetRecTypes@ and definitions for the function bodies as a lambda
mrFreshLetRecVars :: Term -> Term -> MRM [Term]
mrFreshLetRecVars lrts defs_f =
  do
    -- First, make fresh function constants for all the bound functions, using
    -- the names bound by defs_f and just "F" if those run out
    let fun_var_names =
          map fst (fst $ asLambdaList defs_f) ++ repeat "F"
    fun_tps <- asLRTList lrts
    funs <- zipWithM mrFreshVar fun_var_names fun_tps
    fun_tms <- mapM mrVarTerm funs

    -- Next, apply the definition function defs_f to our function vars, yielding
    -- the definitions of the individual letrec-bound functions in terms of the
    -- new function constants
    defs_tm <- mrApplyAll defs_f fun_tms
    defs <- case asNestedPairs defs_tm of
      Just defs -> return defs
      Nothing -> throwMRFailure (MalformedDefsFun defs_f)

    -- Remember the body associated with each fresh function constant
    zipWithM_ (\f body ->
                lambdaUVarsM body >>= \cl_body ->
                mrSetVarInfo f (FunVarInfo cl_body)) funs defs

    -- Finally, return the terms for the fresh function variables
    return fun_tms


-- | Normalize a 'Term' of monadic type to monadic normal form
normCompTerm :: Term -> MRM NormComp
normCompTerm = normComp . CompTerm

-- | Normalize a computation to monadic normal form, assuming any 'Term's it
-- contains have already been normalized with respect to beta and projections
-- (but constants need not be unfolded)
normComp :: Comp -> MRM NormComp
normComp (CompReturn t) = return $ ReturnM t
normComp (CompBind m f) =
  do norm <- normComp m
     normBind norm f
normComp (CompTerm t) =
  withFailureCtx (FailCtxMNF t) $
  case asApplyAll t of
    (isGlobalDef "Prelude.returnM" -> Just (), [_, x]) ->
      return $ ReturnM x
    (isGlobalDef "Prelude.bindM" -> Just (), [_, _, m, f]) ->
      do norm <- normComp (CompTerm m)
         normBind norm (CompFunTerm f)
    (isGlobalDef "Prelude.errorM" -> Just (), [_, str]) ->
      return (ErrorM str)
    (isGlobalDef "Prelude.ite" -> Just (), [_, cond, then_tm, else_tm]) ->
      return $ Ite cond (CompTerm then_tm) (CompTerm else_tm)
    (isGlobalDef "Prelude.either" -> Just (), [ltp, rtp, _, f, g, eith]) ->
      return $ Either (Type ltp) (Type rtp) (CompFunTerm f) (CompFunTerm g) eith
    (isGlobalDef "Prelude.maybe" -> Just (), [tp, _, m, f, mayb]) ->
      return $ MaybeElim (Type tp) (CompTerm m) (CompFunTerm f) mayb
    (isGlobalDef "Prelude.orM" -> Just (), [_, m1, m2]) ->
      return $ OrM (CompTerm m1) (CompTerm m2)
    (isGlobalDef "Prelude.existsM" -> Just (), [tp, _, body_tm]) ->
      return $ ExistsM (Type tp) (CompFunTerm body_tm)
    (isGlobalDef "Prelude.forallM" -> Just (), [tp, _, body_tm]) ->
      return $ ForallM (Type tp) (CompFunTerm body_tm)
    (isGlobalDef "Prelude.precondHint" -> Just (), [_, _, body_tm]) ->
      normCompTerm body_tm
    (isGlobalDef "Prelude.letRecM" -> Just (), [lrts, _, defs_f, body_f]) ->
      do
        -- Bind fresh function vars for the letrec-bound functions
        fun_tms <- mrFreshLetRecVars lrts defs_f
        -- Apply the body function to our function vars and recursively
        -- normalize the resulting computation
        body_tm <- mrApplyAll body_f fun_tms
        normComp (CompTerm body_tm)

    -- Only unfold constants that are not recursive functions, i.e., whose
    -- bodies do not contain letrecs
    {- FIXME: this should be handled by mrRefines; we want it to be handled there
       so that we use refinement assumptions before unfolding constants, to give
       the user control over refinement proofs
    ((asConstant -> Just (_, body)), args)
      | not (containsLetRecM body) ->
        mrApplyAll body args >>= normCompTerm
    -}

    -- Recognize (multiFixM lrts (\ f1 ... fn -> (body1, ..., bodyn))).i args
    (asTupleSelector ->
     Just (asApplyAll -> (isGlobalDef "Prelude.multiFixM" -> Just (),
                          [lrts, defs_f]),
           i), args)
      -- Extract out the function \f1 ... fn -> bodyi
      | Just (vars, body_i) <- synProjFunBody i defs_f ->
        do
          -- Bind fresh function variables for the functions f1 ... fn
          fun_tms <- mrFreshLetRecVars lrts defs_f
          -- Re-abstract the body
          body_f <- liftSC2 scLambdaList vars body_i
          -- Apply body_f to f1 ... fn and the top-level arguments
          body_tm <- mrApplyAll body_f (fun_tms ++ args)
          normComp (CompTerm body_tm)


    -- For an ExtCns, we have to check what sort of variable it is
    -- FIXME: substitute for evars if they have been instantiated
    ((asExtCns -> Just ec), args) ->
      do fun_name <- extCnsToFunName ec
         return $ FunBind fun_name args CompFunReturn

    ((asGlobalFunName -> Just f), args) ->
      return $ FunBind f args CompFunReturn

    _ -> throwMRFailure (MalformedComp t)


-- | Bind a computation in whnf with a function, and normalize
normBind :: NormComp -> CompFun -> MRM NormComp
normBind (ReturnM t) k = applyNormCompFun k t
normBind (ErrorM msg) _ = return (ErrorM msg)
normBind (Ite cond comp1 comp2) k =
  return $ Ite cond (CompBind comp1 k) (CompBind comp2 k)
normBind (Either ltp rtp f g t) k =
  return $ Either ltp rtp (compFunComp f k) (compFunComp g k) t
normBind (MaybeElim tp m f t) k =
  return $ MaybeElim tp (CompBind m k) (compFunComp f k) t
normBind (OrM comp1 comp2) k =
  return $ OrM (CompBind comp1 k) (CompBind comp2 k)
normBind (ExistsM tp f) k = return $ ExistsM tp (compFunComp f k)
normBind (ForallM tp f) k = return $ ForallM tp (compFunComp f k)
normBind (FunBind f args k1) k2 =
  return $ FunBind f args (compFunComp k1 k2)

-- | Bind a 'Term' for a computation with a function and normalize
normBindTerm :: Term -> CompFun -> MRM NormComp
normBindTerm t f = normCompTerm t >>= \m -> normBind m f

-- | Apply a computation function to a term argument to get a computation
applyCompFun :: CompFun -> Term -> MRM Comp
applyCompFun (CompFunComp f g) t =
  -- (f >=> g) t == f t >>= g
  do comp <- applyCompFun f t
     return $ CompBind comp g
applyCompFun CompFunReturn t =
  return $ CompReturn t
applyCompFun (CompFunTerm f) t = CompTerm <$> mrApplyAll f [t]

-- | Apply a 'CompFun' to a term and normalize the resulting computation
applyNormCompFun :: CompFun -> Term -> MRM NormComp
applyNormCompFun f arg = applyCompFun f arg >>= normComp

-- | Apply a 'Comp

{- FIXME: do these go away?
-- | Lookup the definition of a function or throw a 'CannotLookupFunDef' if this is
-- not allowed, either because it is a global function we are treating as opaque
-- or because it is a locally-bound function variable
mrLookupFunDef :: FunName -> MRM Term
mrLookupFunDef f@(GlobalName _) = throwMRFailure (CannotLookupFunDef f)
mrLookupFunDef f@(LocalName var) =
  mrVarInfo var >>= \case
  Just (FunVarInfo body) -> return body
  Just _ -> throwMRFailure (CannotLookupFunDef f)
  Nothing -> error "mrLookupFunDef: unknown variable!"

-- | Unfold a call to function @f@ in term @f args >>= g@
mrUnfoldFunBind :: FunName -> [Term] -> Mark -> CompFun -> MRM Comp
mrUnfoldFunBind f _ mark _ | inMark f mark = throwMRFailure (RecursiveUnfold f)
mrUnfoldFunBind f args mark g =
  do f_def <- mrLookupFunDef f
     CompBind <$>
       (CompMark <$> (CompTerm <$> liftSC2 scApplyAll f_def args)
        <*> (return $ singleMark f `mappend` mark))
       <*> return g
-}

{-
FIXME HERE NOW: maybe each FunName should stipulate whether it is recursive or
not, so that mrRefines can unfold the non-recursive ones early but wait on
handling the recursive ones
-}


----------------------------------------------------------------------
-- * Handling Coinductive Hypotheses
----------------------------------------------------------------------

-- | Prove the precondition of a coinductive hypothesis
proveCoIndHypPreCond :: CoIndHyp -> MRM ()
proveCoIndHypPreCond hyp =
  do (pre1, pre2) <- applyCoIndHypPreconds hyp
     pre <- liftSC2 scAnd pre1 pre2
     success <- mrProvable pre
     if success then return () else
       throwMRFailure $
       PrecondNotProvable (coIndHypLHSFun hyp) (coIndHypRHSFun hyp) pre

-- | Co-inductively prove the refinement
--
-- > forall x1, ..., xn. preF y1 ... ym -> preG z1 ... zl ->
-- >   F y1 ... ym |= G z1 ... zl@
--
-- where @F@ and @G@ are the given 'FunName's, @y1, ..., ym@ and @z1, ..., zl@
-- are the given argument lists, @x1, ..., xn@ is the current context of uvars,
-- and @preF@ and @preG@ are the preconditions associated with @F@ and @G@,
-- respectively. This proof is performed by coinductively assuming the
-- refinement holds and proving the refinement with the definitions of @F@ and
-- @G@ unfolded to their bodies. Note that this refinement is performed with
-- /only/ the preconditions @preF@ and @preG@ as assumptions; all other
-- assumptions are thrown away. If while running the refinement computation a
-- 'CoIndHypMismatchWidened' error is reached with the given names, the state is
-- restored and the computation is re-run with the widened hypothesis.
mrRefinesCoInd :: FunName -> [Term] -> FunName -> [Term] -> MRM ()
mrRefinesCoInd f1 args1 f2 args2 =
  do ctx <- mrUVarCtx
     preF1 <- mrGetPrecond f1
     preF2 <- mrGetPrecond f2
     let hyp = CoIndHyp ctx f1 f2 args1 args2 preF1 preF2
     proveCoIndHypPreCond hyp
     proveCoIndHyp hyp

-- | Prove the refinement represented by a 'CoIndHyp' coinductively. This is the
-- main loop implementing 'mrRefinesCoInd'. See that function for documentation.
proveCoIndHyp :: CoIndHyp -> MRM ()
proveCoIndHyp hyp =
  do let f1 = coIndHypLHSFun hyp
         f2 = coIndHypRHSFun hyp
         args1 = coIndHypLHS hyp
         args2 = coIndHypRHS hyp
     debugPretty 1 ("proveCoIndHyp" <+> ppInEmptyCtx hyp)
     lhs <- fromMaybe (error "proveCoIndHyp") <$> mrFunBody f1 args1
     rhs <- fromMaybe (error "proveCoIndHyp") <$> mrFunBody f2 args2
     (pre1, pre2) <- applyCoIndHypPreconds hyp
     pre <- liftSC2 scAnd pre1 pre2
     (withOnlyUVars (coIndHypCtx hyp) $ withOnlyAssumption pre $
      withCoIndHyp hyp $ mrRefines lhs rhs) `catchError` \case
       MRExnWiden nm1' nm2' new_vars
         | f1 == nm1' && f2 == nm2' ->
           -- NOTE: the state automatically gets reset here because we defined
           -- MRM with ExceptT at a lower level than StateT
           do mrDebugPPPrefixSep 1 "Widening recursive assumption for" nm1' "|=" nm2'
              debugPrint 2 ("Widening indices: " ++
                            intercalate ", " (map show new_vars))
              hyp' <- generalizeCoIndHyp hyp new_vars
              proveCoIndHyp hyp'
       e -> throwError e


-- | Test that a coinductive hypothesis for the given function names matches the
-- given arguments, otherwise throw an exception saying that widening is needed
matchCoIndHyp :: CoIndHyp -> [Term] -> [Term] -> MRM ()
matchCoIndHyp hyp args1 args2 =
  do (args1', args2') <- instantiateCoIndHyp hyp
     eqs1 <- zipWithM mrProveEq args1' args1
     eqs2 <- zipWithM mrProveEq args2' args2
     if and (eqs1 ++ eqs2) then return () else
       throwError $ MRExnWiden (coIndHypLHSFun hyp) (coIndHypRHSFun hyp)
       (map Left (findIndices not eqs1) ++ map Right (findIndices not eqs2))
     proveCoIndHypPreCond hyp


-- | Generalize some of the arguments of a coinductive hypothesis
generalizeCoIndHyp :: CoIndHyp -> [Either Int Int] -> MRM CoIndHyp
generalizeCoIndHyp hyp [] = return hyp
generalizeCoIndHyp hyp all_specs@(arg_spec:arg_specs) =
  withOnlyUVars (coIndHypCtx hyp) $ do
  mrDebugPPPrefixSep 2 "generalizeCoIndHyp" hyp "with arg specs" (show all_specs)
  -- Get the arg and type associated with arg_spec
  let arg = coIndHypArg hyp arg_spec
  arg_tp <- mrTypeOf arg
  ctx <- mrUVarCtx
  debugPretty 2 ("Current context: " <> ppCtx ctx)
  -- Sort out the other args that equal arg
  eq_uneq_specs <- forM arg_specs $ \spec' ->
    do let arg' = coIndHypArg hyp spec'
       tp' <- mrTypeOf arg'
       mrDebugPPPrefixSep 2 "generalizeCoIndHyp: the type of" arg' "is" tp'
       debugPrint 2 ("arg' = " ++ show arg')
       tps_eq <- mrConvertible arg_tp tp'
       args_eq <- if tps_eq then mrProveEq arg arg' else return False
       return $ if args_eq then Left spec' else Right spec'
  let (eq_specs, uneq_specs) = partitionEithers eq_uneq_specs
  -- Add a new variable of type arg_tp, set all eq_specs plus our original
  -- arg_spec to it, and recurse
  hyp' <- generalizeCoIndHypArgs hyp arg_tp (arg_spec:eq_specs)
  generalizeCoIndHyp hyp' uneq_specs

-- | Add a new variable of the given type to the context of a coinductive
-- hypothesis and set the specified arguments to that new variable
generalizeCoIndHypArgs :: CoIndHyp -> Term -> [Either Int Int] -> MRM CoIndHyp
generalizeCoIndHypArgs (CoIndHyp ctx f1 f2 args1 args2 pre1 pre2) tp specs =
  do let set_arg i args =
           take i args ++ (Unshared $ LocalVar 0) : drop (i+1) args
     let (specs1, specs2) = partitionEithers specs
     -- NOTE: need to lift the arguments because we are adding a variable
     args1' <- liftTermLike 0 1 args1
     args2' <- liftTermLike 0 1 args2
     let args1'' = foldr set_arg args1' specs1
         args2'' = foldr set_arg args2' specs2
     return $ CoIndHyp (ctx ++ [("z",tp)]) f1 f2 args1'' args2'' pre1 pre2


----------------------------------------------------------------------
-- * Mr Solver Himself (He Identifies as Male)
----------------------------------------------------------------------

-- | An object that can be converted to a normalized computation
class ToNormComp a where
  toNormComp :: a -> MRM NormComp

instance ToNormComp NormComp where
  toNormComp = return
instance ToNormComp Comp where
  toNormComp = normComp
instance ToNormComp Term where
  toNormComp = normComp . CompTerm

-- | Prove that the left-hand computation refines the right-hand one. See the
-- rules described at the beginning of this module.
mrRefines :: (ToNormComp a, ToNormComp b) => a -> b -> MRM ()
mrRefines t1 t2 =
  do m1 <- toNormComp t1
     m2 <- toNormComp t2
     mrDebugPPPrefixSep 1 "mrRefines" m1 "|=" m2
     withFailureCtx (FailCtxRefines m1 m2) $ mrRefines' m1 m2

-- | The main implementation of 'mrRefines'
mrRefines' :: NormComp -> NormComp -> MRM ()

mrRefines' (ReturnM e1) (ReturnM e2) = mrAssertProveEq e1 e2
mrRefines' (ErrorM _) (ErrorM _) = return ()
mrRefines' (ReturnM e) (ErrorM _) = throwMRFailure (ReturnNotError e)
mrRefines' (ErrorM _) (ReturnM e) = throwMRFailure (ReturnNotError e)

-- FIXME: Add support for arbitrary maybe asusmptions, like the either case
mrRefines' (MaybeElim (Type (asEq -> Just (tp,e1,e2))) m1 f1 _) m2 =
  do cond <- mrEq' tp e1 e2
     not_cond <- liftSC1 scNot cond
     cond_pf <-
       liftSC1 scEqTrue cond >>= piUVarsM >>= mrFreshVar "pf" >>= mrVarTerm
     m1' <- applyNormCompFun f1 cond_pf
     cond_holds <- mrProvable cond
     if cond_holds then mrRefines m1' m2 else
       withAssumption cond (mrRefines m1' m2) >>
       withAssumption not_cond (mrRefines m1 m2)
mrRefines' m1 (MaybeElim (Type (asEq -> Just (tp,e1,e2))) m2 f2 _) =
  do cond <- mrEq' tp e1 e2
     not_cond <- liftSC1 scNot cond
     cond_pf <-
       liftSC1 scEqTrue cond >>= piUVarsM >>= mrFreshVar "pf" >>= mrVarTerm
     m2' <- applyNormCompFun f2 cond_pf
     cond_holds <- mrProvable cond
     if cond_holds then mrRefines m1 m2' else
       withAssumption cond (mrRefines m1 m2') >>
       withAssumption not_cond (mrRefines m1 m2)

mrRefines' (Ite cond1 m1 m1') m2 =
  liftSC1 scNot cond1 >>= \not_cond1 ->
  mrProvable cond1 >>= \cond1_true_pv->
  mrProvable not_cond1 >>= \cond1_false_pv ->
  case (cond1_true_pv, cond1_false_pv) of
    (True, _) -> mrRefines m1 m2
    (_, True) -> mrRefines m1' m2
    _ -> withAssumption cond1 (mrRefines m1 m2) >>
         withAssumption not_cond1 (mrRefines m1' m2)
mrRefines' m1 (Ite cond2 m2 m2') =
  liftSC1 scNot cond2 >>= \not_cond2 ->
  mrProvable cond2 >>= \cond2_true_pv->
  mrProvable not_cond2 >>= \cond2_false_pv ->
  case (cond2_true_pv, cond2_false_pv) of
    (True, _) -> mrRefines m1 m2
    (_, True) -> mrRefines m1 m2'
    _ -> withAssumption cond2 (mrRefines m1 m2) >>
         withAssumption not_cond2 (mrRefines m1 m2')

mrRefines' (Either ltp1 rtp1 f1 g1 t1) m2 =
  liftSC1 scWhnf t1 >>= \t1' ->
  mrGetDataTypeAssump t1' >>= \mb_assump ->
  case (mb_assump, asEither t1') of
    (_, Just (Left  x)) -> applyNormCompFun f1 x >>= flip mrRefines m2
    (_, Just (Right x)) -> applyNormCompFun g1 x >>= flip mrRefines m2
    (Just (IsLeft  x), _) -> applyNormCompFun f1 x >>= flip mrRefines m2
    (Just (IsRight x), _) -> applyNormCompFun g1 x >>= flip mrRefines m2
    _ -> let lnm = maybe "x_left" id (compFunVarName f1)
             rnm = maybe "x_right" id (compFunVarName g1)
         in withUVarLift lnm ltp1 (f1, t1', m2) (\x (f1', t1'', m2') ->
             applyNormCompFun f1' x >>= withDataTypeAssump t1'' (IsLeft x)
                                        . flip mrRefines m2') >>
            withUVarLift rnm rtp1 (g1, t1', m2) (\x (g1', t1'', m2') ->
             applyNormCompFun g1' x >>= withDataTypeAssump t1'' (IsRight x)
                                        . flip mrRefines m2')
mrRefines' m1 (Either ltp2 rtp2 f2 g2 t2) =
  liftSC1 scWhnf t2 >>= \t2' ->
  mrGetDataTypeAssump t2' >>= \mb_assump ->
  case (mb_assump, asEither t2') of
    (_, Just (Left  x)) -> applyNormCompFun f2 x >>= mrRefines m1
    (_, Just (Right x)) -> applyNormCompFun g2 x >>= mrRefines m1
    (Just (IsLeft  x), _) -> applyNormCompFun f2 x >>= mrRefines m1
    (Just (IsRight x), _) -> applyNormCompFun g2 x >>= mrRefines m1
    _ -> let lnm = maybe "x_left" id (compFunVarName f2)
             rnm = maybe "x_right" id (compFunVarName g2)
         in withUVarLift lnm ltp2 (f2, t2', m1) (\x (f2', t2'', m1') ->
             applyNormCompFun f2' x >>= withDataTypeAssump t2'' (IsLeft x)
                                        . mrRefines m1') >>
            withUVarLift rnm rtp2 (g2, t2', m1) (\x (g2', t2'', m1') ->
             applyNormCompFun g2' x >>= withDataTypeAssump t2'' (IsRight x)
                                        . mrRefines m1')

mrRefines' m1 (ForallM tp f2) =
  let nm = maybe "x" id (compFunVarName f2) in
  withUVarLift nm tp (m1,f2) $ \x (m1',f2') ->
  applyNormCompFun f2' x >>= \m2' ->
  mrRefines m1' m2'
mrRefines' (ExistsM tp f1) m2 =
  let nm = maybe "x" id (compFunVarName f1) in
  withUVarLift nm tp (f1,m2) $ \x (f1',m2') ->
  applyNormCompFun f1' x >>= \m1' ->
  mrRefines m1' m2'

mrRefines' m1 (OrM m2 m2') =
  mrOr (mrRefines m1 m2) (mrRefines m1 m2')
mrRefines' (OrM m1 m1') m2 =
  mrRefines m1 m2 >> mrRefines m1' m2
     
-- FIXME: the following cases don't work unless we either allow evars to be set
-- to NormComps or we can turn NormComps back into terms
mrRefines' m1@(FunBind (EVarFunName _) _ _) m2 =
  throwMRFailure (CompsDoNotRefine m1 m2)
mrRefines' m1 m2@(FunBind (EVarFunName _) _ _) =
  throwMRFailure (CompsDoNotRefine m1 m2)
{-
mrRefines' (FunBind (EVarFunName evar) args CompFunReturn) m2 =
  mrGetEVar evar >>= \case
  Just f ->
    (mrApplyAll f args >>= normCompTerm) >>= \m1' ->
    mrRefines m1' m2
  Nothing -> mrTrySetAppliedEVar evar args m2
-}

mrRefines' (FunBind (LetRecName f) args1 k1) (FunBind (LetRecName f') args2 k2)
  | f == f' && length args1 == length args2 =
    zipWithM_ mrAssertProveEq args1 args2 >>
    mrRefinesFun k1 k2

mrRefines' m1@(FunBind f1 args1 k1) m2@(FunBind f2 args2 k2) =
  mrFunOutType f1 args1 >>= \tp1 ->
  mrFunOutType f2 args2 >>= \tp2 ->
  mrConvertible tp1 tp2 >>= \tps_eq ->
  mrFunBodyRecInfo f1 args1 >>= \maybe_f1_body ->
  mrFunBodyRecInfo f2 args2 >>= \maybe_f2_body ->
  mrGetCoIndHyp f1 f2 >>= \maybe_coIndHyp ->
  mrGetFunAssump f1 >>= \maybe_fassump ->
  case (maybe_coIndHyp, maybe_fassump) of

  -- If we have a co-inductive assumption that f1 args1' |= f2 args2':
  -- * If it is convertible to our goal, continue and prove that k1 |= k2
  -- * If it can be widened with our goal, restart the current proof branch
  --   with the widened hypothesis (done by throwing a
  --   'CoIndHypMismatchWidened' error for 'proveCoIndHyp' to catch)
  -- * Otherwise, throw a 'CoIndHypMismatchFailure' error.
  (Just hyp, _) ->
    matchCoIndHyp hyp args1 args2 >>
    mrRefinesFun k1 k2

  -- If we have an assumption that f1 args' refines some rhs, then prove that
  -- args1 = args' and then that rhs refines m2
  (_, Just fassump) ->
    do (assump_args, assump_rhs) <- instantiateFunAssump fassump
       zipWithM_ mrAssertProveEq assump_args args1
       m1' <- normBind assump_rhs k1
       mrRefines m1' m2

  -- If f1 unfolds and is not recursive in itself, unfold it and recurse
  _ | Just (f1_body, False) <- maybe_f1_body ->
      normBindTerm f1_body k1 >>= \m1' -> mrRefines m1' m2

  -- If f2 unfolds and is not recursive in itself, unfold it and recurse
  _ | Just (f2_body, False) <- maybe_f2_body ->
      normBindTerm f2_body k2 >>= \m2' -> mrRefines m1 m2'

  -- If we don't have a co-inducitve hypothesis for f1 and f2, don't have an
  -- assumption that f1 refines some specification, and both f1 and f2 are
  -- recursive and have the same return type, then try to coinductively prove
  -- that f1 args1 |= f2 args2 under the assumption that f1 args1 |= f2 args2,
  -- and then try to prove that k1 |= k2
  _ | tps_eq
    , Just _ <- maybe_f1_body
    , Just _ <- maybe_f2_body ->
      mrRefinesCoInd f1 args1 f2 args2 >> mrRefinesFun k1 k2

  -- If we cannot line up f1 and f2, then making progress here would require us
  -- to somehow split either m1 or m2 into some bind m' >>= k' such that m' is
  -- related to the function call on the other side and k' is related to the
  -- continuation on the other side, but we don't know how to do that, so give
  -- up
  _ ->
    mrDebugPPPrefixSep 1 "mrRefines: bind types not equal:" tp1 "/=" tp2 >>
    throwMRFailure (CompsDoNotRefine m1 m2)

{- FIXME: handle FunBind on just one side
mrRefines' m1@(FunBind f@(GlobalName _) args k1) m2 =
  mrGetFunAssump f >>= \case
  Just fassump ->
    -- If we have an assumption that f args' refines some rhs, then prove that
    -- args = args' and then that rhs refines m2
    do (assump_args, assump_rhs) <- instantiateFunAssump fassump
       zipWithM_ mrAssertProveEq assump_args args
       m1' <- normBind assump_rhs k1
       mrRefines m1' m2
  Nothing ->
    -- We don't want to do inter-procedural proofs, so if we don't know anything
    -- about f already then give up
    throwMRFailure (CompsDoNotRefine m1 m2)
-}


mrRefines' m1@(FunBind f1 args1 k1) m2 =
  mrGetFunAssump f1 >>= \case

  -- If we have an assumption that f1 args' refines some rhs, then prove that
  -- args1 = args' and then that rhs refines m2
  Just fassump ->
    do (assump_args, assump_rhs) <- instantiateFunAssump fassump
       zipWithM_ mrAssertProveEq assump_args args1
       m1' <- normBind assump_rhs k1
       mrRefines m1' m2

  -- Otherwise, see if we can unfold f1
  Nothing ->
    mrFunBodyRecInfo f1 args1 >>= \case

    -- If f1 unfolds and is not recursive in itself, unfold it and recurse
    Just (f1_body, False) ->
      normBindTerm f1_body k1 >>= \m1' -> mrRefines m1' m2

    -- Otherwise we would have to somehow split m2 into some computation of the
    -- form m2' >>= k2 where f1 args1 |= m2' and k1 |= k2, but we don't know how
    -- to do this splitting, so give up
    _ ->
      throwMRFailure (CompsDoNotRefine m1 m2)


mrRefines' m1 m2@(FunBind f2 args2 k2) =
  mrFunBodyRecInfo f2 args2 >>= \case

  -- If f2 unfolds and is not recursive in itself, unfold it and recurse
  Just (f2_body, False) ->
    normBindTerm f2_body k2 >>= \m2' -> mrRefines m1 m2'

  -- If f2 unfolds but is recursive, and k2 is the trivial continuation, meaning
  -- m2 is just f2 args2, use the law of coinduction to prove m1 |= f2 args2 by
  -- proving m1 |= f2_body under the assumption that m1 |= f2 args2
  {- FIXME: implement something like this
  Just (f2_body, True)
    | CompFunReturn <- k2 ->
      withFunAssumpR m1 f2 args2 $
   -}

    -- Otherwise we would have to somehow split m1 into some computation of the
    -- form m1' >>= k1 where m1' |= f2 args2 and k1 |= k2, but we don't know how
    -- to do this splitting, so give up
  _ ->
    throwMRFailure (CompsDoNotRefine m1 m2)


-- NOTE: the rules that introduce existential variables need to go last, so that
-- they can quantify over as many universals as possible
mrRefines' m1 (ExistsM tp f2) =
  do let nm = maybe "x" id (compFunVarName f2)
     evar <- mrFreshEVar nm tp
     m2' <- applyNormCompFun f2 evar
     mrRefines m1 m2'
mrRefines' (ForallM tp f1) m2 =
  do let nm = maybe "x" id (compFunVarName f1)
     evar <- mrFreshEVar nm tp
     m1' <- applyNormCompFun f1 evar
     mrRefines m1' m2

-- If none of the above cases match, then fail
mrRefines' m1 m2 = throwMRFailure (CompsDoNotRefine m1 m2)


-- | Prove that one function refines another for all inputs
mrRefinesFun :: CompFun -> CompFun -> MRM ()
mrRefinesFun CompFunReturn CompFunReturn = return ()
mrRefinesFun f1 f2
  | Just nm <- compFunVarName f1 `mplus` compFunVarName f2
  , Just tp <- compFunInputType f1 `mplus` compFunInputType f2 =
    withUVarLift nm tp (f1,f2) $ \x (f1', f2') ->
    do m1' <- applyNormCompFun f1' x
       m2' <- applyNormCompFun f2' x
       mrRefines m1' m2'
mrRefinesFun _ _ = error "mrRefinesFun: unreachable!"


----------------------------------------------------------------------
-- * External Entrypoints
----------------------------------------------------------------------

-- | Test two monadic, recursive terms for equivalence
askMRSolver ::
  SharedContext ->
  Int {- ^ The debug level -} ->
  MREnv {- ^ The Mr Solver environment -} ->
  Maybe Integer {- ^ Timeout in milliseconds for each SMT call -} ->
  Term -> Term -> IO (Maybe MRFailure)

askMRSolver sc dlvl env timeout t1 t2 =
  do tp1 <- scTypeOf sc t1 >>= scWhnf sc
     tp2 <- scTypeOf sc t2 >>= scWhnf sc
     case asPiList tp1 of
       (uvar_ctx, asCompM -> Just _) ->
         fmap (either Just (const Nothing)) $
         runMRM sc timeout dlvl env $
         withUVars uvar_ctx $ \vars ->
         do tps_are_eq <- mrConvertible tp1 tp2
            if tps_are_eq then return () else
              throwMRFailure (TypesNotEq (Type tp1) (Type tp2))
            mrDebugPPPrefixSep 1 "mr_solver" t1 "|=" t2
            m1 <- mrApplyAll t1 vars >>= normCompTerm
            m2 <- mrApplyAll t2 vars >>= normCompTerm
            mrRefines m1 m2
       _ -> return $ Just $ NotCompFunType tp1
