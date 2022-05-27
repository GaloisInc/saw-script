{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

-- This is to stop GHC 8.8.4's pattern match checker exceeding its limit when
-- checking the pattern match in the 'CompTerm' case of 'normComp'
{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ <= 808
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
#endif

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
(assumingM b m) >>= k         = assumingM b (m >>= k)
(assertingM b m) >>= k        = assertingM b (m >>= k)
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
import Data.Bits (shiftL)
import Control.Monad.Except
import qualified Data.Map as Map
import qualified Data.Text as Text

import Prettyprinter

import Verifier.SAW.Term.Functor
import Verifier.SAW.Term.CtxTerm (substTerm)
import Verifier.SAW.SharedTerm
import Verifier.SAW.Recognizer
import Verifier.SAW.Cryptol.Monadify

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
  (>>) (mrDebugPPPrefix 3 "normCompTerm:" t) $
  withFailureCtx (FailCtxMNF t) $
  case asApplyAll t of
    (f@(asLambda -> Just _), args) ->
      mrApplyAll f args >>= normCompTerm
    (isGlobalDef "Prelude.returnM" -> Just (), [_, x]) ->
      return $ ReturnM x
    (isGlobalDef "Prelude.bindM" -> Just (), [_, _, m, f]) ->
      do norm <- normCompTerm m
         normBind norm (CompFunTerm f)
    (isGlobalDef "Prelude.errorM" -> Just (), [_, str]) ->
      return (ErrorM str)
    (isGlobalDef "Prelude.ite" -> Just (), [_, cond, then_tm, else_tm]) ->
      return $ Ite cond (CompTerm then_tm) (CompTerm else_tm)
    (isGlobalDef "Prelude.either" -> Just (), [ltp, rtp, _, f, g, eith]) ->
      return $ Either (Type ltp) (Type rtp) (CompFunTerm f) (CompFunTerm g) eith
    (isGlobalDef "Prelude.maybe" -> Just (), [tp, _, m, f, mayb]) ->
      do tp' <- case asApplyAll tp of
                  -- Always unfold: is_bvult, is_bvule
                  (tpf@(asGlobalDef -> Just ident), args)
                    | ident `elem` ["Prelude.is_bvult", "Prelude.is_bvule"]
                    , Just (_, Just body) <- asConstant tpf ->
                      mrApplyAll body args
                  _ -> return tp
         return $ MaybeElim (Type tp') (CompTerm m) (CompFunTerm f) mayb
    (isGlobalDef "Prelude.orM" -> Just (), [_, m1, m2]) ->
      return $ OrM (CompTerm m1) (CompTerm m2)
    (isGlobalDef "Prelude.assertingM" -> Just (), [_, cond, body_tm]) ->
      return $ AssertingM cond (CompTerm body_tm)
    (isGlobalDef "Prelude.assumingM" -> Just (), [_, cond, body_tm]) ->
      return $ AssumingM cond (CompTerm body_tm)
    (isGlobalDef "Prelude.existsM" -> Just (), [tp, _, body_tm]) ->
      return $ ExistsM (Type tp) (CompFunTerm body_tm)
    (isGlobalDef "Prelude.forallM" -> Just (), [tp, _, body_tm]) ->
      return $ ForallM (Type tp) (CompFunTerm body_tm)
    (isGlobalDef "Prelude.letRecM" -> Just (), [lrts, _, defs_f, body_f]) ->
      do
        -- Bind fresh function vars for the letrec-bound functions
        fun_tms <- mrFreshLetRecVars lrts defs_f
        -- Apply the body function to our function vars and recursively
        -- normalize the resulting computation
        body_tm <- mrApplyAll body_f fun_tms
        normCompTerm body_tm

    -- Recognize (multiFixM lrts (\ f1 ... fn -> (body1, ..., bodyn))).i args
    (asTupleSelector ->
     Just (asApplyAll -> (isGlobalDef "Prelude.multiFixM" -> Just (),
                          [lrts, defs_f]),
           i), args) ->
      do
        -- Bind fresh function variables for the functions f1 ... fn
        fun_tms <- mrFreshLetRecVars lrts defs_f
        -- Apply fi to the top-level arguments, keeping in mind that tuple
        -- selectors are one-based, not zero-based, so we subtract 1 from i
        body_tm <-
          if i > 0 && i <= length fun_tms then
            mrApplyAll (fun_tms !! (i-1)) args
          else throwMRFailure (MalformedComp t)
        normCompTerm body_tm

    -- Convert `vecMapM (bvToNat ...)` into `bvVecMapInvarM`, with the
    -- invariant being the current set of assumptions
    (asGlobalDef -> Just "CryptolM.vecMapM", [a, b, asBvToNat -> Just (w, n),
                                              f, xs]) ->
      do invar <- mrAssumptions
         liftSC2 scGlobalApply "CryptolM.bvVecMapInvarM"
                               [a, b, w, n, f, xs, invar] >>= normCompTerm

    -- Convert `atM (bvToNat ...) ... (bvToNat ...)` into the unfolding of
    -- `bvVecAtM`
    (asGlobalDef -> Just "CryptolM.atM", [asBvToNat -> Just (w1, n), a, xs,
                                          asBvToNat -> Just (w2, i)]) ->
      do body <- mrGlobalDefBody "CryptolM.bvVecAtM"
         ws_are_eq <- mrConvertible w1 w2
         if ws_are_eq then
           mrApplyAll body [w1, n, a, xs, i] >>= normCompTerm
         else throwMRFailure (MalformedComp t)

    -- Convert `atM n ... xs (bvToNat ...)` for a constant `n` into the
    -- unfolding of `bvVecAtM` after converting `n` to a bitvector constant
    -- and applying `genBVVecFromVec` to `xs`
    (asGlobalDef -> Just "CryptolM.atM", [n_tm@(asNat -> Just n), a, xs,
                                          asBvToNat ->
                                            Just (w_tm@(asNat -> Just w),
                                                  i)]) ->
      do body <- mrGlobalDefBody "CryptolM.bvVecAtM"
         if n < 1 `shiftL` fromIntegral w then do
           n' <- mrBvConst w (toInteger n)
           err_str <- liftSC1 scString "FIXME: normComp (atM) error"
           err_tm <- liftSC2 scGlobalApply "Prelude.error" [a, err_str]
           xs' <- liftSC2 scGlobalApply "Prelude.genBVVecFromVec"
                                        [n_tm, a, xs, err_tm, w_tm, n'] 
           mrApplyAll body [w_tm, n', a, xs', i] >>= normCompTerm
         else throwMRFailure (MalformedComp t)

    -- Convert `updateM (bvToNat ...) ... (bvToNat ...)` into the unfolding of
    -- `bvVecUpdateM`
    (asGlobalDef -> Just "CryptolM.updateM", [asBvToNat -> Just (w1, n), a, xs,
                                              asBvToNat -> Just (w2, i), x]) ->
      do body <- mrGlobalDefBody "CryptolM.bvVecUpdateM"
         ws_are_eq <- mrConvertible w1 w2
         if ws_are_eq then
           mrApplyAll body [w1, n, a, xs, i, x] >>= normCompTerm
         else throwMRFailure (MalformedComp t)

    -- Convert `updateM n ... xs (bvToNat ...)` for a constant `n` into the
    -- unfolding of `bvVecUpdateM` after converting `n` to a bitvector constant
    -- and applying `genBVVecFromVec` to `xs`
    (asGlobalDef -> Just "CryptolM.updateM", [n_tm@(asNat -> Just n), a, xs,
                                              asBvToNat ->
                                                Just (w_tm@(asNat -> Just w),
                                                      i), x]) ->
      do body <- mrGlobalDefBody "CryptolM.fromBVVecUpdateM"
         if n < 1 `shiftL` fromIntegral w then do
           n' <- mrBvConst w (toInteger n)
           err_str <- liftSC1 scString "FIXME: normComp (updateM) error"
           err_tm <- liftSC2 scGlobalApply "Prelude.error" [a, err_str]
           xs' <- liftSC2 scGlobalApply "Prelude.genBVVecFromVec"
                                        [n_tm, a, xs, err_tm, w_tm, n'] 
           mrApplyAll body [w_tm, n', a, xs', i, x, err_tm, n_tm] >>= normCompTerm
         else throwMRFailure (MalformedComp t)

    -- Always unfold: sawLet, multiArgFixM, invariantHint, Num_rec
    (f@(asGlobalDef -> Just ident), args)
      | ident `elem` ["Prelude.sawLet", "Prelude.multiArgFixM",
                      "Prelude.invariantHint", "Cryptol.Num_rec"]
      , Just (_, Just body) <- asConstant f ->
        mrApplyAll body args >>= normCompTerm

    -- Always unfold recursors applied to constructors
    (asRecursorApp -> Just (rc, crec, _, arg), args)
      | Just (c, _, cargs) <- asCtorParams arg ->
      do hd' <- liftSC4 scReduceRecursor rc crec c cargs 
                  >>= liftSC1 betaNormalize
         t' <- mrApplyAll hd' args
         normCompTerm t'

    -- Always unfold record selectors applied to record values (after scWhnf)
    (asRecordSelector -> Just (r, fld), args) ->
      do r' <- liftSC1 scWhnf r
         case asRecordValue r' of
           Just (Map.lookup fld -> Just f) -> do t' <- mrApplyAll f args
                                                 normCompTerm t'
           _ -> throwMRFailure (MalformedComp t)

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
normBind (AssertingM cond comp) k = return $ AssertingM cond (CompBind comp k)
normBind (AssumingM cond comp) k = return $ AssumingM cond (CompBind comp k)
normBind (ExistsM tp f) k = return $ ExistsM tp (compFunComp f k)
normBind (ForallM tp f) k = return $ ForallM tp (compFunComp f k)
normBind (FunBind f args k1) k2
  -- Turn `bvVecMapInvarM ... >>= k` into `bvVecMapInvarBindM ... k`
  | GlobalName (globalDefString -> "CryptolM.bvVecMapInvarM") [] <- f
  , not (isCompFunReturn (compFunComp k1 k2)) =
    do f' <- mrGlobalDef "CryptolM.bvVecMapInvarBindM"
       cont <- compFunToTerm (compFunComp k1 k2)
       return $ FunBind f' (args ++ [cont]) CompFunReturn
  -- Turn `bvVecMapInvarBindM ... k1 >>= k2` into
  -- `bvVecMapInvarBindM ... (composeM ... k1 k2)`
  | GlobalName (globalDefString -> "CryptolM.bvVecMapInvarBindM") [] <- f
  , (args_pre, [cont]) <- splitAt 8 args
  , not (isCompFunReturn (compFunComp k1 k2)) =
    do cont' <- compFunToTerm (compFunComp (compFunComp (CompFunTerm cont) k1) k2)
       return $ FunBind f (args_pre ++ [cont']) CompFunReturn
  | otherwise = return $ FunBind f args (compFunComp k1 k2)

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

-- | Convert a 'CompFun' which is not a 'CompFunReturn' into a 'Term'
compFunToTerm :: CompFun -> MRM Term
compFunToTerm (CompFunTerm t) = return t
compFunToTerm (CompFunComp f g) =
  do f' <- compFunToTerm f
     g' <- compFunToTerm g
     f_tp <- mrTypeOf f'
     g_tp <- mrTypeOf g'
     case (f_tp, g_tp) of
       (asPi -> Just (_, a, asCompM -> Just b),
        asPi -> Just (_, _, asCompM -> Just c)) ->
         liftSC2 scGlobalApply "Prelude.composeM" [a, b, c, f', g']
       _ -> error "compFunToTerm: type(s) not of the form: a -> CompM b"
compFunToTerm CompFunReturn = error "compFunToTerm: got a CompFunReturn"

-- | Convert a 'Comp' into a 'Term'
compToTerm :: Comp -> MRM Term
compToTerm (CompTerm t) = return t
compToTerm (CompReturn t) =
   do tp <- mrTypeOf t
      liftSC2 scGlobalApply "Prelude.returnM" [tp, t]
compToTerm (CompBind m CompFunReturn) = compToTerm m
compToTerm (CompBind m f) =
  do m' <- compToTerm m
     f' <- compFunToTerm f
     mrTypeOf f' >>= \case
       (asPi -> Just (_, a, asCompM -> Just b)) ->
         liftSC2 scGlobalApply "Prelude.bindM" [a, b, m', f']
       _ -> error "compToTerm: type not of the form: a -> CompM b"

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

-- | Prove the invariant of a coinductive hypothesis
proveCoIndHypInvariant :: CoIndHyp -> MRM ()
proveCoIndHypInvariant hyp =
  do (invar1, invar2) <- applyCoIndHypInvariants hyp
     invar <- liftSC2 scAnd invar1 invar2
     success <- mrProvable invar
     if success then return () else
       throwMRFailure $
       InvariantNotProvable (coIndHypLHSFun hyp) (coIndHypRHSFun hyp) invar

-- | Co-inductively prove the refinement
--
-- > forall x1, ..., xn. preF y1 ... ym -> preG z1 ... zl ->
-- >   F y1 ... ym |= G z1 ... zl@
--
-- where @F@ and @G@ are the given 'FunName's, @y1, ..., ym@ and @z1, ..., zl@
-- are the given argument lists, @x1, ..., xn@ is the current context of uvars,
-- and @invarF@ and @invarG@ are the invariants associated with @F@ and @G@,
-- respectively. This proof is performed by coinductively assuming the
-- refinement holds and proving the refinement with the definitions of @F@ and
-- @G@ unfolded to their bodies. Note that this refinement is performed with
-- /only/ the invariants @invarF@ and @invarG@ as assumptions; all other
-- assumptions are thrown away. If while running the refinement computation a
-- 'CoIndHypMismatchWidened' error is reached with the given names, the state is
-- restored and the computation is re-run with the widened hypothesis.
mrRefinesCoInd :: FunName -> [Term] -> FunName -> [Term] -> MRM ()
mrRefinesCoInd f1 args1 f2 args2 =
  do ctx <- mrUVarCtx
     preF1 <- mrGetInvariant f1
     preF2 <- mrGetInvariant f2
     let hyp = CoIndHyp ctx f1 f2 args1 args2 preF1 preF2
     proveCoIndHypInvariant hyp
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
     (invar1, invar2) <- applyCoIndHypInvariants hyp
     invar <- liftSC2 scAnd invar1 invar2
     (withOnlyUVars (coIndHypCtx hyp) $ withOnlyAssumption invar $
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
     proveCoIndHypInvariant hyp


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
generalizeCoIndHypArgs (CoIndHyp ctx f1 f2 args1 args2 invar1 invar2) tp specs =
  do let set_arg i args =
           take i args ++ (Unshared $ LocalVar 0) : drop (i+1) args
     let (specs1, specs2) = partitionEithers specs
     -- NOTE: need to lift the arguments because we are adding a variable
     args1' <- liftTermLike 0 1 args1
     args2' <- liftTermLike 0 1 args2
     let args1'' = foldr set_arg args1' specs1
         args2'' = foldr set_arg args2' specs2
     return $ CoIndHyp (ctx ++ [("z",tp)]) f1 f2 args1'' args2'' invar1 invar2


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

mrRefines' (ReturnM e1) (ReturnM e2) = mrAssertProveRel True e1 e2
mrRefines' (ErrorM _) (ErrorM _) = return ()
mrRefines' (ReturnM e) (ErrorM _) = throwMRFailure (ReturnNotError e)
mrRefines' (ErrorM _) (ReturnM e) = throwMRFailure (ReturnNotError e)

-- maybe elimination on equality types
mrRefines' (MaybeElim (Type (asEq -> Just (tp,e1,e2))) m1 f1 _) m2 =
  do cond <- mrEq' tp e1 e2
     not_cond <- liftSC1 scNot cond
     cond_pf <- liftSC1 scEqTrue cond >>= mrDummyProof
     m1' <- applyNormCompFun f1 cond_pf
     cond_holds <- mrProvable cond
     not_cond_holds <- mrProvable not_cond
     case (cond_holds, not_cond_holds) of
       (True, _) -> mrRefines m1' m2
       (_, True) -> mrRefines m1 m2
       _ -> withAssumption cond (mrRefines m1' m2) >>
            withAssumption not_cond (mrRefines m1 m2)
mrRefines' m1 (MaybeElim (Type (asEq -> Just (tp,e1,e2))) m2 f2 _) =
  do cond <- mrEq' tp e1 e2
     not_cond <- liftSC1 scNot cond
     cond_pf <- liftSC1 scEqTrue cond >>= mrDummyProof
     m2' <- applyNormCompFun f2 cond_pf
     cond_holds <- mrProvable cond
     not_cond_holds <- mrProvable not_cond
     case (cond_holds, not_cond_holds) of
       (True, _) -> mrRefines m1 m2'
       (_, True) -> mrRefines m1 m2
       _ -> withAssumption cond (mrRefines m1 m2') >>
            withAssumption not_cond (mrRefines m1 m2)

-- maybe elimination on isFinite types
mrRefines' (MaybeElim (Type (asIsFinite -> Just n1)) m1 f1 _) m2 =
  do n1_norm <- mrNormOpenTerm n1
     maybe_assump <- mrGetDataTypeAssump n1_norm
     fin_pf <- mrIsFinite n1_norm >>= mrDummyProof
     case (maybe_assump, asNum n1_norm) of
       (_, Just (Left _)) -> applyNormCompFun f1 fin_pf >>= flip mrRefines m2
       (_, Just (Right _)) -> mrRefines m1 m2
       (Just (IsNum _), _) -> applyNormCompFun f1 fin_pf >>= flip mrRefines m2
       (Just IsInf, _) -> mrRefines m1 m2
       _ ->
         withDataTypeAssump n1_norm IsInf (mrRefines m1 m2) >>
         liftSC0 scNatType >>= \nat_tp ->
         (withUVarLift "n" (Type nat_tp) (n1_norm, f1, m2) $ \ n (n1', f1', m2') ->
           withDataTypeAssump n1' (IsNum n)
           (applyNormCompFun f1' n >>= flip mrRefines m2'))
mrRefines' m1 (MaybeElim (Type (asIsFinite -> Just n2)) m2 f2 _) =
  do n2_norm <- mrNormOpenTerm n2
     maybe_assump <- mrGetDataTypeAssump n2_norm
     fin_pf <- mrIsFinite n2_norm >>= mrDummyProof
     case (maybe_assump, asNum n2_norm) of
       (_, Just (Left _)) -> applyNormCompFun f2 fin_pf >>= mrRefines m1
       (_, Just (Right _)) -> mrRefines m1 m2
       (Just (IsNum _), _) -> applyNormCompFun f2 fin_pf >>= mrRefines m1
       (Just IsInf, _) -> mrRefines m1 m2
       _ ->
         withDataTypeAssump n2_norm IsInf (mrRefines m1 m2) >>
         liftSC0 scNatType >>= \nat_tp ->
         (withUVarLift "n" (Type nat_tp) (n2_norm, f2, m1) $ \ n (n2', f2', m1') ->
           withDataTypeAssump n2' (IsNum n)
           (applyNormCompFun f2' n >>= mrRefines m1'))

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
  mrNormOpenTerm t1 >>= \t1' ->
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
  mrNormOpenTerm t2 >>= \t2' ->
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

mrRefines' m1 (AssumingM cond2 m2) =
  withAssumption cond2 $ mrRefines m1 m2
mrRefines' (AssertingM cond1 m1) m2 =
  withAssumption cond1 $ mrRefines m1 m2

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

  -- If we have an opaque FunAssump that f1 args1' refines f2 args2', then
  -- prove that args1 = args1', args2 = args2', and then that k1 refines k2
  (_, Just (FunAssump ctx args1' (OpaqueFunAssump f2' args2'))) | f2 == f2' ->
    do evars <- mrFreshEVars ctx
       (args1'', args2'') <- substTermLike 0 evars (args1', args2')
       zipWithM_ mrAssertProveEq args1'' args1
       zipWithM_ mrAssertProveEq args2'' args2
       mrRefinesFun k1 k2

  -- If we have an opaque FunAssump that f1 refines some f /= f2, and f2
  -- unfolds and is not recursive in itself, unfold f2 and recurse
  (_, Just (FunAssump _ _ (OpaqueFunAssump _ _)))
    | Just (f2_body, False) <- maybe_f2_body ->
    normBindTerm f2_body k2 >>= \m2' -> mrRefines m1 m2'

  -- If we have a rewrite FunAssump, or we have an opaque FunAssump that
  -- f1 args1' refines some f args where f /= f2 and f2 does not match the
  -- case above, treat either case like we have a rewrite FunAssump and prove
  -- that args1 = args1' and then that f args refines m2
  (_, Just (FunAssump ctx args1' (funAssumpRHSAsNormComp -> rhs))) ->
    do evars <- mrFreshEVars ctx
       (args1'', rhs') <- substTermLike 0 evars (args1', rhs)
       zipWithM_ mrAssertProveEq args1'' args1
       m1' <- normBind rhs' k1
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

mrRefines' m1@(FunBind f1 args1 k1) m2 =
  mrGetFunAssump f1 >>= \case

  -- If we have an assumption that f1 args' refines some rhs, then prove that
  -- args1 = args' and then that rhs refines m2
  Just (FunAssump ctx args1' (funAssumpRHSAsNormComp -> rhs)) ->
    do evars <- mrFreshEVars ctx
       (args1'', rhs') <- substTermLike 0 evars (args1', rhs)
       zipWithM_ mrAssertProveEq args1'' args1
       m1' <- normBind rhs' k1
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
    _ -> mrRefines'' m1 m2

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
  _ -> mrRefines'' m1 m2

mrRefines' m1 m2 = mrRefines'' m1 m2

-- | The cases of 'mrRefines' which must occur after the ones in 'mrRefines''.
-- For example, the rules that introduce existential variables need to go last,
-- so that they can quantify over as many universals as possible
mrRefines'' :: NormComp -> NormComp -> MRM ()

mrRefines'' m1 (AssertingM cond2 m2) =
  mrProvable cond2 >>= \cond2_pv ->
  if cond2_pv then mrRefines m1 m2
  else throwMRFailure (AssertionNotProvable cond2)
mrRefines'' (AssumingM cond1 m1) m2 =
  mrProvable cond1 >>= \cond1_pv ->
  if cond1_pv then mrRefines m1 m2
  else throwMRFailure (AssumptionNotProvable cond1)

mrRefines'' m1 (ExistsM tp f2) =
  do let nm = maybe "x" id (compFunVarName f2)
     evar <- mrFreshEVar nm tp
     m2' <- applyNormCompFun f2 evar
     mrRefines m1 m2'
mrRefines'' (ForallM tp f1) m2 =
  do let nm = maybe "x" id (compFunVarName f1)
     evar <- mrFreshEVar nm tp
     m1' <- applyNormCompFun f1 evar
     mrRefines m1' m2

-- If none of the above cases match, then fail
mrRefines'' m1 m2 = throwMRFailure (CompsDoNotRefine m1 m2)


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

-- | The result of a successful call to Mr. Solver: either a 'FunAssump' to
-- (optionally) add to the 'MREnv', or 'Nothing' if the left-hand-side was not
-- a function name
type MRSolverResult = Maybe (FunName, FunAssump)

-- | The main loop of 'askMRSolver'. The first argument is an accumulator of
-- variables to introduce, innermost first.
askMRSolverH :: [Term] -> Term -> Term -> Term -> Term -> MRM MRSolverResult

-- If we need to introduce a bitvector on one side and a Num on the other,
-- introduce a bitvector variable and substitute `TCNum` of `bvToNat` of that
-- variable on the Num side
askMRSolverH vars (asPi -> Just (nm1, tp@(asBitvectorType -> Just n), body1)) t1
                  (asPi -> Just (nm2, asDataType -> Just (primName -> "Cryptol.Num", _), body2)) t2 =
  let nm = if Text.head nm2 == '_' then nm1 else nm2 in
  withUVarLift nm (Type tp) (vars, t1, t2) $ \var (vars', t1', t2') ->
  do nat_tm <- liftSC2 scBvToNat n var
     num_tm <- liftSC2 scCtorApp "Cryptol.TCNum" [nat_tm]
     body2' <- substTerm 0 (num_tm : vars') body2
     t1'' <- mrApplyAll t1' [var]
     t2'' <- mrApplyAll t2' [num_tm]
     askMRSolverH (var : vars') body1 t1'' body2' t2''
askMRSolverH vars (asPi -> Just (nm1, asDataType -> Just (primName -> "Cryptol.Num", _), body1)) t1
                  (asPi -> Just (nm2, tp@(asBitvectorType -> Just n), body2)) t2 =
  let nm = if Text.head nm2 == '_' then nm1 else nm2 in
  withUVarLift nm (Type tp) (vars, t1, t2) $ \var (vars', t1', t2') ->
  do nat_tm <- liftSC2 scBvToNat n var
     num_tm <- liftSC2 scCtorApp "Cryptol.TCNum" [nat_tm]
     body1' <- substTerm 0 (num_tm : vars') body1
     t1'' <- mrApplyAll t1' [num_tm]
     t2'' <- mrApplyAll t2' [var]
     askMRSolverH (var : vars') body1' t1'' body2 t2''

-- If we need to introduce a BVVec on one side and a non-BVVec vector on the
-- other, introduce a BVVec variable and substitute `genBVVecFromVec` of that
-- variable on the non-BVVec side
askMRSolverH vars tp1@(asPi -> Just (nm1, tp@(asBVVecType -> Just (n, len, a)), body1)) t1
                  tp2@(asPi -> Just (nm2, asNonBVVecVectorType -> Just (m, a'), body2)) t2 =
  do m' <- mrBvToNat n len
     ms_are_eq <- mrConvertible m' m
     as_are_eq <- mrConvertible a a'
     if ms_are_eq && as_are_eq then return () else
       throwMRFailure (TypesNotEq (Type tp1) (Type tp2))
     let nm = if Text.head nm2 == '_' then nm1 else nm2
     withUVarLift nm (Type tp) (vars, t1, t2) $ \var (vars', t1', t2') ->
       do err_str_tm <- liftSC1 scString "FIXME: askMRSolverH error"
          err_tm <- liftSC2 scGlobalApply "Prelude.error" [a, err_str_tm]
          bvvec_tm <- liftSC2 scGlobalApply "Prelude.genFromBVVec"
                                            [n, len, a, var, err_tm, m]
          body2' <- substTerm 0 (bvvec_tm : vars') body2
          t1'' <- mrApplyAll t1' [var]
          t2'' <- mrApplyAll t2' [bvvec_tm]
          askMRSolverH (var : vars') body1 t1'' body2' t2''
askMRSolverH vars tp1@(asPi -> Just (nm1, asNonBVVecVectorType -> Just (m, a'), body2)) t1
                  tp2@(asPi -> Just (nm2, tp@(asBVVecType -> Just (n, len, a)), body1)) t2 =
  do m' <- mrBvToNat n len
     ms_are_eq <- mrConvertible m' m
     as_are_eq <- mrConvertible a a'
     if ms_are_eq && as_are_eq then return () else
       throwMRFailure (TypesNotEq (Type tp1) (Type tp2))
     let nm = if Text.head nm2 == '_' then nm1 else nm2
     withUVarLift nm (Type tp) (vars, t1, t2) $ \var (vars', t1', t2') ->
       do err_str_tm <- liftSC1 scString "FIXME: askMRSolverH error"
          err_tm <- liftSC2 scGlobalApply "Prelude.error" [a, err_str_tm]
          bvvec_tm <- liftSC2 scGlobalApply "Prelude.genFromBVVec"
                                            [n, len, a, var, err_tm, m]
          body1' <- substTerm 0 (bvvec_tm : vars') body1
          t1'' <- mrApplyAll t1' [var]
          t2'' <- mrApplyAll t2' [bvvec_tm]
          askMRSolverH (var : vars') body1' t1'' body2 t2''

-- Introduce variables of the same type together
askMRSolverH vars tp11@(asPi -> Just (nm1, tp1, body1)) t1
                  tp22@(asPi -> Just (nm2, tp2, body2)) t2 =
  do tps_are_eq <- mrConvertible tp1 tp2
     if tps_are_eq then return () else
       throwMRFailure (TypesNotEq (Type tp11) (Type tp22))
     let nm = if Text.head nm2 == '_' then nm1 else nm2
     withUVarLift nm (Type tp1) (vars, t1, t2) $ \var (vars', t1', t2') ->
       do t1'' <- mrApplyAll t1' [var]
          t2'' <- mrApplyAll t2' [var]
          askMRSolverH (var : vars') body1 t1'' body2 t2''

-- Error if we don't have the same number of arguments on both sides
askMRSolverH _ tp1@(asPi -> Just _) _ tp2 _ =
  throwMRFailure (TypesNotEq (Type tp1) (Type tp2))
askMRSolverH _ tp1 _ tp2@(asPi -> Just _) _ =
  throwMRFailure (TypesNotEq (Type tp1) (Type tp2))

-- The base case: both sides are CompM of the same type
askMRSolverH _ (asCompM -> Just _) t1 (asCompM -> Just _) t2 =
  do m1 <- normCompTerm t1 
     m2 <- normCompTerm t2
     mrRefines m1 m2
     case (m1, m2) of
       -- If t1 and t2 are both named functions, our result is the opaque
       -- FunAssump that forall xs. f1 xs |= f2 xs'
       (FunBind f1 args1 CompFunReturn, FunBind f2 args2 CompFunReturn) ->
         mrUVarCtx >>= \uvar_ctx ->
         return $ Just (f1, FunAssump { fassumpCtx = uvar_ctx,
                                        fassumpArgs = args1,
                                        fassumpRHS = OpaqueFunAssump f2 args2 })
       -- If just t1 is a named function, our result is the rewrite FunAssump
       -- that forall xs. f1 xs |= m2
       (FunBind f1 args1 CompFunReturn, _) ->
         mrUVarCtx >>= \uvar_ctx ->
         return $ Just (f1, FunAssump { fassumpCtx = uvar_ctx,
                                        fassumpArgs = args1,
                                        fassumpRHS = RewriteFunAssump m2 })
       _ -> return Nothing

-- Error if we don't have CompM at the end
askMRSolverH _ (asCompM -> Just _) _ tp2 _ =
  throwMRFailure (NotCompFunType tp2)
askMRSolverH _ tp1 _ _ _ =
  throwMRFailure (NotCompFunType tp1)


-- | Test two monadic, recursive terms for refinement. On success, if the
-- left-hand term is a named function, add the refinement to the 'MREnv'
-- environment.
askMRSolver ::
  SharedContext ->
  MREnv {- ^ The Mr Solver environment -} ->
  Maybe Integer {- ^ Timeout in milliseconds for each SMT call -} ->
  Term -> Term -> IO (Either MRFailure MRSolverResult)

askMRSolver sc env timeout t1 t2 =
  do tp1 <- scTypeOf sc t1 >>= scWhnf sc
     tp2 <- scTypeOf sc t2 >>= scWhnf sc
     runMRM sc timeout env $
       mrDebugPPPrefixSep 1 "mr_solver" t1 "|=" t2 >>
       askMRSolverH [] tp1 t1 tp2 t2
