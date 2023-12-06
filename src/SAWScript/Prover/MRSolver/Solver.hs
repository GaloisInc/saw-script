{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
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
computations, which uses the following laws to simplify binds and calls to
@liftStackS@ in computations, where @either@ is the sum elimination function
defined in the SAW core prelude:

> retS x >>= k                  = k x
> errorS str >>= k              = errorM
> (m >>= k1) >>= k2             = m >>= \x -> k1 x >>= k2
> (existsS f) >>= k             = existsM (\x -> f x >>= k)
> (forallS f) >>= k             = forallM (\x -> f x >>= k)
> (assumingS b m) >>= k         = assumingM b (m >>= k)
> (assertingS b m) >>= k        = assertingM b (m >>= k)
> (orS m1 m2) >>= k             = orM (m1 >>= k) (m2 >>= k)
> (if b then m1 else m2) >>= k  = if b then m1 >>= k else m2 >>= k
> (either f1 f2 e) >>= k        = either (\x -> f1 x >>= k) (\x -> f2 x >>= k) e
> (multiFixS funs body) >>= k   = multiFixS funs (\F1 ... Fn -> body F1 ... Fn >>= k)
> 
> liftStackS (retS x)                = retS x
> liftStackS (errorS str)            = errorS str
> liftStackS (m >>= k)               = liftStackS m >>= \x -> liftStackS (k x)
> liftStackS (existsS f)             = existsM (\x -> liftStackS (f x))
> liftStackS (forallS f)             = forallM (\x -> liftStackS (f x))
> liftStackS (assumingS b m)         = assumingM b (liftStackS m)
> liftStackS (assertingS b m)        = assertingM b (liftStackS m)
> liftStackS (orS m1 m2)             = orM (liftStackS m1) (liftStackS m2)
> liftStackS (if b then m1 else m2)  = if b then liftStackS m1 else liftStackS m2
> liftStackS (either f1 f2 e)        = either (\x -> liftStackS f1 x) (\x -> liftStackS f2 x) e
> liftStackS (multiFixS funs body)   = multiFixS funs (\F1 ... Fn -> liftStackS (body F1 ... Fn))

The resulting computations are in one of the following forms:

> returnM e  |  errorM str  |  existsM f  |  forallM f  |  assumingS b m  |
> assertingS b m  |  orM m1 m2  |  if b then m1 else m2  |  either f1 f2 e  |
> F e1 ... en  |  liftStackS (F e1 ... en)  |
> F e1 ... en >>= k  | liftStackS (F e1 ... en) >>= k  |
> multiFixS (\F1 ... Fn -> (f1, ..., fn)) (\F1 ... Fn -> m)

The form @F e1 ... en@ refers to a recursively-defined function or a function
variable that has been locally bound by a @multiFixS@. Either way, monadic
normalization does not attempt to normalize these functions.

The algorithm maintains a context of three sorts of variables: @multiFixS@-bound
variables, existential variables, and universal variables. Universal variables
are represented as free SAW core variables, while the other two forms of
variable are represented as SAW core 'ExtCns's terms, which are essentially
axioms that have been generated internally. These 'ExtCns's are Skolemized,
meaning that they take in as arguments all universal variables that were in
scope when they were created. The context also maintains a partial substitution
for the existential variables, as they become instantiated with values, and it
additionally remembers the bodies / unfoldings of the @multiFixS@-bound variables.

The goal of the solver at any point is of the form @C |- m1 |= m2@, meaning that
we are trying to prove @m1@ refines @m2@ in context @C@. This proceeds by cases:

> C |- retS e1 |= retS e2: prove C |- e1 = e2
> 
> C |- errorS str1 |= errorS str2: vacuously true
> 
> C |- if b then m1' else m1'' |= m2: prove C,b=true |- m1' |= m2 and
> C,b=false |- m1'' |= m2, skipping either case where C,b=X is unsatisfiable;
> 
> C |- m1 |= if b then m2' else m2'': similar to the above
> 
> C |- either T U (SpecM V) f1 f2 e |= m: prove C,x:T,e=inl x |- f1 x |= m and
> C,y:U,e=inl y |- f2 y |= m, again skippping any case with unsatisfiable context;
> 
> C |- m |= either T U (SpecM V) f1 f2 e: similar to previous
> 
> C |- m |= forallS f: make a new universal variable x and recurse
> 
> C |- existsS f |= m: make a new universal variable x and recurse (existential
> elimination uses universal variables and vice-versa)
> 
> C |- m |= existsS f: make a new existential variable x and recurse
> 
> C |- forallS f |= m: make a new existential variable x and recurse
> 
> C |- m |= orS m1 m2: try to prove C |- m |= m1, and if that fails, backtrack and
> prove C |- m |= m2
> 
> C |- orS m1 m2 |= m: prove both C |- m1 |= m and C |- m2 |= m
> 
> C |- multiFixS (\F1 ... Fn -> (f1, ..., fn)) (\F1 ... Fn -> body) |= m: create
> multiFixS-bound variables F1 through Fn in the context bound to their unfoldings
> f1 through fn, respectively, and recurse on body |= m
> 
> C |- m |= multiFixS (\F1 ... Fn -> (f1, ..., fn)) (\F1 ... Fn -> body): similar to
> previous case
> 
> C |- F e1 ... en >>= k |= F e1' ... en' >>= k': prove C |- ei = ei' for each i
> and then prove k x |= k' x for new universal variable x
> 
> C |- F e1 ... en >>= k |= F' e1' ... em' >>= k':
> 
> * If we have an assumption that forall x1 ... xj, F a1 ... an |= F' a1' .. am',
>   prove ei = ai and ei' = ai' and then that C |- k x |= k' x for fresh uvar x
> 
> * If we have an assumption that forall x1, ..., xn, F e1'' ... en'' |= m' for
>   some ei'' and m', match the ei'' against the ei by instantiating the xj with
>   fresh evars, and if this succeeds then recursively prove C |- m' >>= k |= RHS
> 
> (We don't do this one right now)
> * If we have an assumption that forall x1', ..., xn', m |= F e1'' ... en'' for
>   some ei'' and m', match the ei'' against the ei by instantiating the xj with
>   fresh evars, and if this succeeds then recursively prove C |- LHS |= m' >>= k'
> 
> * If either side is a definition whose unfolding does not contain multiFixS, or
>   any related operations, unfold it
> 
> * If F and F' have the same return type, add an assumption forall uvars in scope
>   that F e1 ... en |= F' e1' ... em' and unfold both sides, recursively proving
>   that F_body e1 ... en |= F_body' e1' ... em'. Then also prove k x |= k' x for
>   fresh uvar x.
> 
> * Otherwise we don't know to "split" one of the sides into a bind whose
>   components relate to the two components on the other side, so just fail

Note that if either side of the final case is wrapped in a @liftStackS@, the
behavior is identical, just with a @liftStackS@ wrapped around the appropriate
unfolded function body or bodies. The only exception is the second to final case,
which also requires the both functions either be lifted or unlifted.
-}

module SAWScript.Prover.MRSolver.Solver where

import Data.Maybe
import Data.Either
import Numeric.Natural (Natural)
import qualified Data.Text as T
import Data.List (find, findIndices)
import Data.Foldable (foldlM)
import Data.Bits (shiftL)
import Control.Monad.Reader
import Control.Monad.Except
import qualified Data.Map as Map
import qualified Data.Text as Text
import Data.Set (Set)

import Verifier.SAW.Term.Functor
import Verifier.SAW.SharedTerm
import Verifier.SAW.Recognizer
import Verifier.SAW.Cryptol.Monadify
import SAWScript.Prover.SolverStats
import SAWScript.Proof (Sequent, SolveResult)
import SAWScript.Value (TopLevel)

import SAWScript.Prover.MRSolver.Term
import SAWScript.Prover.MRSolver.Evidence
import SAWScript.Prover.MRSolver.Monad
import SAWScript.Prover.MRSolver.SMT


----------------------------------------------------------------------
-- * Normalizing and Matching on Terms
----------------------------------------------------------------------

-- | Match a right-nested series of pairs. This is similar to 'asTupleValue'
-- except that it expects a unit value to always be at the end.
asNestedPairs :: Recognizer Term [Term]
asNestedPairs (asPairValue -> Just (x, asNestedPairs -> Just xs)) = Just (x:xs)
asNestedPairs (asFTermF -> Just UnitValue) = Just []
asNestedPairs _ = Nothing

-- | Recognize a term of the form @Cons1 _ x1 (Cons1 _ x2 (... (Nil1 _)))@
asList1 :: Recognizer Term [Term]
asList1 (asCtor -> Just (nm, [_]))
  | primName nm == "Prelude.Nil1" = return []
asList1 (asCtor -> Just (nm, [_, hd, tl]))
  | primName nm == "Prelude.Cons1" = (hd:) <$> asList1 tl
asList1 _ = Nothing

-- | Recognize a term of the form @mkFrameCall frame n arg1 ... argn@
asMkFrameCall :: Recognizer Term (Term, Natural, [Term])
asMkFrameCall (asApplyAll -> ((isGlobalDef "Prelude.mkFrameCall" -> Just ()),
                              (frame : (asNat -> Just n) : args))) =
  Just (frame, n, args)
asMkFrameCall _ = Nothing

-- | Recognize a term of the form @CallS _ _ _ (mkFrameCall frame n args)@
asCallS :: Recognizer Term (Term, Natural, [Term])
asCallS (asApplyAll ->
         ((isGlobalDef "Prelude.callS" -> Just ()),
          [_, _, _,
           (asMkFrameCall -> Just (frame, n, args))])) =
  Just (frame, n, args)
asCallS _ = Nothing

-- | Recursively traverse a 'Term' and replace each term of the form
--
-- > CallS _ _ _ (mkFrameCall _ i arg1 ... argn)
--
-- with the term @tmi arg1 ... argn@, where @tmi@ is the @i@th term in the list
--
-- FIXME: what we /actually/ want here is to only replace recursive calls as
-- they get normalized; that is, it would be more correct to only recurse inside
-- lambdas, to the left and right of binds, and into the computational subterms
-- of our variable monadic operations (including, e.g., if-then-else and the
-- either and maybe eliminators). But the implementation here should give the
-- correct result for any code we are actually going to see...
mrReplaceCallsWithTerms :: [Term] -> Term -> MRM t Term
mrReplaceCallsWithTerms top_tms top_t =
  flip runReaderT top_tms $
  flip memoFixTermFun top_t $ \recurse t -> case t of
  (asCallS -> Just (_, i, args)) ->
    -- Replace a CallS with its corresponding term
    ask >>= \tms -> lift $ mrApplyAll (tms!!(fromIntegral i)) args
  (asApplyAll ->
   (isGlobalDef "Prelude.multiFixS" -> Just (), _)) ->
    -- Don't recurse inside another multiFixS, since it binds new calls
    return t
  (asLambda -> Just (x, tp, body)) ->
    -- Lift our terms when we recurse inside a binder; also, not that we don't
    -- expect to lift types, so we leave tp alone
    do tms <- ask
       tms' <- liftTermLike 0 1 tms
       body' <- local (const tms') $ recurse body
       lift $ liftSC3 scLambda x tp body'
  (asPi -> Just _) ->
    -- We don't expect to lift types, so we leave them alone
    return t
  _ -> traverseSubterms recurse t


-- | Bind fresh function variables for a @multiFixS@ with the given list of
-- @LetRecType@s and tuple of definitions for the function bodies
mrFreshCallVars :: Term -> Term -> Term -> Term -> MRM t [MRVar]
mrFreshCallVars ev stack frame defs_tm =
  do
    -- First, make fresh function constants for all the recursive functions,
    -- noting that each constant must abstract out the current uvar context
    -- (see mrFreshVar)
    new_stack <- liftSC2 scGlobalApply "Prelude.pushFunStack" [frame, stack]
    lrts <- liftSC1 scWhnf frame >>= \case
       (asList1 -> Just lrts) -> return lrts
       _ -> throwMRFailure (MalformedLetRecTypes frame)
    fun_tps <- forM lrts $ \lrt ->
      liftSC2 scGlobalApply "Prelude.LRTType" [ev, new_stack, lrt]
    fun_vars <- mapM (mrFreshVar "F") fun_tps

    -- Next, match on the tuple of recursive function definitions and convert
    -- each definition to a function body, by replacing all recursive calls in
    -- each function body with our new variable terms (which are applied to the
    -- current uvars; see mrVarTerm) and then lambda-abstracting all the
    -- current uvars
    fun_tms <- mapM mrVarTerm fun_vars
    defs_tm' <- liftSC1 scWhnf defs_tm
    bodies <- case asNestedPairs defs_tm' of
      Just defs -> mapM (mrReplaceCallsWithTerms fun_tms >=> lambdaUVarsM) defs
      Nothing -> throwMRFailure (MalformedDefs defs_tm)

    -- Remember the body associated with each fresh function constant
    zipWithM_ (\f body -> mrSetVarInfo f (CallVarInfo body)) fun_vars bodies

    -- Finally, return the fresh function variables
    return fun_vars


-- | Normalize a 'Term' of monadic type to monadic normal form
normCompTerm :: Term -> MRM t NormComp
normCompTerm = normComp . CompTerm

-- | Normalize a computation to monadic normal form, assuming any 'Term's it
-- contains have already been normalized with respect to beta and projections
-- (but constants need not be unfolded)
normComp :: Comp -> MRM t NormComp
normComp (CompReturn t) = return $ RetS t
normComp (CompBind m f) =
  do norm <- normComp m
     normBind norm f
normComp (CompTerm t) =
  (>>) (mrDebugPPPrefix 3 "normCompTerm:" t) $
  withFailureCtx (FailCtxMNF t) $
  case asApplyAll t of
    (f@(asLambda -> Just _), args@(_:_)) ->
      mrApplyAll f args >>= normCompTerm
    (isGlobalDef "Prelude.retS" -> Just (), [_, _, _, x]) ->
      return $ RetS x
    (isGlobalDef "Prelude.bindS" -> Just (), [e, stack, _, _, m, f]) ->
      do norm <- normCompTerm m
         normBind norm (CompFunTerm (SpecMParams e stack) f)
    (isGlobalDef "Prelude.errorS" -> Just (), [_, _, _, str]) ->
      return (ErrorS str)
    (isGlobalDef "Prelude.liftStackS" -> Just (), [ev, stk, _, t']) ->
      normCompTerm t' >>= liftStackNormComp (SpecMParams ev stk)
    (isGlobalDef "Prelude.ite" -> Just (), [_, cond, then_tm, else_tm]) ->
      return $ Ite cond (CompTerm then_tm) (CompTerm else_tm)
    (isGlobalDef "Prelude.either" -> Just (),
     [ltp, rtp, (asSpecM -> Just (params, _)), f, g, eith]) ->
      return $ Eithers [(Type ltp, CompFunTerm params f),
                        (Type rtp, CompFunTerm params g)] eith
    (isGlobalDef "Prelude.eithers" -> Just (),
     [_, (matchEitherElims -> Just elims), eith]) ->
      return $ Eithers elims eith
    (isGlobalDef "Prelude.maybe" -> Just (),
     [tp, (asSpecM -> Just (params, _)), m, f, mayb]) ->
      do tp' <- case asApplyAll tp of
                  -- Always unfold: is_bvult, is_bvule
                  (tpf@(asGlobalDef -> Just ident), args)
                    | ident `elem` ["Prelude.is_bvult", "Prelude.is_bvule"]
                    , Just (_, Just body) <- asConstant tpf ->
                      mrApplyAll body args
                  _ -> return tp
         return $ MaybeElim (Type tp') (CompTerm m) (CompFunTerm params f) mayb
    (isGlobalDef "Prelude.orS" -> Just (), [_, _, _, m1, m2]) ->
      return $ OrS (CompTerm m1) (CompTerm m2)
    (isGlobalDef "Prelude.assertBoolS" -> Just (), [ev, stack, cond]) ->
      do unit_tp <- mrUnitType
         return $ AssertBoolBind cond (CompFunReturn
                                       (SpecMParams ev stack) unit_tp)
    (isGlobalDef "Prelude.assumeBoolS" -> Just (), [ev, stack, cond]) ->
      do unit_tp <- mrUnitType
         return $ AssumeBoolBind cond (CompFunReturn
                                       (SpecMParams ev stack) unit_tp)
    (isGlobalDef "Prelude.existsS" -> Just (), [ev, stack, tp]) ->
      do unit_tp <- mrUnitType
         return $ ExistsBind (Type tp) (CompFunReturn
                                        (SpecMParams ev stack) unit_tp)
    (isGlobalDef "Prelude.forallS" -> Just (), [ev, stack, tp]) ->
      do unit_tp <- mrUnitType
         return $ ForallBind (Type tp) (CompFunReturn
                                        (SpecMParams ev stack) unit_tp)
    (isGlobalDef "Prelude.multiFixS" -> Just (),
     [ev, stack, frame, defs, (asMkFrameCall -> Just (_, i, args))]) ->
      do
        -- Bind fresh function vars for the new recursive functions
        fun_vars <- mrFreshCallVars ev stack frame defs
        -- Return the @i@th variable to args as a normalized computation, noting
        -- that it must be applied to all of the uvars as well as the args
        let var = CallSName (fun_vars !! (fromIntegral i))
        all_args <- (++ args) <$> getAllUVarTerms
        FunBind var all_args Unlifted <$> mkCompFunReturn <$>
          mrFunOutType var all_args

    (isGlobalDef "Prelude.multiArgFixS" -> Just (), _ev:_stack:_lrt:body:args) ->
      do
        -- Bind a fresh function var for the new recursive function
        body_tp <- mrTypeOf body
        fun_tp <- case asPi body_tp of
          Just (_, tp_in, _) -> return tp_in
          Nothing -> throwMRFailure (MalformedDefs body)
        fun_var <- mrFreshVar "F" fun_tp
        fun_tm <- mrVarTerm fun_var

        -- Set the new function var to have body applied to it
        body_app <- mrApply body fun_tm >>= lambdaUVarsM
        mrSetVarInfo fun_var (CallVarInfo body_app)

        -- Return the function variable applied to args as a normalized
        -- computation, noting that it must be applied to all of the uvars as
        -- well as the args
        let var = CallSName fun_var
        all_args <- (++ args) <$> getAllUVarTerms
        FunBind var all_args Unlifted <$> mkCompFunReturn <$>
          mrFunOutType var all_args

    -- Convert `vecMapM (bvToNat ...)` into `bvVecMapInvarM`, with the
    -- invariant being the current set of assumptions
    (asGlobalDef -> Just "CryptolM.vecMapM", [_a, _b, (asBvToNat -> Just (_w, _n)),
                                              _f, _xs]) ->
      error "FIXME HERE NOW: need SpecM version of vecMapM"
      {-
      do invar <- mrAssumptions
         liftSC2 scGlobalApply "CryptolM.bvVecMapInvarM"
                               [a, b, w, n, f, xs, invar] >>= normCompTerm
      -}

    -- Convert `atM (bvToNat ...) ... (bvToNat ...)` into the unfolding of
    -- `bvVecAtM`
    (asGlobalDef -> Just "CryptolM.atM", [ev, stack,
                                          (asBvToNat -> Just (w, n)),
                                          a, xs, i_nat]) ->
      do body <- mrGlobalDefBody "CryptolM.bvVecAtM"
         liftSC1 scWhnf i_nat >>= mrBvNatInRange w >>= \case
           Just i -> mrApplyAll body [ev, stack, w, n, a, xs, i]
                       >>= normCompTerm
           _ -> throwMRFailure (MalformedComp t)

    -- Convert `atM n ... xs (bvToNat ...)` for a constant `n` into the
    -- unfolding of `bvVecAtM` after converting `n` to a bitvector constant
    -- and applying `genBVVecFromVec` to `xs`
    (asGlobalDef -> Just "CryptolM.atM", [ev, stack,
                                          n_tm@(asNat -> Just n),
                                          a@(asBoolType -> Nothing), xs,
                                          (asBvToNat ->
                                             Just (w_tm@(asNat -> Just w),
                                                   i))]) ->
      do body <- mrGlobalDefBody "CryptolM.bvVecAtM"
         if n < 1 `shiftL` fromIntegral w then do
           n' <- liftSC2 scBvLit w (toInteger n)
           xs' <- mrGenBVVecFromVec n_tm a xs "normComp (atM)" w_tm n'
           mrApplyAll body [ev, stack, w_tm, n', a, xs', i] >>= normCompTerm
         else throwMRFailure (MalformedComp t)

    -- Convert `updateM (bvToNat ...) ... (bvToNat ...)` into the unfolding of
    -- `bvVecUpdateM`
    (asGlobalDef -> Just "CryptolM.updateM", [ev, stack,
                                              (asBvToNat -> Just (w, n)),
                                              a, xs, i_nat, x]) ->
      do body <- mrGlobalDefBody "CryptolM.bvVecUpdateM"
         liftSC1 scWhnf i_nat >>= mrBvNatInRange w >>= \case
           Just i -> mrApplyAll body [ev, stack, w, n, a, xs, i, x]
                       >>= normCompTerm
           _ -> throwMRFailure (MalformedComp t)

    -- Convert `updateM n ... xs (bvToNat ...)` for a constant `n` into the
    -- unfolding of `bvVecUpdateM` after converting `n` to a bitvector constant
    -- and applying `genBVVecFromVec` to `xs`
    (asGlobalDef -> Just "CryptolM.updateM", [ev, stack,
                                              n_tm@(asNat -> Just n),
                                              a@(asBoolType -> Nothing), xs,
                                              (asBvToNat ->
                                                 Just (w_tm@(asNat -> Just w),
                                                       i)), x]) ->
      do body <- mrGlobalDefBody "CryptolM.fromBVVecUpdateM"
         if n < 1 `shiftL` fromIntegral w then do
           n' <- liftSC2 scBvLit w (toInteger n)
           xs' <- mrGenBVVecFromVec n_tm a xs "normComp (updateM)" w_tm n'
           err_tm <- mrErrorTerm a "normComp (updateM)"
           mrApplyAll body [ev, stack, w_tm, n', a, xs', i, x, err_tm, n_tm]
             >>= normCompTerm
         else throwMRFailure (MalformedComp t)

    -- Always unfold: sawLet, invariantHint, assumingS, assertingS,
    --                multiArgFixS, lrtLambda, Num_rec
    (f@(asGlobalDef -> Just ident), args)
      | ident `elem` ["Prelude.sawLet", "Prelude.invariantHint",
                      "Prelude.assumingS", "Prelude.assertingS",
                      "Prelude.multiArgFixS", "Prelude.lrtLambda",
                      "Cryptol.Num_rec"]
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
         FunBind fun_name args Unlifted <$> mkCompFunReturn <$>
           mrFunOutType fun_name args

    ((asGlobalFunName -> Just f), args) ->
      FunBind f args Unlifted <$> mkCompFunReturn <$> mrFunOutType f args

    _ -> throwMRFailure (MalformedComp t)


-- | Bind a computation in whnf with a function, and normalize
normBind :: NormComp -> CompFun -> MRM t NormComp
normBind (RetS t) k = applyNormCompFun k t
normBind (ErrorS msg) _ = return (ErrorS msg)
normBind (Ite cond comp1 comp2) k =
  return $ Ite cond (CompBind comp1 k) (CompBind comp2 k)
normBind (Eithers elims t) k =
  return $ Eithers (map (\(tp,f) -> (tp, compFunComp f k)) elims) t
normBind (MaybeElim tp m f t) k =
  return $ MaybeElim tp (CompBind m k) (compFunComp f k) t
normBind (OrS comp1 comp2) k =
  return $ OrS (CompBind comp1 k) (CompBind comp2 k)
normBind (AssertBoolBind cond f) k =
  return $ AssertBoolBind cond (compFunComp f k)
normBind (AssumeBoolBind cond f) k =
  return $ AssumeBoolBind cond (compFunComp f k)
normBind (ExistsBind tp f) k = return $ ExistsBind tp (compFunComp f k)
normBind (ForallBind tp f) k = return $ ForallBind tp (compFunComp f k)
normBind (FunBind f args isLifted k1) k2
  -- Turn `bvVecMapInvarM ... >>= k` into `bvVecMapInvarBindM ... k`
  {-
  | GlobalName (globalDefString -> "CryptolM.bvVecMapInvarM") [] <- f
  , (a:b:args_rest) <- args =
    do f' <- mrGlobalDef "CryptolM.bvVecMapInvarBindM"
       cont <- compFunToTerm (compFunComp k1 k2)
       c <- compFunReturnType k2
       return $ FunBind f' ((a:b:c:args_rest) ++ [cont])
                           (CompFunReturn (Type c))
  -- Turn `bvVecMapInvarBindM ... k1 >>= k2` into
  -- `bvVecMapInvarBindM ... (composeM ... k1 k2)`
  | GlobalName (globalDefString -> "CryptolM.bvVecMapInvarBindM") [] <- f
  , (args_pre, [cont]) <- splitAt 8 args =
    do cont' <- compFunToTerm (compFunComp (compFunComp (CompFunTerm cont) k1) k2)
       c <- compFunReturnType k2
       return $ FunBind f (args_pre ++ [cont']) (CompFunReturn (Type c))
  | otherwise -} = return $ FunBind f args isLifted (compFunComp k1 k2)

-- | Bind a computation in whnf with a function, normalize, and then call
-- 'liftStackNormComp' if the first argument is 'Lifted'. If the first argument
-- is 'Unlifted', this function is the same as 'normBind'.
normBindLiftStack :: IsLifted -> NormComp -> CompFun -> MRM t NormComp
normBindLiftStack Unlifted t f = normBind t f
normBindLiftStack Lifted t f =
  liftStackNormComp (compFunSpecMParams f) t >>= \t' -> normBind t' f

-- | Bind a 'Term' for a computation with with a function, normalize, and then
-- call 'liftStackNormComp' if the first argument is 'Lifted'. See:
-- 'normBindLiftStack'.
normBindTermLiftStack :: IsLifted -> Term -> CompFun -> MRM t NormComp
normBindTermLiftStack isLifted t f =
  normCompTerm t >>= \m -> normBindLiftStack isLifted m f


-- | Apply @liftStackS@ to a computation in whnf, and normalize
liftStackNormComp :: SpecMParams Term -> NormComp -> MRM t NormComp
liftStackNormComp _ (RetS t) = return (RetS t)
liftStackNormComp _ (ErrorS msg) = return (ErrorS msg)
liftStackNormComp params (Ite cond comp1 comp2) =
  Ite cond <$> liftStackComp params comp1 <*> liftStackComp params comp2
liftStackNormComp params (Eithers elims t) =
  Eithers <$> mapM (\(tp,f) -> (tp,) <$> liftStackCompFun params f) elims
          <*> return t
liftStackNormComp params (MaybeElim tp m f t) =
  MaybeElim tp <$> liftStackComp params m
               <*> liftStackCompFun params f <*> return t
liftStackNormComp params (OrS comp1 comp2) =
  OrS <$> liftStackComp params comp1 <*> liftStackComp params comp2
liftStackNormComp params (AssertBoolBind cond f) =
  AssertBoolBind cond <$> liftStackCompFun params f
liftStackNormComp params (AssumeBoolBind cond f) =
  AssumeBoolBind cond <$> liftStackCompFun params f
liftStackNormComp params (ExistsBind tp f) =
  ExistsBind tp <$> liftStackCompFun params f
liftStackNormComp params (ForallBind tp f) =
  ForallBind tp <$> liftStackCompFun params f
liftStackNormComp params (FunBind f args _ k) =
  FunBind f args Lifted <$> liftStackCompFun params k

-- | Apply @liftStackS@ to a computation
liftStackComp :: SpecMParams Term -> Comp -> MRM t Comp
liftStackComp (SpecMParams ev stk) (CompTerm t) = mrTypeOf t >>= \case
  (asSpecM -> Just (_, tp)) ->
    CompTerm <$> liftSC2 scGlobalApply "Prelude.liftStackS" [ev, stk, tp, t]
  _ -> error "liftStackComp: type not of the form: SpecM a"
liftStackComp _ (CompReturn t) = return $ CompReturn t
liftStackComp params (CompBind c f) =
  CompBind <$> liftStackComp params c <*> liftStackCompFun params f

-- | Apply @liftStackS@ to the bodies of a composition of functions
liftStackCompFun :: SpecMParams Term -> CompFun -> MRM t CompFun
liftStackCompFun params@(SpecMParams ev stk) (CompFunTerm _ f) = mrTypeOf f >>= \case
  (asPi -> Just (_, _, asSpecM -> Just (_, tp))) ->
    let nm = maybe "ret_val" id (asLambdaName f) in
    CompFunTerm params <$>
      mrLambdaLift1 (nm, tp) (ev, stk, tp, f) (\arg (ev', stk', tp', f') ->
        do app <- mrApplyAll f' [arg]
           liftSC2 scGlobalApply "Prelude.liftStackS" [ev', stk', tp', app])
  _ -> error "liftStackCompFun: type not of the form: a -> SpecM b"
liftStackCompFun params (CompFunReturn _ tp) = return $ CompFunReturn params tp
liftStackCompFun params (CompFunComp f g) =
  CompFunComp <$> liftStackCompFun params f <*> liftStackCompFun params g


{-
-- | Get the return type of a 'CompFun'
compFunReturnType :: CompFun -> MRM t Term
compFunReturnType (CompFunTerm _ t) = mrTypeOf t
compFunReturnType (CompFunComp _ g) = compFunReturnType g
compFunReturnType (CompFunReturn _ _) = error "FIXME"
-}

-- | Apply a computation function to a term argument to get a computation
applyCompFun :: CompFun -> Term -> MRM t Comp
applyCompFun (CompFunComp f g) t =
  -- (f >=> g) t == f t >>= g
  do comp <- applyCompFun f t
     return $ CompBind comp g
applyCompFun (CompFunReturn _ _) t =
  return $ CompReturn t
applyCompFun (CompFunTerm _ f) t = CompTerm <$> mrApplyAll f [t]

-- | Convert a 'CompFun' into a 'Term'
compFunToTerm :: CompFun -> MRM t Term
compFunToTerm (CompFunTerm _ t) = return t
compFunToTerm (CompFunComp f g) =
  do f' <- compFunToTerm f
     g' <- compFunToTerm g
     f_tp <- mrTypeOf f'
     g_tp <- mrTypeOf g'
     case (f_tp, g_tp) of
       (asPi -> Just (_, a, asSpecM -> Just (params, b)),
        asPi -> Just (_, _, asSpecM -> Just (_, c))) ->
         -- we explicitly unfold @Prelude.composeM@ here so @mrApplyAll@ will
         -- beta-reduce
         let nm = maybe "ret_val" id (compFunVarName f) in
         mrLambdaLift1 (nm, a) (b, c, f', g') $ \arg (b', c', f'', g'') ->
           do app <- mrApplyAll f'' [arg]
              liftSC2 scGlobalApply "Prelude.bindS" (specMParamsArgs params ++
                                                     [b', c', app, g''])
       _ -> error "compFunToTerm: type(s) not of the form: a -> SpecM b"
compFunToTerm (CompFunReturn params (Type a)) =
  mrLambdaLift1 ("ret_val", a) a $ \ret_val a' ->
    liftSC2 scGlobalApply "Prelude.retS" (specMParamsArgs params ++ [a', ret_val])

{-
-- | Convert a 'Comp' into a 'Term'
compToTerm :: Comp -> MRM t Term
compToTerm (CompTerm t) = return t
compToTerm (CompReturn t) =
   do tp <- mrTypeOf t
      liftSC2 scGlobalApply "Prelude.returnM" [tp, t]
compToTerm (CompBind m (CompFunReturn _)) = compToTerm m
compToTerm (CompBind m f) =
  do m' <- compToTerm m
     f' <- compFunToTerm f
     mrTypeOf f' >>= \case
       (asPi -> Just (_, a, asSpecM -> Just b)) ->
         liftSC2 scGlobalApply "Prelude.bindM" [a, b, m', f']
       _ -> error "compToTerm: type not of the form: a -> SpecM b"
-}

-- | Apply a 'CompFun' to a term and normalize the resulting computation
applyNormCompFun :: CompFun -> Term -> MRM t NormComp
applyNormCompFun f arg = applyCompFun f arg >>= normComp


-- | Convert a 'FunAssumpRHS' to a 'NormComp'
mrFunAssumpRHSAsNormComp :: FunAssumpRHS -> MRM t NormComp
mrFunAssumpRHSAsNormComp (OpaqueFunAssump f args) =
  FunBind f args Unlifted <$> mkCompFunReturn <$> mrFunOutType f args
mrFunAssumpRHSAsNormComp (RewriteFunAssump rhs) = normCompTerm rhs


-- | Match a term as a static list of eliminators for an Eithers type
matchEitherElims :: Term -> Maybe [EitherElim]
matchEitherElims (asCtor ->
                  Just (primName -> "Prelude.FunsTo_Nil", [_])) = Just []
matchEitherElims (asCtor -> Just (primName -> "Prelude.FunsTo_Cons",
                                  [asSpecM -> Just (params, _), tp, f, rest])) =
  ((Type tp, CompFunTerm params f):) <$>
  matchEitherElims rest
matchEitherElims _ = Nothing

-- | Construct the type @Eithers tps@ eliminated by a list of 'EitherElim's
elimsEithersType :: [EitherElim] -> MRM t Type
elimsEithersType elims =
  Type <$>
  (do f <- mrGlobalTerm "Prelude.Eithers"
      tps <-
        foldr
        (\(Type tp,_) restM ->
          restM >>= \rest -> mrCtorApp "Prelude.LS_Cons" [tp,rest])
        (mrCtorApp "Prelude.LS_Nil" [])
        elims
      mrApply f tps)


{- FIXME: do these go away?
-- | Lookup the definition of a function or throw a 'CannotLookupFunDef' if this is
-- not allowed, either because it is a global function we are treating as opaque
-- or because it is a locally-bound function variable
mrLookupFunDef :: FunName -> MRM t Term
mrLookupFunDef f@(GlobalName _) = throwMRFailure (CannotLookupFunDef f)
mrLookupFunDef f@(LocalName var) =
  mrVarInfo var >>= \case
  Just (FunVarInfo body) -> return body
  Just _ -> throwMRFailure (CannotLookupFunDef f)
  Nothing -> error "mrLookupFunDef: unknown variable!"

-- | Unfold a call to function @f@ in term @f args >>= g@
mrUnfoldFunBind :: FunName -> [Term] -> Mark -> CompFun -> MRM t Comp
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
proveCoIndHypInvariant :: CoIndHyp -> MRM t ()
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
mrRefinesCoInd :: FunName -> [Term] -> FunName -> [Term] -> MRM t ()
mrRefinesCoInd f1 args1 f2 args2 =
  do ctx <- mrUVars
     preF1 <- mrGetInvariant f1
     preF2 <- mrGetInvariant f2
     let hyp = CoIndHyp ctx f1 f2 args1 args2 preF1 preF2
     proveCoIndHypInvariant hyp
     proveCoIndHyp hyp

-- | Prove the refinement represented by a 'CoIndHyp' coinductively. This is the
-- main loop implementing 'mrRefinesCoInd'. See that function for documentation.
proveCoIndHyp :: CoIndHyp -> MRM t ()
proveCoIndHyp hyp = withFailureCtx (FailCtxCoIndHyp hyp) $
  do let f1 = coIndHypLHSFun hyp
         f2 = coIndHypRHSFun hyp
         args1 = coIndHypLHS hyp
         args2 = coIndHypRHS hyp
     mrDebugPPInCtxM 1 (prettyWithCtx emptyMRVarCtx $
                        prettyPrefix "proveCoIndHyp" hyp)
     lhs <- fromMaybe (error "proveCoIndHyp") <$> mrFunBody f1 args1
     rhs <- fromMaybe (error "proveCoIndHyp") <$> mrFunBody f2 args2
     (invar1, invar2) <- applyCoIndHypInvariants hyp
     invar <- liftSC2 scAnd invar1 invar2
     (withOnlyUVars (coIndHypCtx hyp) $ withOnlyAssumption invar $
      withCoIndHyp hyp $ mrRefines lhs rhs) `catchError` \case
       MRExnWiden nm1' nm2' new_vars
         | f1 == nm1' && f2 == nm2' ->
           -- NOTE: the state automatically gets reset here because we defined
           -- MRM t with ExceptT at a lower level than StateT
           do mrDebugPPPrefixSep 1 "Widening recursive assumption for" nm1' "|=" nm2'
              hyp' <- generalizeCoIndHyp hyp new_vars
              proveCoIndHyp hyp'
       e -> throwError e

-- | Test that a coinductive hypothesis for the given function names matches the
-- given arguments, otherwise throw an exception saying that widening is needed
matchCoIndHyp :: CoIndHyp -> [Term] -> [Term] -> MRM t ()
matchCoIndHyp hyp args1 args2 =
  do mrDebugPPPrefix 1 "matchCoIndHyp" hyp
     (args1', args2') <- instantiateCoIndHyp hyp
     mrDebugPPPrefixSep 3 "matchCoIndHyp args" args1 "," args2
     mrDebugPPPrefixSep 3 "matchCoIndHyp args'" args1' "," args2'
     eqs1 <- zipWithM mrProveEq args1' args1
     eqs2 <- zipWithM mrProveEq args2' args2
     if and (eqs1 ++ eqs2) then return () else
       throwError $ MRExnWiden (coIndHypLHSFun hyp) (coIndHypRHSFun hyp)
       (map Left (findIndices not eqs1) ++ map Right (findIndices not eqs2))
     proveCoIndHypInvariant hyp

-- | Generalize some of the arguments of a coinductive hypothesis
generalizeCoIndHyp :: CoIndHyp -> [Either Int Int] -> MRM t CoIndHyp
generalizeCoIndHyp hyp [] = return hyp
generalizeCoIndHyp hyp all_specs@(arg_spec_0:arg_specs) =
  withOnlyUVars (coIndHypCtx hyp) $ do
  withNoUVars $ mrDebugPPPrefixSep 2 "generalizeCoIndHyp with indices"
                                     all_specs "on" hyp
  -- Get the arg and type associated with arg_spec
  let arg_tm_0 = coIndHypArg hyp arg_spec_0
  arg_tp_0 <- mrTypeOf arg_tm_0
  -- Partition @arg_specs@ into a left list (@eq_specs@) and a right list
  -- (@uneq_specs@) where an @arg_spec_i@ is put in the left list if
  -- 'findInjConvs' returns 'Just' and @arg_tm_0@ and @arg_tm_i@ are related
  -- via 'mrProveRel' - i.e. if there exists a type @tp_i@ and 'InjConversion's
  -- @c1_i@ and @c2_i@ such that @c1_i@ is an injective conversion from
  -- 'tp_i' to 'arg_tp_0', @c2_i@ is an injective conversion from
  -- 'tp_i' to 'arg_tp_i', and @arg_tm_0@ and @arg_tm_i@ are convertible when
  -- the inverses of @c1_i@ and @c2_i@ are applied. In other words, @eq_specs@
  -- contains all the specs which are equal to @arg_spec_0@ up to some
  -- injective conversions.
  (eq_specs, uneq_specs) <- fmap partitionEithers $ forM arg_specs $ \arg_spec_i ->
    let arg_tm_i = coIndHypArg hyp arg_spec_i in
    mrTypeOf arg_tm_i >>= \arg_tp_i ->
    findInjConvs arg_tp_0 (Just arg_tm_0) arg_tp_i (Just arg_tm_i) >>= \case
      Just cvs -> mrProveRel True arg_tm_0 arg_tm_i >>= \case
        True -> return $ Left (arg_spec_i, cvs)
        _ -> return $ Right arg_spec_i
      _ -> return $ Right arg_spec_i
  -- What want to do is generalize all the arg_specs in @eq_specs@ into a
  -- single variable (with some appropriate conversions applied). So, what
  -- we need to do is find a @tp@ (and appropriate conversions) such that the
  -- following diagram holds for all @i@ and @j@ (using the names from the
  -- previous comment):
  --
  -- > arg_tp_i  arg_tp_0  arg_tp_j
  -- >      ^      ^  ^      ^
  -- >       \    /    \    /
  -- >        tp_i      tp_j
  -- >           ^      ^
  -- >            \    /
  -- >              tp
  --
  -- To do this, we simply need to call 'findInjConvs' iteratively as we fold
  -- through @eq_specs@, and compose the injective conversions appropriately.
  -- Each step of this iteration is @cbnConvs@, which can be pictured as:
  --
  -- >      arg_tp_0    arg_tp_i
  -- >      ^      ^       ^
  -- >  c_0 |  c1_i \     / c2_i
  -- >      |        \   /
  -- >      tp        tp_i
  -- >       ^        ^
  -- >     c1 \      / c2
  -- >         \    /
  -- >           tp'
  --
  -- where @c1@, @c2@, and @tp'@ come from 'findInjConvs' on @tp@ and @tp_i@,
  -- and the @tp@ and @c_0@ to use for the next (@i+1@th) iteration are @tp'@
  -- and @c_0 <> c1@.
  let cbnConvs :: (Term, InjConversion, [(a, InjConversion)]) ->
                  (a, (Term, InjConversion, InjConversion)) ->
                  MRM t (Term, InjConversion, [(a, InjConversion)])
      cbnConvs (tp, c_0, cs) (arg_spec_i, (tp_i, _, c2_i)) =
        findInjConvs tp Nothing tp_i Nothing >>= \case
          Just (tp', c1, c2) ->
            let cs' = fmap (\(spec_j, c_j) -> (spec_j, c_j <> c1)) cs in
            return $ (tp', c_0 <> c1, (arg_spec_i, c2_i <> c2) : cs')
          Nothing -> error "generalizeCoIndHyp: could not find mutual conversion"
  (tp, c_0, eq_specs_cs) <- foldlM cbnConvs (arg_tp_0, NoConv, []) eq_specs
  -- Finally we generalize: We add a new variable of type @tp@ and substitute
  -- it for all of the arguments in @hyp@ given by @eq_specs@, applying the
  -- appropriate conversions from @eq_specs_cs@
  (hyp', var) <- coIndHypWithVar hyp "z" (Type tp)
  hyp'' <- foldlM (\hyp_i (arg_spec_i, c_i) ->
                    coIndHypSetArg hyp_i arg_spec_i <$> mrApplyConv c_i var)
                  hyp' ((arg_spec_0, c_0) : eq_specs_cs)
  -- We finish by recursing on any remaining arg_specs
  generalizeCoIndHyp hyp'' uneq_specs


----------------------------------------------------------------------
-- * Mr Solver Himself (He Identifies as Male)
----------------------------------------------------------------------

-- | An object that can be converted to a normalized computation
class ToNormComp a where
  toNormComp :: a -> MRM t NormComp

instance ToNormComp NormComp where
  toNormComp = return
instance ToNormComp Comp where
  toNormComp = normComp
instance ToNormComp Term where
  toNormComp = normComp . CompTerm

-- | Prove that the left-hand computation refines the right-hand one. See the
-- rules described at the beginning of this module.
mrRefines :: (ToNormComp a, ToNormComp b) => a -> b -> MRM t ()
mrRefines t1 t2 =
  do m1 <- toNormComp t1
     m2 <- toNormComp t2
     mrDebugPPPrefixSep 1 "mrRefines" m1 "|=" m2
     -- ctx <- reverse . map (\(a,Type b) -> (a,b)) <$> mrUVars
     -- mrDebugPPPrefix 2 "in context:" $ ppCtx ctx
     withFailureCtx (FailCtxRefines m1 m2) $ mrRefines' m1 m2

-- | The main implementation of 'mrRefines'
mrRefines' :: NormComp -> NormComp -> MRM t ()

mrRefines' (RetS e1) (RetS e2) = mrAssertProveRel True e1 e2
mrRefines' (ErrorS _) (ErrorS _) = return ()
mrRefines' (RetS e) (ErrorS err) = throwMRFailure (ReturnNotError (Right err) e)
mrRefines' (ErrorS err) (RetS e) = throwMRFailure (ReturnNotError (Left  err) e)

-- maybe elimination on equality types
mrRefines' (MaybeElim (Type cond_tp@(asEq -> Just (tp,e1,e2))) m1 f1 _) m2 =
  do cond <- mrEq' tp e1 e2
     not_cond <- liftSC1 scNot cond
     cond_pf <- mrDummyProof cond_tp
     m1' <- applyNormCompFun f1 cond_pf
     cond_holds <- mrProvable cond
     not_cond_holds <- mrProvable not_cond
     case (cond_holds, not_cond_holds) of
       (True, _) -> mrRefines m1' m2
       (_, True) -> mrRefines m1 m2
       _ -> withAssumption cond (mrRefines m1' m2) >>
            withAssumption not_cond (mrRefines m1 m2)
mrRefines' m1 (MaybeElim (Type cond_tp@(asEq -> Just (tp,e1,e2))) m2 f2 _) =
  do cond <- mrEq' tp e1 e2
     not_cond <- liftSC1 scNot cond
     cond_pf <- mrDummyProof cond_tp
     m2' <- applyNormCompFun f2 cond_pf
     cond_holds <- mrProvable cond
     not_cond_holds <- mrProvable not_cond
     case (cond_holds, not_cond_holds) of
       (True, _) -> mrRefines m1 m2'
       (_, True) -> mrRefines m1 m2
       _ -> withAssumption cond (mrRefines m1 m2') >>
            withAssumption not_cond (mrRefines m1 m2)

-- maybe elimination on isFinite types
mrRefines' (MaybeElim (Type fin_tp@(asIsFinite -> Just n1)) m1 f1 _) m2 =
  do n1_norm <- mrNormOpenTerm n1
     maybe_assump <- mrGetDataTypeAssump n1_norm
     fin_pf <- mrDummyProof fin_tp
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
mrRefines' m1 (MaybeElim (Type fin_tp@(asIsFinite -> Just n2)) m2 f2 _) =
  do n2_norm <- mrNormOpenTerm n2
     maybe_assump <- mrGetDataTypeAssump n2_norm
     fin_pf <- mrDummyProof fin_tp
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

mrRefines' (Eithers [] _) _ = return ()
mrRefines' _ (Eithers [] _) = return ()
mrRefines' (Eithers [(_,f)] t1) m2 =
  applyNormCompFun f t1 >>= \m1 ->
  mrRefines m1 m2
mrRefines' m1 (Eithers [(_,f)] t2) =
  applyNormCompFun f t2 >>= \m2 ->
  mrRefines m1 m2

mrRefines' (Eithers ((tp,f1):elims) t1) m2 =
  mrNormOpenTerm t1 >>= \t1' ->
  mrGetDataTypeAssump t1' >>= \mb_assump ->
  case (mb_assump, asEither t1') of
    (_, Just (Left  x)) -> applyNormCompFun f1 x >>= flip mrRefines m2
    (_, Just (Right x)) -> mrRefines (Eithers elims x) m2
    (Just (IsLeft  x), _) -> applyNormCompFun f1 x >>= flip mrRefines m2
    (Just (IsRight x), _) -> mrRefines (Eithers elims x) m2
    _ -> let lnm = maybe "x_left" id (compFunVarName f1)
             rnm = "x_right" in
         elimsEithersType elims >>= \elims_tp ->
         withUVarLift lnm tp (f1, t1', m2) (\x (f1', t1'', m2') ->
           applyNormCompFun f1' x >>= withDataTypeAssump t1'' (IsLeft x)
                                      . flip mrRefines m2') >>
         withUVarLift rnm elims_tp (elims, t1', m2)
           (\x (elims', t1'', m2') ->
             withDataTypeAssump t1'' (IsRight x) (mrRefines (Eithers elims' x) m2'))

mrRefines' m1 (Eithers ((tp,f2):elims) t2) =
  mrNormOpenTerm t2 >>= \t2' ->
  mrGetDataTypeAssump t2' >>= \mb_assump ->
  case (mb_assump, asEither t2') of
    (_, Just (Left  x)) -> applyNormCompFun f2 x >>= mrRefines m1
    (_, Just (Right x)) -> mrRefines m1 (Eithers elims x)
    (Just (IsLeft  x), _) -> applyNormCompFun f2 x >>= mrRefines m1
    (Just (IsRight x), _) -> mrRefines m1 (Eithers elims x)
    _ -> let lnm = maybe "x_left" id (compFunVarName f2)
             rnm = "x_right" in
         elimsEithersType elims >>= \elims_tp ->
         withUVarLift lnm tp (f2, t2', m1) (\x (f2', t2'', m1') ->
           applyNormCompFun f2' x >>= withDataTypeAssump t2'' (IsLeft x)
                                      . mrRefines m1') >>
         withUVarLift rnm elims_tp (elims, t2', m1)
           (\x (elims', t2'', m1') ->
             withDataTypeAssump t2'' (IsRight x) (mrRefines m1' (Eithers elims' x)))

mrRefines' m1 (AssumeBoolBind cond2 k2) =
  do m2 <- liftSC0 scUnitValue >>= applyCompFun k2
     not_cond2 <- liftSC1 scNot cond2
     cond2_true_pv <- mrProvable cond2
     cond2_false_pv <- mrProvable not_cond2
     case (cond2_true_pv, cond2_false_pv) of
       (True, _) -> mrRefines m1 m2
       (_, True) -> return ()
       _ -> withAssumption cond2 $ mrRefines m1 m2
mrRefines' (AssertBoolBind cond1 k1) m2 =
  do m1 <- liftSC0 scUnitValue >>= applyCompFun k1
     cond1_str <- mrShowInCtx cond1
     let err_txt = "mrRefines failed assertion: " <> T.pack cond1_str
     m1' <- ErrorS <$> liftSC1 scString err_txt
     not_cond1 <- liftSC1 scNot cond1
     cond1_true_pv <- mrProvable cond1
     cond1_false_pv <- mrProvable not_cond1
     case (cond1_true_pv, cond1_false_pv) of
       (True, _) -> mrRefines m1 m2
       (_, True) -> mrRefines m1' m2
       _ -> withAssumption cond1 $ mrRefines m1 m2

mrRefines' m1 (ForallBind tp f2) =
  let nm = maybe "x" id (compFunVarName f2) in
  withUVarLift nm tp (m1,f2) $ \x (m1',f2') ->
  applyNormCompFun f2' x >>= \m2' ->
  mrRefines m1' m2'
mrRefines' (ExistsBind tp f1) m2 =
  let nm = maybe "x" id (compFunVarName f1) in
  withUVarLift nm tp (f1,m2) $ \x (f1',m2') ->
  applyNormCompFun f1' x >>= \m1' ->
  mrRefines m1' m2'

mrRefines' m1 (OrS m2 m2') =
  mrOr (mrRefines m1 m2) (mrRefines m1 m2')
mrRefines' (OrS m1 m1') m2 =
  mrRefines m1 m2 >> mrRefines m1' m2

-- FIXME: the following cases don't work unless we either allow evars to be set
-- to NormComps or we can turn NormComps back into terms
mrRefines' m1@(FunBind (EVarFunName _) _ _ _) m2 =
  throwMRFailure (CompsDoNotRefine m1 m2)
mrRefines' m1 m2@(FunBind (EVarFunName _) _ _ _) =
  throwMRFailure (CompsDoNotRefine m1 m2)
{-
mrRefines' (FunBind (EVarFunName evar) args (CompFunReturn _)) m2 =
  mrGetEVar evar >>= \case
  Just f ->
    (mrApplyAll f args >>= normCompTerm) >>= \m1' ->
    mrRefines m1' m2
  Nothing -> mrTrySetAppliedEVar evar args m2
-}

mrRefines' (FunBind f args1 _ k1) (FunBind f' args2 _ k2)
  | f == f' && length args1 == length args2 =
    zipWithM_ mrAssertProveEq args1 args2 >>
    mrFunOutType f args1 >>= \(_, tp) ->
    mrRefinesFun tp k1 tp k2

mrRefines' m1@(FunBind f1 args1 isLifted1 k1)
           m2@(FunBind f2 args2 isLifted2 k2) =
  mrFunOutType f1 args1 >>= \(_, tp1) ->
  mrFunOutType f2 args2 >>= \(_, tp2) ->
  findInjConvs tp1 Nothing tp2 Nothing >>= \mb_convs ->
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
    mrRefinesFun tp1 k1 tp2 k2

  -- If we have an opaque FunAssump that f1 args1' refines f2 args2', then
  -- prove that args1 = args1', args2 = args2', and then that k1 refines k2
  (_, Just fa@(FunAssump ctx _ args1' (OpaqueFunAssump f2' args2') _)) | f2 == f2' ->
    do mrDebugPPInCtxM 2 $ prettyWithCtx ctx $
         prettyAppList [return "mrRefines using opaque FunAssump:",
                        prettyInCtx ctx, return ".",
                        prettyTermApp (funNameTerm f1) args1',
                        return "|=",
                        prettyTermApp (funNameTerm f2) args2']
       evars <- mrFreshEVars ctx
       (args1'', args2'') <- substTermLike 0 evars (args1', args2')
       zipWithM_ mrAssertProveEq args1'' args1
       zipWithM_ mrAssertProveEq args2'' args2
       recordUsedFunAssump fa >> mrRefinesFun tp1 k1 tp2 k2

  -- -- If we have an opaque FunAssump that f1 refines some f /= f2, and f2
  -- -- unfolds and is not recursive in itself, unfold f2 and recurse
  -- (_, Just fa@(FunAssump _ _ _ (OpaqueFunAssump _ _) _))
  --   | Just (f2_body, False) <- maybe_f2_body ->
  --   normBindTermLiftStack isLifted2 f2_body k2 >>= \m2' ->
  --   recordUsedFunAssump fa >> mrRefines m1 m2'

  -- If we have a rewrite FunAssump, or we have an opaque FunAssump that
  -- f1 args1' refines some f args where f /= f2 and f2 does not match the
  -- case above, treat either case like we have a rewrite FunAssump and prove
  -- that args1 = args1' and then that f args refines m2
  (_, Just fa@(FunAssump ctx _ args1' rhs _)) ->
    do let fassump_tp_str = case fassumpRHS fa of
                              OpaqueFunAssump _ _ -> "opaque"
                              RewriteFunAssump _ -> "rewrite"
       mrDebugPPInCtxM 2 $ prettyWithCtx ctx $
         prettyAppList [return ("mrRefines rewriting by " <> fassump_tp_str
                                                          <> " FunAssump:"),
                        prettyInCtx ctx, return ".",
                        prettyTermApp (funNameTerm f1) args1',
                        return "|=",
                        case rhs of
                          OpaqueFunAssump f2' args2' ->
                            prettyTermApp (funNameTerm f2') args2'
                          RewriteFunAssump rhs_tm ->
                            prettyInCtx rhs_tm]
       rhs' <- mrFunAssumpRHSAsNormComp rhs
       evars <- mrFreshEVars ctx
       (args1'', rhs'') <- substTermLike 0 evars (args1', rhs')
       zipWithM_ mrAssertProveEq args1'' args1
       -- It's important to instantiate the evars here so that rhs is well-typed
       -- when bound with k1
       rhs''' <- mapTermLike mrSubstEVars rhs''
       m1' <- normBindLiftStack isLifted1 rhs''' k1
       recordUsedFunAssump fa >> mrRefines m1' m2

  -- If f1 unfolds and is not recursive in itself, unfold it and recurse
  _ | Just (f1_body, False) <- maybe_f1_body ->
      normBindTermLiftStack isLifted1 f1_body k1 >>= \m1' -> mrRefines m1' m2

  -- If f2 unfolds and is not recursive in itself, unfold it and recurse
  _ | Just (f2_body, False) <- maybe_f2_body ->
      normBindTermLiftStack isLifted2 f2_body k2 >>= \m2' -> mrRefines m1 m2'

  -- If we don't have a co-inducitve hypothesis for f1 and f2, don't have an
  -- assumption that f1 refines some specification, both are either lifted or
  -- unlifted, and both f1 and f2 are recursive and have return types which are
  -- heterogeneously related, then try to coinductively prove that
  -- f1 args1 |= f2 args2 under the assumption that f1 args1 |= f2 args2, and
  -- then try to prove that k1 |= k2
  _ | Just _ <- maybe_f1_body
    , Just _ <- maybe_f2_body ->
      case mb_convs of
        Just _ -> mrRefinesCoInd f1 args1 f2 args2 >> mrRefinesFun tp1 k1 tp2 k2
        _ -> throwMRFailure (BindTypesNotEq (Type tp1) (Type tp2))

  -- If we cannot line up f1 and f2, then making progress here would require us
  -- to somehow split either m1 or m2 into some bind m' >>= k' such that m' is
  -- related to the function call on the other side and k' is related to the
  -- continuation on the other side, but we don't know how to do that, so give
  -- up
  _ -> throwMRFailure (FunNamesDoNotRefine f1 args1 f2 args2)

mrRefines' m1@(FunBind f1 args1 isLifted1 k1) m2 =
  mrGetFunAssump f1 >>= \case

  -- If we have an assumption that f1 args' refines some rhs, then prove that
  -- args1 = args' and then that rhs refines m2
  Just fa@(FunAssump ctx _ args1' rhs _) ->
    do rhs' <- mrFunAssumpRHSAsNormComp rhs
       evars <- mrFreshEVars ctx
       (args1'', rhs'') <- substTermLike 0 evars (args1', rhs')
       zipWithM_ mrAssertProveEq args1'' args1
       -- It's important to instantiate the evars here so that rhs is well-typed
       -- when bound with k1
       rhs''' <- mapTermLike mrSubstEVars rhs''
       m1' <- normBindLiftStack isLifted1 rhs''' k1
       recordUsedFunAssump fa >> mrRefines m1' m2

  -- Otherwise, see if we can unfold f1
  Nothing ->
    mrFunBodyRecInfo f1 args1 >>= \case

    -- If f1 unfolds and is not recursive in itself, unfold it and recurse
    Just (f1_body, False) ->
      normBindTermLiftStack isLifted1 f1_body k1 >>= \m1' -> mrRefines m1' m2

    -- Otherwise we would have to somehow split m2 into some computation of the
    -- form m2' >>= k2 where f1 args1 |= m2' and k1 |= k2, but we don't know how
    -- to do this splitting, so give up
    _ -> mrRefines'' m1 m2

mrRefines' m1 m2@(FunBind f2 args2 isLifted2 k2) =
  mrFunBodyRecInfo f2 args2 >>= \case

  -- If f2 unfolds and is not recursive in itself, unfold it and recurse
  Just (f2_body, False) ->
    normBindTermLiftStack isLifted2 f2_body k2 >>= \m2' -> mrRefines m1 m2'

  -- If f2 unfolds but is recursive, and k2 is the trivial continuation, meaning
  -- m2 is just f2 args2, use the law of coinduction to prove m1 |= f2 args2 by
  -- proving m1 |= f2_body under the assumption that m1 |= f2 args2
  {- FIXME: implement something like this
  Just (f2_body, True)
    | CompFunReturn _ <- k2 ->
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
mrRefines'' :: NormComp -> NormComp -> MRM t ()

mrRefines'' m1 (AssertBoolBind cond2 k2) =
  do m2 <- liftSC0 scUnitValue >>= applyCompFun k2
     cond2_pv <- mrProvable cond2
     if cond2_pv then mrRefines m1 m2
       else throwMRFailure (AssertionNotProvable cond2)
mrRefines'' (AssumeBoolBind cond1 k1) m2 =
  do m1 <- liftSC0 scUnitValue >>= applyCompFun k1
     cond1_pv <- mrProvable cond1
     if cond1_pv then mrRefines m1 m2
       else throwMRFailure (AssumptionNotProvable cond1)

mrRefines'' m1 (ExistsBind tp f2) =
  do let nm = maybe "x" id (compFunVarName f2)
     evar <- mrFreshEVar nm tp
     m2' <- applyNormCompFun f2 evar
     mrRefines m1 m2'
mrRefines'' (ForallBind tp f1) m2 =
  do let nm = maybe "x" id (compFunVarName f1)
     evar <- mrFreshEVar nm tp
     m1' <- applyNormCompFun f1 evar
     mrRefines m1' m2

-- If none of the above cases match, then fail
mrRefines'' m1 m2 = throwMRFailure (CompsDoNotRefine m1 m2)

-- | Prove that one function refines another for all inputs
mrRefinesFun :: Term -> CompFun -> Term -> CompFun -> MRM t ()
mrRefinesFun tp1 f1 tp2 f2 =
  do mrDebugPPPrefixSep 1 "mrRefinesFun on types:" tp1 "," tp2
     f1' <- compFunToTerm f1 >>= liftSC1 scWhnf
     f2' <- compFunToTerm f2 >>= liftSC1 scWhnf
     mrDebugPPPrefixSep 1 "mrRefinesFun" f1' "|=" f2'
     let nm1 = maybe "call_ret_val" id (compFunVarName f1)
         nm2 = maybe "call_ret_val" id (compFunVarName f2)
     f1'' <- mrLambdaLift1 (nm1, tp1) f1' $ flip mrApply
     f2'' <- mrLambdaLift1 (nm2, tp2) f2' $ flip mrApply
     piTp1 <- mrTypeOf f1''
     piTp2 <- mrTypeOf f2''
     mrRefinesFunH mrRefines [] piTp1 f1'' piTp2 f2''

-- | The main loop of 'mrRefinesFun' and 'askMRSolver': given a continuation,
-- two terms of function type, and two equal-length lists representing the
-- argument types of the two terms, add a uvar for each corresponding pair of
-- types (assuming the types are either equal or are heterogeneously related,
-- as in 'HetRelated'), apply the terms to these uvars (modulo possibly some
-- wrapper functions determined by how the types are heterogeneously related),
-- and call the continuation on the resulting terms. The second argument is
-- an accumulator of variables to introduce, innermost first.
mrRefinesFunH :: (Term -> Term -> MRM t a) -> [Term] ->
                 Term -> Term -> Term -> Term -> MRM t a

-- Ignore units on either side
mrRefinesFunH k vars (asPi -> Just (_, asTupleType -> Just [], _)) t1 piTp2 t2 =
  do u <- liftSC0 scUnitValue
     t1' <- mrApplyAll t1 [u]
     piTp1' <- mrTypeOf t1'
     mrRefinesFunH k vars piTp1' t1' piTp2 t2
mrRefinesFunH k vars piTp1 t1 (asPi -> Just (_, asTupleType -> Just [], _)) t2 =
  do u <- liftSC0 scUnitValue
     t2' <- mrApplyAll t2 [u]
     piTp2' <- mrTypeOf t2'
     mrRefinesFunH k vars piTp1 t1 piTp2' t2'

-- Introduce equalities on either side as assumptions
mrRefinesFunH k vars (asPi -> Just (nm1, tp1@(asEq -> Just (asBoolType -> Just (), b1, b2)), _)) t1 piTp2 t2 =
  liftSC2 scBoolEq b1 b2 >>= \eq ->
  withAssumption eq $
  let nm = maybe "_" id $ find ((/=) '_' . Text.head)
                        $ [nm1] ++ catMaybes [ asLambdaName t1 ] in
  withUVarLift nm (Type tp1) (vars,t1,piTp2,t2) $ \var (vars',t1',piTp2',t2') ->
  do t1'' <- mrApplyAll t1' [var]
     piTp1' <- mrTypeOf t1''
     mrRefinesFunH k (var : vars') piTp1' t1'' piTp2' t2'
mrRefinesFunH k vars piTp1 t1 (asPi -> Just (nm2, tp2@(asEq -> Just (asBoolType -> Just (), b1, b2)), _)) t2 =
  liftSC2 scBoolEq b1 b2 >>= \eq ->
  withAssumption eq $
  let nm = maybe "_" id $ find ((/=) '_' . Text.head)
                        $ [nm2] ++ catMaybes [ asLambdaName t2 ] in
  withUVarLift nm (Type tp2) (vars,piTp1,t1,t2) $ \var (vars',piTp1',t1',t2') ->
  do t2'' <- mrApplyAll t2' [var]
     piTp2' <- mrTypeOf t2''
     mrRefinesFunH k (var : vars') piTp1' t1' piTp2' t2''

-- We always curry pair values before introducing them (NOTE: we do this even
-- when the have the same types to ensure we never have to unify a projection
-- of an evar with a non-projected value, e.g. evar.1 == val)
mrRefinesFunH k vars (asPi -> Just (nm1, asPairType -> Just (tpL1, tpR1), _)) t1
                     (asPi -> Just (nm2, asPairType -> Just (tpL2, tpR2), _)) t2 =
  do t1'' <- mrLambdaLift2 (nm1, tpL1) (nm1, tpR1) t1 $ \prj1 prj2 t1' ->
               liftSC2 scPairValue prj1 prj2 >>= mrApply t1'
     t2'' <- mrLambdaLift2 (nm2, tpL2) (nm2, tpR2) t2 $ \prj1 prj2 t2' ->
               liftSC2 scPairValue prj1 prj2 >>= mrApply t2'
     piTp1' <- mrTypeOf t1''
     piTp2' <- mrTypeOf t2''
     mrRefinesFunH k vars piTp1' t1'' piTp2' t2''

mrRefinesFunH k vars (asPi -> Just (nm1, tp1, _)) t1
                     (asPi -> Just (nm2, tp2, _)) t2 =
  findInjConvs tp1 Nothing tp2 Nothing >>= \case
  -- If we can find injective conversions from from a type @tp@ to @tp1@ and
  -- @tp2@, introduce a variable of type @tp@, apply both conversions to it,
  -- and substitute the results on the left and right sides, respectively
  Just (tp, c1, c2) ->
    mrDebugPPPrefixSep 3 "mrRefinesFunH calling findInjConvs" tp1 "," tp2 >>
    mrDebugPPPrefix 3 "mrRefinesFunH got type" tp >>
    let nm = maybe "_" id $ find ((/=) '_' . Text.head)
                          $ [nm1, nm2] ++ catMaybes [ asLambdaName t1
                                                    , asLambdaName t2 ] in
    withUVarLift nm (Type tp) (vars,c1,c2,t1,t2) $ \var (vars',c1',c2',t1',t2') ->
    do tm1 <- mrApplyConv c1' var
       tm2 <- mrApplyConv c2' var
       t1'' <- mrApplyAll t1' [tm1]
       t2'' <- mrApplyAll t2' [tm2]
       piTp1' <- mrTypeOf t1'' >>= liftSC1 scWhnf
       piTp2' <- mrTypeOf t2'' >>= liftSC1 scWhnf
       mrRefinesFunH k (var : vars') piTp1' t1'' piTp2' t2''
  -- Otherwise, error
  Nothing -> throwMRFailure (TypesNotRel True (Type tp1) (Type tp2))

-- Error if we don't have the same number of arguments on both sides
-- FIXME: Add a specific error for this case
mrRefinesFunH _ _ (asPi -> Just (_,tp1,_)) _ (asPi -> Nothing) _ =
  liftSC0 scUnitType >>= \utp ->
  throwMRFailure (TypesNotEq (Type tp1) (Type utp))
mrRefinesFunH _ _ (asPi -> Nothing) _ (asPi -> Just (_,tp2,_)) _ =
  liftSC0 scUnitType >>= \utp ->
  throwMRFailure (TypesNotEq (Type utp) (Type tp2))

-- Error if either side's return type is not SpecM
mrRefinesFunH _ _ tp1@(asSpecM -> Nothing) _ _ _ =
  throwMRFailure (NotCompFunType tp1)
mrRefinesFunH _ _ _ _ tp2@(asSpecM -> Nothing) _ =
  throwMRFailure (NotCompFunType tp2)

mrRefinesFunH k _ _ t1 _ t2 = k t1 t2


----------------------------------------------------------------------
-- * External Entrypoints
----------------------------------------------------------------------

-- | The continuation passed to 'mrRefinesFunH' in 'askMRSolver' - normalizes
-- both resulting terms using 'normCompTerm' then calls the given monadic
-- function
askMRSolverH :: (NormComp -> NormComp -> MRM t a) -> Term -> Term -> MRM t a
askMRSolverH f t1 t2 =
  do mrUVars >>= mrDebugPPPrefix 1 "askMRSolverH uvars:"
     m1 <- normCompTerm t1
     m2 <- normCompTerm t2
     f m1 m2

-- | Test two monadic, recursive terms for refinement
askMRSolver ::
  SharedContext ->
  MREnv {- ^ The Mr Solver environment -} ->
  Maybe Integer {- ^ Timeout in milliseconds for each SMT call -} ->
  (Set VarIndex -> Sequent -> TopLevel (SolverStats, SolveResult))
    {- ^ The callback to use for making SMT queries -} ->
  Refnset t {- ^ Any additional refinements to be assumed by Mr Solver -} ->
  [(LocalName, Term)] {- ^ Any universally quantified variables in scope -} ->
  Term -> Term -> TopLevel (Either MRFailure (SolverStats, MREvidence t))
askMRSolver sc env timeout askSMT rs args t1 t2 =
  execMRM sc env timeout askSMT rs $
  withUVars (mrVarCtxFromOuterToInner args) $ \_ ->
    do tp1 <- liftIO $ scTypeOf sc t1 >>= scWhnf sc
       tp2 <- liftIO $ scTypeOf sc t2 >>= scWhnf sc
       mrDebugPPPrefixSep 1 "mr_solver" t1 "|=" t2
       mrRefinesFunH (askMRSolverH mrRefines) [] tp1 t1 tp2 t2

-- | The continuation passed to 'mrRefinesFunH' in 'refinementTerm' - returns
-- the 'Term' which is the refinement (@Prelude.refinesS@) of the given
-- 'Term's, after quantifying over all current 'mrUVars' with Pi types. Note
-- that this assumes both terms have the same event and stack types - if they
-- do not a saw-core typechecking error will be raised.
refinementTermH :: Term -> Term -> MRM t Term
refinementTermH t1 t2 =
  do (SpecMParams _ev1 _stack1, tp1) <- fromJust . asSpecM <$> mrTypeOf t1
     (SpecMParams  ev2  stack2, tp2) <- fromJust . asSpecM <$> mrTypeOf t2
     tps_eq <- mrConvertible tp1 tp2
     unless tps_eq $ throwMRFailure (ReturnTypesNotEq (Type tp1) (Type tp2))
     rpre <- liftSC2 scGlobalApply "Prelude.eqPreRel" [ev2, stack2]
     rpost <- liftSC2 scGlobalApply "Prelude.eqPostRel" [ev2, stack2]
     rr <- liftSC2 scGlobalApply "Prelude.eqRR" [tp2]
     -- NB: This will throw a type error if _ev1 /= ev2 or _stack1 /= stack2
     ref_tm <- liftSC2 scGlobalApply "Prelude.refinesS"
                       [ev2, ev2, stack2, stack2, rpre, rpost,
                        tp1, tp2, rr, t1, t2]
     uvars <- mrUVarsOuterToInner
     liftSC2 scPiList uvars ref_tm

-- | Return the 'Term' which is the refinement (@Prelude.refinesS@) of fully
-- applied versions of the given 'Term's, after quantifying over all the given
-- arguments as well as any additional arguments needed to fully apply the given
-- terms, and adding any calls to @assertS@ on the right hand side needed for
-- unifying the arguments generated when fully applying the given terms
refinementTerm ::
  SharedContext ->
  MREnv {- ^ The Mr Solver environment -} ->
  Maybe Integer {- ^ Timeout in milliseconds for each SMT call -} ->
  (Set VarIndex -> Sequent -> TopLevel (SolverStats, SolveResult))
    {- ^ The callback to use for making SMT queries -} ->
  Refnset t {- ^ Any additional refinements to be assumed by Mr Solver -} ->
  [(LocalName, Term)] {- ^ Any universally quantified variables in scope -} ->
  Term -> Term -> TopLevel (Either MRFailure Term)
refinementTerm sc env timeout askSMT rs args t1 t2 =
  evalMRM sc env timeout askSMT rs $
  withUVars (mrVarCtxFromOuterToInner args) $ \_ ->
    do tp1 <- liftIO $ scTypeOf sc t1 >>= scWhnf sc
       tp2 <- liftIO $ scTypeOf sc t2 >>= scWhnf sc
       mrRefinesFunH refinementTermH [] tp1 t1 tp2 t2
