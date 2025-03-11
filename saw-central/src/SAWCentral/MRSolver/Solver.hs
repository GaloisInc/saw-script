{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}

-- This is to stop GHC 8.8.4's pattern match checker exceeding its limit when
-- checking the pattern match in the 'CompTerm' case of 'normComp'
{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ <= 808
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
#endif

{- |
Module      : SAWCentral.MRSolver.Solver
Copyright   : Galois, Inc. 2022
License     : BSD3
Maintainer  : westbrook@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

This module implements a monadic-recursive solver, for proving that one monadic
term refines another. The algorithm works on the "monadic normal form" of
computations, which uses the following laws to simplify binds, where @either@ is
the sum elimination function defined in the SAW core prelude:

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

The resulting computations are in one of the following forms:

> returnM e  |  errorM str  |  existsM f  |  forallM f  |  assumingS b m  |
> assertingS b m  |  orM m1 m2  |  if b then m1 else m2  |  either f1 f2 e  |
> F e1 ... en  | F e1 ... en >>= k

The form @F e1 ... en@ refers to a recursively-defined function or a function
variable that has been locally bound by a @FixS@. Either way, monadic
normalization does not attempt to normalize these functions.

The algorithm maintains a context of three sorts of variables: @FixS@-bound
variables, existential variables, and universal variables. Universal variables
are represented as free SAW core variables, while the other two forms of
variable are represented as SAW core 'ExtCns's terms, which are essentially
axioms that have been generated internally. These 'ExtCns's are Skolemized,
meaning that they take in as arguments all universal variables that were in
scope when they were created. The context also maintains a partial substitution
for the existential variables, as they become instantiated with values, and it
additionally remembers the bodies / unfoldings of the @FixS@-bound variables.

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
> C |- FixS fdef args |= m: create a FixS-bound variable F bound to (fdef F) and
> recurse on fdef F args |= m
>
> C |- m |= FixS fdef args: similar to previous case
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
> * If either side is a definition whose unfolding does not contain FixS or any
>   related operations, unfold it
>
> * If F and F' have the same return type, add an assumption forall uvars in scope
>   that F e1 ... en |= F' e1' ... em' and unfold both sides, recursively proving
>   that F_body e1 ... en |= F_body' e1' ... em'. Then also prove k x |= k' x for
>   fresh uvar x.
>
> * Otherwise we don't know to "split" one of the sides into a bind whose
>   components relate to the two components on the other side, so just fail
-}

module SAWCentral.MRSolver.Solver where

import Data.Maybe
import qualified Data.Text as T
import Data.List (find, findIndices)
import Data.Foldable (foldlM)
import Data.Bits (shiftL)
import Control.Monad (void, foldM, forM, zipWithM, zipWithM_, (>=>))
import Control.Monad.Except (MonadError(..))
import qualified Data.Map as Map
import qualified Data.Text as Text
import Data.Set (Set)

import Verifier.SAW.Utils (panic)
import Verifier.SAW.Term.Functor
import Verifier.SAW.SharedTerm
import Verifier.SAW.Recognizer
import SAWCentral.Prover.SolverStats
import SAWCentral.Proof (Sequent, SolveResult)
import SAWScript.Value (TopLevel)

import SAWCentral.MRSolver.Term
import SAWCentral.MRSolver.Evidence
import SAWCentral.MRSolver.Monad
import SAWCentral.MRSolver.SMT


----------------------------------------------------------------------
-- * Normalizing and Matching on Terms
----------------------------------------------------------------------

-- FIXME: move these to Recognizer.hs

-- | Recognize an equality proposition over Booleans
asBoolEq :: Recognizer Term (Term,Term)
asBoolEq (asEq -> Just ((asBoolType -> Just ()), e1, e2)) = Just (e1, e2)
asBoolEq _ = Nothing

-- | Match a right-nested series of pairs. This is similar to 'asTupleValue'
-- except that it expects a unit value to always be at the end.
asNestedPairs :: Recognizer Term [Term]
asNestedPairs (asPairValue -> Just (x, asNestedPairs -> Just xs)) = Just (x:xs)
asNestedPairs (asFTermF -> Just UnitValue) = Just []
asNestedPairs _ = Nothing

-- | Recognize a term of the form @Cons _ x1 (Cons _ x2 (... (Nil _)))@
asList :: Recognizer Term [Term]
asList (asCtor -> Just (nm, [_]))
  | primName nm == "Prelude.Nil" = return []
asList (asCtor -> Just (nm, [_, hd, tl]))
  | primName nm == "Prelude.Cons" = (hd:) <$> asList tl
asList _ = Nothing

-- | Apply a SAW core term of type @MultiFixBodies@ to a list of monadic
-- functions bound for the functions it is defining, and return the bodies for
-- those definitions. That is, take a term of the form
--
-- > \F1 F2 ... Fn -> (f1, (f2, ... (fn, ())))
--
-- that defines corecursive functions @f1@ through @fn@ using function variables
-- @F1@ through @Fn@ to represent recursive calls and apply that term to
-- function variables for @F1@ throughh @Fn@, returning @f1@ through @fn@.
mrApplyMFixBodies :: Term -> [Term] -> MRM t [Term]
mrApplyMFixBodies (asConstant -> Just (_, Just defs_tm)) fun_tms =
  -- If defs is a constant, unfold it
  mrApplyMFixBodies defs_tm fun_tms
mrApplyMFixBodies defs_tm fun_tms =
  do defs_app <- mrApplyAll defs_tm fun_tms
     case asNestedPairs defs_app of
       Just defs -> return defs
       Nothing -> throwMRFailure (MalformedDefs defs_tm)

-- | Bind fresh function variables for a @LetRecS@ or @MultiFixS@ whose types
-- are given in the supplied list (which should all be monadic function types)
-- and whose bodies are monadic functions that can corecursively call those same
-- fresh function variables. In order to represent this corecursion, the bodies
-- are specified by a function that takes in SAW core terms for the newly bound
-- functions and returns their bodies.
mrFreshCallVars :: [Term] -> ([Term] -> MRM t [Term]) -> MRM t [MRVar]
mrFreshCallVars fun_tps bodies_f =
  do
    -- Bind fresh function variables with the types given by fun_tps
    fun_vars <- mapM (mrFreshVar "F") fun_tps
    fun_tms <- mapM mrVarTerm fun_vars

    -- Pass the newly-bound functions to bodies_f to generate the corecursive
    -- function bodies, and lift them out of the current uvars
    bodies <- bodies_f fun_tms >>= mapM lambdaUVarsM

    -- Remember the body associated with each fresh function constant
    zipWithM_ (\f body -> mrSetVarInfo f (CallVarInfo body)) fun_vars bodies

    -- Finally, return the fresh function variables
    return fun_vars


-- | Bind a single fresh function variable for a @FixS@ with a given type (which
-- must be a monadic type) and a body that can be corecursive in the function
-- variable itself
mrFreshCallVar :: Term -> (Term -> MRM t Term) -> MRM t MRVar
mrFreshCallVar fun_tp body_f =
  mrFreshCallVars [fun_tp]
  (\case
      [v] -> (: []) <$> body_f v
      _ -> panic "mrFreshCallVar" ["Expected one function variable"]) >>= \case
  [ret] -> return ret
  _ -> panic "mrFreshCallVar" ["Expected on return variable"]


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
    (isGlobalDef "SpecM.retS" -> Just (), [_, _, x]) ->
      return $ RetS x
    (isGlobalDef "SpecM.bindS" -> Just (), [ev, _, _, m, f]) ->
      do norm <- normCompTerm m
         normBind norm (CompFunTerm (EvTerm ev) f)
    (isGlobalDef "SpecM.errorS" -> Just (), [_, _, str]) ->
      return (ErrorS str)
    (isGlobalDef "Prelude.ite" -> Just (), [_, cond, then_tm, else_tm]) ->
      return $ Ite cond (CompTerm then_tm) (CompTerm else_tm)
    (isGlobalDef "Prelude.iteWithProof" -> Just (), [_, cond, then_f, else_f]) ->
      do bool_tp <- liftSC0 scBoolType
         then_tm <-
           (liftSC1 scBool >=> mrEqProp bool_tp cond >=> mrDummyProof >=>
            liftSC2 scApply then_f) True
         else_tm <-
           (liftSC1 scBool >=> mrEqProp bool_tp cond >=> mrDummyProof >=>
            liftSC2 scApply else_f) False
         return $ Ite cond (CompTerm then_tm) (CompTerm else_tm)
    (isGlobalDef "Prelude.either" -> Just (),
     [ltp, rtp, (asSpecM -> Just (ev, _)), f, g, eith]) ->
      return $ Eithers [(Type ltp, CompFunTerm ev f),
                        (Type rtp, CompFunTerm ev g)] eith
    (isGlobalDef "Prelude.eithers" -> Just (),
     [_, (matchEitherElims -> Just elims), eith]) ->
      return $ Eithers elims eith
    (isGlobalDef "Prelude.maybe" -> Just (),
     [tp, (asSpecM -> Just (ev, _)), m, f, mayb]) ->
      do tp' <- case asApplyAll tp of
                  -- Always unfold: is_bvult, is_bvule
                  (tpf@(asGlobalDef -> Just ident), args)
                    | ident `elem` ["Prelude.is_bvult", "Prelude.is_bvule"]
                    , Just (_, Just body) <- asConstant tpf ->
                      mrApplyAll body args
                  _ -> return tp
         return $ MaybeElim (Type tp') (CompTerm m) (CompFunTerm ev f) mayb
    (isGlobalDef "SpecM.orS" -> Just (), [_, _, m1, m2]) ->
      return $ OrS (CompTerm m1) (CompTerm m2)
    (isGlobalDef "SpecM.assertBoolS" -> Just (), [ev, cond]) ->
      do unit_tp <- mrUnitType
         return $ AssertBoolBind cond (CompFunReturn (EvTerm ev) unit_tp)
    (isGlobalDef "SpecM.assumeBoolS" -> Just (), [ev, cond]) ->
      do unit_tp <- mrUnitType
         return $ AssumeBoolBind cond (CompFunReturn (EvTerm ev) unit_tp)
    (isGlobalDef "SpecM.existsS" -> Just (), [ev, tp]) ->
      do unit_tp <- mrUnitType
         return $ ExistsBind (Type tp) (CompFunReturn (EvTerm ev) unit_tp)
    (isGlobalDef "SpecM.forallS" -> Just (), [ev, tp]) ->
      do unit_tp <- mrUnitType
         return $ ForallBind (Type tp) (CompFunReturn (EvTerm ev) unit_tp)
    (isGlobalDef "SpecM.FixS" -> Just (), _ev:_tp_d:body:args) ->
      do
        -- Bind a fresh function var for the new recursive function, getting the
        -- type of the new function as the input type of body, which should have
        -- type specFun E T -> specFun E T
        body_tp <- mrTypeOf body
        fun_tp <- case asPi body_tp of
          Just (_, tp_in, _) -> return tp_in
          Nothing -> throwMRFailure (MalformedDefs body)
        fun_var <- mrFreshCallVar fun_tp (mrApply body)

        -- Return the function variable applied to args as a normalized
        -- computation, noting that it must be applied to all of the uvars as
        -- well as the args
        let var = CallSName fun_var
        all_args <- (++ args) <$> getAllUVarTerms
        FunBind var all_args <$> mkCompFunReturn <$>
          mrFunOutType var all_args

        {-
FIXME HERE NOW: match a tuple projection of a MultiFixS

    (isGlobalDef "SpecM.MultiFixS" -> Just (), ev:tp_ds:defs:args) ->
      do
        -- Bind fresh function vars for the new recursive functions
        fun_vars <- mrFreshCallVars ev tp_ds defs
        -- Return the @i@th variable to args as a normalized computation, noting
        -- that it must be applied to all of the uvars as well as the args
        let var = CallSName (fun_vars !! (fromIntegral i))
        all_args <- (++ args) <$> getAllUVarTerms
        FunBind var all_args <$> mkCompFunReturn <$>
          mrFunOutType var all_args -}

    (isGlobalDef "SpecM.LetRecS" -> Just (), [ev,tp_ds,_,defs,body]) ->
      do
        -- First compute the types of the recursive functions being bound by
        -- mapping @tpElem@ to the type descriptions, and bind functions of
        -- those types
        tpElem_fun <- mrGlobalTerm "SpecM.tpElem"
        fun_tps <- case asList tp_ds of
          Just ds -> mapM (\d -> mrApplyAll tpElem_fun [ev, d]) ds
          Nothing -> throwMRFailure (MalformedTpDescList tp_ds)

        -- Bind fresh function vars for the new recursive functions
        fun_vars <- mrFreshCallVars fun_tps (mrApplyMFixBodies defs)
        fun_tms <- mapM mrVarTerm fun_vars

        -- Continue normalizing body applied to those fresh function vars
        body_app <- mrApplyAll body fun_tms
        normCompTerm body_app

    -- Treat forNatLtThenS like FixS with a body of forNatLtThenSBody
    (isGlobalDef "SpecM.forNatLtThenS" -> Just (), [ev,st,ret,n,f,k,s0]) ->
      do
        -- Bind a fresh function with type Nat -> st -> SpecM E ret
        type_f <- mrGlobalTermUnfold "SpecM.forNatLtThenSBodyType"
        fun_tp <- mrApplyAll type_f [ev,st,ret]

        -- Build the function for applying forNatLtThenSBody to its arguments to
        -- define the body of the recursive definition, including the invariant
        -- argument that is bound to the current assumptions
        invar <- mrAssumptions
        body_fun_tm <- mrGlobalTermUnfold "SpecM.forNatLtThenSBody"
        let body_f rec_fun =
              mrApplyAll body_fun_tm [ev,st,ret,n,f,k,invar,rec_fun]

        -- Bind a fresh function var for the new recursive function
        fun_var <- mrFreshCallVar fun_tp body_f

        -- Return the function variable applied to 0 and s0 as a normalized
        -- computation, noting that it must be applied to all of the uvars as
        -- well as the args
        let var = CallSName fun_var
        z <- liftSC1 scNat 0
        all_args <- (++ [z,s0]) <$> getAllUVarTerms
        FunBind var all_args <$> mkCompFunReturn <$>
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
    (asGlobalDef -> Just "CryptolM.atM", [ev, (asBvToNat -> Just (w, n)),
                                          a, xs, i_nat]) ->
      do body <- mrGlobalDefBody "CryptolM.bvVecAtM"
         liftSC1 scWhnf i_nat >>= mrBvNatInRange w >>= \case
           Just i -> mrApplyAll body [ev, w, n, a, xs, i]
                       >>= normCompTerm
           _ -> throwMRFailure (MalformedComp t)

    -- Convert `atM n ... xs (bvToNat ...)` for a constant `n` into the
    -- unfolding of `bvVecAtM` after converting `n` to a bitvector constant
    -- and applying `genBVVecFromVec` to `xs`
    (asGlobalDef -> Just "CryptolM.atM", [ev, n_tm@(asNat -> Just n),
                                          a@(asBoolType -> Nothing), xs,
                                          (asBvToNat ->
                                             Just (w_tm@(asNat -> Just w),
                                                   i))]) ->
      do body <- mrGlobalDefBody "CryptolM.bvVecAtM"
         if n < 1 `shiftL` fromIntegral w then do
           n' <- liftSC2 scBvLit w (toInteger n)
           xs' <- mrGenBVVecFromVec n_tm a xs "normComp (atM)" w_tm n'
           mrApplyAll body [ev, w_tm, n', a, xs', i] >>= normCompTerm
           else throwMRFailure (MalformedComp t)

    -- Convert `updateM (bvToNat ...) ... (bvToNat ...)` into the unfolding of
    -- `bvVecUpdateM`
    (asGlobalDef -> Just "CryptolM.updateM", [ev, (asBvToNat -> Just (w, n)),
                                              a, xs, i_nat, x]) ->
      do body <- mrGlobalDefBody "CryptolM.bvVecUpdateM"
         liftSC1 scWhnf i_nat >>= mrBvNatInRange w >>= \case
           Just i -> mrApplyAll body [ev, w, n, a, xs, i, x]
                       >>= normCompTerm
           _ -> throwMRFailure (MalformedComp t)

    -- Convert `updateM n ... xs (bvToNat ...)` for a constant `n` into the
    -- unfolding of `bvVecUpdateM` after converting `n` to a bitvector constant
    -- and applying `genBVVecFromVec` to `xs`
    (asGlobalDef -> Just "CryptolM.updateM", [ev, n_tm@(asNat -> Just n),
                                              a@(asBoolType -> Nothing), xs,
                                              (asBvToNat ->
                                                 Just (w_tm@(asNat -> Just w),
                                                       i)), x]) ->
      do body <- mrGlobalDefBody "CryptolM.fromBVVecUpdateM"
         if n < 1 `shiftL` fromIntegral w then do
           n' <- liftSC2 scBvLit w (toInteger n)
           xs' <- mrGenBVVecFromVec n_tm a xs "normComp (updateM)" w_tm n'
           err_tm <- mrErrorTerm a "normComp (updateM)"
           mrApplyAll body [ev, w_tm, n', a, xs', i, x, err_tm, n_tm]
             >>= normCompTerm
           else throwMRFailure (MalformedComp t)

    -- Always unfold: sawLet, Num_rec, invariantHint, assumingS, assertingS,
    -- forNatLtThenSBody, vecMapM, vecMapBindM, seqMapM
    (f@(asGlobalDef -> Just ident), args)
      | ident `elem`
        ["Prelude.sawLet", "Prelude.ifWithProof", "Prelude.iteWithProof",
         "Cryptol.Num_rec", "SpecM.invariantHint",
         "SpecM.assumingS", "SpecM.assertingS", "SpecM.forNatLtThenSBody",
         "CryptolM.vecMapM", "CryptolM.vecMapBindM", "CryptolM.seqMapM"]
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
         FunBind fun_name args <$> mkCompFunReturn <$>
           mrFunOutType fun_name args

    ((asGlobalFunName -> Just f), args) ->
      FunBind f args <$> mkCompFunReturn <$> mrFunOutType f args

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
normBind (FunBind f args k1) k2
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
  | otherwise -} = return $ FunBind f args (compFunComp k1 k2)

-- | Bind a 'Term' for a computation with a function and normalize
normBindTerm :: Term -> CompFun -> MRM t NormComp
normBindTerm t f = normCompTerm t >>= \m -> normBind m f

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
       (asPi -> Just (_, a, asSpecM -> Just (ev, b)),
        asPi -> Just (_, _, asSpecM -> Just (_, c))) ->
         -- we explicitly unfold @SpecM.composeS@ here so @mrApplyAll@ will
         -- beta-reduce
         let nm = maybe "ret_val" id (compFunVarName f) in
         mrLambdaLift1 (nm, a) (b, c, f', g') $ \arg (b', c', f'', g'') ->
           do app <- mrApplyAll f'' [arg]
              liftSC2 scGlobalApply "SpecM.bindS" [unEvTerm ev,
                                                   b', c', app, g'']
       _ -> error "compFunToTerm: type(s) not of the form: a -> SpecM b"
compFunToTerm (CompFunReturn ev (Type a)) =
  mrLambdaLift1 ("ret_val", a) a $ \ret_val a' ->
    liftSC2 scGlobalApply "SpecM.retS" [unEvTerm ev, a', ret_val]

{-
-- | Convert a 'Comp' into a 'Term'
compToTerm :: Comp -> MRM t Term
compToTerm (CompTerm t) = return t
compToTerm (CompReturn t) =
   do tp <- mrTypeOf t
      liftSC2 scGlobalApply "SpecM.retS" [tp, t]
compToTerm (CompBind m (CompFunReturn _)) = compToTerm m
compToTerm (CompBind m f) =
  do m' <- compToTerm m
     f' <- compFunToTerm f
     mrTypeOf f' >>= \case
       (asPi -> Just (_, a, asSpecM -> Just b)) ->
         liftSC2 scGlobalApply "SpecM.bindS" [a, b, m', f']
       _ -> error "compToTerm: type not of the form: a -> SpecM b"
-}

-- | Apply a 'CompFun' to a term and normalize the resulting computation
applyNormCompFun :: CompFun -> Term -> MRM t NormComp
applyNormCompFun f arg = applyCompFun f arg >>= normComp


-- | Convert a 'FunAssumpRHS' to a 'NormComp'
mrFunAssumpRHSAsNormComp :: FunAssumpRHS -> MRM t NormComp
mrFunAssumpRHSAsNormComp (OpaqueFunAssump f args) =
  FunBind f args <$> mkCompFunReturn <$> mrFunOutType f args
mrFunAssumpRHSAsNormComp (RewriteFunAssump rhs) = normCompTerm rhs


-- | Match a term as a static list of eliminators for an Eithers type
matchEitherElims :: Term -> Maybe [EitherElim]
matchEitherElims (asCtor ->
                  Just (primName -> "Prelude.FunsTo_Nil", [_])) = Just []
matchEitherElims (asCtor -> Just (primName -> "Prelude.FunsTo_Cons",
                                  [asSpecM -> Just (ev, _), tp, f, rest])) =
  ((Type tp, CompFunTerm ev f):) <$>
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
FIXME HERE: maybe each FunName should stipulate whether it is recursive or
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
     proveCoIndHyp [] hyp

-- | Prove the refinement represented by a 'CoIndHyp' coinductively. This is the
-- main loop implementing 'mrRefinesCoInd'. See that function for documentation.
proveCoIndHyp :: [[Either Int Int]] -> CoIndHyp -> MRM t ()
proveCoIndHyp prev_specs hyp = withFailureCtx (FailCtxCoIndHyp hyp) $
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
         | f1 == nm1' && f2 == nm2' && elem new_vars prev_specs ->
           -- This should never happen, since it means that generalizing
           -- new_vars led to the exact same arguments not unifying, but at
           -- least one more should unify when we generalize
           panic "proveCoIndHyp" ["Generalization loop detected!"]
         | f1 == nm1' && f2 == nm2' ->
           -- NOTE: the state automatically gets reset here because we defined
           -- MRM t with ExceptT at a lower level than StateT
           do mrDebugPPPrefixSep 1 "Widening recursive assumption for" nm1' "|=" nm2'
              hyp' <- generalizeCoIndHyp hyp new_vars
              proveCoIndHyp (new_vars:prev_specs) hyp'
       e -> throwError e

-- | Test that a coinductive hypothesis for the given function names matches the
-- given arguments, otherwise throw an exception saying that widening is needed
matchCoIndHyp :: CoIndHyp -> [Term] -> [Term] -> MRM t ()
matchCoIndHyp hyp args1 args2 =
  do mrDebugPPPrefix 1 "matchCoIndHyp" hyp
     (args1', args2') <- instantiateCoIndHyp hyp
     mrDebugPPPrefixSep 3 "matchCoIndHyp args" args1 "," args2
     mrDebugPPPrefixSep 3 "matchCoIndHyp args'" args1' "," args2'
     eqs1 <- zipWithM mrProveEqBiRef args1' args1
     eqs2 <- zipWithM mrProveEqBiRef args2' args2
     if and (eqs1 ++ eqs2) then return () else
       throwError $ MRExnWiden (coIndHypLHSFun hyp) (coIndHypRHSFun hyp)
       (map Left (findIndices not eqs1) ++ map Right (findIndices not eqs2))
     proveCoIndHypInvariant hyp

-- | Generalize a coinductive hypothesis of the form
--
-- > forall x1..xn. f args_l |= g args_r
--
-- by replacing some of the arguments with fresh variables that are added to the
-- coinductive hypothesis, i.e., to the list @x1..xn@ of quantified variables.
-- The arguments that need to be generalized are given by index on either the
-- left- or right-hand list of arguments. Any of the arguments being generalized
-- that are equivalent (in the sense of 'mrProveRel') get generalized to the
-- same fresh variable, so we preserve as much equality as we can between
-- arguments being generalized. Note that generalized arguments are not unified
-- with non-generalized arguments, since they are being generalized because they
-- didn't match the non-generalized arguments in some refinement call that the
-- solver tried to make and couldn't.
generalizeCoIndHyp :: CoIndHyp -> [Either Int Int] -> MRM t CoIndHyp
generalizeCoIndHyp hyp [] = return hyp
generalizeCoIndHyp hyp all_specs@(arg_spec_0:arg_specs) =
  withOnlyUVars (coIndHypCtx hyp) $ do
  withNoUVars $ mrDebugPPPrefixSep 2 "generalizeCoIndHyp with indices"
                                     all_specs "on" hyp
  -- Get the arg and type associated with the first arg_spec and build an
  -- injective representation for it, keeping track of the representation term
  -- and type
  let arg_tm_0 = coIndHypArg hyp arg_spec_0
  arg_tp_0 <- mrTypeOf arg_tm_0 >>= mrNormOpenTerm
  (tp_r0, tm_r0, repr0) <- mkInjReprTerm arg_tp_0 arg_tm_0

  -- Attempt to unify the representation of arg 0 with each of the arg_specs
  -- being generalized using injUnifyRepr. When unification succeeds, this could
  -- result in a more specific representation type, so use injReprRestrict to
  -- update the representations of all the arguments that have already been
  -- unified with arg 0
  (tp_r, _, repr, eq_args, arg_reprs, uneq_args) <-
    foldM
    (\(tp_r, tm_r, repr, eq_args, arg_reprs, uneq_args) arg_spec ->
      do let arg_tm = coIndHypArg hyp arg_spec
         arg_tp <- mrTypeOf arg_tm >>= mrNormOpenTerm
         unify_res <- injUnifyRepr tp_r tm_r repr arg_tp arg_tm
         case unify_res of
           Just (tp_r',tm_r',repr',arg_repr) ->
             -- If unification succeeds, add arg to the list of eq_args and add
             -- its repr to the list of arg_reprs, and restrict the previous
             -- arg_reprs to use the new representation type tp_r'
             do arg_reprs' <- mapM (injReprRestrict tp_r' repr' tp_r) arg_reprs
                return (tp_r', tm_r', repr',
                        arg_spec:eq_args, arg_repr:arg_reprs', uneq_args)
           Nothing ->
             -- If unification fails, add arg_spec to the list of uneq_args
             return (tp_r, tm_r, repr, eq_args, arg_reprs, arg_spec:uneq_args))
    (tp_r0, tm_r0, repr0, [], [], [])
    arg_specs

  -- Now we generalize the arguments that unify with arg_spec0 by adding a new
  -- variable z of type tp_r to hyp and setting each arg in eq_args to the
  -- result of applying its corresponding repr to z
  (hyp', var) <- coIndHypWithVar hyp "z" (Type tp_r)
  arg_reprs' <- liftTermLike 0 1 (repr:arg_reprs)
  hyp'' <- foldlM (\hyp_i (arg_spec_i, repr_i) ->
                    coIndHypSetArg hyp_i arg_spec_i <$> mrApplyRepr repr_i var)
                  hyp' (zip (arg_spec_0:eq_args) arg_reprs')
  -- We finish by recursing on any remaining arg_specs
  generalizeCoIndHyp hyp'' uneq_args


----------------------------------------------------------------------
-- * Decidable Propositions
----------------------------------------------------------------------

-- | A function for assuming a proposition or its negation, that also lifts a
-- 'TermLike' argument in the sense of 'withUVarLift'
newtype AssumpFun t = AssumpFun { appAssumpFun ::
                                    forall tm a. TermLike tm =>
                                    Bool -> tm -> (tm -> MRM t a) -> MRM t a }

-- | Test if a 'Term' is a propostion that has a corresponding Boolean SAW core
-- term that decides it; e.g., IsLtNat n m is a Prop that corresponds to the
-- Boolean expression ltNat n m. If so, return the Boolean expression
asBoolProp :: Term -> Maybe (MRM t Term)
asBoolProp (asEq -> Just (asSimpleEq -> Just eqf, e1, e2)) =
  Just $ liftSC2 eqf e1 e2
asBoolProp (asApplyAll -> (isGlobalDef "Prelude.IsLtNat" -> Just (), [n,m])) =
  Just $ liftSC2 scLtNat n m
asBoolProp _ = Nothing

-- | Test if a 'Term' is a propostion that MR solver can decide, i.e., test if
-- it or its negation holds. If so, return: a function to decide the propostion,
-- that returns 'Just' of a Boolean iff the proposition definitely does or does
-- not hold; and a function to assume the proposition or its negation in a
-- sub-computation. This latter function also takes a 'TermLike' that it will
-- lift in the sense of 'withUVarLift' in the sub-computation.
asDecProp :: Term -> Maybe (MRM t (Maybe Bool, AssumpFun t))
asDecProp (asBoolProp -> Just condM) =
  Just $
  do cond <- condM
     not_cond <- liftSC1 scNot cond
     let assumeM b tm m = withAssumption (if b then cond else not_cond) (m tm)
     mrProvable cond >>= \case
       True -> return (Just True, AssumpFun assumeM)
       False ->
         mrProvable not_cond >>= \case
         True -> return (Just False, AssumpFun assumeM)
         False -> return (Nothing, AssumpFun assumeM)
asDecProp (asIsFinite -> Just n) =
  Just $
  do n_norm <- mrNormOpenTerm n
     maybe_assump <- mrGetDataTypeAssump n_norm
     -- The assumption function that requires b == req, in which case it is just
     -- the identity, and otherwise panics
     let requireIdAssumeM req b tm m =
           if req == b then m tm else
             panic "asDecProp" ["Unexpected inconsistent assumption"]
     case (maybe_assump, asNum n_norm) of
       (_, Just (Left _)) ->
         return (Just True, AssumpFun (requireIdAssumeM True))
       (_, Just (Right _)) ->
         return (Just False, AssumpFun (requireIdAssumeM False))
       (Just (IsNum _), _) ->
         return (Just True, AssumpFun (requireIdAssumeM True))
       (Just IsInf, _) ->
         return (Just False, AssumpFun (requireIdAssumeM False))
       _ ->
         return (Nothing,
                 AssumpFun $ \b tm m ->
                  if b then
                    (liftSC0 scNatType >>= \nat_tp ->
                      (withUVarLift "n" (Type nat_tp) (n_norm, tm) $ \n_nat (n', tm') ->
                        withDataTypeAssump n' (IsNum n_nat) (m tm')))
                  else
                    withDataTypeAssump n_norm IsInf (m tm))
asDecProp _ = Nothing


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

-- | Helper function that applies 'mrRefines' to a pair
mrRefinesPair :: (ToNormComp a, ToNormComp b) => (a, b) -> MRM t ()
mrRefinesPair (a,b) = mrRefines a b

-- | The main implementation of 'mrRefines'
mrRefines' :: NormComp -> NormComp -> MRM t ()

mrRefines' (RetS e1) (RetS e2) = mrAssertProveEqBiRef e1 e2
mrRefines' (ErrorS _) (ErrorS _) = return ()
mrRefines' (RetS e) (ErrorS err) = throwMRFailure (ReturnNotError (Right err) e)
mrRefines' (ErrorS err) (RetS e) = throwMRFailure (ReturnNotError (Left  err) e)

mrRefines' (MaybeElim (Type prop_tp@(asDecProp -> Just decPropM)) m1 f1 _) m2 =
  decPropM >>= \case
  (Just True, AssumpFun assumeM) ->
    do m1' <- mrDummyProof prop_tp >>= applyNormCompFun f1
       assumeM True (m1',m2) mrRefinesPair
  (Just False, AssumpFun assumeM) -> assumeM False (m1,m2) mrRefinesPair
  (Nothing, AssumpFun assumeM) ->
    do m1' <- mrDummyProof prop_tp >>= applyNormCompFun f1
       assumeM True (m1',m2) mrRefinesPair
       assumeM False (m1,m2) mrRefinesPair

mrRefines' m1 (MaybeElim (Type prop_tp@(asDecProp -> Just decPropM)) m2 f2 _) =
  decPropM >>= \case
  (Just True, AssumpFun assumeM) ->
    do m2' <- mrDummyProof prop_tp >>= applyNormCompFun f2
       assumeM True (m1,m2') mrRefinesPair
  (Just False, AssumpFun assumeM) -> assumeM False (m1,m2) mrRefinesPair
  (Nothing, AssumpFun assumeM) ->
    do m2' <- mrDummyProof prop_tp >>= applyNormCompFun f2
       assumeM True (m1,m2') mrRefinesPair
       assumeM False (m1,m2) mrRefinesPair

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
  mrNormOpenTerm (typeTm tp) >>= mkInjReprType >>= \(tp', r) ->
  withUVarLift nm (Type tp') (m1,f2) $ \x (m1',f2') ->
  mrApplyRepr r x >>= \x' ->
  applyNormCompFun f2' x' >>= \m2' ->
  mrRefines m1' m2'
mrRefines' (ExistsBind tp f1) m2 =
  let nm = maybe "x" id (compFunVarName f1) in
  mrNormOpenTerm (typeTm tp) >>= mkInjReprType >>= \(tp', r) ->
  withUVarLift nm (Type tp') (f1,m2) $ \x (f1',m2') ->
  mrApplyRepr r x >>= \x' ->
  applyNormCompFun f1' x' >>= \m1' ->
  mrRefines m1' m2'

mrRefines' m1 (OrS m2 m2') =
  mrOr (mrRefines m1 m2) (mrRefines m1 m2')
mrRefines' (OrS m1 m1') m2 =
  mrRefines m1 m2 >> mrRefines m1' m2

-- FIXME: the following cases don't work unless we either allow evars to be set
-- to NormComps or we can turn NormComps back into terms
mrRefines' m1@(FunBind (EVarFunName _) _ _) m2 =
  throwMRFailure (CompsDoNotRefine m1 m2)
mrRefines' m1 m2@(FunBind (EVarFunName _) _ _) =
  throwMRFailure (CompsDoNotRefine m1 m2)
{-
mrRefines' (FunBind (EVarFunName evar) args (CompFunReturn _)) m2 =
  mrGetEVar evar >>= \case
  Just f ->
    (mrApplyAll f args >>= normCompTerm) >>= \m1' ->
    mrRefines m1' m2
  Nothing -> mrTrySetAppliedEVar evar args m2
-}

mrRefines' (FunBind f args1 k1) (FunBind f' args2 k2)
  | f == f' && length args1 == length args2 =
    zipWithM_ mrAssertProveEqBiRef args1 args2 >>
    mrFunOutType f args1 >>= \(_, tp) ->
    mrRefinesFun tp k1 tp k2

mrRefines' m1@(FunBind f1 args1 k1)
           m2@(FunBind f2 args2 k2) =
  mrFunOutType f1 args1 >>= mapM mrNormOpenTerm >>= \(_, tp1) ->
  mrFunOutType f2 args2 >>= mapM mrNormOpenTerm >>= \(_, tp2) ->
  injUnifyTypes tp1 tp2 >>= \mb_convs ->
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
       zipWithM_ mrAssertProveEqBiRef args1'' args1
       zipWithM_ mrAssertProveEqBiRef args2'' args2
       recordUsedFunAssump fa >> mrRefinesFun tp1 k1 tp2 k2

  -- If we have an opaque FunAssump that f1 refines some f /= f2, and f2
  -- unfolds and is not recursive in itself, unfold f2 and recurse
  (_, Just fa@(FunAssump _ _ _ (OpaqueFunAssump _ _) _))
    | Just (f2_body, False) <- maybe_f2_body ->
    normBindTerm f2_body k2 >>= \m2' ->
    recordUsedFunAssump fa >> mrRefines m1 m2'

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
       zipWithM_ mrAssertProveEqBiRef args1'' args1
       -- It's important to instantiate the evars here so that rhs is well-typed
       -- when bound with k1
       rhs''' <- mapTermLike mrSubstEVars rhs''
       m1' <- normBind rhs''' k1
       recordUsedFunAssump fa >> mrRefines m1' m2

  -- If f1 unfolds and is not recursive in itself, unfold it and recurse
  _ | Just (f1_body, False) <- maybe_f1_body ->
      normBindTerm f1_body k1 >>= \m1' -> mrRefines m1' m2

  -- If f2 unfolds and is not recursive in itself, unfold it and recurse
  _ | Just (f2_body, False) <- maybe_f2_body ->
      normBindTerm f2_body k2 >>= \m2' -> mrRefines m1 m2'

  -- If we don't have a co-inducitve hypothesis for f1 and f2, don't have an
  -- assumption that f1 refines some specification, both f1 and f2 are recursive
  -- and have return types which can be injectively unified, then try to
  -- coinductively prove that f1 args1 |= f2 args2 under the assumption that
  -- f1 args1 |= f2 args2, and then try to prove that k1 |= k2
  _ | Just _ <- maybe_f1_body
    , Just _ <- maybe_f2_body ->
      case mb_convs of
        Just _ -> mrRefinesCoInd f1 args1 f2 args2 >> mrRefinesFun tp1 k1 tp2 k2
        _ -> throwMRFailure (BindTypesNotUnifiable (Type tp1) (Type tp2))

  -- If we cannot line up f1 and f2, then making progress here would require us
  -- to somehow split either m1 or m2 into some bind m' >>= k' such that m' is
  -- related to the function call on the other side and k' is related to the
  -- continuation on the other side, but we don't know how to do that, so give
  -- up
  _ -> throwMRFailure (FunNamesDoNotRefine f1 args1 f2 args2)

mrRefines' m1@(FunBind f1 args1 k1) m2 =
  mrGetFunAssump f1 >>= \case

  -- If we have an assumption that f1 args' refines some rhs, then prove that
  -- args1 = args' and then that rhs refines m2
  Just fa@(FunAssump ctx _ args1' rhs _) ->
    do rhs' <- mrFunAssumpRHSAsNormComp rhs
       evars <- mrFreshEVars ctx
       (args1'', rhs'') <- substTermLike 0 evars (args1', rhs')
       zipWithM_ mrAssertProveEqBiRef args1'' args1
       -- It's important to instantiate the evars here so that rhs is well-typed
       -- when bound with k1
       rhs''' <- mapTermLike mrSubstEVars rhs''
       m1' <- normBind rhs''' k1
       recordUsedFunAssump fa >> mrRefines m1' m2

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
     tp' <- mrNormOpenTerm (typeTm tp)
     evars <- forM (fromMaybe [tp'] (asTupleType tp')) $ \tp_i ->
       mkInjReprType tp_i >>= \(tp_i', r) ->
       mrFreshEVar nm (Type tp_i') >>= mrApplyRepr r
     x <- liftSC1 scTuple evars 
     m2' <- applyNormCompFun f2 x
     mrRefines m1 m2'
mrRefines'' (ForallBind tp f1) m2 =
  do let nm = maybe "x" id (compFunVarName f1)
     tp' <- mrNormOpenTerm (typeTm tp)
     evars <- forM (fromMaybe [tp'] (asTupleType tp')) $ \tp_i ->
       mkInjReprType tp_i >>= \(tp_i', r) ->
       mrFreshEVar nm (Type tp_i') >>= mrApplyRepr r
     x <- liftSC1 scTuple evars 
     m1' <- applyNormCompFun f1 x
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
     piTp1 <- mrTypeOf f1'' >>= mrNormOpenTerm
     piTp2 <- mrTypeOf f2'' >>= mrNormOpenTerm
     mrRefinesFunH mrRefines [] piTp1 f1'' piTp2 f2''

-- | Prove that two functions both refine another for all inputs
mrBiRefinesFuns :: MRRel t ()
mrBiRefinesFuns piTp1 f1 piTp2 f2 =
  mrDebugPPPrefixSep 1 "mrBiRefinesFuns" f1 "=|=" f2 >>
  mrNormOpenTerm piTp1 >>= \piTp1' ->
  mrNormOpenTerm piTp2 >>= \piTp2' ->
  mrRefinesFunH mrRefines [] piTp1' f1 piTp2' f2 >>
  mrRefinesFunH mrRefines [] piTp2' f2 piTp1' f1

-- | Prove that two terms are related via bi-refinement on terms of SpecFun
-- type (as in 'isSpecFunType') or via equality otherwise, returning false if
-- this is not possible and instantiating evars if necessary
mrProveEqBiRef :: Term -> Term -> MRM t Bool
mrProveEqBiRef = mrProveRel (Just mrBiRefinesFuns)

-- | Prove that two terms are related via bi-refinement on terms of SpecFun
-- type (as in 'isSpecFunType') or via equality otherwise, throwing an error if
-- this is not possible and instantiating evars if necessary
mrAssertProveEqBiRef :: Term -> Term -> MRM t ()
mrAssertProveEqBiRef = mrAssertProveRel (Just mrBiRefinesFuns)


-- | The main loop of 'mrRefinesFun', 'askMRSolver': given a function that
-- attempts to prove refinement between two computational terms, i.e., terms of
-- type @SpecM a@ and @SpecM b@ for some types @a@ and @b@, attempt to prove
-- refinement between two monadic functions. The list of 'Term's argument
-- contains all the variables that have so far been abstracted by
-- 'mrRefinesFunH', and the remaining 'Term's are the left-hand type, left-hand
-- term of that type, right-hand type, and right-hand term of that type for the
-- refinement we are trying to prove.
--
-- This function works by abstracting over arguments of the left- and right-hand
-- sides, as determined by their types, and applying the functions to these
-- variables until we get terms of non-functional monadic type, that are passed
-- to the supplied helper function. Proposition arguments in the form of
-- equality on Boolean values can occur on either side, and are added as
-- assumptions to the refinement. Regular non-proof arguments must occur on both
-- sides, and are added as a single variable that is passed to both sides. This
-- means that these regular argument types must be either equal or
-- injectively unifiable with 'injUnifyTypes'.
mrRefinesFunH :: (Term -> Term -> MRM t a) -> [Term] -> MRRel t a

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
mrRefinesFunH k vars (asPi -> Just (nm1, tp1@(asBoolEq ->
                                              Just (b1, b2)), _)) t1 piTp2 t2 =
  liftSC2 scBoolEq b1 b2 >>= \eq ->
  withAssumption eq $
  let nm = maybe "p" id $ find ((/=) '_' . Text.head)
                        $ [nm1] ++ catMaybes [ asLambdaName t1 ] in
  withUVarLift nm (Type tp1) (vars,t1,piTp2,t2) $ \var (vars',t1',piTp2',t2') ->
  do t1'' <- mrApplyAll t1' [var]
     piTp1' <- mrTypeOf t1''
     mrRefinesFunH k (var : vars') piTp1' t1'' piTp2' t2'
mrRefinesFunH k vars piTp1 t1 (asPi -> Just (nm2, tp2@(asBoolEq ->
                                                       Just (b1, b2)), _)) t2 =
  liftSC2 scBoolEq b1 b2 >>= \eq ->
  withAssumption eq $
  let nm = maybe "p" id $ find ((/=) '_' . Text.head)
                        $ [nm2] ++ catMaybes [ asLambdaName t2 ] in
  withUVarLift nm (Type tp2) (vars,piTp1,t1,t2) $ \var (vars',piTp1',t1',t2') ->
  do t2'' <- mrApplyAll t2' [var]
     piTp2' <- mrTypeOf t2''
     mrRefinesFunH k (var : vars') piTp1' t1' piTp2' t2''

-- We always curry pair values before introducing them (NOTE: we do this even
-- when the have the same types to ensure we never have to unify a projection
-- of an evar with a non-projected value, e.g. evar.1 == val)
-- FIXME: Only do this if we have corresponding pairs on both sides?
mrRefinesFunH k vars (asPi -> Just (nm1, asPairType -> Just (tpL1, tpR1), _)) t1
                     (asPi -> Just (nm2, asPairType -> Just (tpL2, tpR2), _)) t2 =
  do t1'' <- mrLambdaLift2 (nm1, tpL1) (nm1, tpR1) t1 $ \prj1 prj2 t1' ->
               liftSC2 scPairValue prj1 prj2 >>= mrApply t1'
     t2'' <- mrLambdaLift2 (nm2, tpL2) (nm2, tpR2) t2 $ \prj1 prj2 t2' ->
               liftSC2 scPairValue prj1 prj2 >>= mrApply t2'
     piTp1' <- mrTypeOf t1''
     piTp2' <- mrTypeOf t2''
     mrRefinesFunH k vars piTp1' t1'' piTp2' t2''
mrRefinesFunH k vars (asPi -> Just (nm1, asPairType -> Just (tpL1, tpR1), _)) t1 tp2 t2 =
  do t1'' <- mrLambdaLift2 (nm1, tpL1) (nm1, tpR1) t1 $ \prj1 prj2 t1' ->
               liftSC2 scPairValue prj1 prj2 >>= mrApply t1'
     piTp1' <- mrTypeOf t1''
     mrRefinesFunH k vars piTp1' t1'' tp2 t2
mrRefinesFunH k vars tp1 t1 (asPi -> Just (nm2, asPairType -> Just (tpL2, tpR2), _)) t2 =
  do t2'' <- mrLambdaLift2 (nm2, tpL2) (nm2, tpR2) t2 $ \prj1 prj2 t2' ->
               liftSC2 scPairValue prj1 prj2 >>= mrApply t2'
     piTp2' <- mrTypeOf t2''
     mrRefinesFunH k vars tp1 t1 piTp2' t2''

mrRefinesFunH k vars (asPi -> Just (nm1, tp1, _)) t1
                     (asPi -> Just (nm2, tp2, _)) t2 =
  injUnifyTypes tp1 tp2 >>= \case
  -- If we can find injective conversions from from a type @tp@ to @tp1@ and
  -- @tp2@, introduce a variable of type @tp@, apply both conversions to it,
  -- and substitute the results on the left and right sides, respectively
  Just (tp, r1, r2) ->
    mrDebugPPPrefixSep 3 "mrRefinesFunH calling findInjConvs" tp1 "," tp2 >>
    mrDebugPPPrefix 3 "mrRefinesFunH got type" tp >>
    let nm = maybe "x" id $ find ((/=) '_' . Text.head)
                          $ [nm1, nm2] ++ catMaybes [ asLambdaName t1
                                                    , asLambdaName t2 ] in
    withUVarLift nm (Type tp) (vars,r1,r2,t1,t2) $ \var (vars',r1',r2',t1',t2') ->
    do tm1 <- mrApplyRepr r1' var
       tm2 <- mrApplyRepr r2' var
       t1'' <- mrApplyAll t1' [tm1]
       t2'' <- mrApplyAll t2' [tm2]
       piTp1' <- mrTypeOf t1'' >>= liftSC1 scWhnf
       piTp2' <- mrTypeOf t2'' >>= liftSC1 scWhnf
       mrRefinesFunH k (var : vars') piTp1' t1'' piTp2' t2''
  -- Otherwise, error
  Nothing -> throwMRFailure (TypesNotUnifiable (Type tp1) (Type tp2))

-- Error if we don't have the same number of arguments on both sides
-- FIXME: Add a specific error for this case
mrRefinesFunH _ _ (asPi -> Just (_,tp1,_)) _ (asPi -> Nothing) _ =
  liftSC0 scUnitType >>= \utp ->
  throwMRFailure (TypesNotEq (Type tp1) (Type utp))
mrRefinesFunH _ _ (asPi -> Nothing) _ (asPi -> Just (_,tp2,_)) _ =
  liftSC0 scUnitType >>= \utp ->
  throwMRFailure (TypesNotEq (Type utp) (Type tp2))

-- Error if either side's return type is not SpecM
mrRefinesFunH _ _ tp1@(asSpecM -> Nothing) t1 _ _ =
  throwMRFailure (NotCompFunType tp1 t1)
mrRefinesFunH _ _ _ _ tp2@(asSpecM -> Nothing) t2 =
  throwMRFailure (NotCompFunType tp2 t2)

-- This case means we must be proving refinement on two SpecM computations, so
-- call the helper function k
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
    do tp1 <- liftSC1 scTypeOf t1 >>= mrNormOpenTerm
       tp2 <- liftSC1 scTypeOf t2 >>= mrNormOpenTerm
       mrDebugPPPrefixSep 1 "mr_solver" t1 "|=" t2
       mrRefinesFunH (askMRSolverH mrRefines) [] tp1 t1 tp2 t2

-- | Helper function for 'refinementTerm': returns the proposition stating that
-- one 'Term' refines another, after quantifying over all current 'mrUVars' with
-- Pi types. Note that this assumes both terms have the same event types; if
-- they do not a saw-core typechecking error will be raised.
refinementTermH :: Term -> Term -> MRM t Term
refinementTermH t1 t2 =
  do (EvTerm ev, tp1) <- fromJust . asSpecM <$> mrTypeOf t1
     (EvTerm  _, tp2) <- fromJust . asSpecM <$> mrTypeOf t2
     -- FIXME: Add a direct way to check that the types are related, instead of
     -- calling 'mrRelTerm' on dummy variables and ignoring the result
     withUVarLift "ret_val" (Type tp1) (tp1,tp2) $ \x1 (tp1',tp2') ->
       withUVarLift "ret_val" (Type tp2') (tp1',tp2',x1) $ \x2 (tp1'',tp2'',x1') ->
         do tp1''' <- mrSubstEVars tp1''
            tp2''' <- mrSubstEVars tp2''
            void $ mrRelTerm Nothing tp1''' x1' tp2''' x2
     rr <- liftSC2 scGlobalApply "SpecM.eqRR" [tp1]
     ref_tm <- liftSC2 scGlobalApply "SpecM.refinesS" [ev, tp1, tp1, rr, t1, t2]
     uvars <- mrUVarsOuterToInner
     liftSC2 scPiList uvars ref_tm

-- | Build the proposition stating that one function term refines another, after
-- quantifying over all the given arguments as well as any additional arguments
-- needed to fully apply the given terms, and adding any calls to @assertS@ on
-- the right hand side needed for unifying the arguments generated when fully
-- applying the given terms
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
    do tp1 <- liftSC1 scTypeOf t1 >>= mrNormOpenTerm
       tp2 <- liftSC1 scTypeOf t2 >>= mrNormOpenTerm
       mrRefinesFunH refinementTermH [] tp1 t1 tp2 t2
