{- |
Module      : SAWCore.Term.CtxTerm
Copyright   : Galois, Inc. 2018
License     : BSD3
Stability   : experimental
Portability : non-portable (language extensions)
-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module SAWCore.Term.CtxTerm
  (
    -- * Operations on Terms-in-Context
    MonadTerm(..)
  , ctxLambda, ctxPi, ctxPi1
    -- * Constructor Argument Types
  , CtorArg(..), CtorArgStruct(..), ctxCtorType
    -- * Computing with Eliminators
  , mkPRetTp
  , ctxCtorElimType, mkCtorElimTypeFun
  , ctxReduceRecursor
    -- * Parsing and Building Constructor Types
  , mkCtorArgStruct
  ) where

import Control.Monad
import Control.Monad.Trans

import SAWCore.Name
import SAWCore.Recognizer
import SAWCore.Term.Functor


--
-- * Terms In Context
--

-- | Get the head and tail of a non-empty '[Term]' list
ctxTermsCtxHeadTail :: [Term] -> ([Term], Term)
ctxTermsCtxHeadTail as = (init as, last as)

-- | Take a list of terms and match them up with a sequence of bindings,
-- returning a structured '[Term]' list.
ctxTermsForBindings :: [(LocalName, tp)] -> [Term] -> Maybe [Term]
ctxTermsForBindings bs ts
  | length bs == length ts = Just ts
  | otherwise = Nothing

splitCtxTermsCtx :: [(LocalName, tp)] ->
                    [Term] ->
                    ([Term], [Term])
splitCtxTermsCtx ctx terms =
  splitAt (length terms - length ctx) terms

--
-- * Operations on Terms-in-Context
--

-- | The class of monads that can build terms and substitute into them
class Monad m => MonadTerm m where
  mkTermF :: TermF Term -> m Term
  liftTerm :: DeBruijnIndex -> DeBruijnIndex -> Term -> m Term
  whnfTerm :: Term -> m Term
  substTerm :: DeBruijnIndex -> [Term] -> Term -> m Term
               -- ^ NOTE: the first term in the list is substituted for the most
               -- recently-bound variable, i.e., deBruijn index 0

instance (MonadTerm m, MonadTrans t, Monad (t m)) => MonadTerm (t m) where
  mkTermF = lift . mkTermF
  liftTerm n i t = lift $ liftTerm n i t
  whnfTerm = lift . whnfTerm
  substTerm n s t = lift $ substTerm n s t

-- | Build a 'Term' from a 'FlatTermF' in a 'MonadTerm'
mkFlatTermF :: MonadTerm m => FlatTermF Term -> m Term
mkFlatTermF = mkTermF . FTermF

-- | Build a free variable as a 'Term'
ctxVar :: MonadTerm m => [(LocalName, tp)] -> m Term
ctxVar ctx = mkTermF (LocalVar $ length ctx)

-- | Build a list of all the free variables as 'Term's
ctxVars :: MonadTerm m => [(LocalName, tp)] -> m [Term]
ctxVars ctx_top =
  helper ctx_top []
      where
        helper :: MonadTerm m => [(LocalName, tp)] -> [(LocalName, tp)] -> m [Term]
        helper [] _ = return []
        helper vars_ctx ctx =
          snoc <$> helper (init vars_ctx) (last vars_ctx : ctx) <*> ctxVar ctx
        snoc xs x = xs ++ [x]

-- | Build two lists of the free variables, split at a specific point
ctxVars2 :: MonadTerm m => [(LocalName, tp)] ->
            [(LocalName, tp)] ->
            m ([Term], [Term])
ctxVars2 vars1 vars2 =
  splitCtxTermsCtx vars2 <$> ctxVars (vars1 ++ vars2)

-- | Build a 'Term' for a 'Sort'
ctxSort :: MonadTerm m => Sort -> m Term
ctxSort s = mkFlatTermF (Sort s noFlags)

-- | Apply two 'Term's
ctxApply :: MonadTerm m => m Term -> m Term -> m Term
ctxApply fm argm =
  do f <- fm
     arg <- argm
     mkTermF (App f arg)

-- | Apply a 'Term' to a list of arguments
ctxApplyMulti :: MonadTerm m =>
                 m Term ->
                 m [Term] ->
                 m Term
ctxApplyMulti fm argsm =
  fm >>= \f -> argsm >>= \args -> helper f args
  where
    helper :: MonadTerm m => Term -> [Term] -> m Term
    helper f [] = return f
    helper f (arg : args) =
      do f' <- ctxApply (return f) (return arg)
         helper f' args

-- | Form a lambda-abstraction as a 'Term'
ctxLambda1 :: MonadTerm m => LocalName -> Term ->
              (Term -> m Term) ->
              m Term
ctxLambda1 x tp body_f =
  do var <- ctxVar []
     body <- body_f var
     mkTermF (Lambda x tp body)

-- | Form a multi-arity lambda-abstraction as a 'Term'
ctxLambda :: MonadTerm m => [(LocalName, Term)] ->
             ([Term] -> m Term) -> m Term
ctxLambda [] body_f = body_f []
ctxLambda ((x, tp) : xs) body_f =
  ctxLambda1 x tp $ \_ ->
  ctxLambda xs $ \vars ->
  do var <- ctxVar xs
     body_f (var : vars)

-- | Form a pi-abstraction as a 'Term'
ctxPi1 :: MonadTerm m => LocalName -> Term ->
          (Term -> m Term) -> m Term
ctxPi1 x tp body_f =
  do var <- ctxVar []
     body <- body_f var
     mkTermF (Pi x tp body)

-- | Form a multi-arity pi-abstraction as a 'Term'
ctxPi :: MonadTerm m => [(LocalName, Term)] ->
         ([Term] -> m Term) -> m Term
ctxPi [] body_f = body_f []
ctxPi ((x, tp) : xs) body_f =
  ctxPi1 x tp $ \_ ->
  ctxPi xs $ \vars ->
  do var <- ctxVar xs
     body_f (var : vars)

-- | Build an application of a datatype as a 'Term'
ctxDataTypeM ::
  forall m.
  MonadTerm m =>
  Name ->
  m [Term] ->
  m [Term] ->
  m Term
ctxDataTypeM d paramsM ixsM =
  ctxApplyMulti (ctxApplyMulti t paramsM) ixsM
  where
    t :: m Term
    t = mkTermF (Constant d)

-- | Test if a 'Term' is an application of a specific datatype with the
-- supplied context of parameters and indices
ctxAsDataTypeApp :: Name -> [(LocalName, tp1)] ->
                    [(LocalName, tp2)] -> Term ->
                    Maybe ([Term], [Term])
ctxAsDataTypeApp d params ixs t =
  do let (f, args) = asApplyAll t
     d' <- asConstant f
     guard (d == d')
     guard (length args == length params + length ixs)
     let (params', ixs') = splitAt (length params) args
     params_ret <- ctxTermsForBindings params params'
     ixs_ret <- ctxTermsForBindings ixs ixs'
     pure (params_ret, ixs_ret)


-- | Build an application of a constructor as a 'Term'
ctxCtorAppM ::
  forall m.
  MonadTerm m =>
  Name ->
  ExtCns Term ->
  m [Term] ->
  m [Term] ->
  m Term
ctxCtorAppM _d c paramsM argsM =
  ctxApplyMulti (ctxApplyMulti t paramsM) argsM
  where
    t :: m Term
    t = mkTermF (Constant (Name (ecVarIndex c) (ecName c)))

ctxRecursorAppM :: MonadTerm m =>
  m Term ->
  m [Term] ->
  m Term ->
  m Term
ctxRecursorAppM recM ixsM argM =
  do app <- RecursorApp <$> recM <*> ixsM <*> argM
     mkFlatTermF app

--
-- * Generalized Lifting and Substitution
--

-- | The class of "in-context" types that support lifting and substitution
class Monad m => CtxLiftSubst f m where
  -- | Lift an @f@ into an extended context
  ctxLift :: DeBruijnIndex -> DeBruijnIndex -> f -> m f
  -- | Substitute a list of terms into an @f@
  ctxSubst :: [Term] -> DeBruijnIndex -> f -> m f

instance MonadTerm m => CtxLiftSubst Term m where
  ctxLift i j t = liftTerm i j t
  ctxSubst subst i t =
    -- NOTE: our term lists put the least recently-bound variable first, so we
    -- have to reverse here to call substTerm, which wants the term for the most
    -- recently-bound variable first
    substTerm i (reverse subst) t

instance MonadTerm m => CtxLiftSubst [Term] m where
  ctxLift i j ts = traverse (ctxLift i j) ts
  ctxSubst subst i ts = traverse (ctxSubst subst i) ts

instance CtxLiftSubst tp m => CtxLiftSubst [(LocalName, tp)] m where
  ctxLift _ _ [] = return []
  ctxLift i j ((x, x_tp) : bs) =
    (\t -> (:) (x, t)) <$> ctxLift i j x_tp <*>
    ctxLift (i + 1) j bs
  ctxSubst _ _ [] = return []
  ctxSubst subst i ((x, x_tp) : bs) =
    (\t -> (:) (x, t)) <$> ctxSubst subst i x_tp <*>
    ctxSubst subst (i + 1) bs

instance MonadTerm m => CtxLiftSubst CtorArg m where
  ctxLift i j (ConstArg tp) = ConstArg <$> ctxLift i j tp
  ctxLift i j (RecursiveArg zs ixs) =
    RecursiveArg <$> ctxLift i j zs <*>
    ctxLift (i + length zs) j ixs
  ctxSubst subst i (ConstArg tp) = ConstArg <$> ctxSubst subst i tp
  ctxSubst subst i (RecursiveArg zs ixs) =
    RecursiveArg <$> ctxSubst subst i zs <*>
    ctxSubst subst (i + length zs) ixs


--
-- * Constructor Argument Types
--

-- | A specification of the type of an argument for a constructor of datatype
-- @d@, that has a specified list @ixs@ of indices, inside a context @ctx@ of
-- parameters and earlier arguments
data CtorArg where
  -- | A fixed, constant type
  ConstArg :: Term -> CtorArg
  -- | The construct @'RecursiveArg [(z1,tp1),..,(zn,tpn)] [e1,..,ek]'@
  -- specifies a recursive argument type of the form
  --
  -- > (z1::tp1) -> .. -> (zn::tpn) -> d p1 .. pm e1 .. ek
  --
  -- where @d@ is the datatype, the @zi::tpi@ are the elements of the Pi
  -- context (the first argument to 'RecursiveArgType'), the @pi@ are the
  -- parameters of @d@ (not given here), and the @ei@ are the type indices of
  -- @d@.
  RecursiveArg ::
    [(LocalName, Term)] ->
    [Term] ->
    CtorArg

-- | A structure that defines the parameters, arguments, and return type indices
-- of a constructor, using 'Term' and friends to get the bindings right
data CtorArgStruct =
  CtorArgStruct
  {
    ctorParams :: [(LocalName, Term)],
    ctorArgs :: [(LocalName, CtorArg)],
    ctorIndices :: [Term],
    dataTypeIndices :: [(LocalName, Term)]
  }


-- | Convert a 'CtorArg' into the type that it represents, given a context of
-- the parameters and of the previous arguments
ctxCtorArgType :: MonadTerm m => Name ->
                  [(LocalName, Term)] ->
                  [(LocalName, Term)] ->
                  CtorArg ->
                  m Term
ctxCtorArgType _ _ _ (ConstArg tp) = return tp
ctxCtorArgType d params prevs (RecursiveArg zs_ctx ixs) =
  ctxPi zs_ctx $ \_ ->
  ctxDataTypeM d ((fst <$> ctxVars2 params prevs) >>= ctxLift 0 (length zs_ctx))
  (return ixs)

-- | Convert a bindings list of 'CtorArg's to a binding list of types
ctxCtorArgBindings :: MonadTerm m => Name ->
                      [(LocalName, Term)] ->
                      [(LocalName, Term)] ->
                      [(LocalName, CtorArg)] ->
                      m [(LocalName, Term)]
ctxCtorArgBindings _ _ _ [] = return []
ctxCtorArgBindings d params prevs ((x, arg) : args) =
  do tp <- ctxCtorArgType d params prevs arg
     rest <- ctxCtorArgBindings d params (prevs ++ [(x, tp)]) args
     return ((x, tp) : rest)

-- | Compute the type of a constructor from the name of its datatype and its
-- 'CtorArgStruct'
ctxCtorType :: MonadTerm m => Name -> CtorArgStruct -> m Term
ctxCtorType d (CtorArgStruct{..}) =
  (ctxPi ctorParams $ \params ->
    do bs <-
         ctxCtorArgBindings d ctorParams
         [] ctorArgs
       ctxPi bs $ \_ ->
         ctxDataTypeM d
         (ctxLift 0 (length bs) params)
         (return ctorIndices))


--
-- * Computing with Eliminators
--

-- | Build the type of the @p_ret@ function, also known as the "motive"
-- function, of a recursor on datatype @d@. This type has the form
--
-- > (i1::ix1) -> .. -> (im::ixm) -> d p1 .. pn i1 .. im -> s
--
-- where the @pi@ are free variables for the parameters of @d@, the @ixj@
-- are the indices of @d@, and @s@ is any sort supplied as an argument.
ctxPRetTp :: MonadTerm m => Name ->
             [(LocalName, Term)] ->
             [(LocalName, Term)] -> Sort ->
             m Term
ctxPRetTp d params ixs s =
  ctxPi ixs $ \ix_vars ->
  do param_vars <- ctxVars params
     dt <- ctxDataTypeM d (ctxLift 0 (length ixs) param_vars)
       (return ix_vars)
     ctxPi1 "_" dt $ \_ -> ctxSort s

-- | Like 'ctxPRetTp', but also take in a list of parameters and substitute them
-- for the parameter variables returned by that function
mkPRetTp :: MonadTerm m =>
  Name ->
  [(LocalName, Term)] ->
  [(LocalName, Term)] ->
  [Term] ->
  Sort ->
  m Term
mkPRetTp d untyped_p_ctx untyped_ix_ctx untyped_params s =
  case untyped_p_ctx of
    p_ctx ->
      case (untyped_ix_ctx,
            ctxTermsForBindings p_ctx untyped_params) of
        (ix_ctx, Just params) ->
          do p_ret <- (ctxPRetTp d
                       p_ctx ix_ctx s)
             ctxSubst params 0
               (castPRet p_ctx p_ret)
        (_, Nothing) ->
          error "mkPRetTp: incorrect number of parameters"
  where
    castPRet :: [(LocalName, tp)] -> Term -> Term
    castPRet _ctx = id


-- | Compute the type of an eliminator function for a constructor from the name
-- of its datatype, its name, and its 'CtorArgStruct'. This type has, as free
-- variables, both the parameters of the datatype and a "motive" function from
-- indices of the datatype to a return type. It is of the form
--
-- > (x1::arg1) -> maybe (rec1::rec_tp1) -> .. ->
-- > (xn::argn) -> maybe (recn::rec_tpn) ->
-- >   p_ret ix_1 .. ix_k (ctor params x1 .. xn)
--
-- where the ixs are the type indices of the return type for the constructor,
-- the (xi::argi) are the arguments of the constructor, and the @maybe@s
-- indicate additional arguments that are present only for arguments of
-- recursive type, that is, where @argi@ has the form
--
-- > (z1::Z1) -> .. -> (zm::Zm) -> d params t1 .. tk
--
-- In this case, @rec_tpi@ has the form
--
-- > (z1::Z1) -> .. -> (zm::Zm) -> p_ret t1 .. tk (f z1 .. zm)
--
-- Note that the output type cannot be expressed in the type of this function,
-- since it depends on fields of the 'CtorArgStruct', so, instead, the result is
-- just casted to whatever type the caller specifies.
ctxCtorElimType :: MonadTerm m =>
  Name ->
  ExtCns Term ->
  CtorArgStruct ->
  m Term
ctxCtorElimType d_top c
  (CtorArgStruct{..}) =
  (do let params = ctorParams
      -- NOTE: we use propSort for the type of p_ret just as arbitrary sort, but
      -- it doesn't matter because p_ret_tp is only actually used to form
      -- contexts, and is never actually used directly in the output
      p_ret_tp <- ctxPRetTp d_top params dataTypeIndices propSort

      -- Lift the argument and return indices into the context of p_ret
      args <- ctxLift 0 1 ctorArgs
      ixs <-
        ctxLift (length ctorArgs) 1
        ctorIndices
      -- Form the context (params ::> p_ret)
      let params_pret = params ++ [("_", p_ret_tp)]
      -- Call the helper and cast the result to (Typ ret)
      helper d_top params_pret [] args ixs
  ) where

  -- Iterate through the argument types of the constructor, building up a
  -- function from those arguments to the result type of the p_ret function.
  -- Note that, technically, this function also takes in recursive calls, so has
  -- a slightly richer type, but we are not going to try to compute this richer
  -- type in Haskell land.
  helper :: MonadTerm m =>
    Name ->
    [(LocalName, Term)] ->
    [(LocalName, Term)] ->
    [(LocalName, CtorArg)] ->
    [Term] ->
    m Term
  helper d params_pret prevs [] ret_ixs =
    -- If we are finished with our arguments, construct the final result type
    -- (p_ret ret_ixs (c params prevs))
    do (vars, prev_vars) <- ctxVars2 params_pret prevs
       let (param_terms, p_ret) = ctxTermsCtxHeadTail vars
       ctxApply (ctxApplyMulti (return p_ret) (return ret_ixs)) $
         ctxCtorAppM d c (return param_terms) (return prev_vars)
  helper d params_pret prevs ((str, ConstArg tp) : args) ixs =
    -- For a constant argument type, just abstract it and continue
    (ctxPi [(str, tp)] $ \_ ->
      helper d params_pret (prevs ++ [(str, tp)]) args ixs)
  helper d params_pret
    prevs ((str, RecursiveArg zs ts) : args) ixs =
    -- For a recursive argument type of the form
    --
    -- (z1::Z1) -> .. -> (zm::Zm) -> d params t1 .. tk
    --
    -- form the type abstraction
    --
    -- (arg:: (z1::Z1) -> .. -> (zm::Zm) -> d params t1 .. tk) ->
    -- (ih :: (z1::Z1) -> .. -> (zm::Zm) -> p_ret t1 .. tk (arg z1 .. zm)) ->
    -- rest
    --
    -- where rest is the result of a recursive call
    do
      -- Build terms for the params and p_ret variables
      (param_vars, p_ret) <-
        ctxTermsCtxHeadTail <$> fst <$> ctxVars2 params_pret prevs
      -- Build the type of the argument arg
      arg_tp <- ctxPi zs (\_ -> ctxDataTypeM d
                                (ctxLift 0 (length zs) param_vars)
                                (return ts))
      -- Lift zs and ts into the context of arg
      zs' <- ctxLift 0 1 zs
      ts' <- ctxLift (length zs) 1 ts
      -- Build the pi-abstraction for arg
      ctxPi1 str arg_tp $ \arg ->
        do rest <-
             helper d params_pret (prevs ++ [(str, arg_tp)]) args ixs
           -- Build the type of ih, in the context of arg
           ih_tp <- ctxPi zs' $ \z_vars ->
             ctxApply
             (ctxApplyMulti
              (ctxLift 0 (length zs' + 1) p_ret) (return ts'))
             (ctxApplyMulti (ctxLift 0 (length zs') arg) (return z_vars))
           -- Finally, build the pi-abstraction for ih around the rest
           --
           -- NOTE: we cast away the IH argument, because that is a type that is
           -- computed from the argument structure, and we cannot (well, we
           -- could, but it would be much more work to) express that computation
           -- in the Haskell type system
           (ctxPi1 "_" ih_tp $ \_ ->
               ctxLift 0 1 rest)

-- | Build a function that substitutes parameters and a @p_ret@ return type
-- function into the type of an eliminator, as returned by 'ctxCtorElimType',
-- for the given constructor. We return the substitution function in the monad
-- so that we only call 'ctxCtorElimType' once but can call the function many
-- times, in order to amortize the overhead of 'ctxCtorElimType'.
mkCtorElimTypeFun :: MonadTerm m =>
  Name {- ^ data type -} ->
  ExtCns Term {- ^ constructor type -} ->
  CtorArgStruct ->
  m ([Term] -> Term -> m Term)
mkCtorElimTypeFun d c argStruct@(CtorArgStruct {..}) =
  do ctxElimType <- ctxCtorElimType d c argStruct
     return $ \params p_ret ->
         whnfTerm =<<
         case ctxTermsForBindings ctorParams params of
           Nothing -> error "ctorElimTypeFun: wrong number of parameters!"
           Just paramsCtx ->
             ctxSubst
             (paramsCtx ++ [p_ret])
             0 ctxElimType


-- | Reduce an application of a recursor to a particular constructor.
-- This is known in the Coq literature as an iota reduction. More specifically,
-- the call
--
-- > ctxReduceRecursor rec f_c [x1, .., xk]
--
-- reduces the term @(RecursorApp rec ixs (CtorApp c ps xs))@ to
--
-- > f_c x1 (maybe rec_tm_1) .. xk (maybe rec_tm_k)
--
-- where @f_c@ is the eliminator function associated to the constructor @c@ by the
-- recursor value @rec@.  Here @maybe rec_tm_i@ indicates an optional recursive call
-- of the recursor on one of the @xi@. These recursive calls only exist for those
-- arguments @xi@ that are recursive arguments, i.e., that are specified with
-- 'RecursiveArg', and are omitted for non-recursive arguments specified by 'ConstArg'.
--
-- Specifically, for a @'RecursiveArg' zs ixs@ argument @xi@, which has type
-- @\(z1::Z1) -> .. -> d p1 .. pn ix1 .. ixp@, we build the recursive call
--
-- > \(z1::[xs/args]Z1) -> .. ->
-- >   RecursorApp rec [xs/args]ixs (xi z1 ... zn)
--
-- where @[xs/args]@ substitutes the concrete values for the earlier
-- constructor arguments @xs@ for the remaining free variables.

ctxReduceRecursor :: forall m.
  MonadTerm m =>
  Term {- ^ abstracted recursor -} ->
  Term {- ^ constructor elimnator function -} ->
  [Term] {- ^ constructor arguments -} ->
  CtorArgStruct {- ^ constructor formal argument descriptor -} ->
  m Term
ctxReduceRecursor rec elimf c_args CtorArgStruct{..} =
  case ctxTermsForBindings ctorArgs c_args of
     Just argsCtx ->
       ctxReduceRecursor_ rec elimf argsCtx ctorArgs
     Nothing ->
       error "ctxReduceRecursorRaw: wrong number of constructor arguments!"


-- | This operation does the real work of building the
--   iota reduction for @ctxReduceRecursor@.  We assume
--   the input terms we are given live in an ambient
--   context @amb@.
ctxReduceRecursor_ :: forall m.
  MonadTerm m =>
  Term     {- ^ recursor value eliminatiting data type d -}->
  Term     {- ^ eliminator function for the constructor -} ->
  [Term]    {- ^ constructor actual arguments -} ->
  [(LocalName, CtorArg)]
    {- ^ telescope describing the constructor arguments -} ->
  m Term
ctxReduceRecursor_ rec fi args0 argCtx =
  do args <- mk_args [] args0 argCtx
     whnfTerm =<< foldM (\f arg -> mkTermF $ App f arg) fi args

 where
    mk_args :: [Term] ->  -- already processed parameters/arguments
               [Term] ->     -- remaining actual arguments to process
               [(LocalName, CtorArg)] ->
                 -- telescope for typing the actual arguments
               m [Term]
    -- no more arguments to process
    mk_args _ _ [] = return []

    -- process an argument that is not a recursive call
    mk_args pre_xs (x : xs) ((_, ConstArg _) : args) =
      do tl <- mk_args (pre_xs ++ [x]) xs args
         pure (x : tl)

    -- process an argument that is a recursive call
    mk_args pre_xs (x : xs) ((_, RecursiveArg zs ixs) : args) =
      do zs'  <- ctxSubst pre_xs 0 zs
         ixs' <- ctxSubst pre_xs (length zs) ixs
         recx <- mk_rec_arg zs' ixs' x
         tl   <- mk_args (pre_xs ++ [x]) xs args
         pure (x : recx : tl)

    mk_args _ _ _ = error "mk_args: impossible"

    -- Build an individual recursive call, given the parameters, the bindings
    -- for the RecursiveArg, and the argument we are going to recurse on
    mk_rec_arg ::
      [(LocalName, Term)] ->                -- telescope describing the zs
      [Term] ->                        -- actual values for the indices, shifted under zs
      Term ->                         -- actual value in recursive position
      m Term
    mk_rec_arg zs_ctx ixs x =
      -- eta expand over the zs and apply the RecursorApp form
      ctxLambda zs_ctx (\zs ->
        ctxRecursorAppM
          (ctxLift 0 (length zs_ctx) rec)
          (return ixs)
          (ctxApplyMulti
            (ctxLift 0 (length zs_ctx) x)
            (return zs)))


--
-- * Parsing and Building Constructor Types
--

-- | Generic method for testing whether a datatype occurs in an object
class UsesDataType a where
  usesDataType :: Name -> a -> Bool

instance UsesDataType (TermF Term) where
  usesDataType d (Constant d')
    | d' == d = True
--  usesDataType d (FTermF (DataTypeApp d' _ _))
--    | d' == d = True
  usesDataType d (FTermF (RecursorType d' _ _ _))
    | d' == d = True
  usesDataType d (FTermF (Recursor rec))
    | recursorDataType rec == d = True
  usesDataType d tf = any (usesDataType d) tf

instance UsesDataType Term where
  usesDataType d = usesDataType d . unwrapTermF

instance UsesDataType [(LocalName, Term)] where
  usesDataType _ [] = False
  usesDataType d ((_, tp) : tps) = usesDataType d tp || usesDataType d tps


-- | Check that a type is a valid application of datatype @d@ for use in
-- specific ways in the type of a constructor for @d@. This requires that this
-- application of @d@ be of the form
--
-- > d p1 .. pn x1 .. xm
--
-- where the @pi@ are the distinct bound variables bound in the @params@
-- context, given as argument, and that the @xj@ have no occurrences of @d@. If
-- the given type is of this form, return the @xj@.
asCtorDTApp :: Name -> [(LocalName, Term)] ->
               [(LocalName, Term)] ->
               [(LocalName, tp1)] ->
               [(LocalName, tp2)] ->
               Term ->
               Maybe [Term]
asCtorDTApp d params dt_ixs ctx1 ctx2 (ctxAsDataTypeApp d params dt_ixs ->
                                       Just (param_vars, ixs))
  | isVarList params ctx1 ctx2 param_vars &&
    not (any (usesDataType d) ixs)
  = Just ixs
  where
    -- Check that the given list of terms is a list of bound variables, one for
    -- each parameter, in the context extended by the given arguments
    isVarList :: [(LocalName, tp1)] ->
                 [(LocalName, tp2)] ->
                 [(LocalName, tp3)] ->
                 [Term] ->
                 Bool
    isVarList _ _ _ [] = True
    isVarList (_ : ps) c1 c2 ((unwrapTermF -> LocalVar i) : ts) =
      i == length ps + length c1 + length c2 &&
      isVarList ps c1 c2 ts
    isVarList _ _ _ _ = False
asCtorDTApp _ _ _ _ _ _ = Nothing


-- | Check that an argument for a constructor has one of the allowed forms
asCtorArg :: Name -> [(LocalName, Term)] ->
             [(LocalName, Term)] ->
             [(LocalName, tp)] ->
             Term ->
             Maybe CtorArg
asCtorArg d params dt_ixs prevs (asPiList ->
                                 (zs,
                                  asCtorDTApp d params dt_ixs prevs zs ->
                                  Just ixs))
  | not (usesDataType d zs)
  = Just (RecursiveArg zs ixs)
asCtorArg d _ _ _ tp
  | not (usesDataType d tp)
  = Just (ConstArg tp)
asCtorArg _ _ _ _ _ = Nothing

-- | Check that a constructor type is a pi-abstraction that takes as input an
-- argument of one of the allowed forms described by 'CtorArg'
asPiCtorArg :: Name -> [(LocalName, Term)] ->
               [(LocalName, Term)] ->
               [(LocalName, tp)] ->
               Term ->
               Maybe (LocalName, CtorArg, Term)
asPiCtorArg d params dt_ixs prevs (asPi ->
                                   Just (x,
                                         asCtorArg d params dt_ixs prevs ->
                                          Just arg, rest)) =
  Just (x, arg, rest)
asPiCtorArg _ _ _ _ _ = Nothing

-- | Helper function for 'mkCtorArgStruct'
mkCtorArgsIxs :: Name -> [(LocalName, Term)] ->
                 [(LocalName, Term)] ->
                 [(LocalName, CtorArg)] ->
                 Term ->
                 Maybe ([(LocalName, CtorArg)], [Term])
mkCtorArgsIxs d params dt_ixs prevs (asPiCtorArg d params dt_ixs prevs ->
                                     Just (x, arg, rest)) =
  case mkCtorArgsIxs d params dt_ixs (prevs ++ [(x, arg)]) rest of
    Just (args, ixs) -> Just ((x, arg) : args, ixs)
    Nothing -> Nothing
mkCtorArgsIxs d params dt_ixs prevs (asCtorDTApp d params dt_ixs prevs [] ->
                                     Just ixs) =
  Just ([], ixs)
mkCtorArgsIxs _ _ _ _ _ = Nothing


-- | Take in a datatype and bindings lists for its parameters and indices, and
-- also a prospective type of a constructor for that datatype, where the
-- constructor type is allowed to have the parameters but not the indices free.
-- Test that the constructor type is an allowed type for a constructor of this
-- datatype, and, if so, build a 'CtorArgStruct' for it.
mkCtorArgStruct ::
  Name ->
  [(LocalName, Term)] ->
  [(LocalName, Term)] ->
  Term ->
  Maybe CtorArgStruct
mkCtorArgStruct d params dt_ixs ctor_tp =
  case mkCtorArgsIxs d params dt_ixs [] ctor_tp of
    Just (args, ctor_ixs) ->
      Just (CtorArgStruct params args ctor_ixs dt_ixs)
    Nothing -> Nothing
