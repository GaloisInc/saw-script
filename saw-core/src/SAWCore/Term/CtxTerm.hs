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
    -- * Contexts and Bindings
    Bindings(..), bindingsLength, InvBindings(..)
  , invAppendBindings, invertBindings
    -- * Terms in Context
  , CtxTerm(..), CtxTerms(..), CtxTermsCtx(..)
  , mkClosedTerm, mkClosedTyp, elimClosedTerm
  , ExistsTp(..), ctxBindingsOfTerms
  , ctxTermsForBindings
    -- * Operations on Terms-in-Context
  , MonadTerm(..)
  , ctxLambda, ctxPi, ctxPi1
    -- * Generalized Lifting and Substitution
  , CtxLiftSubst(..), ctxLift1, ctxLiftInBindings
  , mkLiftedClosedTerm
    -- * Constructor Argument Types
  , CtorArg(..), CtorArgStruct(..), ctxCtorArgType, ctxCtorType
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
-- * Contexts and Bindings
--

-- | A sequence of bindings of pairs of a variable name and a type of some form
-- for that variable. These bindings are relative to ambient context @ctx@, use
-- @tp@ for the variable types, and bind variables whose types are listed in
-- @as@.
--
-- Note that each type in a bindings list has type 'Typ', but is "represented"
-- by a Haskell type @a@ in the 'Bind' constructor. There is no way to actually
-- related the Haskell type @a@ to the type it "represents", so we do not try,
-- and just write "represent" in quotes.
data Bindings tp where
  NoBind :: Bindings tp
  Bind :: LocalName -> tp -> Bindings tp ->
          Bindings tp

-- | Compute the number of bindings in a bindings list
bindingsLength :: Bindings tp -> Int
bindingsLength NoBind = 0
bindingsLength (Bind _ _ bs) = 1 + bindingsLength bs

-- | An inverted list of bindings, seen from the "inside out"
data InvBindings tp where
  InvNoBind :: InvBindings tp
  InvBind :: InvBindings tp -> LocalName -> tp -> InvBindings tp

-- | Compute the number of bindings in an inverted bindings list
invBindingsLength :: InvBindings tp -> Int
invBindingsLength InvNoBind = 0
invBindingsLength (InvBind bs _ _) = 1 + invBindingsLength bs

-- | Map over all types in an inverted bindings list
mapInvBindings :: (f -> g) -> InvBindings f -> InvBindings g
mapInvBindings _ InvNoBind = InvNoBind
mapInvBindings f (InvBind ctx x tp) =
  InvBind (mapInvBindings f ctx) x (f tp)

ctxLiftNil :: InvBindings tp -> f -> f
ctxLiftNil _ctx f = f

-- | Append a 'Bindings' list to an inverted 'InvBindings' list, inverting the
-- former as we go to yield an inverted 'InvBindings' list. Intuitively, this
-- means we are already "inside" the inverted bindings lists, and we are moving
-- further "inside" the regular bindings list; at the end we will be "inside"
-- both, meaning that we will see the combination "from the inside".
invAppendBindings :: InvBindings tp ->
                     Bindings tp ->
                     InvBindings tp
invAppendBindings as NoBind = as
invAppendBindings as (Bind y y_tp bs) =
  (invAppendBindings (InvBind as y y_tp) bs)

-- | Invert a 'Bindings' list; i.e., move "inside" those bindings
invertBindings :: Bindings tp -> InvBindings tp
invertBindings = invAppendBindings InvNoBind

-- | Append two inverted contexts, where the first one is top-level. This
-- restriction allows us to avoid writing a proof of associativity of '(<+>)',
-- and instead just using 'ctxAppNilEq'
appendTopInvBindings :: InvBindings tp ->
                        InvBindings tp ->
                        InvBindings tp
appendTopInvBindings ctx1 InvNoBind = ctx1
appendTopInvBindings ctx1 (InvBind ctx2 x tp) =
  let ret = appendTopInvBindings ctx1 ctx2 in
  InvBind ret x (ctxLiftNil ret tp)

--
-- * Terms In Context
--

-- | A 'Term' with a given "type" relative to a given context. Since we cannot
-- hope to represent dependent type theory in Haskell types anyway, these
-- "types" are usually instantiated with a dummy, such as '()', but the code
-- that consumes them cannot know that and has to be agnostic to what type it
-- is.
newtype CtxTerm = CtxTerm Term

-- | Convert a 'CtxTerm' to an untyped term. This is "unsafe" because it throws
-- away our typing information.
unCtxTermUnsafe :: CtxTerm -> Term
unCtxTermUnsafe (CtxTerm t) = t

-- | Because we cannot capture the SAW type system in Haskell, sometimes we have
-- to cast our terms. We try not to use this very often, and we only allow
-- casting the output type, not the context, since the latter could screw up our
-- deBruijn indices.
castCtxTerm :: CtxTerm -> CtxTerm
castCtxTerm (CtxTerm t) = CtxTerm t

-- | Build a term in the empty context
mkClosedTerm :: Term -> CtxTerm
mkClosedTerm = CtxTerm

-- | Build a term to represent a type in the empty context
mkClosedTyp :: Term -> CtxTerm
mkClosedTyp = mkClosedTerm

-- | Take a term out of the empty context
elimClosedTerm :: CtxTerm -> Term
elimClosedTerm (CtxTerm t) = t

-- | Existentially quantify over the "type" of an object
data ExistsTp tp = ExistsTp tp

-- | Build a 'Bindings' list from a list of variable names and types, assuming
-- that each variable is free in the remaining types and that @ctx@ describes
-- the ambient context of the top-level type in the context. Note that nothing
-- here ensures that the Haskell-level types used to "represent" the bindings
-- created by this function have anything to do with the actual SAW types, but
-- the Haskell type system is not powerful enough to represent all the SAW types
-- anyway, and any code that consumes this 'Bindings' list cannot know that
-- anyway. See also the comments for 'CtxTerm'.
ctxBindingsOfTerms :: [(LocalName, Term)] -> ExistsTp (Bindings CtxTerm)
ctxBindingsOfTerms [] = ExistsTp NoBind
ctxBindingsOfTerms ((x,tp):ctx) =
  case ctxBindingsOfTerms ctx of
    ExistsTp rest -> ExistsTp (Bind x (CtxTerm tp) rest)

-- | A dummy unit type that takes in a context
data CtxUnit ctx a = CtxUnit

-- | An 'Either' type relative to a context and type
newtype CtxEither f g = CtxEither (Either f g)

-- | A list of terms in a given context
data CtxTerms where
  CtxTermsNil :: CtxTerms
  CtxTermsCons :: CtxTerm -> CtxTerms -> CtxTerms

-- | A list of terms in a given context, stored "inside-out"
data CtxTermsCtx where
  CtxTermsCtxNil :: CtxTermsCtx
  CtxTermsCtxCons :: CtxTermsCtx -> CtxTerm -> CtxTermsCtx

{-
-- | Get the head and tail of a non-empty 'CtxTerms' list
ctxTermsHeadTail :: CtxTerms -> (CtxTerm, CtxTerms)
ctxTermsHeadTail (CtxTermsCons a as) = (a, as)
-}

-- | Get the head and tail of a non-empty 'CtxTermsCtx' list
ctxTermsCtxHeadTail :: CtxTermsCtx -> (CtxTermsCtx, CtxTerm)
ctxTermsCtxHeadTail (CtxTermsCtxCons as a) = (as, a)
ctxTermsCtxHeadTail CtxTermsCtxNil = error "ctxTermCtxHeadTail: unexpected CtxTermsCtxNil"

-- | Convert a typed list of terms to a list of untyped terms; this is "unsafe"
-- because it throws away our typing information
ctxTermsToListUnsafe :: CtxTerms -> [Term]
ctxTermsToListUnsafe CtxTermsNil = []
ctxTermsToListUnsafe (CtxTermsCons (CtxTerm t) ts) =
  t : ctxTermsToListUnsafe ts

-- | Convert a typed list of terms to a list of untyped terms; this is "unsafe"
-- because it throws away our typing information
ctxTermsCtxToListUnsafe :: CtxTermsCtx -> [Term]
ctxTermsCtxToListUnsafe CtxTermsCtxNil = []
ctxTermsCtxToListUnsafe (CtxTermsCtxCons ts (CtxTerm t)) =
  ctxTermsCtxToListUnsafe ts ++ [t]

-- | Like 'ctxTermsForBindings' but can return a 'CtxTerms' in an arbitrary
-- context. We consider this "unsafe" because it associates an arbitrary context
-- with these terms, and so we do not export this function.
ctxTermsForBindingsOpen :: Bindings tp -> [Term] -> Maybe CtxTerms
ctxTermsForBindingsOpen NoBind [] = Just CtxTermsNil
ctxTermsForBindingsOpen (Bind _ _ bs) (t : ts) =
  CtxTermsCons (CtxTerm t) <$> ctxTermsForBindingsOpen bs ts
ctxTermsForBindingsOpen _ _ = Nothing

-- | Take a list of terms and match them up with a sequence of bindings,
-- returning a structured 'CtxTerms' list. Note that the bindings themselves can
-- be in an arbitrary context, but the terms passed in are assumed to be closed,
-- i.e., in the empty context.
ctxTermsForBindings :: Bindings tp -> [Term] -> Maybe CtxTerms
ctxTermsForBindings NoBind [] = Just CtxTermsNil
ctxTermsForBindings (Bind _ _ bs) (t : ts) =
  CtxTermsCons (mkClosedTerm t) <$> ctxTermsForBindings bs ts
ctxTermsForBindings _ _ = Nothing

-- | Invert a 'CtxTerms' list and append it to an already-inverted 'CtxTermsCtx'
-- list
invertAppendCtxTerms :: CtxTermsCtx -> CtxTerms -> CtxTermsCtx
invertAppendCtxTerms as CtxTermsNil = as
invertAppendCtxTerms as (CtxTermsCons b bs) =
  invertAppendCtxTerms (CtxTermsCtxCons as b) bs

-- | Invert a 'CtxTerms' list
invertCtxTerms :: CtxTerms -> CtxTermsCtx
invertCtxTerms = invertAppendCtxTerms CtxTermsCtxNil

splitCtxTermsCtx :: InvBindings tp ->
                    CtxTermsCtx ->
                    (CtxTermsCtx, CtxTermsCtx)
splitCtxTermsCtx InvNoBind terms = (terms, CtxTermsCtxNil)
splitCtxTermsCtx (InvBind ctx _ _) (CtxTermsCtxCons ts t) =
  let (ts1, ts2) = splitCtxTermsCtx ctx ts in
  (ts1, CtxTermsCtxCons ts2 t)
splitCtxTermsCtx _ _ = error "splitCtxTermsCtx: impossible"

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

-- | Build a free variable as a 'CtxTerm'
ctxVar :: MonadTerm m => Bindings tp -> m CtxTerm
ctxVar ctx = CtxTerm <$> mkTermF (LocalVar $ bindingsLength ctx)

-- | Build a list of all the free variables as 'CtxTerm's
--
-- FIXME: there should be a nicer way to do this that does not require
-- ctxAppNilEq
ctxVars :: MonadTerm m => InvBindings tp -> m CtxTermsCtx
ctxVars ctx_top =
  helper ctx_top NoBind
      where
        helper :: MonadTerm m => InvBindings tp -> Bindings tp -> m CtxTermsCtx
        helper InvNoBind _ = return CtxTermsCtxNil
        helper (InvBind vars_ctx x tp) ctx =
          CtxTermsCtxCons <$> helper vars_ctx (Bind x tp ctx) <*> ctxVar ctx

-- | Build two lists of the free variables, split at a specific point
--
-- FIXME: there should be a nicer way to do this that does not require
-- splitCtxTermsCtx and appendTopInvBindings (the latter of which requires
-- ctxAppNilEq)
ctxVars2 :: MonadTerm m => InvBindings tp ->
            InvBindings tp ->
            m (CtxTermsCtx, CtxTermsCtx)
ctxVars2 vars1 vars2 =
  splitCtxTermsCtx vars2 <$> ctxVars (appendTopInvBindings vars1 vars2)

-- | Build a 'CtxTerm' for a 'Sort'
ctxSort :: MonadTerm m => Sort -> m CtxTerm
ctxSort s = CtxTerm <$> mkFlatTermF (Sort s noFlags)

-- | Apply two 'CtxTerm's
ctxApply :: MonadTerm m => m CtxTerm -> m CtxTerm -> m CtxTerm
ctxApply fm argm =
  do CtxTerm f <- fm
     CtxTerm arg <- argm
     CtxTerm <$> mkTermF (App f arg)

-- | Apply a 'CtxTerm' to a list of arguments
ctxApplyMulti :: MonadTerm m =>
                 m CtxTerm ->
                 m CtxTerms ->
                 m CtxTerm
ctxApplyMulti fm argsm =
  fm >>= \f -> argsm >>= \args -> helper f args
  where
    helper :: MonadTerm m => CtxTerm -> CtxTerms -> m CtxTerm
    helper f CtxTermsNil = return f
    helper f (CtxTermsCons arg args) =
      do f' <- ctxApply (return f) (return arg)
         helper f' args

-- | Form a lambda-abstraction as a 'CtxTerm'
ctxLambda1 :: MonadTerm m => LocalName -> CtxTerm ->
              (CtxTerm -> m CtxTerm) ->
              m CtxTerm
ctxLambda1 x (CtxTerm tp) body_f =
  do var <- ctxVar NoBind
     CtxTerm body <- body_f var
     CtxTerm <$> mkTermF (Lambda x tp body)

-- | Form a multi-arity lambda-abstraction as a 'CtxTerm'
ctxLambda :: MonadTerm m => Bindings CtxTerm ->
             (CtxTerms -> m CtxTerm) -> m CtxTerm
ctxLambda NoBind body_f = body_f CtxTermsNil
ctxLambda (Bind x tp xs) body_f =
  ctxLambda1 x tp $ \_ ->
  ctxLambda xs $ \vars ->
  do var <- ctxVar xs
     body_f (CtxTermsCons var vars)

-- | Form a pi-abstraction as a 'CtxTerm'
ctxPi1 :: MonadTerm m => LocalName -> CtxTerm ->
          (CtxTerm -> m CtxTerm) -> m CtxTerm
ctxPi1 x (CtxTerm tp) body_f =
  do var <- ctxVar NoBind
     CtxTerm body <- body_f var
     CtxTerm <$> mkTermF (Pi x tp body)

-- | Form a multi-arity pi-abstraction as a 'CtxTerm'
ctxPi :: MonadTerm m => Bindings CtxTerm ->
         (CtxTerms -> m CtxTerm) -> m CtxTerm
ctxPi NoBind body_f = body_f CtxTermsNil
ctxPi (Bind x tp xs) body_f =
  ctxPi1 x tp $ \_ ->
  ctxPi xs $ \vars ->
  do var <- ctxVar xs
     body_f (CtxTermsCons var vars)

-- | Existential return type of 'ctxAsPi'
data CtxPi =
  CtxPi LocalName CtxTerm CtxTerm

-- | Test if a 'CtxTerm' is a pi-abstraction, returning its components if so.
-- Note that we are not returning any equality constraints on the input type,
-- @a@; i.e., if a term is a pi-abstraction, one would expect @a@ to have the
-- form @b -> c@, but this would require a /lot/ more work...
ctxAsPi :: CtxTerm -> Maybe CtxPi
ctxAsPi (CtxTerm (unwrapTermF -> Pi x tp body)) =
  Just (CtxPi x (CtxTerm tp) (CtxTerm body))
ctxAsPi _ = Nothing

-- | Existential return type of 'ctxAsPiMulti'
data CtxMultiPi =
  CtxMultiPi (Bindings CtxTerm) CtxTerm

-- | Repeatedly apply 'ctxAsPi', returning the 'Bindings' list of 0 or more
-- pi-abstraction bindings in the given term
ctxAsPiMulti :: CtxTerm -> CtxMultiPi
ctxAsPiMulti (ctxAsPi -> Just (CtxPi x tp body)) =
  case ctxAsPiMulti body of
    CtxMultiPi as body' -> CtxMultiPi (Bind x tp as) body'
ctxAsPiMulti t = CtxMultiPi NoBind t

-- | Build an application of a datatype as a 'CtxTerm'
ctxDataTypeM ::
  forall m.
  MonadTerm m =>
  Name ->
  m CtxTermsCtx ->
  m CtxTermsCtx ->
  m CtxTerm
ctxDataTypeM d paramsM ixsM =
  ctxApplyMultiInv (ctxApplyMultiInv t paramsM) ixsM
  where
    t :: m CtxTerm
    t = CtxTerm <$> mkTermF (Constant d)

-- | Test if a 'CtxTerm' is an application of a specific datatype with the
-- supplied context of parameters and indices
ctxAsDataTypeApp :: Name -> Bindings tp1 ->
                    Bindings tp2 -> CtxTerm ->
                    Maybe (CtxTerms, CtxTerms)
ctxAsDataTypeApp d params ixs (CtxTerm t) =
  do let (f, args) = asApplyAll t
     d' <- asConstant f
     guard (d == d')
     guard (length args == bindingsLength params + bindingsLength ixs)
     let (params', ixs') = splitAt (bindingsLength params) args
     params_ret <- ctxTermsForBindingsOpen params params'
     ixs_ret <- ctxTermsForBindingsOpen ixs ixs'
     pure (params_ret, ixs_ret)


-- | Build an application of a constructor as a 'CtxTerm'
ctxCtorAppM ::
  forall m.
  MonadTerm m =>
  Name ->
  ExtCns Term ->
  m CtxTermsCtx ->
  m CtxTermsCtx ->
  m CtxTerm
ctxCtorAppM _d c paramsM argsM =
  ctxApplyMultiInv (ctxApplyMultiInv t paramsM) argsM
  where
    t :: m CtxTerm
    t = CtxTerm <$> mkTermF (Constant (Name (ecVarIndex c) (ecName c)))

-- | Apply a 'CtxTerm' to an inside-out list of arguments. Used only
-- to define 'ctxDataTypeM' and 'ctxCtorAppM`.
ctxApplyMultiInv ::
  MonadTerm m =>
  m CtxTerm ->
  m CtxTermsCtx ->
  m CtxTerm
ctxApplyMultiInv fm argsm =
  do f <- fm
     args <- argsm
     helper f args
  where
    helper :: MonadTerm m => CtxTerm -> CtxTermsCtx -> m CtxTerm
    helper f CtxTermsCtxNil = pure f
    helper f (CtxTermsCtxCons args arg) = ctxApply (helper f args) (pure arg)

ctxRecursorAppM :: MonadTerm m =>
  m CtxTerm ->
  m CtxTermsCtx ->
  m CtxTerm ->
  m CtxTerm
ctxRecursorAppM recM ixsM argM =
  do app <- RecursorApp <$>
              (unCtxTermUnsafe <$> recM) <*>
              (ctxTermsCtxToListUnsafe <$> ixsM) <*>
              (unCtxTermUnsafe <$> argM)
     CtxTerm <$> mkFlatTermF app

--
-- * Generalized Lifting and Substitution
--

-- | The class of "in-context" types that support lifting and substitution
class Monad m => CtxLiftSubst f m where
  -- | Lift an @f@ into an extended context
  ctxLift :: InvBindings tp1 -> Bindings tp2 -> f -> m f
  -- | Substitute a list of terms into an @f@
  ctxSubst :: CtxTermsCtx -> InvBindings tp -> f -> m f

-- | Lift an @f@ into a context extended with one type
ctxLift1 :: CtxLiftSubst f m => f -> m f
ctxLift1 = ctxLift InvNoBind (Bind "_" CtxUnit NoBind)

-- | Lift an @f@ that is in an extended list of 'Bindings'
ctxLiftInBindings :: CtxLiftSubst f m => InvBindings tp1 ->
                     Bindings tp2 ->
                     Bindings tp3 ->
                     f -> m f
ctxLiftInBindings = helper . mapInvBindings (CtxEither . Left)
  where
    helper :: CtxLiftSubst f m => InvBindings (CtxEither tp1 tp2) ->
              Bindings tp2 ->
              Bindings tp3 ->
              f -> m f
    helper ctx1 NoBind as = ctxLift ctx1 as
    helper ctx1 (Bind str tp ctx2) as =
      helper (InvBind ctx1 str (CtxEither $ Right tp)) ctx2 as

-- | Substitute into an @f@ that is in an extended list of 'Bindings'
ctxSubstInBindings :: CtxLiftSubst f m => CtxTermsCtx ->
                      InvBindings tp1 ->
                      Bindings tp2 ->
                      f -> m f
ctxSubstInBindings subst =
  helper subst . mapInvBindings (CtxEither . Left) where
  helper :: CtxLiftSubst f m => CtxTermsCtx ->
            InvBindings (CtxEither tp1 tp2) ->
            Bindings tp2 ->
            f -> m f
  helper s ctx2 NoBind f = ctxSubst s ctx2 f
  helper s ctx2 (Bind x tp ctx3) f =
    helper s (InvBind ctx2 x (CtxEither $ Right tp)) ctx3 f

instance MonadTerm m => CtxLiftSubst CtxTerm m where
  ctxLift ctx1 ctx2 (CtxTerm t) =
    CtxTerm <$> liftTerm (invBindingsLength ctx1) (bindingsLength ctx2) t
  ctxSubst subst ctx (CtxTerm t) =
    -- NOTE: our term lists put the least recently-bound variable first, so we
    -- have to reverse here to call substTerm, which wants the term for the most
    -- recently-bound variable first
    CtxTerm <$>
    substTerm (invBindingsLength ctx) (reverse (ctxTermsCtxToListUnsafe subst)) t

instance MonadTerm m => CtxLiftSubst CtxTerms m where
  ctxLift _ _ CtxTermsNil = return CtxTermsNil
  ctxLift ctx1 ctx2 (CtxTermsCons t ts) =
    CtxTermsCons <$> ctxLift ctx1 ctx2 t <*> ctxLift ctx1 ctx2 ts
  ctxSubst _ _ CtxTermsNil = return CtxTermsNil
  ctxSubst subst ctx (CtxTermsCons t ts) =
    CtxTermsCons <$> ctxSubst subst ctx t <*>
    ctxSubst subst ctx ts

instance MonadTerm m => CtxLiftSubst CtxTermsCtx m where
  ctxLift _ _ CtxTermsCtxNil = return CtxTermsCtxNil
  ctxLift ctx1 ctx2 (CtxTermsCtxCons ts t) =
    CtxTermsCtxCons <$> ctxLift ctx1 ctx2 ts <*> ctxLift ctx1 ctx2 t
  ctxSubst _ _ CtxTermsCtxNil = return CtxTermsCtxNil
  ctxSubst subst ctx (CtxTermsCtxCons ts t) =
    CtxTermsCtxCons <$> ctxSubst subst ctx ts <*>
    ctxSubst subst ctx t

instance CtxLiftSubst tp m => CtxLiftSubst (Bindings tp) m where
  ctxLift _ _ NoBind = return NoBind
  ctxLift ctx1 ctx2 (Bind x x_tp bs) =
    Bind x <$> ctxLift ctx1 ctx2 x_tp <*>
    ctxLift (InvBind ctx1 x (error "Unused")) ctx2 bs
  ctxSubst _ _ NoBind = return NoBind
  ctxSubst subst ctx (Bind x x_tp bs) =
    Bind x <$> ctxSubst subst ctx x_tp <*>
    ctxSubst subst (InvBind ctx x (error "Unused")) bs

instance MonadTerm m => CtxLiftSubst CtorArg m where
  ctxLift ctx1 ctx2 (ConstArg tp) = ConstArg <$> ctxLift ctx1 ctx2 tp
  ctxLift ctx1 ctx2 (RecursiveArg zs ixs) =
    RecursiveArg <$> ctxLift ctx1 ctx2 zs <*>
    ctxLiftInBindings ctx1 zs ctx2 ixs
  ctxSubst subst ctx (ConstArg tp) = ConstArg <$> ctxSubst subst ctx tp
  ctxSubst subst ctx (RecursiveArg zs ixs) =
    RecursiveArg <$> ctxSubst subst ctx zs <*>
    ctxSubstInBindings subst ctx zs ixs

-- | Make a closed term and then lift it into a context
mkLiftedClosedTerm :: MonadTerm m => Bindings tp -> Term -> m CtxTerm
mkLiftedClosedTerm inners t = ctxLift InvNoBind inners $ mkClosedTerm t


--
-- * Constructor Argument Types
--

-- | A specification of the type of an argument for a constructor of datatype
-- @d@, that has a specified list @ixs@ of indices, inside a context @ctx@ of
-- parameters and earlier arguments
data CtorArg where
  -- | A fixed, constant type
  ConstArg :: CtxTerm -> CtorArg
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
    Bindings CtxTerm ->
    CtxTerms ->
    CtorArg

-- | A structure that defines the parameters, arguments, and return type indices
-- of a constructor, using 'CtxTerm' and friends to get the bindings right
data CtorArgStruct =
  CtorArgStruct
  {
    ctorParams :: Bindings CtxTerm,
    ctorArgs :: Bindings CtorArg,
    ctorIndices :: CtxTerms,
    dataTypeIndices :: Bindings CtxTerm
  }


-- | Convert a 'CtorArg' into the type that it represents, given a context of
-- the parameters and of the previous arguments
ctxCtorArgType :: MonadTerm m => Name ->
                  InvBindings CtxTerm ->
                  InvBindings CtxTerm ->
                  CtorArg ->
                  m CtxTerm
ctxCtorArgType _ _ _ (ConstArg tp) = return tp
ctxCtorArgType d params prevs (RecursiveArg zs_ctx ixs) =
  ctxPi zs_ctx $ \_ ->
  ctxDataTypeM d ((fst <$> ctxVars2 params prevs) >>= ctxLift InvNoBind zs_ctx)
  (return $ invertCtxTerms ixs)

-- | Convert a bindings list of 'CtorArg's to a binding list of types
ctxCtorArgBindings :: MonadTerm m => Name ->
                      InvBindings CtxTerm ->
                      InvBindings CtxTerm ->
                      Bindings CtorArg ->
                      m (Bindings CtxTerm)
ctxCtorArgBindings _ _ _ NoBind = return NoBind
ctxCtorArgBindings d params prevs (Bind x arg args) =
  do tp <- ctxCtorArgType d params prevs arg
     rest <- ctxCtorArgBindings d params (InvBind prevs x tp) args
     return (Bind x tp rest)

-- | Compute the type of a constructor from the name of its datatype and its
-- 'CtorArgStruct'
ctxCtorType :: MonadTerm m => Name -> CtorArgStruct -> m Term
ctxCtorType d (CtorArgStruct{..}) =
  elimClosedTerm <$>
  (ctxPi ctorParams $ \params ->
    do bs <-
         ctxCtorArgBindings d (invertBindings ctorParams)
         InvNoBind ctorArgs
       ctxPi bs $ \_ ->
         ctxDataTypeM d
         (ctxLift InvNoBind bs $ invertCtxTerms params)
         (return $ invertCtxTerms ctorIndices))


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
             InvBindings CtxTerm ->
             Bindings CtxTerm -> Sort ->
             m CtxTerm
ctxPRetTp d params ixs s =
  ctxPi ixs $ \ix_vars ->
  do param_vars <- ctxVars params
     dt <- ctxDataTypeM d (ctxLift InvNoBind ixs param_vars)
       (return $ invertCtxTerms ix_vars)
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
  case ctxBindingsOfTerms untyped_p_ctx of
    ExistsTp p_ctx ->
      case (ctxBindingsOfTerms untyped_ix_ctx,
            ctxTermsForBindings p_ctx untyped_params) of
        (ExistsTp ix_ctx, Just params) ->
          do p_ret <- (ctxPRetTp d
                       (invertBindings p_ctx) ix_ctx s)
             elimClosedTerm <$>
               ctxSubst (invertCtxTerms params) InvNoBind
               (castPRet (invertBindings p_ctx) p_ret)
        (_, Nothing) ->
          error "mkPRetTp: incorrect number of parameters"
  where
    castPRet :: InvBindings tp -> CtxTerm -> CtxTerm
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
  m CtxTerm
ctxCtorElimType d_top c
  (CtorArgStruct{..}) =
  (do let params = invertBindings ctorParams
      -- NOTE: we use propSort for the type of p_ret just as arbitrary sort, but
      -- it doesn't matter because p_ret_tp is only actually used to form
      -- contexts, and is never actually used directly in the output
      p_ret_tp <- ctxPRetTp d_top params dataTypeIndices propSort

      -- Lift the argument and return indices into the context of p_ret
      args <- ctxLift InvNoBind (Bind "_" p_ret_tp NoBind) ctorArgs
      ixs <-
        ctxLiftInBindings InvNoBind ctorArgs (Bind "_" p_ret_tp NoBind)
        ctorIndices
      -- Form the context (params ::> p_ret)
      let params_pret = InvBind params "_" (ctxLiftNil params p_ret_tp)
      -- Call the helper and cast the result to (Typ ret)
      castCtxTerm <$>
        helper d_top params_pret InvNoBind args ixs
  ) where

  -- Iterate through the argument types of the constructor, building up a
  -- function from those arguments to the result type of the p_ret function.
  -- Note that, technically, this function also takes in recursive calls, so has
  -- a slightly richer type, but we are not going to try to compute this richer
  -- type in Haskell land.
  helper :: MonadTerm m =>
    Name ->
    InvBindings CtxTerm ->
    InvBindings CtxTerm ->
    Bindings CtorArg ->
    CtxTerms ->
    m CtxTerm
  helper d params_pret prevs NoBind ret_ixs =
    -- If we are finished with our arguments, construct the final result type
    -- (p_ret ret_ixs (c params prevs))
    do (vars, prev_vars) <- ctxVars2 params_pret prevs
       let (param_terms, p_ret) = ctxTermsCtxHeadTail vars
       ctxApply (ctxApplyMulti (return p_ret) (return ret_ixs)) $
         ctxCtorAppM d c (return param_terms) (return prev_vars)
  helper d params_pret prevs (Bind str (ConstArg tp) args) ixs =
    -- For a constant argument type, just abstract it and continue
    (ctxPi (Bind str tp NoBind) $ \_ ->
      helper d params_pret (InvBind prevs str tp) args ixs)
  helper d params_pret
    prevs (Bind str (RecursiveArg zs ts) args) ixs =
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
                                (ctxLift InvNoBind zs param_vars)
                                (return $ invertCtxTerms ts))
      -- Lift zs and ts into the context of arg
      let arg_ctx = Bind "_" arg_tp NoBind
      zs' <- ctxLift InvNoBind arg_ctx zs
      ts' <- ctxLiftInBindings InvNoBind zs arg_ctx ts
      -- Build the pi-abstraction for arg
      ctxPi1 str arg_tp $ \arg ->
        do rest <-
             helper d params_pret (InvBind prevs str arg_tp) args ixs
           -- Build the type of ih, in the context of arg
           ih_tp <- ctxPi zs' $ \z_vars ->
             ctxApply
             (ctxApplyMulti
              (ctxLift InvNoBind (Bind "_" arg_tp zs') p_ret) (return ts'))
             (ctxApplyMulti (ctxLift InvNoBind zs' arg) (return z_vars))
           -- Finally, build the pi-abstraction for ih around the rest
           --
           -- NOTE: we cast away the IH argument, because that is a type that is
           -- computed from the argument structure, and we cannot (well, we
           -- could, but it would be much more work to) express that computation
           -- in the Haskell type system
           castCtxTerm <$>
             (ctxPi1 "_" ih_tp $ \_ ->
               ctxLift InvNoBind (Bind "_" ih_tp NoBind) rest)

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
             elimClosedTerm <$>
             ctxSubstInBindings
             (CtxTermsCtxCons (invertCtxTerms paramsCtx) (mkClosedTerm p_ret))
             InvNoBind NoBind ctxElimType


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
  let inctx :: Term -> CtxTerm
      inctx = CtxTerm
   in
  case ctxTermsForBindingsOpen ctorArgs c_args of
     Just argsCtx ->
       ctxReduceRecursor_ (inctx rec) (inctx elimf) argsCtx ctorArgs
     Nothing ->
       error "ctxReduceRecursorRaw: wrong number of constructor arguments!"


-- | This operation does the real work of building the
--   iota reduction for @ctxReduceRecursor@.  We assume
--   the input terms we are given live in an ambient
--   context @amb@.
ctxReduceRecursor_ :: forall m.
  MonadTerm m =>
  CtxTerm     {- ^ recursor value eliminatiting data type d -}->
  CtxTerm     {- ^ eliminator function for the constructor -} ->
  CtxTerms    {- ^ constructor actual arguments -} ->
  Bindings CtorArg
    {- ^ telescope describing the constructor arguments -} ->
  m Term
ctxReduceRecursor_ rec fi args0 argCtx =
  do args <- mk_args CtxTermsCtxNil args0 argCtx
     whnfTerm =<< foldM (\f arg -> mkTermF $ App f arg) (unAmb fi) args

 where
   -- extract a raw term into the ambient context
    unAmb :: CtxTerm -> Term
    unAmb (CtxTerm t) = t

    mk_args :: CtxTermsCtx ->  -- already processed parameters/arguments
               CtxTerms ->     -- remaining actual arguments to process
               Bindings CtorArg ->
                 -- telescope for typing the actual arguments
               m [Term]
    -- no more arguments to process
    mk_args _ _ NoBind = return []

    -- process an argument that is not a recursive call
    mk_args pre_xs (CtxTermsCons x xs) (Bind _ (ConstArg _) args) =
      do tl <- mk_args (CtxTermsCtxCons pre_xs x) xs args
         pure (unAmb x : tl)

    -- process an argument that is a recursive call
    mk_args pre_xs (CtxTermsCons x xs) (Bind _ (RecursiveArg zs ixs) args) =
      do zs'  <- ctxSubstInBindings pre_xs InvNoBind NoBind zs
         ixs' <- ctxSubstInBindings pre_xs InvNoBind zs ixs
         recx <- mk_rec_arg zs' ixs' x
         tl   <- mk_args (CtxTermsCtxCons pre_xs x) xs args
         pure (unAmb x : recx : tl)

    mk_args _ _ _ = error "mk_args: impossible"

    -- Build an individual recursive call, given the parameters, the bindings
    -- for the RecursiveArg, and the argument we are going to recurse on
    mk_rec_arg ::
      Bindings CtxTerm ->                -- telescope describing the zs
      CtxTerms ->                        -- actual values for the indices, shifted under zs
      CtxTerm ->                         -- actual value in recursive position
      m Term
    mk_rec_arg zs_ctx ixs x = unAmb <$>
      -- eta expand over the zs and apply the RecursorApp form
      ctxLambda zs_ctx (\zs ->
        ctxRecursorAppM
          (ctxLift InvNoBind zs_ctx rec)
          (return (invertCtxTerms ixs))
          (ctxApplyMulti
            (ctxLift InvNoBind zs_ctx x)
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

instance UsesDataType CtxTerm where
  usesDataType d (CtxTerm t) = usesDataType d t

instance UsesDataType (Bindings CtxTerm) where
  usesDataType _ NoBind = False
  usesDataType d (Bind _ tp tps) = usesDataType d tp || usesDataType d tps


-- | Check that a type is a valid application of datatype @d@ for use in
-- specific ways in the type of a constructor for @d@. This requires that this
-- application of @d@ be of the form
--
-- > d p1 .. pn x1 .. xm
--
-- where the @pi@ are the distinct bound variables bound in the @params@
-- context, given as argument, and that the @xj@ have no occurrences of @d@. If
-- the given type is of this form, return the @xj@.
asCtorDTApp :: Name -> Bindings CtxTerm ->
               Bindings CtxTerm ->
               InvBindings tp1 ->
               Bindings tp2 ->
               CtxTerm ->
               Maybe CtxTerms
asCtorDTApp d params dt_ixs ctx1 ctx2 (ctxAsDataTypeApp d params dt_ixs ->
                                       Just (param_vars, ixs))
  | isVarList params ctx1 ctx2 param_vars &&
    not (any (usesDataType d) $ ctxTermsToListUnsafe ixs)
  = Just ixs
  where
    -- Check that the given list of terms is a list of bound variables, one for
    -- each parameter, in the context extended by the given arguments
    isVarList :: Bindings tp1 ->
                 InvBindings tp2 ->
                 Bindings tp3 ->
                 CtxTerms ->
                 Bool
    isVarList _ _ _ CtxTermsNil = True
    isVarList (Bind _ _ ps) c1 c2 (CtxTermsCons
                                     (CtxTerm (unwrapTermF -> LocalVar i)) ts) =
      i == bindingsLength ps + invBindingsLength c1 + bindingsLength c2 &&
      isVarList ps c1 c2 ts
    isVarList _ _ _ _ = False
asCtorDTApp _ _ _ _ _ _ = Nothing


-- | Existential return type for 'asCtorArg'
data ExCtorArg =
  ExCtorArg CtorArg

-- | Check that an argument for a constructor has one of the allowed forms
asCtorArg :: Name -> Bindings CtxTerm ->
             Bindings CtxTerm ->
             InvBindings tp ->
             CtxTerm ->
             Maybe ExCtorArg
asCtorArg d params dt_ixs prevs (ctxAsPiMulti ->
                                 CtxMultiPi zs
                                 (asCtorDTApp d params dt_ixs prevs zs ->
                                  Just ixs))
  | not (usesDataType d zs)
  = Just (ExCtorArg $ RecursiveArg zs ixs)
asCtorArg d _ _ _ tp
  | not (usesDataType d tp)
  = Just (ExCtorArg $ ConstArg tp)
asCtorArg _ _ _ _ _ = Nothing

-- | Existential return type of 'asPiCtorArg'
data CtxPiCtorArg =
  CtxPiCtorArg LocalName CtorArg CtxTerm

-- | Check that a constructor type is a pi-abstraction that takes as input an
-- argument of one of the allowed forms described by 'CtorArg'
asPiCtorArg :: Name -> Bindings CtxTerm ->
               Bindings CtxTerm ->
               InvBindings tp ->
               CtxTerm ->
               Maybe CtxPiCtorArg
asPiCtorArg d params dt_ixs prevs (ctxAsPi ->
                                   Just (CtxPi x
                                         (asCtorArg d params dt_ixs prevs ->
                                          Just (ExCtorArg arg)) rest)) =
  Just $ CtxPiCtorArg x arg (castTopCtxElem rest)
  where
    castTopCtxElem :: CtxTerm -> CtxTerm
    castTopCtxElem (CtxTerm t) = CtxTerm t
asPiCtorArg _ _ _ _ _ = Nothing

-- | Existential return type of 'mkCtorArgsIxs'
data CtorArgsIxs =
  CtorArgsIxs (Bindings CtorArg) CtxTerms

-- | Helper function for 'mkCtorArgStruct'
mkCtorArgsIxs :: Name -> Bindings CtxTerm ->
                 Bindings CtxTerm ->
                 InvBindings CtorArg ->
                 CtxTerm ->
                 Maybe CtorArgsIxs
mkCtorArgsIxs d params dt_ixs prevs (asPiCtorArg d params dt_ixs prevs ->
                                     Just (CtxPiCtorArg x arg rest)) =
  case mkCtorArgsIxs d params dt_ixs (InvBind prevs x arg) rest of
    Just (CtorArgsIxs args ixs) -> Just (CtorArgsIxs (Bind x arg args) ixs)
    Nothing -> Nothing
mkCtorArgsIxs d params dt_ixs prevs (asCtorDTApp d params dt_ixs prevs NoBind ->
                                     Just ixs) =
  Just (CtorArgsIxs NoBind ixs)
mkCtorArgsIxs _ _ _ _ _ = Nothing


-- | Take in a datatype and 'Bindings' lists for its parameters and indices, and
-- also a prospective type of a constructor for that datatype, where the
-- constructor type is allowed to have the parameters but not the indices free.
-- Test that the constructor type is an allowed type for a constructor of this
-- datatype, and, if so, build a 'CtorArgStruct' for it.
mkCtorArgStruct ::
  Name ->
  Bindings CtxTerm ->
  Bindings CtxTerm ->
  Term ->
  Maybe CtorArgStruct
mkCtorArgStruct d params dt_ixs ctor_tp =
  case mkCtorArgsIxs d params dt_ixs InvNoBind (CtxTerm ctor_tp) of
    Just (CtorArgsIxs args ctor_ixs) ->
      Just (CtorArgStruct params args ctor_ixs dt_ixs)
    Nothing -> Nothing
