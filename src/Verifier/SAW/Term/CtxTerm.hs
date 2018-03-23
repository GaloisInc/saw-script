{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

{- |
Module      : Verifier.SAW.Term.CtxTerm
Copyright   : Galois, Inc. 2018
License     : BSD3
Stability   : experimental
Portability : non-portable (language extensions)

The purpose of this module is to define a dependently-typed / GADT approach
to representing SAW core terms, that reflects (to some degree) the typing
and context information in the Haskell type of a term.

Why are we doing this, when GADT programming can be so gross? The point of all
this is to get all the deBruijn indices right. Doing deBruijn index math when
manipulating open terms can be error prone and hard to read, and those bugs are
really hard to track down. Although GADT programming can be a pain sometimes,
this file is organized so at least you will always get the deBruijn indices
right when you finally get GHC to accept your code. :)
-}

module Verifier.SAW.Term.CtxTerm (
  Ctx(..), CtxInvApp, (:++:), Arrows, CtxExtends(..)
  , ctxTermsForBindings, invAppendBindings, invertBindings
    -- , appendBinding, appendBindings
  , CtxTerm(..), CtxTerms(..), CtxTermsCtx(..)
  , Typ, mkClosedTerm, mkClosedTyp, elimClosedTerm
  , CtxPair(..), Bindings(..), InvBindings(..), InBindings(..)
  , mkLiftedClosedTerm, ctxSubstElimTerm
  , ctxLambda, ctxPi
  , MonadTerm(..), CtxLiftSubst(..)
  , CtorArg(..), ctxCtorArgType, CtorArgStruct(..)
  , ctxCtorType, ctxRecursorRecArgs
  ) where

import Control.Monad

import Verifier.SAW.Term.Functor


--
-- * Contexts and Bindings
--

-- | We use DataKinds to represent contexts of free variables at the type level.
-- These contexts are "inside-out", meaning that the most recently-bound
-- variable is listed on the outside. We reflect this by having that most
-- recently-bound variable to the right in 'CCons'.
data Ctx a = CNil | CCons (Ctx a) a

-- | Append two lists of types
--
-- FIXME HERE: remove if not needed
type family as :++: bs where
  '[] :++: bs = bs
  (a ': as) :++: bs = a ': as :++: bs

-- | Proof that one context is an extension of another
data CtxExtends ctx1 ctx2 where
  CtxExtendsRefl :: CtxExtends ctx ctx
  CtxExtendsCons :: CtxExtends ctx1 ctx2 -> CtxExtends ctx1 ('CCons ctx2 a)

-- | Append two contexts, where the second one is to the "inside" of the first
type family CtxApp ctx1 ctx2 where
  CtxApp ctx1 'CNil = ctx1
  CtxApp ctx1 ('CCons ctx2 a) = 'CCons (CtxApp ctx1 ctx2) a

-- | Append a list of types to a context, i.e., "invert" the list of types,
-- putting the last type on the "outside", and append it. The way to think of
-- this operation is that we are already "inside" @ctx@, and we are moving
-- further "inside" of @as@, one type at a time, to yield a combined context
-- where the last type of @as@ is bound last, i.e., most recently.
type family CtxInvApp ctx as where
  CtxInvApp ctx '[] = ctx
  CtxInvApp ctx (a ': as) = CtxInvApp ('CCons ctx a) as

-- | Invert a type list to make a context
type CtxInv as = CtxInvApp 'CNil as

-- | A sequence of bindings of pairs of a variable name and a type of some form
-- for that variable. These bindings are relative to ambient context @ctx@, use
-- @tp@ for the variable types, and bind variables whose types are listed in
-- @as@.
--
-- Note that each type in a bindings list has type 'Typ', but is "represented"
-- by a Haskell type @a@ in the 'Bind' constructor. There is no way to actually
-- related the Haskell type @a@ to the type it "represents", so we do not try,
-- and just write "represent" in quotes.
data Bindings (tp :: Ctx * -> * -> *) (ctx :: Ctx *) (as :: [*]) where
  NoBind :: Bindings tp ctx '[]
  Bind :: String -> tp ctx Typ -> Bindings tp ('CCons ctx a) as ->
          Bindings tp ctx (a ': as)

-- | Compute the number of bindings in a bindings list
bindingsLength :: Bindings tp ctx as -> Int
bindingsLength NoBind = 0
bindingsLength (Bind _ _ bs) = 1 + bindingsLength bs

-- | An inverted list of bindings, seen from the "inside out"
data InvBindings (tp :: Ctx * -> * -> *) (ctx :: Ctx *) (as :: Ctx *) where
  InvNoBind :: InvBindings tp ctx 'CNil
  InvBind :: InvBindings tp ctx as -> String -> tp (CtxApp ctx as) Typ ->
             InvBindings tp ctx ('CCons as a)

-- | Compute the number of bindings in an inverted bindings list
invBindingsLength :: InvBindings tp ctx as -> Int
invBindingsLength InvNoBind = 0
invBindingsLength (InvBind bs _ _) = 1 + invBindingsLength bs

-- | Append a 'Bindings' list to an inverted 'InvBindings' list, inverting the
-- former as we go to yield an inverted 'InvBidnings' list. Intuitively, this
-- means we are already "inside" the inverted bindings lists, and we are moving
-- further "inside" the regular bindings list; at the end we will be "inside"
-- both, meaning that we will see the combination "from the inside".
invAppendBindings :: InvBindings tp ctx as ->
                     Bindings tp (CtxApp ctx as) bs ->
                     InvBindings tp ctx (CtxInvApp as bs)
invAppendBindings as NoBind = as
invAppendBindings as (Bind y y_tp bs) =
  (invAppendBindings (InvBind as y y_tp) bs)

-- | Invert a 'Bindings' list; i.e., move "inside" those bindings
invertBindings :: Bindings tp ctx as -> InvBindings tp ctx (CtxInv as)
invertBindings = invAppendBindings InvNoBind

-- | A sequence of bindings bundled with something that is relative to those
-- bindings
data InBindings tp (f :: Ctx * -> k -> *) ctx (a::k) where
  InBindings :: Bindings tp ctx as -> f (CtxInvApp ctx as) a ->
                InBindings tp f ctx a


--
-- * Terms In Context
--

-- | A dummy type of types
data Typ

-- | Abstract a type list using Haskell arrows. This is done "outside-in", since
-- type-level lists represent bindings from the outside in.
type family Arrows as b where
  Arrows '[] b = b
  Arrows (a ': as) b = a -> Arrows as b

-- | A 'Term' with a given "type" relative to a given context. Since we cannot
-- hope to represent dependent type theory in Haskell types anyway, these
-- "types" are usually instantiated with a dummy, such as the unit type, but the
-- code that consumes them cannot know that and has to be agnostic to what type
-- it is.
newtype CtxTerm (ctx :: Ctx *) (a :: *) = CtxTerm Term

-- | Build a term in the empty context
mkClosedTerm :: Term -> CtxTerm 'CNil a
mkClosedTerm = CtxTerm

-- | Build a term to represent a type in the empty context
mkClosedTyp :: Term -> CtxTerm 'CNil Typ
mkClosedTyp = mkClosedTerm

-- | Take a term out of the empty context
elimClosedTerm :: CtxTerm 'CNil a -> Term
elimClosedTerm (CtxTerm t) = t

-- | A pair of things in a given context
data CtxPair f1 f2 ctx ab where
  CtxPair :: f1 ctx a -> f2 ctx b -> CtxPair f1 f2 ctx (a,b)

-- | A list of terms in a given context
data CtxTerms ctx as where
  CtxTermsNil :: CtxTerms ctx '[]
  CtxTermsCons :: CtxTerm ctx a -> CtxTerms ctx as -> CtxTerms ctx (a ': as)

-- | A list of terms in a given context, stored "inside-out"
data CtxTermsCtx ctx term_ctx where
  CtxTermsCtxNil :: CtxTermsCtx ctx 'CNil
  CtxTermsCtxCons :: CtxTermsCtx ctx as -> CtxTerm ctx a ->
                     CtxTermsCtx ctx ('CCons as a)

-- | Convert a typed list of terms to a list of untyped terms; this is unsafe
ctxTermsToListUnsafe :: CtxTerms ctx as -> [Term]
ctxTermsToListUnsafe CtxTermsNil = []
ctxTermsToListUnsafe (CtxTermsCons (CtxTerm t) ts) =
  t : ctxTermsToListUnsafe ts

-- | Take a list of terms and match them up with a sequence of bindings,
-- returning a structured 'CtxTermsCtx' list. Note that the bindings themselves
-- can be in an arbitrary context, but the terms passed in are assumed to be
-- closed, i.e., in the empty context.
ctxTermsForBindings :: Bindings tp ctx as -> [Term] ->
                       Maybe (CtxTerms 'CNil as)
ctxTermsForBindings NoBind [] = Just CtxTermsNil
ctxTermsForBindings (Bind _ _ bs) (t : ts) =
  CtxTermsCons (mkClosedTerm t) <$> ctxTermsForBindings bs ts
ctxTermsForBindings _ _ = Nothing

{-
ctxTermsForBindings bs_top ts_top = helper bs_top (reverse ts_top)
  where
    helper :: Bindings tp ctx as -> [Term] -> Maybe (CtxTerms 'CNil as)
    helper NoBind [] = Just CtxTermsNil
    helper (Bind bs _ _) (t : ts) =
      CtxTermsCons <$> helper bs ts <*> Just (mkClosedTerm t)
    helper _ _ = Nothing
-}

invertAppendCtxTerms :: CtxTermsCtx ctx as -> CtxTerms ctx bs ->
                        CtxTermsCtx ctx (CtxInvApp as bs)
invertAppendCtxTerms as CtxTermsNil = as
invertAppendCtxTerms as (CtxTermsCons b bs) =
  invertAppendCtxTerms (CtxTermsCtxCons as b) bs

invertCtxTerms :: CtxTerms ctx as -> CtxTermsCtx ctx (CtxInv as)
invertCtxTerms = invertAppendCtxTerms CtxTermsCtxNil


-- | Prepend a single binding to a sequence of bindings
{-
prependBinding :: String -> tp ctx a -> Bindings tp ctx as ->
                  Bindings tp ctx ('CCons as a)
prependBinding NoBind x tp = Bind x tp NoBind
prependBinding (Bind bs y y_tp) x tp = Bind (prependBinding bs x tp) y y_tp
-}

-- | Append two sequences of 'Bindings'
{-
appendBindings :: Bindings tp ctx as ->
                  Bindings tp (CtxApp ctx as) bs ->
                  Bindings tp ctx (CtxApp as bs)
appendBindings as NoBind = as
appendBindings as (Bind bs y y_tp) = Bind (appendBindings as bs) y y_tp
-}


--
-- * Operations on Terms-in-Context
--

-- | The class of monads that can build terms and substitute into them
class Monad m => MonadTerm m where
  mkTermF :: TermF Term -> m Term
  liftTerm :: DeBruijnIndex -> DeBruijnIndex -> Term -> m Term
  substTerm :: DeBruijnIndex -> [Term] -> Term -> m Term
               -- ^ NOTE: the first term in the list is substituted for the most
               -- recently-bound variable, i.e., deBruijn index 0

mkFlatTermF :: MonadTerm m => FlatTermF Term -> m Term
mkFlatTermF = mkTermF . FTermF

ctxLambda :: MonadTerm m => Bindings CtxTerm ctx as ->
             (CtxTerms (CtxInvApp ctx as) as ->
              m (CtxTerm (CtxInvApp ctx as) a)) ->
             m (CtxTerm ctx (Arrows as a))
ctxLambda = error "FIXME HERE NOW"

ctxPi :: MonadTerm m => Bindings CtxTerm ctx as ->
         (CtxTerms (CtxInvApp ctx as) as ->
          m (CtxTerm (CtxInvApp ctx as) Typ)) ->
         m (CtxTerm ctx Typ)
ctxPi = error "FIXME HERE NOW"

ctxDataTypeM :: MonadTerm m => Ident -> m (CtxTerms ctx params) ->
                m (CtxTerms ctx ixs) -> m (CtxTerm ctx Typ)
ctxDataTypeM d params ixs =
  do ftf <-
       DataTypeApp d <$> (ctxTermsToListUnsafe <$> params) <*>
       (ctxTermsToListUnsafe <$> ixs)
     CtxTerm <$> mkFlatTermF ftf

ctxRecursorAppM :: MonadTerm m => Ident -> m (CtxTerms ctx params) ->
                   m (CtxTerm ctx p_ret) -> m [(Ident, CtxTerm ctx elim)] ->
                   m (CtxTerms ctx ixs) -> m (CtxTerm ctx arg) ->
                   m (CtxTerm ctx a)
ctxRecursorAppM = error "FIXME HERE NOW"


--
-- * Generalized Lifting and Substitution
--

-- | The class of "in-context" types that support lifting and substitution
class Monad m => CtxLiftSubst f m where
  -- | Lift an @f@ into an extended context
  ctxLift :: InvBindings tp1 ctx ctx1 -> Bindings tp2 (CtxApp ctx ctx1) as ->
             f ctx a -> m (f (CtxInvApp (CtxApp ctx ctx1) as) a)
  -- | Substitute a list of terms in an @f@
  ctxSubst :: CtxTerms ctx as -> f (CtxInvApp ctx as) a -> m (f ctx a)
  -- | FIXME HERE: figure out which methods you want!
  ctxSubstInv :: CtxTermsCtx 'CNil ctx -> Bindings tp ctx as ->
                 f (CtxInvApp ctx as) a -> m (f (CtxInv as) a)

instance MonadTerm m => CtxLiftSubst CtxTerm m where
  ctxLift ctx1 ctx2 (CtxTerm t) =
    CtxTerm <$> liftTerm 0 (invBindingsLength ctx1 + bindingsLength ctx2) t
  ctxSubst subst (CtxTerm t) =
    -- NOTE: our term lists put the least recently-bound variable first, so we
    -- have to reverse here to call substTerm, which wants the term for the most
    -- recently-bound variable first
    CtxTerm <$> substTerm 0 (reverse $ ctxTermsToListUnsafe subst) t
  ctxSubstInv = error "FIXME HERE NOW"

instance MonadTerm m => CtxLiftSubst CtxTerms m where
  ctxLift _ _ CtxTermsNil = return CtxTermsNil
  ctxLift ctx1 ctx2 (CtxTermsCons t ts) =
    CtxTermsCons <$> ctxLift ctx1 ctx2 t <*> ctxLift ctx1 ctx2 ts
  ctxSubst _ CtxTermsNil = return CtxTermsNil
  ctxSubst subst (CtxTermsCons t ts) =
    CtxTermsCons <$> ctxSubst subst t <*> ctxSubst subst ts
  ctxSubstInv = error "FIXME HERE NOW"

{-
instance CtxLiftSubst tp m => CtxLiftSubst (Bindings tp) m where
  ctxLift _ _ NoBind = return NoBind
  ctxLift ctx1 ctx2 (Bind x x_tp bs) =
    Bind x <$> ctxLift ctx1 ctx2 x_tp <*> ctxLift ctx1 ctx2 bs
  ctxSubst _ NoBind = return NoBind
  ctxSubst subst (Bind x x_tp bs) =
    Bind x <$> ctxSubst subst x_tp <*> ctxSubst subst bs
  ctxSubstInv = error "FIXME HERE NOW"
-}

instance (CtxLiftSubst tp m, CtxLiftSubst f m) =>
         CtxLiftSubst (InBindings tp f) m where
  ctxLift = error "FIXME HERE NOW"
  ctxSubst = error "FIXME HERE NOW"
  ctxSubstInv = error "FIXME HERE NOW"
  {-
  ctxLift ctx1 ctx2 (InBindings bs f) =
    InBindings <$> ctxLift ctx1 ctx2 bs <*> ctxLift ctx1 ctx2 f
  ctxSubst subst (InBindings bs f) =
    InBindings <$> ctxSubst subst bs <*> ctxSubst subst f
  -}

-- | Special-purpose substitution for 'InBindings', because we do not want to
-- write that complicated lift instance!
-- ctxSubstInBindings :: 

-- | Make a closed term and then lift it into a context
mkLiftedClosedTerm :: MonadTerm m => Bindings tp 'CNil as -> Term ->
                      m (CtxTerm (CtxInv as) a)
mkLiftedClosedTerm inners t = ctxLift InvNoBind inners $ mkClosedTerm t

-- | Substitute into a term in a way that yields a closed term, and then
-- eliminate the 'CtxTerm' to yield a regular 'Term'
ctxSubstElimTerm :: MonadTerm m => CtxTerms 'CNil as ->
                    CtxTerm (CtxInv as) a -> m Term
ctxSubstElimTerm subst t = elimClosedTerm <$> ctxSubst subst t


--
-- * Constructor Argument Types
--

-- | A specification of a constructor argument for a constructor of a datatype
-- that has a specified list @ixs@ of indices, inside a context @ctx@ of
-- parameters and earlier arguments
data CtorArg ixs ctx a
  = ConstArg (CtxTerm ctx a)
    -- ^ A fixed, constant type
  | RecursiveArg (InBindings CtxTerm CtxTerms ctx ixs)
    -- | The construct @'RecursiveArg [(z1,tp1),..,(zn,tpn)] [e1,..,ek]'@
    -- specifies a recursive argument type of the form
    --
    -- > (z1::tp1) -> .. -> (zn::tpn) -> d p1 .. pm e1 .. ek
    --
    -- where @d@ is the datatype (not given here), the @zi::tpi@ are the
    -- elements of the Pi context (the first argument to 'RecursiveArgType'),
    -- the @pi@ are the parameters of @d@ (not given here), and the @ei@ are the
    -- type indices of @d@.

-- | Convert a 'CtorArg' into the type that it represents, relative to some
-- parameter values
ctxCtorArgType :: MonadTerm m => Ident ->
                  CtxTerms ctx params ->
                  InvBindings arg_tp ctx arg_ctx ->
                  CtorArg ixs (CtxApp ctx arg_ctx) Typ ->
                  m (CtxTerm (CtxApp ctx arg_ctx) Typ)
ctxCtorArgType _ _ _ (ConstArg tp) = return tp
ctxCtorArgType d params arg_ctx (RecursiveArg (InBindings zs_ctx ixs)) =
  ctxPi zs_ctx $ \_ ->
  ctxDataTypeM d (ctxLift arg_ctx zs_ctx params) (return ixs)

-- | Convert a bindings list of 'CtorArg's to a binding list of types
ctxCtorArgBindings :: MonadTerm m => Ident -> CtxTerms ctx params ->
                      Bindings (CtorArg ixs) ctx args ->
                      m (Bindings CtxTerm ctx args)
ctxCtorArgBindings d params_top args_top =
  helper params_top InvNoBind args_top
  where
    helper :: MonadTerm m =>
              CtxTerms ctx params ->
              InvBindings (CtorArg ixs) ctx prev_args ->
              Bindings (CtorArg ixs) (CtxApp ctx prev_args) args ->
              m (Bindings CtxTerm (CtxApp ctx prev_args) args)
    helper _ _ NoBind = return NoBind
    helper params prev_args (Bind x arg args) =
      Bind x <$> ctxCtorArgType d params prev_args arg <*>
      helper params (InvBind prev_args x arg) args


-- | A structure that defines the parameters, arguments, and return type indices
-- of a constructor, using 'CtxTerm' and friends to get the bindings right
data CtorArgStruct =
  forall params ixs args.
  CtorArgStruct
  {
    ctorParams :: Bindings CtxTerm 'CNil params,
    ctorArgs :: Bindings (CtorArg ixs) (CtxInv params) args,
    ctorIndices :: CtxTerms (CtxInvApp (CtxInv params) args) ixs
  }

-- | Compute the type of a constructor from the name of its datatype and its
-- 'CtorArgStruct'
ctxCtorType :: MonadTerm m => Ident -> CtorArgStruct -> m Term
ctxCtorType d (CtorArgStruct{..}) =
  elimClosedTerm <$>
  (ctxPi ctorParams $ \params ->
    do bs <- ctxCtorArgBindings d params ctorArgs
       ctxPi bs $ \_ ->
         ctxDataTypeM d (ctxLift InvNoBind ctorArgs params)
         (return ctorIndices))

-- | Build the recursive calls needed to reduce an application of a
-- recursor. The call
--
-- > ctxRecursorRecArgs d [p1, .., pn] P [(c1,f1), .., (cm,fm)] ci [x1, .., xk]
--
-- helps reduce @(RecursorApp d ps P cs_fs ixs (CtorApp ci ps xs))@ to
--
-- > fi x1 .. xk rec_tm_1 .. rec_tm_l
--
-- by building the @rec_tm_i@ arguments. These are given by recursion on those
-- arguments @xi@ that are recursive arguments. Specifically, for a
-- @'RecursiveArg' zs ixs@ argument @arg@, which has type @\(z1::Z1) -> .. -> d
-- p1 .. pn ix1 .. ixp@, we build the recursive call
--
-- > \(z1::[ps/params,xs/args]Z1) -> .. ->
-- >   RecursorApp d ps P cs_fs [ps/params,xs/args]ixs arg
--
-- where @[ps/params,xs/args]@ substitutes the concrete parameters @pi@ for the
-- parameter variables of the inductive type and the earlier constructor
-- arguments @xs@ for the remaining free variables.
ctxRecursorRecArgs :: MonadTerm m =>
                      Ident -> CtxTerms 'CNil params -> Term -> [(Ident,Term)] ->
                      CtxTerms 'CNil ctor_args ->
                      Bindings (CtorArg ixs) (CtxInv params) ctor_args ->
                      m [Term]
ctxRecursorRecArgs d params p_ret cs_fs top_args ctor_args =
  mk_rec_args (invertCtxTerms params) top_args ctor_args
  where
    mk_rec_args :: MonadTerm m => CtxTermsCtx 'CNil ctx ->
                   CtxTerms 'CNil args -> Bindings (CtorArg ixs) ctx args ->
                   m [Term]
    mk_rec_args _ _ NoBind = return []
    mk_rec_args pre_xs (CtxTermsCons x xs) (Bind _ (ConstArg _) args) =
      mk_rec_args (CtxTermsCtxCons pre_xs x) xs args
    mk_rec_args pre_xs (CtxTermsCons x xs)
      (Bind _ (RecursiveArg zs_ixs) args) =
      do zs_ixs_subst <- ctxSubstInv pre_xs NoBind zs_ixs
         (:) <$> mk_rec_arg zs_ixs_subst x <*>
           mk_rec_args (CtxTermsCtxCons pre_xs x) xs args

    -- Build an individual recursive call, given the parameters, the bindings
    -- for the RecursiveArg, and the argument we are going to recurse on
    mk_rec_arg :: MonadTerm m => InBindings CtxTerm CtxTerms 'CNil ixs ->
                  CtxTerm 'CNil a -> m Term
    mk_rec_arg (InBindings zs_ctx ixs) x =
      elimClosedTerm <$> ctxLambda zs_ctx
      (\_ ->
        ctxRecursorAppM d (ctxLift InvNoBind zs_ctx params)
        (mkLiftedClosedTerm zs_ctx p_ret)
        (forM cs_fs (\(c,f) -> (c,) <$> mkLiftedClosedTerm zs_ctx f))
        (return ixs)
        (ctxLift InvNoBind zs_ctx x))
