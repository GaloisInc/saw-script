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

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Verifier.SAW.Term.CtxTerm
  (
    -- * Re-exports from "Data.Parameterized.Context"
    -- | We use DataKinds to represent contexts of free variables at the type level.
    -- These contexts are "inside-out", meaning that the most recently-bound
    -- variable is listed on the outside. We reflect this by having that most
    -- recently-bound variable to the right in '::>'.
    Ctx(..), EmptyCtx, (::>), type (<+>)
    -- * Contexts and Bindings
  , Typ
  , CtxInvApp, CtxInv
  , Bindings(..), bindingsLength, InvBindings(..), InBindings(..)
  , invAppendBindings, invertBindings
    -- * Terms in Context
  , Arrows
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

import Data.Kind(Type)
--import Data.Map (Map)
--import qualified Data.Map as Map
import Data.Proxy
import Data.Type.Equality
import Control.Monad

import Data.Parameterized.Context

import Verifier.SAW.Term.Functor


--
-- * Contexts and Bindings
--

-- | A representation of the type of SAW types as a Haskell type. This is
-- actually a singleton type, meaning that a 'CtxTerm' with type @'Typ' a@ is a
-- SAW type that is represented by Haskell type @a@. Of course, the Haskell type
-- system is not rich enough to capture SAW types in complete detail, but we do
-- our best, and capture at least the types and functions.
data Typ (a :: Type)

-- | An identifier for a datatype that is statically associated with Haskell
-- type @d@. Again, we cannot capture all of the SAW type system in Haskell, so
-- we simplify datatypes to arbitrary Haskell types.
newtype DataIdent d = DataIdent (PrimName Term)
  -- Invariant, the type of datatypes is always a closed term

-- | Append a list of types to a context, i.e., "invert" the list of types,
-- putting the last type on the "outside", and append it. The way to think of
-- this operation is that we are already "inside" @ctx@, and we are moving
-- further "inside" of @as@, one type at a time, to yield a combined context
-- where the last type of @as@ is bound last, i.e., most recently.
type family CtxInvApp ctx as where
  CtxInvApp ctx '[] = ctx
  CtxInvApp ctx (a ': as) = CtxInvApp (ctx ::> a) as

-- | Invert a type list to make a context
type CtxInv as = CtxInvApp EmptyCtx as

-- | A sequence of bindings of pairs of a variable name and a type of some form
-- for that variable. These bindings are relative to ambient context @ctx@, use
-- @tp@ for the variable types, and bind variables whose types are listed in
-- @as@.
--
-- Note that each type in a bindings list has type 'Typ', but is "represented"
-- by a Haskell type @a@ in the 'Bind' constructor. There is no way to actually
-- related the Haskell type @a@ to the type it "represents", so we do not try,
-- and just write "represent" in quotes.
data Bindings (tp :: Ctx Type -> Type -> Type) (ctx :: Ctx Type) (as :: [Type]) where
  NoBind :: Bindings tp ctx '[]
  Bind :: LocalName -> tp ctx (Typ a) -> Bindings tp (ctx ::> a) as ->
          Bindings tp ctx (a ': as)

-- | Compute the number of bindings in a bindings list
bindingsLength :: Bindings tp ctx as -> Int
bindingsLength NoBind = 0
bindingsLength (Bind _ _ bs) = 1 + bindingsLength bs

-- | An inverted list of bindings, seen from the "inside out"
data InvBindings (tp :: Ctx Type -> Type -> Type) (ctx :: Ctx Type) (as :: Ctx Type) where
  InvNoBind :: InvBindings tp ctx EmptyCtx
  InvBind :: InvBindings tp ctx as -> LocalName -> tp (ctx <+> as) (Typ a) ->
             InvBindings tp ctx (as ::> a)

-- | Compute the number of bindings in an inverted bindings list
invBindingsLength :: InvBindings tp ctx as -> Int
invBindingsLength InvNoBind = 0
invBindingsLength (InvBind bs _ _) = 1 + invBindingsLength bs

-- | Map over all types in an inverted bindings list
mapInvBindings :: (forall ctx a. f ctx a -> g ctx a) ->
                  InvBindings f c1 c2 -> InvBindings g c1 c2
mapInvBindings _ InvNoBind = InvNoBind
mapInvBindings f (InvBind ctx x tp) =
  InvBind (mapInvBindings f ctx) x (f tp)

-- | Typeclass for things from which we can build proofs that 'EmptyCtx' is the left
-- unit of '(<+>)', i.e., that @'EmptyCtx' '<+>' ctx ~ ctx@
class CtxAppNilEq f where
  ctxAppNilEq :: f ctx -> EmptyCtx <+> ctx :~: ctx

instance CtxAppNilEq (InvBindings tp ctx') where
  ctxAppNilEq InvNoBind = Refl
  ctxAppNilEq (InvBind ctx _ _) =
    case ctxAppNilEq ctx of
      Refl -> Refl

instance CtxAppNilEq (CtxTermsCtx ctx') where
  ctxAppNilEq CtxTermsCtxNil = Refl
  ctxAppNilEq (CtxTermsCtxCons ts _) =
    case ctxAppNilEq ts of
      Refl -> Refl

-- | Use 'ctxAppNilEq' to lift from @ctx@ to @'EmptyCtx' '<+>' ctx@
ctxLiftNil :: InvBindings tp EmptyCtx ctx -> f ctx a -> f (EmptyCtx <+> ctx) a
ctxLiftNil ctx f = case ctxAppNilEq ctx of Refl -> f

-- | Append a 'Bindings' list to an inverted 'InvBindings' list, inverting the
-- former as we go to yield an inverted 'InvBindings' list. Intuitively, this
-- means we are already "inside" the inverted bindings lists, and we are moving
-- further "inside" the regular bindings list; at the end we will be "inside"
-- both, meaning that we will see the combination "from the inside".
invAppendBindings :: InvBindings tp ctx as ->
                     Bindings tp (ctx <+> as) bs ->
                     InvBindings tp ctx (CtxInvApp as bs)
invAppendBindings as NoBind = as
invAppendBindings as (Bind y y_tp bs) =
  (invAppendBindings (InvBind as y y_tp) bs)

-- | Invert a 'Bindings' list; i.e., move "inside" those bindings
invertBindings :: Bindings tp ctx as -> InvBindings tp ctx (CtxInv as)
invertBindings = invAppendBindings InvNoBind

-- | Append two inverted contexts, where the first one is top-level. This
-- restriction allows us to avoid writing a proof of associativity of '(<+>)',
-- and instead just using 'ctxAppNilEq'
appendTopInvBindings :: InvBindings tp EmptyCtx ctx1 ->
                        InvBindings tp ctx1 ctx2 ->
                        InvBindings tp EmptyCtx (ctx1 <+> ctx2)
appendTopInvBindings ctx1 InvNoBind = ctx1
appendTopInvBindings ctx1 (InvBind ctx2 x tp) =
  let ret = appendTopInvBindings ctx1 ctx2 in
  InvBind ret x (ctxLiftNil ret tp)

-- | A sequence of bindings bundled with something that is relative to those
-- bindings
data InBindings tp (f :: Ctx Type -> k -> Type) ctx (a::k) where
  InBindings :: Bindings tp ctx as -> f (CtxInvApp ctx as) a ->
                InBindings tp f ctx a


--
-- * Terms In Context
--

-- | Abstract a type list using Haskell arrows. This is done "outside-in", since
-- type-level lists represent bindings from the outside in.
type family Arrows as b where
  Arrows '[] b = b
  Arrows (a ': as) b = a -> Arrows as b

-- | A 'Term' with a given "type" relative to a given context. Since we cannot
-- hope to represent dependent type theory in Haskell types anyway, these
-- "types" are usually instantiated with a dummy, such as '()', but the code
-- that consumes them cannot know that and has to be agnostic to what type it
-- is.
newtype CtxTerm (ctx :: Ctx Type) (a :: Type) = CtxTerm Term

-- | Convert a 'CtxTerm' to an untyped term. This is "unsafe" because it throws
-- away our typing information.
unCtxTermUnsafe :: CtxTerm ctx a -> Term
unCtxTermUnsafe (CtxTerm t) = t

-- | Because we cannot capture the SAW type system in Haskell, sometimes we have
-- to cast our terms. We try not to use this very often, and we only allow
-- casting the output type, not the context, since the latter could screw up our
-- deBruijn indices.
castCtxTerm :: Proxy a -> Proxy b -> CtxTerm ctx a -> CtxTerm ctx b
castCtxTerm _ _ (CtxTerm t) = CtxTerm t

-- | Build a term in the empty context
mkClosedTerm :: Term -> CtxTerm EmptyCtx a
mkClosedTerm = CtxTerm

-- | Build a term to represent a type in the empty context
mkClosedTyp :: Term -> CtxTerm EmptyCtx (Typ a)
mkClosedTyp = mkClosedTerm

-- | Take a term out of the empty context
elimClosedTerm :: CtxTerm EmptyCtx a -> Term
elimClosedTerm (CtxTerm t) = t

-- | Existentially quantify over the "type" of an object
data ExistsTp tp ctx = forall a. ExistsTp (tp ctx a)

-- | Build a 'Bindings' list from a list of variable names and types, assuming
-- that each variable is free in the remaining types and that @ctx@ describes
-- the ambient context of the top-level type in the context. Note that nothing
-- here ensures that the Haskell-level types used to "represent" the bindings
-- created by this function have anything to do with the actual SAW types, but
-- the Haskell type system is not powerful enough to represent all the SAW types
-- anyway, and any code that consumes this 'Bindings' list cannot know that
-- anyway. See also the comments for 'CtxTerm'.
ctxBindingsOfTerms :: [(LocalName, Term)] -> ExistsTp (Bindings CtxTerm) ctx
ctxBindingsOfTerms [] = ExistsTp NoBind
ctxBindingsOfTerms ((x,tp):ctx) =
  case ctxBindingsOfTerms ctx of
    ExistsTp rest -> ExistsTp (Bind x (CtxTerm tp) rest)

-- | A dummy unit type that takes in a context
data CtxUnit ctx a = CtxUnit

-- | An 'Either' type relative to a context and type
newtype CtxEither f g ctx a = CtxEither (Either (f ctx a) (g ctx a))

-- | A list of terms in a given context
data CtxTerms ctx as where
  CtxTermsNil :: CtxTerms ctx '[]
  CtxTermsCons :: CtxTerm ctx a -> CtxTerms ctx as -> CtxTerms ctx (a ': as)

-- | A list of terms in a given context, stored "inside-out"
data CtxTermsCtx ctx term_ctx where
  CtxTermsCtxNil :: CtxTermsCtx ctx EmptyCtx
  CtxTermsCtxCons :: CtxTermsCtx ctx as -> CtxTerm ctx a ->
                     CtxTermsCtx ctx (as ::> a)

{-
-- | Get the head and tail of a non-empty 'CtxTerms' list
ctxTermsHeadTail :: CtxTerms ctx (a ': as) -> (CtxTerm ctx a, CtxTerms ctx as)
ctxTermsHeadTail (CtxTermsCons a as) = (a, as)
-}

-- | Get the head and tail of a non-empty 'CtxTermsCtx' list
ctxTermsCtxHeadTail :: CtxTermsCtx ctx (as ::> a) ->
                       (CtxTermsCtx ctx as, CtxTerm ctx a)
ctxTermsCtxHeadTail (CtxTermsCtxCons as a) = (as, a)

-- | Convert a typed list of terms to a list of untyped terms; this is "unsafe"
-- because it throws away our typing information
ctxTermsToListUnsafe :: CtxTerms ctx as -> [Term]
ctxTermsToListUnsafe CtxTermsNil = []
ctxTermsToListUnsafe (CtxTermsCons (CtxTerm t) ts) =
  t : ctxTermsToListUnsafe ts

-- | Convert a typed list of terms to a list of untyped terms; this is "unsafe"
-- because it throws away our typing information
ctxTermsCtxToListUnsafe :: CtxTermsCtx ctx as -> [Term]
ctxTermsCtxToListUnsafe CtxTermsCtxNil = []
ctxTermsCtxToListUnsafe (CtxTermsCtxCons ts (CtxTerm t)) =
  ctxTermsCtxToListUnsafe ts ++ [t]

-- | Like 'ctxTermsForBindings' but can return a 'CtxTerms' in an arbitrary
-- context. We consider this "unsafe" because it associates an arbitrary context
-- with these terms, and so we do not export this function.
ctxTermsForBindingsOpen :: Bindings tp ctx_in as -> [Term] ->
                           Maybe (CtxTerms ctx as)
ctxTermsForBindingsOpen NoBind [] = Just CtxTermsNil
ctxTermsForBindingsOpen (Bind _ _ bs) (t : ts) =
  CtxTermsCons (CtxTerm t) <$> ctxTermsForBindingsOpen bs ts
ctxTermsForBindingsOpen _ _ = Nothing

-- | Take a list of terms and match them up with a sequence of bindings,
-- returning a structured 'CtxTerms' list. Note that the bindings themselves can
-- be in an arbitrary context, but the terms passed in are assumed to be closed,
-- i.e., in the empty context.
ctxTermsForBindings :: Bindings tp ctx as -> [Term] -> Maybe (CtxTerms EmptyCtx as)
ctxTermsForBindings NoBind [] = Just CtxTermsNil
ctxTermsForBindings (Bind _ _ bs) (t : ts) =
  CtxTermsCons (mkClosedTerm t) <$> ctxTermsForBindings bs ts
ctxTermsForBindings _ _ = Nothing

-- | Invert a 'CtxTerms' list and append it to an already-inverted 'CtxTermsCtx'
-- list
invertAppendCtxTerms :: CtxTermsCtx ctx as -> CtxTerms ctx bs ->
                        CtxTermsCtx ctx (CtxInvApp as bs)
invertAppendCtxTerms as CtxTermsNil = as
invertAppendCtxTerms as (CtxTermsCons b bs) =
  invertAppendCtxTerms (CtxTermsCtxCons as b) bs

-- | Invert a 'CtxTerms' list
invertCtxTerms :: CtxTerms ctx as -> CtxTermsCtx ctx (CtxInv as)
invertCtxTerms = invertAppendCtxTerms CtxTermsCtxNil

splitCtxTermsCtx :: InvBindings tp any_ctx ctx2 ->
                    CtxTermsCtx ctx (ctx1 <+> ctx2) ->
                    (CtxTermsCtx ctx ctx1, CtxTermsCtx ctx ctx2)
splitCtxTermsCtx InvNoBind terms = (terms, CtxTermsCtxNil)
splitCtxTermsCtx (InvBind ctx _ _) (CtxTermsCtxCons ts t) =
  let (ts1, ts2) = splitCtxTermsCtx ctx ts in
  (ts1, CtxTermsCtxCons ts2 t)


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

-- | Build a 'Term' from a 'FlatTermF' in a 'MonadTerm'
mkFlatTermF :: MonadTerm m => FlatTermF Term -> m Term
mkFlatTermF = mkTermF . FTermF

-- | Build a free variable as a 'CtxTerm'
ctxVar :: MonadTerm m => Bindings tp (ctx1 ::> a) ctx2 ->
          m (CtxTerm (CtxInvApp (ctx1 ::> a) ctx2) a)
ctxVar ctx = CtxTerm <$> mkTermF (LocalVar $ bindingsLength ctx)

-- | Build a list of all the free variables as 'CtxTerm's
--
-- FIXME: there should be a nicer way to do this that does not require
-- ctxAppNilEq
ctxVars :: MonadTerm m => InvBindings tp EmptyCtx ctx -> m (CtxTermsCtx ctx ctx)
ctxVars ctx_top =
  case ctxAppNilEq ctx_top of
    Refl -> helper ctx_top NoBind
      where
        helper :: MonadTerm m => InvBindings tp EmptyCtx ctx ->
                  Bindings tp (EmptyCtx <+> ctx) as ->
                  m (CtxTermsCtx (CtxInvApp (EmptyCtx <+> ctx) as) ctx)
        helper InvNoBind _ = return CtxTermsCtxNil
        helper (InvBind vars_ctx x tp) ctx =
          CtxTermsCtxCons <$> helper vars_ctx (Bind x tp ctx) <*> ctxVar ctx

-- | Build two lists of the free variables, split at a specific point
--
-- FIXME: there should be a nicer way to do this that does not require
-- splitCtxTermsCtx and appendTopInvBindings (the latter of which requires
-- ctxAppNilEq)
ctxVars2 :: MonadTerm m => InvBindings tp EmptyCtx ctx1 ->
            InvBindings tp ctx1 ctx2 ->
            m (CtxTermsCtx (ctx1 <+> ctx2) ctx1,
               CtxTermsCtx (ctx1 <+> ctx2) ctx2)
ctxVars2 vars1 vars2 =
  splitCtxTermsCtx vars2 <$> ctxVars (appendTopInvBindings vars1 vars2)

-- | Build a 'CtxTerm' for a 'Sort'
ctxSort :: MonadTerm m => Sort -> m (CtxTerm ctx (Typ a))
ctxSort s = CtxTerm <$> mkFlatTermF (Sort s)

-- | Apply two 'CtxTerm's
ctxApply :: MonadTerm m => m (CtxTerm ctx (a -> b)) -> m (CtxTerm ctx a) ->
            m (CtxTerm ctx b)
ctxApply fm argm =
  do CtxTerm f <- fm
     CtxTerm arg <- argm
     CtxTerm <$> mkTermF (App f arg)

-- | Apply two 'CtxTerm's, using a 'Proxy' to tell GHC the types
ctxApplyProxy :: MonadTerm m => Proxy a -> Proxy b ->
                 m (CtxTerm ctx (a -> b)) -> m (CtxTerm ctx a) ->
                 m (CtxTerm ctx b)
ctxApplyProxy _ _ = ctxApply

-- | Apply a 'CtxTerm' to a list of arguments
ctxApplyMulti :: MonadTerm m =>
                 m (CtxTerm ctx (Arrows as b)) ->
                 m (CtxTerms ctx as) ->
                 m (CtxTerm ctx b)
ctxApplyMulti fm argsm =
  fm >>= \f -> argsm >>= \args -> helper f args
  where
    helper :: MonadTerm m => CtxTerm ctx (Arrows as b) ->
              CtxTerms ctx as -> m (CtxTerm ctx b)
    helper f CtxTermsNil = return f
    helper f (CtxTermsCons arg args) =
      do f' <- ctxApply (return f) (return arg)
         helper f' args

-- | Form a lambda-abstraction as a 'CtxTerm'
ctxLambda1 :: MonadTerm m => LocalName -> CtxTerm ctx (Typ a) ->
              (CtxTerm (ctx ::> a) a -> m (CtxTerm (ctx ::> a) b)) ->
              m (CtxTerm ctx (a -> b))
ctxLambda1 x (CtxTerm tp) body_f =
  do var <- ctxVar NoBind
     CtxTerm body <- body_f var
     CtxTerm <$> mkTermF (Lambda x tp body)

-- | Form a multi-arity lambda-abstraction as a 'CtxTerm'
ctxLambda :: MonadTerm m => Bindings CtxTerm ctx as ->
             (CtxTerms (CtxInvApp ctx as) as ->
              m (CtxTerm (CtxInvApp ctx as) a)) ->
             m (CtxTerm ctx (Arrows as a))
ctxLambda NoBind body_f = body_f CtxTermsNil
ctxLambda (Bind x tp xs) body_f =
  ctxLambda1 x tp $ \_ ->
  ctxLambda xs $ \vars ->
  do var <- ctxVar xs
     body_f (CtxTermsCons var vars)

-- | Form a pi-abstraction as a 'CtxTerm'
ctxPi1 :: MonadTerm m => LocalName -> CtxTerm ctx (Typ a) ->
          (CtxTerm (ctx ::> a) a ->
           m (CtxTerm (ctx ::> a) (Typ b))) ->
          m (CtxTerm ctx (Typ (a -> b)))
ctxPi1 x (CtxTerm tp) body_f =
  do var <- ctxVar NoBind
     CtxTerm body <- body_f var
     CtxTerm <$> mkTermF (Pi x tp body)

-- | Form a multi-arity pi-abstraction as a 'CtxTerm'
ctxPi :: MonadTerm m => Bindings CtxTerm ctx as ->
         (CtxTerms (CtxInvApp ctx as) as ->
          m (CtxTerm (CtxInvApp ctx as) (Typ b))) ->
         m (CtxTerm ctx (Typ (Arrows as b)))
ctxPi NoBind body_f = body_f CtxTermsNil
ctxPi (Bind x tp xs) body_f =
  ctxPi1 x tp $ \_ ->
  ctxPi xs $ \vars ->
  do var <- ctxVar xs
     body_f (CtxTermsCons var vars)

-- | Form a multi-arity pi-abstraction as a 'CtxTerm', using a 'Proxy' to tell
-- stupid GHC what the result type should be
ctxPiProxy :: MonadTerm m => Proxy (Typ b) -> Bindings CtxTerm ctx as ->
              (CtxTerms (CtxInvApp ctx as) as ->
               m (CtxTerm (CtxInvApp ctx as) (Typ b))) ->
              m (CtxTerm ctx (Typ (Arrows as b)))
ctxPiProxy _ = ctxPi

-- | Existential return type of 'ctxAsPi'
data CtxPi ctx =
  forall b c.
  CtxPi LocalName (CtxTerm ctx (Typ b)) (CtxTerm (ctx ::> b) (Typ c))

-- | Test if a 'CtxTerm' is a pi-abstraction, returning its components if so.
-- Note that we are not returning any equality constraints on the input type,
-- @a@; i.e., if a term is a pi-abstraction, one would expect @a@ to have the
-- form @b -> c@, but this would require a /lot/ more work...
ctxAsPi :: CtxTerm ctx (Typ a) -> Maybe (CtxPi ctx)
ctxAsPi (CtxTerm (unwrapTermF -> Pi x tp body)) =
  Just (CtxPi x (CtxTerm tp) (CtxTerm body))
ctxAsPi _ = Nothing

-- | Existential return type of 'ctxAsPiMulti'
data CtxMultiPi ctx =
  forall as b.
  CtxMultiPi (Bindings CtxTerm ctx as) (CtxTerm (CtxInvApp ctx as) (Typ b))

-- | Repeatedly apply 'ctxAsPi', returning the 'Bindings' list of 0 or more
-- pi-abstraction bindings in the given term
ctxAsPiMulti :: CtxTerm ctx (Typ a) -> CtxMultiPi ctx
ctxAsPiMulti (ctxAsPi -> Just (CtxPi x tp body)) =
  case ctxAsPiMulti body of
    CtxMultiPi as body' -> CtxMultiPi (Bind x tp as) body'
ctxAsPiMulti t = CtxMultiPi NoBind t

-- | Build an application of a datatype as a 'CtxTerm'
ctxDataTypeM :: MonadTerm m =>
  DataIdent d ->
  m (CtxTermsCtx ctx params) ->
  m (CtxTermsCtx ctx ixs) ->
  m (CtxTerm ctx (Typ d))
ctxDataTypeM (DataIdent d) paramsM ixsM =
  CtxTerm <$>
  (mkFlatTermF =<<
   (DataTypeApp d <$> (ctxTermsCtxToListUnsafe <$> paramsM) <*>
    (ctxTermsCtxToListUnsafe <$> ixsM)))


-- | Test if a 'CtxTerm' is an application of a specific datatype with the
-- supplied context of parameters and indices
ctxAsDataTypeApp :: DataIdent d -> Bindings tp1 EmptyCtx params ->
                    Bindings tp2 (CtxInv params) ixs ->
                    CtxTerm ctx (Typ a) ->
                    Maybe (CtxTerms ctx params, CtxTerms ctx ixs)
ctxAsDataTypeApp (DataIdent d) params ixs (CtxTerm
                                           (unwrapTermF ->
                                            FTermF (DataTypeApp d' params' ixs')))
  | d == d'
  = do params_ret <- ctxTermsForBindingsOpen params params'
       ixs_ret <- ctxTermsForBindingsOpen ixs ixs'
       return (params_ret, ixs_ret)
ctxAsDataTypeApp _ _ _ _ = Nothing


-- | Build an application of a constructor as a 'CtxTerm'
ctxCtorAppM :: MonadTerm m =>
  DataIdent d ->
  PrimName Term ->
  m (CtxTermsCtx ctx params) ->
  m (CtxTermsCtx ctx args) ->
  m (CtxTerm ctx d)
ctxCtorAppM _d c paramsM argsM =
  CtxTerm <$>
  (mkFlatTermF =<<
   (CtorApp c <$> (ctxTermsCtxToListUnsafe <$> paramsM) <*>
    (ctxTermsCtxToListUnsafe <$> argsM)))

data Rec d

ctxRecursorAppM :: MonadTerm m =>
  m (CtxTerm ctx (Rec d)) ->
  m (CtxTermsCtx ctx ixs) ->
  m (CtxTerm ctx d) ->
  m (CtxTerm ctx a)
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
  ctxLift :: InvBindings tp1 ctx ctx' -> Bindings tp2 ctx as ->
             f (ctx <+> ctx') a ->
             m (f (CtxInvApp ctx as <+> ctx') a)
  -- | Substitute a list of terms into an @f@
  ctxSubst :: CtxTermsCtx ctx1 subst ->
              InvBindings tp (ctx1 <+> subst) ctx2 ->
              f ((ctx1 <+> subst) <+> ctx2) a ->
              m (f (ctx1 <+> ctx2) a)

-- | Lift an @f@ into a context extended with one type
ctxLift1 :: CtxLiftSubst f m => f ctx b -> m (f (ctx ::> a) b)
ctxLift1 = ctxLift InvNoBind (Bind "_" CtxUnit NoBind)

-- | Lift an @f@ that is in an extended list of 'Bindings'
ctxLiftInBindings :: CtxLiftSubst f m => InvBindings tp1 ctx ctx1 ->
                     Bindings tp2 (ctx <+> ctx1) ctx2 ->
                     Bindings tp3 ctx as ->
                     f (CtxInvApp (ctx <+> ctx1) ctx2) a ->
                     m (f (CtxInvApp (CtxInvApp ctx as <+> ctx1) ctx2) a)
ctxLiftInBindings = helper . mapInvBindings (CtxEither . Left)
  where
    helper :: CtxLiftSubst f m => InvBindings (CtxEither tp1 tp2) ctx ctx1 ->
              Bindings tp2 (ctx <+> ctx1) ctx2 ->
              Bindings tp3 ctx as ->
              f (CtxInvApp (ctx <+> ctx1) ctx2) a ->
              m (f (CtxInvApp (CtxInvApp ctx as <+> ctx1) ctx2) a)
    helper ctx1 NoBind as = ctxLift ctx1 as
    helper ctx1 (Bind str tp ctx2) as =
      helper (InvBind ctx1 str (CtxEither $ Right tp)) ctx2 as

-- | Substitute into an @f@ that is in an extended list of 'Bindings'
ctxSubstInBindings :: CtxLiftSubst f m => CtxTermsCtx ctx1 subst ->
                      InvBindings tp1 (ctx1 <+> subst) ctx2 ->
                      Bindings tp2 ((ctx1 <+> subst) <+> ctx2) ctx3 ->
                      f (CtxInvApp ((ctx1 <+> subst) <+> ctx2) ctx3) a ->
                      m (f (CtxInvApp (ctx1 <+> ctx2) ctx3) a)
ctxSubstInBindings subst =
  helper subst . mapInvBindings (CtxEither . Left) where
  helper :: CtxLiftSubst f m => CtxTermsCtx ctx1 s ->
            InvBindings (CtxEither tp1 tp2) (ctx1 <+> s) ctx2 ->
            Bindings tp2 ((ctx1 <+> s) <+> ctx2) ctx3 ->
            f (CtxInvApp ((ctx1 <+> s) <+> ctx2) ctx3) a ->
            m (f (CtxInvApp (ctx1 <+> ctx2) ctx3) a)
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

instance MonadTerm m => CtxLiftSubst (CtorArg d ixs) m where
  ctxLift ctx1 ctx2 (ConstArg tp) = ConstArg <$> ctxLift ctx1 ctx2 tp
  ctxLift ctx1 ctx2 (RecursiveArg zs ixs) =
    RecursiveArg <$> ctxLift ctx1 ctx2 zs <*>
    ctxLiftInBindings ctx1 zs ctx2 ixs
  ctxSubst subst ctx (ConstArg tp) = ConstArg <$> ctxSubst subst ctx tp
  ctxSubst subst ctx (RecursiveArg zs ixs) =
    RecursiveArg <$> ctxSubst subst ctx zs <*>
    ctxSubstInBindings subst ctx zs ixs

-- | Make a closed term and then lift it into a context
mkLiftedClosedTerm :: MonadTerm m => Bindings tp EmptyCtx as -> Term ->
                      m (CtxTerm (CtxInv as) a)
mkLiftedClosedTerm inners t = ctxLift InvNoBind inners $ mkClosedTerm t


--
-- * Constructor Argument Types
--

-- | A specification of the type of an argument for a constructor of datatype
-- @d@, that has a specified list @ixs@ of indices, inside a context @ctx@ of
-- parameters and earlier arguments
data CtorArg d ixs ctx a where
  -- | A fixed, constant type
  ConstArg :: CtxTerm ctx (Typ a) -> CtorArg d ixs ctx (Typ a)
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
    Bindings CtxTerm ctx zs ->
    CtxTerms (CtxInvApp ctx zs) ixs ->
    CtorArg d ixs ctx (Typ (Arrows zs d))

-- | A structure that defines the parameters, arguments, and return type indices
-- of a constructor, using 'CtxTerm' and friends to get the bindings right
data CtorArgStruct d params ixs =
  forall args.
  CtorArgStruct
  {
    ctorParams :: Bindings CtxTerm EmptyCtx params,
    ctorArgs :: Bindings (CtorArg d ixs) (CtxInv params) args,
    ctorIndices :: CtxTerms (CtxInvApp (CtxInv params) args) ixs,
    dataTypeIndices :: Bindings CtxTerm (CtxInv params) ixs
  }


-- | Convert a 'CtorArg' into the type that it represents, given a context of
-- the parameters and of the previous arguments
ctxCtorArgType :: MonadTerm m => DataIdent d ->
                  InvBindings CtxTerm EmptyCtx params ->
                  InvBindings CtxTerm params prevs ->
                  CtorArg d ixs (params <+> prevs) a ->
                  m (CtxTerm (params <+> prevs) a)
ctxCtorArgType _ _ _ (ConstArg tp) = return tp
ctxCtorArgType d params prevs (RecursiveArg zs_ctx ixs) =
  ctxPi zs_ctx $ \_ ->
  ctxDataTypeM d ((fst <$> ctxVars2 params prevs) >>= ctxLift InvNoBind zs_ctx)
  (return $ invertCtxTerms ixs)

-- | Convert a bindings list of 'CtorArg's to a binding list of types
ctxCtorArgBindings :: MonadTerm m => DataIdent d ->
                      InvBindings CtxTerm EmptyCtx params ->
                      InvBindings CtxTerm params prevs ->
                      Bindings (CtorArg d ixs) (params <+> prevs) args ->
                      m (Bindings CtxTerm (params <+> prevs) args)
ctxCtorArgBindings _ _ _ NoBind = return NoBind
ctxCtorArgBindings d params prevs (Bind x arg args) =
  do tp <- ctxCtorArgType d params prevs arg
     rest <- ctxCtorArgBindings d params (InvBind prevs x tp) args
     return (Bind x tp rest)

-- | Compute the type of a constructor from the name of its datatype and its
-- 'CtorArgStruct'
ctxCtorType :: MonadTerm m => PrimName Term -> CtorArgStruct d params ixs -> m Term
ctxCtorType d (CtorArgStruct{..}) =
  elimClosedTerm <$>
  (ctxPi ctorParams $ \params ->
    do bs <-
         ctxCtorArgBindings (DataIdent d) (invertBindings ctorParams)
         InvNoBind ctorArgs
       ctxPi bs $ \_ ->
         ctxDataTypeM (DataIdent d)
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
ctxPRetTp :: MonadTerm m => Proxy (Typ a) -> DataIdent d ->
             InvBindings CtxTerm EmptyCtx ps ->
             Bindings CtxTerm ps ixs -> Sort ->
             m (CtxTerm ps (Typ (Arrows ixs (d -> Typ a))))
ctxPRetTp (_ :: Proxy (Typ a)) (d :: DataIdent d) params ixs s =
  ctxPiProxy (Proxy :: Proxy (Typ (d -> Typ a))) ixs $ \ix_vars ->
  do param_vars <- ctxVars params
     dt <- ctxDataTypeM d (ctxLift InvNoBind ixs param_vars)
       (return $ invertCtxTerms ix_vars)
     ctxPi1 "_" dt $ \_ -> ctxSort s

-- | Like 'ctxPRetTp', but also take in a list of parameters and substitute them
-- for the parameter variables returned by that function
mkPRetTp :: MonadTerm m =>
  PrimName Term ->
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
          do p_ret <- (ctxPRetTp Proxy (DataIdent d)
                       (invertBindings p_ctx) ix_ctx s)
             elimClosedTerm <$>
               ctxSubst (invertCtxTerms params) InvNoBind
               (castPRet (invertBindings p_ctx) p_ret)
        (_, Nothing) ->
          error "mkPRetTp: incorrect number of parameters"
  where
    castPRet :: InvBindings tp ctx1 ctx -> CtxTerm ctx a ->
                CtxTerm (EmptyCtx <+> ctx) a
    castPRet ctx =
      case ctxAppNilEq ctx of
        Refl -> id


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
  Proxy (Typ ret) ->
  Proxy (Typ a) ->
  DataIdent d ->
  PrimName Term ->
  CtorArgStruct d params ixs ->
  m (CtxTerm (CtxInv params ::>(Arrows ixs (d -> Typ a))) (Typ ret))
ctxCtorElimType ret (a_top :: Proxy (Typ a)) (d_top :: DataIdent d) c
  (CtorArgStruct{..}) =
  (do let params = invertBindings ctorParams
      -- NOTE: we use propSort for the type of p_ret just as arbitrary sort, but
      -- it doesn't matter because p_ret_tp is only actually used to form
      -- contexts, and is never actually used directly in the output
      p_ret_tp <- ctxPRetTp a_top d_top params dataTypeIndices propSort

      -- Lift the argument and return indices into the context of p_ret
      args <- ctxLift InvNoBind (Bind "_" p_ret_tp NoBind) ctorArgs
      ixs <-
        ctxLiftInBindings InvNoBind ctorArgs (Bind "_" p_ret_tp NoBind)
        ctorIndices
      -- Form the context (params ::> p_ret)
      let params_pret = InvBind params "_" (ctxLiftNil params p_ret_tp)
      -- Call the helper and cast the result to (Typ ret)
      castCtxTerm Proxy ret <$>
        helper a_top d_top params_pret InvNoBind args ixs
  ) where

  -- Iterate through the argument types of the constructor, building up a
  -- function from those arguments to the result type of the p_ret function.
  -- Note that, technically, this function also takes in recursive calls, so has
  -- a slightly richer type, but we are not going to try to compute this richer
  -- type in Haskell land.
  helper :: MonadTerm m =>
    Proxy (Typ a) ->
    DataIdent d ->
    InvBindings CtxTerm EmptyCtx (ps ::> Arrows ixs (d -> Typ a)) ->
    InvBindings CtxTerm (ps ::> Arrows ixs (d -> Typ a)) prevs ->
    Bindings (CtorArg d ixs) ((ps ::> Arrows ixs (d -> Typ a)) <+> prevs) args ->
    CtxTerms (CtxInvApp ((ps ::> Arrows ixs (d -> Typ a)) <+> prevs) args) ixs ->
    m (CtxTerm ((ps ::> Arrows ixs (d -> Typ a)) <+> prevs) (Typ (Arrows args a)))
  helper _a d params_pret prevs NoBind ret_ixs =
    -- If we are finished with our arguments, construct the final result type
    -- (p_ret ret_ixs (c params prevs))
    do (vars, prev_vars) <- ctxVars2 params_pret prevs
       let (param_terms, p_ret) = ctxTermsCtxHeadTail vars
       ctxApply (ctxApplyMulti (return p_ret) (return ret_ixs)) $
         ctxCtorAppM d c (return param_terms) (return prev_vars)
  helper a d params_pret prevs (Bind str (ConstArg tp) args) ixs =
    -- For a constant argument type, just abstract it and continue
    (ctxPi (Bind str tp NoBind) $ \_ ->
      helper a d params_pret (InvBind prevs str tp) args ixs)
  helper (a :: Proxy (Typ a)) (d::DataIdent d) params_pret
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
             helper a d params_pret (InvBind prevs str arg_tp) args ixs
           -- Build the type of ih, in the context of arg
           ih_tp <- ctxPi zs' $ \z_vars ->
             ctxApplyProxy (Proxy :: Proxy d) (Proxy :: Proxy (Typ a))
             (ctxApplyMulti
              (ctxLift InvNoBind (Bind "_" arg_tp zs') p_ret) (return ts'))
             (ctxApplyMulti (ctxLift InvNoBind zs' arg) (return z_vars))
           -- Finally, build the pi-abstraction for ih around the rest
           --
           -- NOTE: we cast away the IH argument, because that is a type that is
           -- computed from the argument structure, and we cannot (well, we
           -- could, but it would be much more work to) express that computation
           -- in the Haskell type system
           castCtxTerm Proxy Proxy <$>
             (ctxPi1 "_" ih_tp $ \_ ->
               ctxLift InvNoBind (Bind "_" ih_tp NoBind) rest)

-- | Build a function that substitutes parameters and a @p_ret@ return type
-- function into the type of an eliminator, as returned by 'ctxCtorElimType',
-- for the given constructor. We return the substitution function in the monad
-- so that we only call 'ctxCtorElimType' once but can call the function many
-- times, in order to amortize the overhead of 'ctxCtorElimType'.
mkCtorElimTypeFun :: MonadTerm m =>
  PrimName Term {- ^ data type -} ->
  PrimName Term {- ^ constructor type -} ->
  CtorArgStruct d params ixs ->
  m ([Term] -> Term -> m Term)
mkCtorElimTypeFun d c argStruct@(CtorArgStruct {..}) =
  do ctxElimType <- ctxCtorElimType Proxy Proxy (DataIdent d) c argStruct
     case ctxAppNilEq (invertBindings ctorParams) of
       Refl ->
         return $ \params p_ret ->
         whnfTerm =<<
         case ctxTermsForBindings ctorParams params of
           Nothing -> error "ctorElimTypeFun: wrong number of parameters!"
           Just paramsCtx ->
             elimClosedTerm <$>
             ctxSubstInBindings
             (CtxTermsCtxCons (invertCtxTerms paramsCtx) (mkClosedTerm p_ret))
             InvNoBind NoBind ctxElimType


-- | Reduce an application of a recursor. This is known in the Coq literature as
-- an iota reduction. More specifically, the call
--
-- > ctxReduceRecursor d [p1, .., pn] P [(c1,f1), .., (cm,fm)] ci [x1, .., xk]
--
-- reduces the term @(RecursorApp d ps P cs_fs ixs (CtorApp ci ps xs))@ to
--
-- > fi x1 (maybe rec_tm_1) .. xk (maybe rec_tm_k)
--
-- where @maybe rec_tm_i@ indicates an optional recursive call of the recursor
-- on one of the @xi@. These recursive calls only exist for those arguments @xi@
-- that are recursive arguments, i.e., that are specified with 'RecursiveArg',
-- and are omitted for non-recursive arguments specified by 'ConstArg'.
--
-- Specifically, for a @'RecursiveArg' zs ixs@ argument @xi@, which has type
-- @\(z1::Z1) -> .. -> d p1 .. pn ix1 .. ixp@, we build the recursive call
--
-- > \(z1::[ps/params,xs/args]Z1) -> .. ->
-- >   RecursorApp d ps P cs_fs [ps/params,xs/args]ixs (xi z1 ... zn)
--
-- where @[ps/params,xs/args]@ substitutes the concrete parameters @pi@ for the
-- parameter variables of the inductive type and the earlier constructor
-- arguments @xs@ for the remaining free variables.

ctxReduceRecursor :: forall m d params ixs.
  MonadTerm m =>
  Term {- ^ abstracted recursor -} ->
  Term {- ^ constructor elimnator function -} ->
  [Term] {- ^ constructor arguments -} ->
  CtorArgStruct d params ixs {- ^ constructor formal argument descriptor -} ->
  m Term
ctxReduceRecursor rec elimf c_args CtorArgStruct{..} =
  let inctx :: Term -> CtxTerm (CtxInv params) tp
      inctx = CtxTerm
   in
  case ctxTermsForBindingsOpen ctorArgs c_args of
     Just argsCtx ->
       ctxReduceRecursor_ (inctx rec) (inctx elimf) argsCtx ctorArgs
     Nothing ->
       error "ctxReduceRecursorRaw: wrong number of constructor arguments!"


ctxReduceRecursor_ :: forall m amb d ixs elim args.
  MonadTerm m =>
  CtxTerm amb (Rec d) ->
  CtxTerm amb elim ->
  CtxTerms amb args {- ^ constructor actual arguments -} ->
  Bindings (CtorArg d ixs) amb args
    {- ^ telescope describing the constructor arguments -} ->
  m Term
ctxReduceRecursor_ rec fi args0 argCtx =
  do args <- mk_args CtxTermsCtxNil args0 argCtx
     whnfTerm =<< foldM (\f arg -> mkTermF $ App f arg) (unAmb fi) args

 where
    unAmb :: forall tp. CtxTerm amb tp -> Term
    unAmb (CtxTerm t) = t

    mk_args :: forall ctx xs.
               CtxTermsCtx amb ctx ->  -- already processed parameters/arguments
               CtxTerms    amb xs ->   -- remaining actual arguments to process
               Bindings (CtorArg d ixs) (amb<+>ctx) xs ->
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

    -- Build an individual recursive call, given the parameters, the bindings
    -- for the RecursiveArg, and the argument we are going to recurse on
    mk_rec_arg :: forall zs.
      Bindings CtxTerm amb zs ->         -- telescope describing the zs
      CtxTerms (CtxInvApp amb zs) ixs -> -- actual values for the indicies, shifted under zs
      CtxTerm amb (Arrows zs d) ->       -- actual value in recursive position
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
  usesDataType :: DataIdent d -> a -> Bool

instance UsesDataType (TermF Term) where
  usesDataType (DataIdent d) (FTermF (DataTypeApp d' _ _))
    | d' == d = True
  usesDataType (DataIdent d) (FTermF (RecursorType d' _ _ _))
    | d' == d = True
  usesDataType (DataIdent d) (FTermF (Recursor rec))
    | recursorDataType rec == d = True
  usesDataType d tf = any (usesDataType d) tf

instance UsesDataType Term where
  usesDataType d = usesDataType d . unwrapTermF

instance UsesDataType (CtxTerm ctx a) where
  usesDataType d (CtxTerm t) = usesDataType d t

instance UsesDataType (Bindings CtxTerm ctx as) where
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
asCtorDTApp :: DataIdent d -> Bindings CtxTerm EmptyCtx params ->
               Bindings CtxTerm (CtxInv params) ixs ->
               InvBindings tp1 (CtxInv params) ctx1 ->
               Bindings tp2 (CtxInv params <+> ctx1) ctx2 ->
               CtxTerm (CtxInvApp (CtxInv params <+> ctx1) ctx2) (Typ a) ->
               Maybe (CtxTerms (CtxInvApp (CtxInv params <+> ctx1) ctx2) ixs)
asCtorDTApp d params dt_ixs ctx1 ctx2 (ctxAsDataTypeApp d params dt_ixs ->
                                       Just (param_vars, ixs))
  | isVarList Proxy params ctx1 ctx2 param_vars &&
    not (any (usesDataType d) $ ctxTermsToListUnsafe ixs)
  = Just ixs
  where
    -- Check that the given list of terms is a list of bound variables, one for
    -- each parameter, in the context extended by the given arguments
    isVarList :: Proxy prev_params ->
                 Bindings tp1 prev_params params ->
                 InvBindings tp2 (CtxInvApp prev_params params) ctx1 ->
                 Bindings tp3 (CtxInvApp prev_params params <+> ctx1) ctx2 ->
                 CtxTerms (CtxInvApp
                           (CtxInvApp prev_params params <+> ctx1) ctx2) params ->
                 Bool
    isVarList _ _ _ _ CtxTermsNil = True
    isVarList _ (Bind _ _ ps) c1 c2 (CtxTermsCons
                                     (CtxTerm (unwrapTermF -> LocalVar i)) ts) =
      i == bindingsLength ps + invBindingsLength c1 + bindingsLength c2 &&
      isVarList Proxy ps c1 c2 ts
    isVarList _ _ _ _ _ = False
asCtorDTApp _ _ _ _ _ _ = Nothing


-- | Existential return type for 'asCtorArg'
data ExCtorArg d ixs ctx =
  forall a. ExCtorArg (CtorArg d ixs ctx (Typ a))

-- | Check that an argument for a constructor has one of the allowed forms
asCtorArg :: DataIdent d -> Bindings CtxTerm EmptyCtx params ->
             Bindings CtxTerm (CtxInv params) ixs ->
             InvBindings tp (CtxInv params) prevs ->
             CtxTerm (CtxInv params <+> prevs) (Typ a) ->
             Maybe (ExCtorArg d ixs (CtxInv params <+> prevs))
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
data CtxPiCtorArg d ixs ctx =
  forall a b .
  CtxPiCtorArg LocalName (CtorArg d ixs ctx (Typ a))
  (CtxTerm (ctx ::> a) (Typ b))

-- | Check that a constructor type is a pi-abstraction that takes as input an
-- argument of one of the allowed forms described by 'CtorArg'
asPiCtorArg :: DataIdent d -> Bindings CtxTerm EmptyCtx params ->
               Bindings CtxTerm (CtxInv params) ixs ->
               InvBindings tp (CtxInv params) prevs ->
               CtxTerm (CtxInv params <+> prevs) (Typ a) ->
               Maybe (CtxPiCtorArg d ixs (CtxInv params <+> prevs))
asPiCtorArg d params dt_ixs prevs (ctxAsPi ->
                                   Just (CtxPi x
                                         (asCtorArg d params dt_ixs prevs ->
                                          Just (ExCtorArg arg)) rest)) =
  Just $ CtxPiCtorArg x arg (castTopCtxElem rest)
  where
    castTopCtxElem :: CtxTerm (ctx ::> a1) b -> CtxTerm (ctx ::> a2) b
    castTopCtxElem (CtxTerm t) = CtxTerm t
asPiCtorArg _ _ _ _ _ = Nothing

-- | Existential return type of 'mkCtorArgsIxs'
data CtorArgsIxs d ixs prevs =
  forall args.
  CtorArgsIxs (Bindings (CtorArg d ixs) prevs args)
  (CtxTerms (CtxInvApp prevs args) ixs)

-- | Helper function for 'mkCtorArgStruct'
mkCtorArgsIxs :: DataIdent d -> Bindings CtxTerm EmptyCtx params ->
                 Bindings CtxTerm (CtxInv params) ixs ->
                 InvBindings (CtorArg d ixs) (CtxInv params) prevs ->
                 CtxTerm (CtxInv params <+> prevs) (Typ a) ->
                 Maybe (CtorArgsIxs d ixs (CtxInv params <+> prevs))
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
  PrimName Term ->
  Bindings CtxTerm EmptyCtx params ->
  Bindings CtxTerm (CtxInv params) ixs ->
  Term ->
  Maybe (CtorArgStruct d params ixs)
mkCtorArgStruct d params dt_ixs ctor_tp =
  case mkCtorArgsIxs (DataIdent d) params dt_ixs InvNoBind (CtxTerm ctor_tp) of
    Just (CtorArgsIxs args ctor_ixs) ->
      Just (CtorArgStruct params args ctor_ixs dt_ixs)
    Nothing -> Nothing
