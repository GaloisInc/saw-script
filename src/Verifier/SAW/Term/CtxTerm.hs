{-# LANGUAGE RankNTypes #-}
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
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PartialTypeSignatures #-}

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
  Ctx(..), CtxApp, CtxInvApp, Arrows
  , ctxTermsForBindings, invAppendBindings, invertBindings
  , CtxTerm(..), CtxTerms(..), CtxTermsCtx(..)
  , Typ, mkClosedTerm, mkClosedTyp, elimClosedTerm
  , Bindings(..), InvBindings(..), InBindings(..)
  , mkLiftedClosedTerm
  , ctxLambda, ctxPi, ctxPi1
  , MonadTerm(..), CtxLiftSubst(..), ctxLift1, ctxLiftInBindings
  , CtorArg(..), CtorArgStruct(..), ctxCtorArgType
  , ctxCtorType, ctxCtorElimType, ctxReduceRecursor
  ) where

import Data.Proxy
import Data.Type.Equality
import Control.Monad

import Verifier.SAW.Term.Functor


--
-- * Contexts and Bindings
--

-- | A representation of the type of SAW types as a Haskell type. This is
-- actually a singleton type, meaning that a 'CtxTerm' with type @'Typ' a@ is a
-- SAW type that is represented by Haskell type @a@. Of course, the Haskell type
-- system is not rich enough to capture SAW types in complete detail, but we do
-- our best, and capture at least the types and functions.
data Typ (a :: *)

-- | An identifier for a datatype that is statically associated with Haskell
-- type @d@. Again, we cannot capture all of the SAW type system in Haskell, so
-- we simplify datatypes to arbitrary Haskell types.
newtype DataIdent d = DataIdent Ident

-- | We use DataKinds to represent contexts of free variables at the type level.
-- These contexts are "inside-out", meaning that the most recently-bound
-- variable is listed on the outside. We reflect this by having that most
-- recently-bound variable to the right in 'CCons'.
data Ctx a = CNil | CCons (Ctx a) a

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
  Bind :: String -> tp ctx (Typ a) -> Bindings tp ('CCons ctx a) as ->
          Bindings tp ctx (a ': as)

-- | Compute the number of bindings in a bindings list
bindingsLength :: Bindings tp ctx as -> Int
bindingsLength NoBind = 0
bindingsLength (Bind _ _ bs) = 1 + bindingsLength bs

-- | An inverted list of bindings, seen from the "inside out"
data InvBindings (tp :: Ctx * -> * -> *) (ctx :: Ctx *) (as :: Ctx *) where
  InvNoBind :: InvBindings tp ctx 'CNil
  InvBind :: InvBindings tp ctx as -> String -> tp (CtxApp ctx as) (Typ a) ->
             InvBindings tp ctx ('CCons as a)

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

-- | Typeclass for things from which we can build proofs that 'CNil' is the left
-- unit of 'CtxApp', i.e., that @'CtxApp' 'CNil' ctx@
class CtxAppNilEq f where
  ctxAppNilEq :: f ctx -> CtxApp 'CNil ctx :~: ctx

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

-- | Use 'ctxAppNilEq' to lift from @ctx@ to @'CtxApp' 'CNil' ctx@
ctxLiftNil :: InvBindings tp 'CNil ctx -> f ctx a -> f (CtxApp 'CNil ctx) a
ctxLiftNil ctx f = case ctxAppNilEq ctx of Refl -> f

{-
-- | Build a proof that 'CtxInvApp' commutes with 'CtxApp'
ctxAppInvAssocEq :: c1 ctx1 -> InvBindings tp2 ctx ctx2 -> c3 ctx3 ->
                    CtxInvApp (CtxApp ctx1 ctx2) ctx3 :~:
                    CtxApp ctx1 (CtxInvApp ctx2 ctx3)
ctxAppInvAssocEq _ InvNoBind _ = error "FIXME HERE NOW"
ctxAppInvAssocEq ctx1 (InvBind ctx2 _ (tp :: tp _ (Typ a))) (ctx3 :: c3 ctx3) =
  case ctxAppInvAssocEq ctx1 ctx2 (Proxy :: Proxy (a ': ctx3)) of
    Refl -> Refl
-}

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

-- | Append two inverted contexts, where the first one is top-level. This
-- restriction allows us to avoid writing a proof of associativity of 'CtxApp',
-- and instead just using 'ctxAppNilEq'
appendTopInvBindings :: InvBindings tp 'CNil ctx1 ->
                        InvBindings tp ctx1 ctx2 ->
                        InvBindings tp 'CNil (CtxApp ctx1 ctx2)
appendTopInvBindings ctx1 InvNoBind = ctx1
appendTopInvBindings ctx1 (InvBind ctx2 x tp) =
  let ret = appendTopInvBindings ctx1 ctx2 in
  InvBind ret x (ctxLiftNil ret tp)

-- | A sequence of bindings bundled with something that is relative to those
-- bindings
data InBindings tp (f :: Ctx * -> k -> *) ctx (a::k) where
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
-- "types" are usually instantiated with a dummy, such as the unit type, but the
-- code that consumes them cannot know that and has to be agnostic to what type
-- it is.
newtype CtxTerm (ctx :: Ctx *) (a :: *) = CtxTerm Term

-- | Because we cannot capture the SAW type system in Haskell, sometimes we have
-- to cast our terms. We try not to use this very often, and we only allow
-- casting the output type, not the context, since the latter could screw up our
-- deBruijn indices.
castCtxTerm :: Proxy a -> Proxy b -> CtxTerm ctx a -> CtxTerm ctx b
castCtxTerm _ _ (CtxTerm t) = CtxTerm t

-- | Build a term in the empty context
mkClosedTerm :: Term -> CtxTerm 'CNil a
mkClosedTerm = CtxTerm

-- | Build a term to represent a type in the empty context
mkClosedTyp :: Term -> CtxTerm 'CNil (Typ a)
mkClosedTyp = mkClosedTerm

-- | Take a term out of the empty context
elimClosedTerm :: CtxTerm 'CNil a -> Term
elimClosedTerm (CtxTerm t) = t

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
  CtxTermsCtxNil :: CtxTermsCtx ctx 'CNil
  CtxTermsCtxCons :: CtxTermsCtx ctx as -> CtxTerm ctx a ->
                     CtxTermsCtx ctx ('CCons as a)

{-
-- | Get the head and tail of a non-empty 'CtxTerms' list
ctxTermsHeadTail :: CtxTerms ctx (a ': as) -> (CtxTerm ctx a, CtxTerms ctx as)
ctxTermsHeadTail (CtxTermsCons a as) = (a, as)
-}

-- | Get the head and tail of a non-empty 'CtxTermsCtx' list
ctxTermsCtxHeadTail :: CtxTermsCtx ctx ('CCons as a) ->
                       (CtxTermsCtx ctx as, CtxTerm ctx a)
ctxTermsCtxHeadTail (CtxTermsCtxCons as a) = (as, a)

{-
-- | Convert a typed list of terms to a list of untyped terms; this is unsafe
ctxTermsToListUnsafe :: CtxTerms ctx as -> [Term]
ctxTermsToListUnsafe CtxTermsNil = []
ctxTermsToListUnsafe (CtxTermsCons (CtxTerm t) ts) =
  t : ctxTermsToListUnsafe ts
-}

-- | Convert a typed list of terms to a list of untyped terms; this is unsafe
ctxTermsCtxToListUnsafe :: CtxTermsCtx ctx as -> [Term]
ctxTermsCtxToListUnsafe CtxTermsCtxNil = []
ctxTermsCtxToListUnsafe (CtxTermsCtxCons ts (CtxTerm t)) =
  ctxTermsCtxToListUnsafe ts ++ [t]

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

splitCtxTermsCtx :: InvBindings tp any_ctx ctx2 ->
                    CtxTermsCtx ctx (CtxApp ctx1 ctx2) ->
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
  substTerm :: DeBruijnIndex -> [Term] -> Term -> m Term
               -- ^ NOTE: the first term in the list is substituted for the most
               -- recently-bound variable, i.e., deBruijn index 0

mkFlatTermF :: MonadTerm m => FlatTermF Term -> m Term
mkFlatTermF = mkTermF . FTermF

ctxVar :: MonadTerm m => Bindings tp ('CCons ctx1 a) ctx2 ->
          m (CtxTerm (CtxInvApp ('CCons ctx1 a) ctx2) a)
ctxVar ctx = CtxTerm <$> mkTermF (LocalVar $ bindingsLength ctx)

ctxVars :: MonadTerm m => InvBindings tp 'CNil ctx -> m (CtxTermsCtx ctx ctx)
ctxVars ctx_top =
  case ctxAppNilEq ctx_top of
    Refl -> helper ctx_top NoBind
      where
        helper :: MonadTerm m => InvBindings tp 'CNil ctx ->
                  Bindings tp (CtxApp 'CNil ctx) as ->
                  m (CtxTermsCtx (CtxInvApp (CtxApp 'CNil ctx) as) ctx)
        helper InvNoBind _ = return CtxTermsCtxNil
        helper (InvBind vars_ctx x tp) ctx =
          CtxTermsCtxCons <$> helper vars_ctx (Bind x tp ctx) <*> ctxVar ctx

ctxVars2 :: MonadTerm m => InvBindings tp 'CNil ctx1 ->
            InvBindings tp ctx1 ctx2 ->
            m (CtxTermsCtx (CtxApp ctx1 ctx2) ctx1,
               CtxTermsCtx (CtxApp ctx1 ctx2) ctx2)
ctxVars2 vars1 vars2 =
  splitCtxTermsCtx vars2 <$> ctxVars (appendTopInvBindings vars1 vars2)

ctxTyp0 :: MonadTerm m => m (CtxTerm ctx (Typ a))
ctxTyp0 = CtxTerm <$> mkFlatTermF (Sort $ mkSort 0)

ctxApply :: MonadTerm m => m (CtxTerm ctx (a -> b)) -> m (CtxTerm ctx a) ->
            m (CtxTerm ctx b)
ctxApply fm argm =
  do CtxTerm f <- fm
     CtxTerm arg <- argm
     CtxTerm <$> mkTermF (App f arg)

ctxApplyProxy :: MonadTerm m => Proxy a -> Proxy b ->
                 m (CtxTerm ctx (a -> b)) -> m (CtxTerm ctx a) ->
                 m (CtxTerm ctx b)
ctxApplyProxy _ _ = ctxApply

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

ctxLambda1 :: MonadTerm m => String -> CtxTerm ctx (Typ a) ->
              (CtxTerm ('CCons ctx a) a -> m (CtxTerm ('CCons ctx a) b)) ->
              m (CtxTerm ctx (a -> b))
ctxLambda1 x (CtxTerm tp) body_f =
  do var <- ctxVar NoBind
     CtxTerm body <- body_f var
     CtxTerm <$> mkTermF (Lambda x tp body)

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

ctxPi1 :: MonadTerm m => String -> CtxTerm ctx (Typ a) ->
          (CtxTerm ('CCons ctx a) a ->
           m (CtxTerm ('CCons ctx a) (Typ b))) ->
          m (CtxTerm ctx (Typ (a -> b)))
ctxPi1 x (CtxTerm tp) body_f =
  do var <- ctxVar NoBind
     CtxTerm body <- body_f var
     CtxTerm <$> mkTermF (Pi x tp body)

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

ctxPiProxy :: MonadTerm m => Proxy (Typ b) -> Bindings CtxTerm ctx as ->
              (CtxTerms (CtxInvApp ctx as) as ->
               m (CtxTerm (CtxInvApp ctx as) (Typ b))) ->
              m (CtxTerm ctx (Typ (Arrows as b)))
ctxPiProxy _ = ctxPi

ctxDataTypeM :: MonadTerm m => DataIdent d -> m (CtxTermsCtx ctx params) ->
                m (CtxTermsCtx ctx ixs) -> m (CtxTerm ctx (Typ d))
ctxDataTypeM (DataIdent d) params ixs =
  do ftf <-
       DataTypeApp d <$> (ctxTermsCtxToListUnsafe <$> params) <*>
       (ctxTermsCtxToListUnsafe <$> ixs)
     CtxTerm <$> mkFlatTermF ftf

ctxCtorAppM :: MonadTerm m => DataIdent d -> Ident ->
               m (CtxTermsCtx ctx params) ->
               m (CtxTermsCtx ctx ixs) -> m (CtxTerm ctx d)
ctxCtorAppM = error "FIXME HERE NOW"

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
  ctxLift :: InvBindings tp1 ctx ctx' -> Bindings tp2 ctx as ->
             f (CtxApp ctx ctx') a ->
             m (f (CtxApp (CtxInvApp ctx as) ctx') a)
  -- | Substitute a list of terms into an @f@
  ctxSubst :: CtxTermsCtx ctx1 ctx2 ->
              InvBindings tp (CtxApp ctx1 ctx2) ctx3 ->
              f (CtxApp (CtxApp ctx1 ctx2) ctx3) a ->
              m (f (CtxApp ctx1 ctx3) a)

ctxLift1 :: CtxLiftSubst f m => f ctx b -> m (f ('CCons ctx a) b)
ctxLift1 = ctxLift InvNoBind (Bind "_" CtxUnit NoBind)

ctxLiftInBindings :: CtxLiftSubst f m => InvBindings tp1 ctx ctx1 ->
                     Bindings tp2 (CtxApp ctx ctx1) ctx2 ->
                     Bindings tp3 ctx as ->
                     f (CtxInvApp (CtxApp ctx ctx1) ctx2) a ->
                     m (f (CtxInvApp (CtxApp (CtxInvApp ctx as) ctx1) ctx2) a)
ctxLiftInBindings = helper . mapInvBindings (CtxEither . Left)
  where
    helper :: CtxLiftSubst f m => InvBindings (CtxEither tp1 tp2) ctx ctx1 ->
              Bindings tp2 (CtxApp ctx ctx1) ctx2 ->
              Bindings tp3 ctx as ->
              f (CtxInvApp (CtxApp ctx ctx1) ctx2) a ->
              m (f (CtxInvApp (CtxApp (CtxInvApp ctx as) ctx1) ctx2) a)
    helper ctx1 NoBind as = ctxLift ctx1 as
    helper ctx1 (Bind str tp ctx2) as =
      ctxLiftInBindings (InvBind ctx1 str (CtxEither $ Right tp)) ctx2 as


-- | Helper substitution function for when the ambient context is 'CNil'; i.e.,
-- this is a "proof" that @'CtxApp' CNil ctx@ equals @ctx@
ctxSubstNil :: CtxLiftSubst f m =>
               CtxTermsCtx 'CNil ctx1 -> Bindings tp ctx1 ctx2 ->
               f (CtxInvApp ctx1 ctx2) a ->
               m (f (CtxInv ctx2) a)
ctxSubstNil subst = helper subst InvNoBind where
  helper :: CtxLiftSubst f m => CtxTermsCtx 'CNil ctx1 ->
            InvBindings tp ctx1 ctx2 -> Bindings tp (CtxApp ctx1 ctx2) ctx3 ->
            f (CtxInvApp (CtxApp ctx1 ctx2) ctx3) a ->
            m (f (CtxInvApp ctx2 ctx3) a)
  helper s ctx2 NoBind f =
    case (ctxAppNilEq s, ctxAppNilEq ctx2) of
      (Refl, Refl) -> ctxSubst s ctx2 f
  helper s ctx2 (Bind x tp ctx3) f =
    helper s (InvBind ctx2 x tp) ctx3 f

instance MonadTerm m => CtxLiftSubst CtxTerm m where
  ctxLift ctx1 ctx2 (CtxTerm t) =
    CtxTerm <$> liftTerm 0 (invBindingsLength ctx1 + bindingsLength ctx2) t
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

{-
instance (CtxLiftSubst tp m, CtxLiftSubst f m) =>
         CtxLiftSubst (InBindings tp f) m where
  ctxLift ctx1 ctx2 (InBindings xs f) =
    do xs' <- ctxLift ctx1 ctx2 xs
       f' <- ctxLiftInBindings ctx1 xs ctx2 f
       return $ InBindings xs' f'
  ctxSubst ctx subst (InBindings xs f) =
    error "FIXME HERE NOW"
    {-
    do xs' <- ctxSubst ctx subst xs
       f' <- helper ctx xs subst f
       return $ InBindings xs' f'
         where
           helper :: CtxLiftSubst f m =>
                     InvBindings tp1 ctx ctx1 -> Bindings 
                     CtxTerms ctx as ->
                     f (CtxApp (CtxInvApp ctx as) ctx') a ->
                     m (f (CtxApp ctx ctx') a) -}
  {-
  ctxLift ctx1 ctx2 (InBindings bs f) =
    InBindings <$> ctxLift ctx1 ctx2 bs <*> ctxLift ctx1 ctx2 f
  ctxSubst subst1 subst2 ctx (InBindings bs f) =
    InBindings <$> ctxSubst subst1 subst2 ctx bs <*> ctxSubst subst1 subst2 ctx f
  -}
-}

instance MonadTerm m => CtxLiftSubst (CtorArg d ixs) m where
  ctxLift = error "FIXME HERE NOW"
  ctxSubst = error "FIXME HERE NOW"

-- | Make a closed term and then lift it into a context
mkLiftedClosedTerm :: MonadTerm m => Bindings tp 'CNil as -> Term ->
                      m (CtxTerm (CtxInv as) a)
mkLiftedClosedTerm inners t = ctxLift InvNoBind inners $ mkClosedTerm t


--
-- * Constructor Argument Types
--

-- | A specification of the type of an argument for a constructor of datatype
-- @d@, that has a specified list @ixs@ of indices, inside a context @ctx@ of
-- parameters and earlier arguments
data CtorArg d ixs ctx a where
  ConstArg :: CtxTerm ctx (Typ a) -> CtorArg d ixs ctx (Typ a)
    -- ^ A fixed, constant type
  RecursiveArg ::
    Bindings CtxTerm ctx zs -> CtxTerms (CtxInvApp ctx zs) ixs ->
    CtorArg d ixs ctx (Typ (Arrows zs d))
    -- ^ The construct @'RecursiveArg [(z1,tp1),..,(zn,tpn)] [e1,..,ek]'@
    -- specifies a recursive argument type of the form
    --
    -- > (z1::tp1) -> .. -> (zn::tpn) -> d p1 .. pm e1 .. ek
    --
    -- where @d@ is the datatype, the @zi::tpi@ are the elements of the Pi
    -- context (the first argument to 'RecursiveArgType'), the @pi@ are the
    -- parameters of @d@ (not given here), and the @ei@ are the type indices of
    -- @d@.

-- | A structure that defines the parameters, arguments, and return type indices
-- of a constructor, using 'CtxTerm' and friends to get the bindings right
data CtorArgStruct d params ixs =
  forall args.
  CtorArgStruct
  {
    ctorParams :: Bindings CtxTerm 'CNil params,
    ctorArgs :: Bindings (CtorArg d ixs) (CtxInv params) args,
    ctorIndices :: CtxTerms (CtxInvApp (CtxInv params) args) ixs
  }

-- | Convert a 'CtorArg' into the type that it represents, given a context of
-- the parameters and of the previous arguments
ctxCtorArgType :: MonadTerm m => DataIdent d ->
                  InvBindings CtxTerm 'CNil params ->
                  InvBindings CtxTerm params prevs ->
                  CtorArg d ixs (CtxApp params prevs) a ->
                  m (CtxTerm (CtxApp params prevs) a)
ctxCtorArgType _ _ _ (ConstArg tp) = return tp
ctxCtorArgType d params prevs (RecursiveArg zs_ctx ixs) =
  ctxPi zs_ctx $ \_ ->
  ctxDataTypeM d ((fst <$> ctxVars2 params prevs) >>= ctxLift InvNoBind zs_ctx)
  (return $ invertCtxTerms ixs)

-- | Convert a bindings list of 'CtorArg's to a binding list of types
ctxCtorArgBindings :: MonadTerm m => DataIdent d ->
                      InvBindings CtxTerm 'CNil params ->
                      InvBindings CtxTerm params prevs ->
                      Bindings (CtorArg d ixs) (CtxApp params prevs) args ->
                      m (Bindings CtxTerm (CtxApp params prevs) args)
ctxCtorArgBindings _ _ _ NoBind = return NoBind
ctxCtorArgBindings d params prevs (Bind x arg args) =
  do tp <- ctxCtorArgType d params prevs arg
     rest <- ctxCtorArgBindings d params (InvBind prevs x tp) args
     return (Bind x tp rest)

-- | Compute the type of a constructor from the name of its datatype and its
-- 'CtorArgStruct'
ctxCtorType :: MonadTerm m => DataIdent d ->
               CtorArgStruct d params ixs -> m Term
ctxCtorType d (CtorArgStruct{..}) =
  elimClosedTerm <$>
  (ctxPi ctorParams $ \params ->
    do bs <- ctxCtorArgBindings d (invertBindings ctorParams) InvNoBind ctorArgs
       ctxPi bs $ \_ ->
         ctxDataTypeM d
         (ctxLift InvNoBind bs $ invertCtxTerms params)
         (return $ invertCtxTerms ctorIndices))


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
                   Proxy (Typ ret) -> Proxy (Typ a) -> DataIdent d -> Ident ->
                   Bindings CtxTerm (CtxInv params) ixs ->
                   CtorArgStruct d params ixs ->
                   m (CtxTerm ('CCons (CtxInv params)
                               (Arrows ixs (d -> Typ a))) (Typ ret))
ctxCtorElimType ret (a_top :: Proxy (Typ a)) (d_top :: DataIdent d) c dt_ixs
  (CtorArgStruct{..}) =
  (do let params = invertBindings ctorParams
      p_ret_tp <- mkPRetTp a_top d_top params dt_ixs

      -- Lift the argument and return indices into the context of p_ret
      args <- ctxLift InvNoBind (Bind "_" p_ret_tp NoBind) ctorArgs
      ixs <-
        ctxLiftInBindings InvNoBind ctorArgs (Bind "_" p_ret_tp NoBind)
        ctorIndices
      -- Form the context ('CCons params p_ret)
      let params_pret = InvBind params "_" (ctxLiftNil params p_ret_tp)
      -- Call the helper and cast the result to (Typ ret)
      castCtxTerm Proxy ret <$>
        helper a_top d_top params_pret InvNoBind args ixs
  ) where
  -- Build the type of the p_ret function
  mkPRetTp :: MonadTerm m => Proxy (Typ a) -> DataIdent d ->
              InvBindings CtxTerm 'CNil ps ->
              Bindings CtxTerm ps ixs ->
              m (CtxTerm ps (Typ (Arrows ixs (d -> Typ a))))
  mkPRetTp (_ :: Proxy (Typ a)) (d :: DataIdent d) params ixs =
    ctxPiProxy (Proxy :: Proxy (Typ (d -> Typ a))) ixs $ \ix_vars ->
    do param_vars <- ctxVars params
       dt <- ctxDataTypeM d (ctxLift InvNoBind ixs param_vars)
         (return $ invertCtxTerms ix_vars)
       ctxPi1 "_" dt $ \_ -> ctxTyp0
  -- Iterate through the argument types of the constructor, building up a
  -- function from those arguments to the result type of the p_ret function.
  -- Note that, technically, this function also takes in recursive calls, so has
  -- a slightly richer type, but we are not going to try to compute this richer
  -- type in Haskell land.
  helper :: MonadTerm m => Proxy (Typ a) -> DataIdent d ->
            InvBindings CtxTerm 'CNil ('CCons ps (Arrows ixs (d -> Typ a))) ->
            InvBindings CtxTerm ('CCons ps (Arrows ixs (d -> Typ a))) prevs ->
            Bindings (CtorArg d ixs) (CtxApp
                                      ('CCons ps
                                       (Arrows ixs (d -> Typ a))) prevs) args ->
            CtxTerms (CtxInvApp (CtxApp ('CCons ps (Arrows ixs (d -> Typ a)))
                                 prevs) args) ixs ->
            m (CtxTerm (CtxApp ('CCons ps
                                (Arrows ixs (d -> Typ a))) prevs)
               (Typ (Arrows args a)))
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
-- >   RecursorApp d ps P cs_fs [ps/params,xs/args]ixs xi
--
-- where @[ps/params,xs/args]@ substitutes the concrete parameters @pi@ for the
-- parameter variables of the inductive type and the earlier constructor
-- arguments @xs@ for the remaining free variables.
ctxReduceRecursor :: MonadTerm m =>
                     Ident -> Bindings CtxTerm 'CNil params ->
                     CtxTerms 'CNil params -> Term -> [(Ident,Term)] ->
                     CtxTerms 'CNil ctor_args -> Ident ->
                     Bindings (CtorArg d ixs) (CtxInv params) ctor_args ->
                     m Term
ctxReduceRecursor d param_ctx params p_ret cs_fs top_args c ctor_args =
  (case ctxAppNilEq (invertBindings param_ctx) of
    Refl ->
      do let fi =
                case lookup c cs_fs of
                  Just f -> f
                  Nothing ->
                    error ("ctxReduceRecursor: eliminator missing for constructor "
                           ++ show c)
         args <- mk_args (invertCtxTerms params) top_args ctor_args
         foldM (\f arg -> mkTermF $ App f arg) fi args)
  where
    mk_args :: (MonadTerm m, CtxApp 'CNil ctx ~ ctx) => CtxTermsCtx 'CNil ctx ->
               CtxTerms 'CNil args -> Bindings (CtorArg d ixs) ctx args ->
               m [Term]
    mk_args _ _ NoBind = return []
    mk_args pre_xs (CtxTermsCons x xs) (Bind _ (ConstArg _) args) =
      (elimClosedTerm x :) <$>
      mk_args (CtxTermsCtxCons pre_xs x) xs args
    mk_args pre_xs (CtxTermsCons x xs) (Bind _ (RecursiveArg zs ixs) args) =
      case ctxAppNilEq (invertBindings zs) of
        Refl ->
          do zs' <- ctxSubstNil pre_xs NoBind zs
             ixs' <- ctxSubstNil pre_xs zs ixs
             (elimClosedTerm x :) <$>
               ((:) <$> mk_rec_arg zs' ixs' x <*>
                mk_args (CtxTermsCtxCons pre_xs x) xs args)

    -- Build an individual recursive call, given the parameters, the bindings
    -- for the RecursiveArg, and the argument we are going to recurse on
    mk_rec_arg :: MonadTerm m =>
                  Bindings CtxTerm 'CNil zs -> CtxTerms (CtxInv zs) ixs ->
                  CtxTerm 'CNil a -> m Term
    mk_rec_arg zs_ctx ixs x =
      elimClosedTerm <$> ctxLambda zs_ctx
      (\_ ->
        ctxRecursorAppM d (ctxLift InvNoBind zs_ctx params)
        (mkLiftedClosedTerm zs_ctx p_ret)
        (forM cs_fs (\(c',f) -> (c',) <$> mkLiftedClosedTerm zs_ctx f))
        (return ixs)
        (ctxLift InvNoBind zs_ctx x))
