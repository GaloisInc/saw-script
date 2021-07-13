{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : Verifier.SAW.Cryptol.Monadify
Copyright   : Galois, Inc. 2021
License     : BSD3
Maintainer  : westbrook@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

This module implements a "monadification" transformation, which converts "pure"
SAW core terms that use inconsistent operations like @fix@ and convert them to
monadic SAW core terms that use monadic versions of these operations that are
consistent. The monad that is used is the @CompM@ monad that is axiomatized in
the SAW cxore prelude. This is only a partial transformation, meaning that it
will fail on some SAW core terms. Specifically, it requires that all
applications @f arg@ in a term either have a non-dependent function type for @f@
(i.e., a function with type @'Pi' x a b@ where @x@ does not occur in @b@) or a
pure argument @arg@ that does not use any of the inconsistent operations.

The monadification @Mon(t)@ of term @t@ is defined as follows (where we have
simplified the input langauge to just contain pairs, sums, units, and
functions):

FIXME: either talk about CPS or drop the definition

> Mon(sort s) = sort s
> Mon(#()) = #()
> Mon(T * U) = Mon(T) * Mon(U)
> Mon(Either T U) = Either Mon(T) Mon(U)
> Mon(Pi x a b) = Pi x Mon(T) (CompM Mon(U))
> Mon()
-}

module Verifier.SAW.Cryptol.Monadify where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Cont
import qualified Control.Monad.Fail as Fail
-- import Control.Monad.IO.Class (MonadIO, liftIO)

import Verifier.SAW.Name
import Verifier.SAW.Term.Functor
import Verifier.SAW.SharedTerm
import Verifier.SAW.OpenTerm


----------------------------------------------------------------------
-- * Typing All Subterms
----------------------------------------------------------------------

-- | A SAW core term where all of the subterms are typed
data TypedSubsTerm
  = TypedSubsTerm { tpSubsIndex :: Maybe TermIndex,
                    tpSubsFreeVars :: BitSet,
                    tpSubsTermF :: TermF TypedSubsTerm,
                    tpSubsTypeF :: TermF TypedSubsTerm }

-- | Convert a 'Term' to a 'TypedSubsTerm'
typeAllSubterms :: SharedContext -> Term -> IO TypedSubsTerm
typeAllSubterms = error "FIXME"


----------------------------------------------------------------------
-- * Monadified Terms and Types
----------------------------------------------------------------------

-- | When we monadify a term @trm@ of type @tp@, we in general get a term
-- @Mon(trm) : CompM Mon(tp)@. But sometimes we can do better, and get a term of
-- a "more pure" type that can be embedded into @CompM Mon(tp)@. A
-- monadification type represents one of these more pure types.
data MonType
     -- | The "pure" type @Mon(tp)@
  = PureMonType OpenTerm
    -- | The "computational" type @CompM Mon(tp)@, where the supplied 'OpenTerm'
    -- gives the pure type @Mon(tp)@
  | CompMonType OpenTerm
    -- | A (dependent) function type @Pi x t u@ for monadification type
    -- @u@. Note that this is "more pure" than 'PureMonType', because that
    -- constructor uses a type of the form @Pi x t (CompM u)@ for functions,
    -- whereas this constructor allows the return type to be pure as well.
  | FunMonType OpenTerm (OpenTerm -> MonType)


-- | Test if a 'MonType' is a computational type, i.e., a @CompM@ type
isCompType :: MonType -> Bool
isCompType (CompMonType _) = True
isCompType _ = False

-- | Convert a 'MonType' to its most general pure type @Mon(tp)@
pureMonType :: MonType -> OpenTerm
pureMonType (PureMonType tp) = tp
pureMonType (CompMonType tp) = tp
pureMonType (FunMonType tp_in tp_out) =
  piOpenTerm "x" tp_in (compMonType . tp_out)

-- | Convert a 'MonType' to its most general computational type @CompM Mon(tp)@
compMonType :: MonType -> OpenTerm
compMonType = applyOpenTerm (globalOpenTerm "Prelude.CompM") . pureMonType

-- | A monadified term is just a term plus a 'MonType'
data MonTerm = MonTerm { monTermTerm :: OpenTerm, monTermType :: MonType }

-- | Test if a 'MonTerm' is a computational term, i.e., of @CompM@ type
isCompTerm :: MonTerm -> Bool
isCompTerm = isCompType . monTermType

-- | Convert a 'FunMonType' function of type @Pi x t u@ to its most general pure
-- type @Pi x t ('pureMonType' u)@
purifyFunTerm :: OpenTerm -> (OpenTerm -> MonType) -> OpenTerm -> OpenTerm
purifyFunTerm tp_in tp_out f =
  lambdaOpenTerm "x" tp_in $ \x ->
  compMonTerm $ MonTerm (applyOpenTerm f x) (tp_out x)

-- | Embed a 'MonTerm' into type @CompM Mon(tp)@
compMonTerm :: MonTerm -> OpenTerm
compMonTerm (MonTerm trm (PureMonType tp)) =
  applyOpenTermMulti (globalOpenTerm "Prelude.returnM") [tp, trm]
compMonTerm (MonTerm trm (CompMonType _)) = trm
compMonTerm (MonTerm trm tp@(FunMonType tp_in tp_out)) =
  applyOpenTermMulti (globalOpenTerm "Prelude.returnM")
  [pureMonType tp, purifyFunTerm tp_in tp_out trm]


----------------------------------------------------------------------
-- * The Monadified Monad
----------------------------------------------------------------------

-- | An environment of named definitions that have already been monadified
type MonadifyEnv = Map Ident MonTerm

-- | The read-only state of a monadification computation
data MonadifyROState = MonadifyROState {
  -- | The monadification environment
  monStEnv :: MonadifyEnv,
  -- | The monadified return type of the top-level term being monadified
  monStTopRetType :: OpenTerm
}

-- | The state of a monadification computation = a memoization table
type MonadifyState = Map TermIndex MonTerm

-- | The monad for monadifying SAW core terms
newtype MonadifyM a =
  MonadifyM { unMonadifyM ::
                ReaderT MonadifyROState (StateT MonadifyState
                                         (Cont OpenTerm)) a }
  deriving (Functor, Applicative, Monad,
            MonadReader MonadifyROState, MonadState MonadifyState)

instance Fail.MonadFail MonadifyM where
  fail str = MonadifyM $ lift $ lift $ cont $ \_ -> failOpenTerm str

-- | Run a monadification computation
--
-- FIXME: document the arguments
runMonadifyM :: MonadifyEnv -> OpenTerm -> MonadifyM OpenTerm -> OpenTerm
runMonadifyM env top_ret_tp m =
  let ro_st = MonadifyROState env top_ret_tp in
  runCont (evalStateT (runReaderT (unMonadifyM m) ro_st) Map.empty) id

-- | Run a monadification computation using a mapping for identifiers that have
-- already been monadified and generate a SAW core term
runCompleteMonadifyM :: MonadIO m => SharedContext -> MonadifyEnv -> OpenTerm ->
                        MonadifyM OpenTerm -> m Term
runCompleteMonadifyM sc env top_ret_tp m =
  liftIO $ completeOpenTerm sc $ runMonadifyM env top_ret_tp m

-- | Memoize a computation of the monadified term associated with a 'TermIndex'
memoizingM :: TermIndex -> MonadifyM MonTerm -> MonadifyM MonTerm
memoizingM i m =
  (Map.lookup i <$> get) >>= \case
  Just ret  -> return ret
  Nothing ->
    do ret <- m
       modify (Map.insert i ret)
       return ret

-- | Capture the current continuation and pass it to a function, which must
-- return the final computation result. Note that this is slightly differnet
-- from normal shift, and I think corresponds to the C operator, but my quick
-- googling couldn't find the right name...
shiftMonadifyM :: ((a -> OpenTerm) -> OpenTerm) -> MonadifyM a
shiftMonadifyM f = MonadifyM $ lift $ lift $ cont f

-- | Locally run a 'MonadifyM' computation with an empty memoization table,
-- making all binds be local to that computation, and return the result
resetMonadifyM :: OpenTerm -> MonadifyM OpenTerm -> MonadifyM OpenTerm
resetMonadifyM ret_tp m =
  do ro_st <- ask
     return $ runMonadifyM (monStEnv ro_st) ret_tp m

-- | Get the monadified return type of the top-level term being monadified
topRetType :: MonadifyM OpenTerm
topRetType = monStTopRetType <$> ask

-- | Turn a 'MonTerm' into a pure term by inserting a monadic bind if the
-- 'MonTerm' is computational and converting any 'CompFunType' function to its
-- most general @Pi x t (CompM u)@ form
purifyMonTerm :: MonTerm -> MonadifyM OpenTerm
purifyMonTerm (MonTerm trm (PureMonType _)) = return trm
purifyMonTerm (MonTerm trm (FunMonType tp_in tp_out)) =
  return $ purifyFunTerm tp_in tp_out trm
purifyMonTerm (MonTerm trm (CompMonType tp)) =
  topRetType >>= \top_ret_tp ->
  shiftMonadifyM $ \k ->
  applyOpenTermMulti (globalOpenTerm "Prelude.bindM")
  [tp, top_ret_tp, trm, lambdaOpenTerm "x" tp k]

-- | Build a 'MonTerm' from a pure 'OpenTerm'
mkPure :: OpenTerm -> MonTerm
mkPure trm = MonTerm trm (PureMonType $ openTermType trm)

-- | Return a pure 'MonTerm' as the result of monadification
retPure :: OpenTerm -> MonadifyM MonTerm
retPure = return . mkPure

-- | Monadify a 'Term' and then purify it using 'purifyMonTerm'
monadifyPure :: Monadify a => a -> MonadifyM OpenTerm
monadifyPure = monadify >=> purifyMonTerm

-- | Generic function to monadify terms
class Monadify a where
  monadify :: a -> MonadifyM MonTerm

instance Monadify TypedSubsTerm where
  monadify (TypedSubsTerm { tpSubsIndex = Just i, tpSubsTermF = tf}) =
    memoizingM i $ monadify tf
  monadify (TypedSubsTerm { tpSubsIndex = Nothing, tpSubsTermF = tf}) =
    monadify tf

instance Monadify (TermF TypedSubsTerm) where
  monadify (FTermF ftf) = monadify ftf
  monadify (App t1 t2) =
    ((,) <$> monadify t1 <*> monadify t2) >>= \case

    -- If t1 has a dependent type and t2 is not pure then monadification fails
    (_, mtrm2)
      | isCompTerm mtrm2
      , Pi _ _ tp_out <- tpSubsTypeF t1
      , inBitSet 0 (tpSubsFreeVars tp_out) ->
        fail "FIXME: better error message!"

    -- If t1 is a pure function, apply it
    (MonTerm trm1 (FunMonType _ tp_out), mtrm2) ->
      purifyMonTerm mtrm2 >>= \trm2 ->
      return $ MonTerm { monTermTerm = applyOpenTerm trm1 trm2,
                         monTermType = tp_out trm2}

    -- Otherwise, purify t1 to a monadic function and apply it
    (mtrm1@(MonTerm _ tp1), mtrm2) ->
      do trm1 <- purifyMonTerm mtrm1
         trm2 <- purifyMonTerm mtrm2
         return $ MonTerm { monTermTerm = applyOpenTerm trm1 trm2,
                            monTermType =
                              CompMonType $
                              applyPiOpenTerm (pureMonType tp1) trm2 }
{-
  monadify (Lambda x tp body) =
    monadifyPure tp >>= \tp' ->

    FIXME HERE NOW: do a reset with the return type of the body
-}
  monadify _ = error "FIXME: missing cases for monadify"

instance Monadify (FlatTermF TypedSubsTerm) where
  monadify UnitValue = retPure unitOpenTerm
  monadify UnitType = retPure unitTypeOpenTerm
  monadify (PairValue t1 t2) =
    mkPure <$> (pairOpenTerm <$> monadifyPure t1 <*> monadifyPure t2)
  monadify (PairType t1 t2) =
    mkPure <$> (pairTypeOpenTerm <$> monadifyPure t1 <*> monadifyPure t2)
  monadify _ = error "FIXME: missing cases for monadify"
