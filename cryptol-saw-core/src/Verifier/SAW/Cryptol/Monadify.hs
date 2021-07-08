{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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

-- | A SAW core term where all of the subterms are typed
data TypedSubsTerm
  = TypedSubsTerm { tpSubsIndex :: Maybe TermIndex,
                    tpSubsTermF :: TermF TypedSubsTerm,
                    tpSubsTypeF :: TermF TypedSubsTerm }

-- | Convert a 'Term' to a 'TypedSubsTerm'
typeAllSubterms :: SharedContext -> Term -> IO TypedSubsTerm
typeAllSubterms = error "FIXME"

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
    -- | A (dependent) function type @Pi x t u@ for monadification type @u@
  | FunMonType OpenTerm (OpenTerm -> MonType)


-- | A monadified term is just a term plus a 'MonType'
data MonTerm { monTermTerm :: OpenTerm, monTermType :: MonType }

-- | Embed a 'MonTerm' into type @CompM Mon(tp)@
compMonTerm :: MonTerm -> OpenTerm
compMonTerm (MonTerm trm (PureMonType tp)) =
  applyOpenTermMulti (globalOpenTerm "Prelude.returnM") [tp, trm]
compMonTerm (MonTerm trm (CompMonType _)) = trm
compMonTerm (MonTerm trm (FunMonType tp tp_f)) =
  lambdaOpenTerm "x" tp (\x -> compMonTerm (applyOpenTerm trm x) (tp_f x))


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
runMonadifyM :: Map Ident Ident -> OpenTerm -> MonadifyM OpenTerm -> OpenTerm
runMonadifyM env top_ret_tp m =
  let ro_st = MonadifyROState env top_ret_tp in
  runCont (evalStateT (runReaderT (unMonadifyM m) ro_st) Map.empty) id

-- | Run a monadification computation using a mapping for identifiers that have
-- already been monadified and generate a SAW core term
runCompleteMonadifyM :: MonadIO m => SharedContext -> Map Ident Ident -> OpenTerm ->
                        MonadifyM OpenTerm -> m Term
runCompleteMonadifyM sc env top_ret_tp m =
  liftIO $ completeOpenTerm sc $ runMonadifyM env top_ret_tp m

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
-- 'MonTerm' is computational
purifyMonTerm :: MonTerm -> MonadifyM OpenTerm
purifyMonTerm (PureMonTerm trm _) = return trm
purifyMonTerm (CompMonTerm trm tp) =
  topRetType >>= \top_ret_tp ->
  MonadifyM $ lift $ lift $ cont $ \k ->
  applyOpenTermMulti (globalOpenTerm "Prelude.bindM")
  [tp, top_ret_tp, trm, lambdaOpenTerm "x" tp k]

-- | Combine 'purifyMonTerm' and 'monTermType'
purifyMonTermTyped :: MonTerm -> MonadifyM (OpenTerm,OpenTerm)
purifyMonTermTyped mt =
  do trm <- purifyMonTerm mt
     let tp = monTermType mt
     return (trm,tp)

-- | Return a pure 'OpenTerm' as the result of monadification
retPure :: OpenTerm -> MonadifyM MonTerm
retPure t = return $ PureMonTerm t (openTermType t)

-- | Monadify a 'Term' and then purify it using 'purifyMonTerm'
monadifyPure :: Monadify a => a -> MonadifyM OpenTerm

-- | Generic function to monadify terms
class Monadify a where
  monadify :: a -> MonadifyM MonTerm

instance Monadify Term where
  monadify (Unshared tf) = monadify tf
  monadify (STApp{ stAppIndex = i, stAppTermF = tf}) =
    do table <- get
       case Map.lookup i table of
         Just mt  -> return mt
         Nothing ->
           do mt <- monadify tf
              modify (Map.insert i mt)
              return mt

instance Monadify (TermF Term) where
  monadify (FTermF ftf) = monadify ftf
  monadify (App t1 t2) =
    do t1' <- monadifyPure t1
       t2' <- monadifyPure t2
       return (PureMonTerm (applyOpenTerm t1' t2') (applyPiOpenTerm t1' t2'))
  monadify (Lambda x tp body) =
    monadifyPure tp >>= \tp' ->

    FIXME HERE NOW: do a reset with the return type of the body

  monadify _ = error "FIXME: missing cases for monadify"

instance Monadify (FlatTermF Term) where
  monadify UnitValue = retPure unitOpenTerm
  monadify UnitType = retPure unitTypeOpenTerm
  monadify (PairValue t1 t2) =
    retPure <$> (pairOpenTerm <$> monadifyPure t1 <*> monadifyPure t2)
  monadify (PairType t1 t2) =
    retPure <$> (pairTypeOpenTerm <$> monadifyPure t1 <*> monadifyPure t2)
  monadify _ = error "FIXME: missing cases for monadify"
