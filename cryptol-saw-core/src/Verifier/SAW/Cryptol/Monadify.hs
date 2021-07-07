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

-- | A SAW core term where all subterms are typed
data AllSubs

-- | The monadification @Mon(trm)@ of a term @trm@ of type @tp@ is either a
-- "pure" term of type @Mon(tp)@ or a computational term of type
-- @CompM(Mon(tp))@, assuming that @Mon(tp)@ is itself a pure type
data MonTerm
     -- | @'CompMonTerm trm tp' trm tp@ is a pure term @t@ of type @tp@
  = PureMonTerm OpenTerm OpenTerm
    -- | @'CompMonTerm' trm tp@ is a computational monadified term @t@ of type
    -- @CompM tp@
  | CompMonTerm OpenTerm OpenTerm

-- | An environment of named definitions that have already been monadified
type MonadifyEnv = Map Ident Ident

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

-- | Get the type @CompM tp@ of the computational term representated by a
-- 'MonTerm' and return the underlying type @tp@
monTermType :: MonTerm -> OpenTerm
monTermType (PureMonTerm _ tp) = tp
monTermType (CompMonTerm _ tp) = tp

-- | Turn a 'MonTerm' into a computational term by inserting a monadic return if
-- the 'MonTerm' is pure
compMonTerm :: MonTerm -> OpenTerm
compMonTerm (PureMonTerm trm tp) =
  applyOpenTermMulti (globalOpenTerm "Prelude.returnM") [tp, trm]
compMonTerm (CompMonTerm trm _) = trm

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
