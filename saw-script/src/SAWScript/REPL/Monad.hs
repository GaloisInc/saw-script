{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

{- |
Module      : SAWScript.REPL.Monad
Description :
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional

Definitions for the REPL's monad and state types.
-}

module SAWScript.REPL.Monad (
    REPL(..), runREPL
  , initREPL
  , resumeREPL
  , exceptionProtect
  , liftTopLevel
  , liftProofScript
  , REPLState(..)
  , getCryptolEnv
  , getTopLevelRO
  , getTopLevelRW
  , getProofState
  ) where

import Control.Monad.Catch (
    MonadThrow(..), MonadCatch(..), MonadMask(..)
 )
import Control.Monad.State (MonadState(..), StateT(..), get, gets, modify)
import Control.Monad.Except (runExceptT)
import Control.Monad.IO.Class (MonadIO(..))
import qualified Control.Exception as X
import System.IO.Error (isUserError, ioeGetErrorString)
import System.Exit (ExitCode)

import qualified SAWSupport.PanicSupport as PanicSupport
import qualified SAWSupport.ConsoleSupport as Cons

import CryptolSAWCore.CryptolEnv

import SAWCentral.Options (Options)
import SAWCentral.Proof (ProofState, ProofResult(..))
import SAWCentral.TopLevel (
    TopLevelRO(..), TopLevelRW(..), TopLevel(..),
    runTopLevel
 )
import SAWCentral.Value (
    ProofScript(..), showsProofResult,
    rwGetCryptolEnv, TopLevelShellHook, ProofScriptShellHook
 )

import SAWScript.Panic (panic)
import SAWScript.Interpreter (buildTopLevelEnv)
import SAWScript.ValueOps (TopLevelCheckpoint, makeCheckpoint, restoreCheckpoint)


------------------------------------------------------------
-- REPL state and state monad

-- | The state maintained by the REPL.
--
-- rContinue starts True and remains true until someone runs @:q@,
-- at which point the main REPL loop exits.
--
-- rIsBatch is True if we're executing the REPL from a file in
-- batch mode (@saw -B@).
--
-- rTopLevelRO and rTopLevelRW are the SAWScript interpreter's
-- TopLevel monad state.
--
-- rProofState is the SAWScript interpreter's ProofScript monad state;
-- it should be `Nothing` when we're running an ordinary TopLevel REPL
-- and `Just` when we're running a ProofScript REPL.
--
-- We carry the state around separately like this (rather than
-- embedding the interpreter's monads) so we can run in either
-- context. This could be done with a monad typeclass instead, though
-- likely that would end up being a lot more complicated, and as we've
-- seen in the interpreter core, it's very easy to mess up code like
-- that so it executes some bits in the wrong monad, which will then
-- generally typecheck and only fail at runtime if you happen to try
-- the right things. So it's probably better this way, although I'd
-- prefer that the internal partitioning of the interpreter state
-- wasn't exposed.
-- 
data REPLState = REPLState
  { rContinue   :: Bool
  , rIsBatch    :: Bool
  , rTopLevelRO :: TopLevelRO
  , rTopLevelRW :: TopLevelRW
  , rProofState :: Maybe ProofState
  }

-- | Create an initial, empty environment.
initREPL ::
    Bool -> Options -> TopLevelShellHook -> ProofScriptShellHook ->
    IO REPLState
initREPL isBatch opts tlhook pshook =
  do (ro, rw) <- buildTopLevelEnv opts [] tlhook pshook
     return REPLState
       { rContinue   = True
       , rIsBatch    = isBatch
       , rTopLevelRO = ro
       , rTopLevelRW = rw
       , rProofState  = Nothing
       }

-- | Create an environment from an existing interpreter state.
--
-- FUTURE: it might be nice to be able to read subshell input from a
-- file in batch mode. Or from the same file that's feeding the parent
-- shell, though that's probably difficult. For now, assume any
-- subshells are intended to be interactive.
resumeREPL :: TopLevelRO -> TopLevelRW -> Maybe ProofState -> REPLState
resumeREPL ro rw mpst =
    REPLState {
        rContinue   = True,
        rIsBatch    = False,
        rTopLevelRO = ro,
        rTopLevelRW = rw,
        rProofState = mpst
    }

-- | REPL monad context.
newtype REPL a = REPL { unREPL :: StateT REPLState IO a }
  deriving (
      Applicative, Functor, Monad, MonadThrow, MonadCatch, MonadMask, MonadFail
  )

deriving instance MonadState REPLState REPL

-- | Run a REPL action on a REPL state.
runREPL :: REPL a -> REPLState -> IO (a, REPLState)
runREPL m st = do
    runStateT (unREPL m) st

-- | Run an IO action in a REPL context.
instance MonadIO REPL where
  liftIO m = REPL (liftIO m)

-- | Run a TopLevel action in a REPL context.
liftTopLevel :: TopLevel a -> REPL a
liftTopLevel m = do
    ro <- getTopLevelRO
    rw <- getTopLevelRW
    (result, rw') <- liftIO $ runTopLevel m ro rw
    modify (\st -> st { rTopLevelRW = rw' })
    return result

-- | Run a ProofScript action in a REPL context.
liftProofScript :: ProofScript a -> REPL a
liftProofScript m = do
    mpst <- gets rProofState
    let pst = case mpst of
          Nothing -> panic "liftProofScript" ["Not in ProofScript mode"]
          Just ps -> ps
    (result, pst') <-
        liftTopLevel $ runStateT (runExceptT (unProofScript m)) pst
    modify (\st -> st { rProofState = Just pst' })
    liftTopLevel $ case result of
       Left (stats, cex) ->
         do ppOpts <- rwPPOpts <$> get
            fail (showsProofResult ppOpts (InvalidProof stats cex pst') "")
       Right x -> return x


------------------------------------------------------------
-- Accessors

getTopLevelRO :: REPL TopLevelRO
getTopLevelRO = gets rTopLevelRO

getTopLevelRW :: REPL TopLevelRW
getTopLevelRW = gets rTopLevelRW

getProofState :: REPL (Maybe ProofState)
getProofState = gets rProofState

getCryptolEnv :: REPL CryptolEnv
getCryptolEnv = do
    rw <- getTopLevelRW
    return $ rwGetCryptolEnv rw


------------------------------------------------------------
-- Exceptions

captureError :: TopLevelCheckpoint -> Maybe String -> REPL ()
captureError chk mmsg = do
    case mmsg of
        Nothing -> pure ()
        Just msg -> do
            liftIO $ putStrLn ""
            liftIO $ putStrLn msg
    liftTopLevel $ restoreCheckpoint chk

-- | Inspect and handle or rethrow exceptions.
--
--   Note: this would be cleaner if it used `catches` with multiple
--   cases; however, the docs say nothing about what `catches` does
--   with overlapping cases, or if it actually works currently,
--   whether that's a supported part of the interface.
--
--   FUTURE: with enough cleanup in lower-level code we could make
--   this not need a blanket case and then `catches` becomes viable.
--
--   This logic controls which exceptions the REPL continues executing
--   for. Anything we rethrow here is fatal and will cause the REPL to
--   exit.
--
handleExceptions :: TopLevelCheckpoint -> X.SomeException -> REPL ()
handleExceptions chk e

    -- Cons.Fatal: catch and continue. We don't need to print the
    -- exception; the point of `Fatal` vs. anything else is that
    -- we already printed the error messages.
  | Just (_ :: Cons.Fatal) <- X.fromException e =
        captureError chk Nothing

    -- IO exceptions: catch and continue on UserError (this includes
    -- `fail` calls), but treat anything else as fatal.
  | Just (e' :: X.IOException) <- X.fromException e =
        if isUserError e' then
            captureError chk $ Just $ ioeGetErrorString e'
        else
            throwM e'

    -- Async exceptions: treat as fatal.
  | Just (e' :: X.AsyncException) <- X.fromException e =
        throwM e'

    -- ExitCode arises when someone makes an explicit call to exit
    -- (`exitSuccess` or `exitWith`); assume they meant it.
  | Just (e' :: ExitCode) <- X.fromException e =
        throwM e'

    -- Exceptions generated by panic: treat as fatal.
  | Just (e' :: PanicSupport.PanicException) <- X.fromException e =
        throwM e'

    -- Trap anything and everything else. XXX: this is way too broad.
  | otherwise =
        captureError chk $ Just $ X.displayException e



-- | Catch the exceptions we expect to catch while running a REPL
--   action.
exceptionProtect :: REPL () -> REPL ()
exceptionProtect cmd = do
    rw <- getTopLevelRW
    chk <- liftIO $ makeCheckpoint rw
    cmd `catch` handleExceptions chk
