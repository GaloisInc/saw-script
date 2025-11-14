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

import Control.Monad (void)
import Control.Monad.Catch (
    MonadThrow(..), MonadCatch(..), MonadMask(..),
    catchJust
 )
import Control.Monad.State (MonadState(..), StateT(..), get, gets, modify)
import Control.Monad.Except (runExceptT)
import Control.Monad.IO.Class (MonadIO(..))
import qualified Control.Exception as X
import System.IO.Error (isUserError, ioeGetErrorString)
import System.Exit (ExitCode)

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
import SAWScript.ValueOps (makeCheckpoint, restoreCheckpoint)


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

-- | Handle generic IO exceptions from `fail` in REPL actions.
catchFail :: REPL a -> (String -> REPL a) -> REPL a
catchFail m k = catchJust sel m k
  where
    sel :: X.IOException -> Maybe String
    sel e | isUserError e = Just (ioeGetErrorString e)
          | otherwise     = Nothing

-- | Handle any other exception (except that we ignore async
--   exceptions and exitWith)
--
-- XXX: we do not apparently ignore the exceptions that panic throws,
-- and we probably should.
catchOther :: REPL a -> (X.SomeException -> REPL a) -> REPL a
catchOther m k = catchJust flt m k
 where
  flt e
    | Just (_ :: X.AsyncException) <- X.fromException e = Nothing
    | Just (_ :: ExitCode)       <- X.fromException e = Nothing
    | otherwise = Just e

-- | Catch the exceptions we expect to catch while running a REPL
--   action.
exceptionProtect :: REPL () -> REPL ()
exceptionProtect cmd =
      do chk <- liftIO . makeCheckpoint =<< getTopLevelRW
         cmd `catchFail`  (handlerFail chk)
             `catchOther` (handlerPrint chk)

    where
    handlerPrint chk e =
      do liftIO (putStrLn "" >> putStrLn (X.displayException e))
         void $ liftTopLevel (restoreCheckpoint chk)

    handlerFail chk s =
      do liftIO (putStrLn "" >> putStrLn s)
         void $ liftTopLevel (restoreCheckpoint chk)
