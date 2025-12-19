{- |
Module      : SAWScript.ValueOps
Description : Operations on the SAWScript Value datatype, plus other code from Value.hs
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional
-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SAWScript.ValueOps (
    -- used by SAWScript.Interpreter
    isVUnit,
    -- used by SAWScript.Interpreter
    -- XXX: name overlaps with unrelated fn from Data.Parameterized.Nonce
    --      and should be changed
    indexValue,
    -- used by SAWScript.Interpreter
    lookupValue,
    -- used by SAWScript.Interpreter
    tupleLookupValue,
    -- used by SAWScript.Interpreter
    bracketTopLevel,
    -- unused but that probably won't stay that way
    TopLevelCheckpoint(..),
    -- used by SAWScript.REPL.Monad
    makeCheckpoint,
    -- used by SAWScript.REPL.Monad
    restoreCheckpoint,
    -- used by SAWScript.Interpreter
    checkpoint,
    -- used by SAWScript.Interpreter
    proof_checkpoint,
    -- used by SAWScript.Interpreter
    withEnviron,
    withEnvironProofScript,
    withEnvironLLVM,
    withEnvironJVM,
    withEnvironMIR,
    -- used in SAWScript.Interpreter
    withOptions,
 ) where

import Prelude hiding (fail)

import Control.Monad.Catch (MonadThrow(..), try)
import Control.Monad.State (get, gets, modify, put)
import qualified Control.Exception as X
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader (local)

import Data.Text (Text)
import qualified Data.Text as Text (pack, unpack)
--import Data.Map ( Map )
import qualified Data.Map as Map
--import Data.Set ( Set )

import SAWCore.SharedTerm

import CryptolSAWCore.CryptolEnv as CEnv

import qualified SAWCentral.Position as SS
--import qualified SAWCentral.AST as SS
--import qualified SAWCentral.Crucible.JVM.MethodSpecIR ()
--import qualified SAWCentral.Crucible.MIR.MethodSpecIR ()
import SAWCentral.Options (Options, Verbosity(..))

import SAWCentral.Value

import SAWScript.Panic (panic)


isVUnit :: Value -> Bool
isVUnit (VTuple []) = True
isVUnit _ = False

indexValue :: SS.Pos -> Value -> Value -> Value
indexValue pos (VArray vs) (VInteger x)
    | i < length vs = vs !! i
    | otherwise = error $ show pos ++ ": Array index out of bounds"
    where i = fromInteger x
indexValue pos v1 v2 =
    panic "indexValue" [
        "Type error that escaped the typechecker",
        "Source position: " <> Text.pack (show pos),
        "Array value: " <> Text.pack (show v1),
        "Index value: " <> Text.pack (show v2)
    ]

lookupValue :: SS.Pos -> Value -> Text -> Value
lookupValue pos (VRecord vm) name =
    case Map.lookup name vm of
      Nothing -> error $ show pos ++ ": No such record field: " ++ Text.unpack name
      Just x -> x
lookupValue pos v1 v2 =
    panic "lookupValue" [
        "Type error that escaped the typechecker",
        "Source position: " <> Text.pack (show pos),
        "Array value: " <> Text.pack (show v1),
        "Index value: " <> Text.pack (show v2)
    ]

tupleLookupValue :: SS.Pos -> Value -> Integer -> Value
tupleLookupValue pos (VTuple vs) i
  | 0 <= i && fromIntegral i < length vs = vs !! fromIntegral i
  | otherwise = error $ show pos ++ ": No such tuple index: " ++ show i
tupleLookupValue pos v1 v2 =
    panic "tupleLookupValue" [
        "Type error that escaped the typechecker",
        "Source position: " <> Text.pack (show pos),
        "Array value: " <> Text.pack (show v1),
        "Index value: " <> Text.pack (show v2)
    ]

-- | A version of 'Control.Exception.bracket' specialized to 'TopLevel'. We
-- can't use 'Control.Monad.Catch.bracket' because it requires 'TopLevel' to
-- implement 'Control.Monad.Catch.MonadMask', which it can't do.
bracketTopLevel :: TopLevel a -> (a -> TopLevel b) -> (a -> TopLevel c) -> TopLevel c
bracketTopLevel acquire release action =
  do  resource <- acquire
      try (action resource) >>= \case
        Left (bad :: X.SomeException) -> release resource >> throwM bad
        Right good -> release resource >> pure good

-- | Represents the mutable state of the TopLevel monad
--   that can later be restored.
data TopLevelCheckpoint =
  TopLevelCheckpoint
    TopLevelRW
    SharedContextCheckpoint

-- | Create a SAWScript checkpoint. This captures the current state of
--   the TopLevel monad.
--
--   Caution: this logic assumes that TopLevelRO is genuinely
--   readonly. Currently it is; but if it isn't (e.g. it used to have
--   some things that updated while in nested blocks, because it's
--   held in a `ReaderT` and not just a value), it won't and can't be
--   restored. This doesn't matter if you don't try to restore a
--   checkpoint that came from a different block; but if you do the
--   resulting behavior can be odd (and likely unsound).
--
makeCheckpoint :: TopLevel TopLevelCheckpoint
makeCheckpoint = do
    rw <- get
    scc <- liftIO $ checkpointSharedContext (rwSharedContext rw)
    return $ TopLevelCheckpoint rw scc

-- | Restore the Cryptol environment stack (full Cryptol environment)
--   from a checkpoint.
--
-- Caution: the stack merge may have unexpected results if the number
-- of scopes doesn't match, e.g. by using a checkpoint to teleport out
-- of (or into) a nested block. But, it doesn't make sense to do that
-- in the first place. Caveat emptor...
--
restoreCryptolEnvStack :: CryptolEnvStack -> CryptolEnvStack -> CryptolEnvStack
restoreCryptolEnvStack chk'cryenv now'cryenv =
     let CryptolEnvStack chk'cenv chk'cenvs = chk'cryenv
         CryptolEnvStack now'cenv now'cenvs = now'cryenv
         result'cenv = CEnv.restoreCryptolEnv chk'cenv now'cenv
         result'cenvs = zipWith CEnv.restoreCryptolEnv chk'cenvs now'cenvs
     in
     CryptolEnvStack result'cenv result'cenvs

-- | Restore a SAWScript checkpoint.
restoreCheckpoint :: TopLevelCheckpoint -> TopLevel ()
restoreCheckpoint (TopLevelCheckpoint chk'rw scc) = do
     now'rw <- getTopLevelRW

     -- First, restore the SAWCore state.
     -- (The SharedContext handle doesn't change; it doesn't matter
     -- which reference to it we use.)
     let sc = rwSharedContext now'rw
     liftIO $ restoreSharedContext scc sc

     -- Second, attend to the Cryptol environment so the Cryptol name
     -- supply gets handled properly.
     let chk'cryenv = rwGetCryptolEnvStack chk'rw
         now'cryenv = rwGetCryptolEnvStack now'rw
         result'cryenv = restoreCryptolEnvStack chk'cryenv now'cryenv

     -- Restore the old TopLevelRW with the adjusted Cryptol environment
     let chk'rw' = rwSetCryptolEnvStack result'cryenv chk'rw
     putTopLevelRW chk'rw'

-- | User-facing checkpoint command. Returns an action in TopLevel
--   that, if invoked, rolls back the state.
--
--   The print is here rather than in `restoreCheckpoint` so only the
--   user's own checkpoints issue it. The checkpoints made by the REPL
--   are supposed to be silent.
checkpoint :: TopLevel (() -> TopLevel ())
checkpoint = do
    chk <- makeCheckpoint
    return $ \_ -> do
        printOutLnTop Info "Restoring state from checkpoint"
        restoreCheckpoint chk

-- | Capture the current proof state and return an action that, if
--   invoked, resets the state back to that point.
proof_checkpoint :: ProofScript (() -> ProofScript ())
proof_checkpoint =
  do ps <- get
     return $ \_ ->
       do scriptTopLevel (printOutLnTop Info "Restoring proof state from checkpoint")
          put ps

withEnviron :: Environ -> TopLevel a -> TopLevel a
withEnviron env m = do
  prevEnv <- gets rwEnviron
  modify (\rw -> rw { rwEnviron = env })
  result <- m
  modify (\rw -> rw { rwEnviron = prevEnv })
  return result

withEnvironProofScript :: Environ -> ProofScript a -> ProofScript a
withEnvironProofScript env (ProofScript m) = do
  ProofScript (underExceptT (underStateT (withEnviron env)) m)

withEnvironLLVM :: Environ -> LLVMCrucibleSetupM a -> LLVMCrucibleSetupM a
withEnvironLLVM env (LLVMCrucibleSetupM m) = do
  LLVMCrucibleSetupM (underReaderT (underStateT (withEnviron env)) m)

withEnvironJVM :: Environ -> JVMSetupM a -> JVMSetupM a
withEnvironJVM env (JVMSetupM m) = do
  JVMSetupM (underReaderT (underStateT (withEnviron env)) m)

withEnvironMIR :: Environ -> MIRSetupM a -> MIRSetupM a
withEnvironMIR env (MIRSetupM m) = do
  MIRSetupM (underReaderT (underStateT (withEnviron env)) m)

withOptions :: (Options -> Options) -> TopLevel a -> TopLevel a
withOptions f (TopLevel_ m) =
  TopLevel_ (local (\x -> x {roOptions = f (roOptions x)}) m)
