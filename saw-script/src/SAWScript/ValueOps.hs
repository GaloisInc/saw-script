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

import Control.Monad (zipWithM)
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

-- Note: this is used only by restoreCheckpoint and restoreCheckpoint is
-- not really expected to work.
--
-- This is good, because whatever this function is doing does not seem
-- to make a great deal of sense. (Which has become more overt with recent
-- reorgs and cleanup, but hasn't itself changed.)
combineRW :: TopLevelCheckpoint -> TopLevelRW -> IO TopLevelRW
combineRW (TopLevelCheckpoint chk scc) rw = do
     let CryptolEnvStack chk'cenv chk'cenvs = rwGetCryptolEnvStack chk
         CryptolEnvStack rw'cenv rw'cenvs = rwGetCryptolEnvStack rw
     -- Caution: this merge may have unexpected results if the
     -- number of scopes doesn't match. But, it doesn't make sense
     -- to do that in the first place. Caveat emptor...
     cenv' <- CEnv.combineCryptolEnv chk'cenv rw'cenv
     cenvs' <- zipWithM CEnv.combineCryptolEnv chk'cenvs rw'cenvs
     sc' <- restoreSharedContext scc (rwSharedContext rw)
     let cryenv' = CryptolEnvStack cenv' cenvs'
     let chk' = rwSetCryptolEnvStack cryenv' chk
     return chk' { rwSharedContext = sc' }

-- | Represents the mutable state of the TopLevel monad
--   that can later be restored.
data TopLevelCheckpoint =
  TopLevelCheckpoint
    TopLevelRW
    SharedContextCheckpoint

makeCheckpoint :: TopLevelRW -> IO TopLevelCheckpoint
makeCheckpoint rw =
  do scc <- checkpointSharedContext (rwSharedContext rw)
     return (TopLevelCheckpoint rw scc)

restoreCheckpoint :: TopLevelCheckpoint -> TopLevel ()
restoreCheckpoint chk =
  do rw <- getTopLevelRW
     rw' <- io (combineRW chk rw)
     putTopLevelRW rw'

-- | Capture the current state of the TopLevel monad
--   and return an action that, if invoked, resets
--   the state back to that point.
checkpoint :: TopLevel (() -> TopLevel ())
checkpoint = TopLevel_ $
  do chk <- liftIO . makeCheckpoint =<< get
     return $ \_ ->
       do printOutLnTop Info "Restoring state from checkpoint"
          restoreCheckpoint chk

-- | Capture the current proof state and return an
--   action that, if invoked, resets the state back to that point.
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
