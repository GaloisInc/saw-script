{- |
Module      : SAWScript.ValueOps
Description : Operations on the SAWScript Value datatype, plus other code from Value.hs
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional
-}
{-# LANGUAGE FlexibleInstances #-}
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
    emptyLocal,
    -- used by SAWScript.Interpreter
    extendLocal,
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
    withLocalEnv,
    withLocalEnvProof,
    withLocalEnvLLVM,
    withLocalEnvJVM,
    withLocalEnvMIR,
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
import qualified Data.Map as M
--import Data.Set ( Set )

import SAWCore.SharedTerm

import CryptolSAWCore.CryptolEnv as CEnv

import qualified SAWCentral.Position as SS
import qualified SAWCentral.AST as SS
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
    case M.lookup name vm of
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

emptyLocal :: LocalEnv
emptyLocal = []

extendLocal :: SS.Name -> SS.Schema -> Maybe String -> Value -> LocalEnv -> LocalEnv
extendLocal x ty md v env = LocalLet x ty md v : env

-- | A version of 'Control.Exception.bracket' specialized to 'TopLevel'. We
-- can't use 'Control.Monad.Catch.bracket' because it requires 'TopLevel' to
-- implement 'Control.Monad.Catch.MonadMask', which it can't do.
bracketTopLevel :: TopLevel a -> (a -> TopLevel b) -> (a -> TopLevel c) -> TopLevel c
bracketTopLevel acquire release action =
  do  resource <- acquire
      try (action resource) >>= \case
        Left (bad :: X.SomeException) -> release resource >> throwM bad
        Right good -> release resource >> pure good

combineRW :: TopLevelCheckpoint -> TopLevelRW -> IO TopLevelRW
combineRW (TopLevelCheckpoint chk scc) rw =
  do cenv' <- CEnv.combineCryptolEnv (rwCryptol chk) (rwCryptol rw)
     sc' <- restoreSharedContext scc (rwSharedContext rw)
     return chk{ rwCryptol = cenv'
               , rwSharedContext = sc'
               }

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

withLocalEnv :: LocalEnv -> TopLevel a -> TopLevel a
withLocalEnv env m = do
  prevEnv <- gets rwLocalEnv
  modify (\rw -> rw { rwLocalEnv = env })
  result <- m
  modify (\rw -> rw { rwLocalEnv = prevEnv })
  return result

withLocalEnvProof :: LocalEnv -> ProofScript a -> ProofScript a
withLocalEnvProof env (ProofScript m) = do
  ProofScript (underExceptT (underStateT (withLocalEnv env)) m)

withLocalEnvLLVM :: LocalEnv -> LLVMCrucibleSetupM a -> LLVMCrucibleSetupM a
withLocalEnvLLVM env (LLVMCrucibleSetupM m) = do
  LLVMCrucibleSetupM (underReaderT (underStateT (withLocalEnv env)) m)

withLocalEnvJVM :: LocalEnv -> JVMSetupM a -> JVMSetupM a
withLocalEnvJVM env (JVMSetupM m) = do
  JVMSetupM (underReaderT (underStateT (withLocalEnv env)) m)

withLocalEnvMIR :: LocalEnv -> MIRSetupM a -> MIRSetupM a
withLocalEnvMIR env (MIRSetupM m) = do
  MIRSetupM (underReaderT (underStateT (withLocalEnv env)) m)

withOptions :: (Options -> Options) -> TopLevel a -> TopLevel a
withOptions f (TopLevel_ m) =
  TopLevel_ (local (\x -> x {roOptions = f (roOptions x)}) m)
