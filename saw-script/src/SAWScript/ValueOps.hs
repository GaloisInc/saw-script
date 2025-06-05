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
    toplevelSubshell,
    -- used by SAWScript.Interpreter
    proofScriptSubshell,
    -- XXX apparently unused
    thenValue,
    -- used by SAWScript.Interpreter
    bindValue,
    -- used by SAWScript.Interpreter
    forValue,
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
    -- used by SAWScript.Interpreter and locally in topLevelSubshell
    withLocalEnv,
    -- used locally in proofScriptSubshell
    withLocalEnvProof,
    -- used in SAWScript.Interpreter
    withOptions,
    -- used in SAWScript.Interpreter
    withStackTraceFrame,
    -- used in SAWScript.Interpreter
    toValueCase,
 ) where

import Prelude hiding (fail)

import Control.Monad.Catch (MonadThrow(..), try)
import Control.Monad.State (get, gets, modify, put)
import qualified Control.Exception as X
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader (ask, local)

import Data.Text (Text, unpack)
--import Data.Map ( Map )
import qualified Data.Map as M
--import Data.Set ( Set )

import SAWCore.SharedTerm

import CryptolSAWCore.CryptolEnv as CEnv

import qualified SAWCentral.AST as SS
import qualified SAWCentral.Position as SS
--import qualified SAWCentral.Crucible.JVM.MethodSpecIR ()
--import qualified SAWCentral.Crucible.MIR.MethodSpecIR ()
import SAWCentral.Options (Options, Verbosity(..))
import SAWCentral.Value



isVUnit :: Value -> Bool
isVUnit (VTuple []) = True
isVUnit _ = False

indexValue :: Value -> Value -> Value
indexValue (VArray vs) (VInteger x)
    | i < length vs = vs !! i
    | otherwise = error "array index out of bounds"
    where i = fromInteger x
indexValue _ _ = error "indexValue"

lookupValue :: Value -> Text -> Value
lookupValue (VRecord vm) name =
    case M.lookup name vm of
      Nothing -> error $ "no such record field: " ++ unpack name
      Just x -> x
lookupValue _ _ = error "lookupValue"

tupleLookupValue :: Value -> Integer -> Value
tupleLookupValue (VTuple vs) i
  | 0 <= i && fromIntegral i < length vs = vs !! fromIntegral i
  | otherwise = error $ "no such tuple index: " ++ show i
tupleLookupValue _ _ = error "tupleLookupValue"

toplevelSubshell :: Value
toplevelSubshell = VLambda $ \_ ->
  do m <- roSubshell <$> ask
     env <- getLocalEnv
     return (VTopLevel (toValue <$> withLocalEnv env m))

proofScriptSubshell :: Value
proofScriptSubshell = VLambda $ \_ ->
  do m <- roProofSubshell <$> ask
     env <- getLocalEnv
     return (VProofScript (toValue <$> withLocalEnvProof env m))

thenValue :: SS.Pos -> Value -> Value -> Value
thenValue pos v1 v2 = VBind pos v1 (VLambda (const (return v2)))

bindValue :: SS.Pos -> Value -> Value -> TopLevel Value
bindValue pos v1 v2 = return (VBind pos v1 v2)

forValue :: [Value] -> Value -> TopLevel Value
forValue [] _ = return $ VReturn (VArray [])
forValue (x : xs) f =
  do m1 <- applyValue f x
     m2 <- forValue xs f
     bindValue (SS.PosInternal "<for>") m1 (VLambda $ \v1 ->
       bindValue (SS.PosInternal "<for>") m2 (VLambda $ \v2 ->
         return $ VReturn (VArray (v1 : fromValue v2))))

emptyLocal :: LocalEnv
emptyLocal = []

extendLocal :: SS.LName -> SS.Schema -> Maybe String -> Value -> LocalEnv -> LocalEnv
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

withOptions :: (Options -> Options) -> TopLevel a -> TopLevel a
withOptions f (TopLevel_ m) =
  TopLevel_ (local (\x -> x {roOptions = f (roOptions x)}) m)

-- | Implement stack tracing by adding error handlers that rethrow
-- user errors, prepended with the given string.
withStackTraceFrame :: String -> Value -> Value
withStackTraceFrame str val =
  let doTopLevel :: TopLevel a -> TopLevel a
      doTopLevel action = do
        trace <- gets rwStackTrace
        modify (\rw -> rw { rwStackTrace = str : trace })
        result <- action
        modify (\rw -> rw { rwStackTrace = trace })
        return result
      doProofScript :: ProofScript a -> ProofScript a
      doProofScript (ProofScript m) =
        let m' =
              underExceptT (underStateT doTopLevel) m
        in
        ProofScript m'
      doLLVM :: LLVMCrucibleSetupM a -> LLVMCrucibleSetupM a
      doLLVM (LLVMCrucibleSetupM m) =
        LLVMCrucibleSetupM (underReaderT (underStateT doTopLevel) m)
      doJVM :: JVMSetupM a -> JVMSetupM a
      doJVM (JVMSetupM m) =
        JVMSetupM (underReaderT (underStateT doTopLevel) m)
      doMIR :: MIRSetupM a -> MIRSetupM a
      doMIR (MIRSetupM m) =
        MIRSetupM (underReaderT (underStateT doTopLevel) m)
  in
  case val of
    VLambda f ->
      let wrap x =
            withStackTraceFrame str `fmap` doTopLevel (f x)
      in
      VLambda wrap
    VTopLevel m ->
      let m' =
            withStackTraceFrame str `fmap` doTopLevel m
      in
      VTopLevel m'
    VProofScript m ->
      let m' =
            withStackTraceFrame str `fmap` doProofScript m
      in
      VProofScript m'
    VBind pos v1 v2 ->
      let v1' = withStackTraceFrame str v1
          v2' = withStackTraceFrame str v2
      in
      VBind pos v1' v2'
    VLLVMCrucibleSetup m ->
      let m' =
            withStackTraceFrame str `fmap` doLLVM m
      in
      VLLVMCrucibleSetup m'
    VJVMSetup m ->
      let m' =
            withStackTraceFrame str `fmap` doJVM m
      in
      VJVMSetup m'
    VMIRSetup m ->
      let m' =
            withStackTraceFrame str `fmap` doMIR m
      in
      VMIRSetup m'
    _ ->
      val

toValueCase :: (FromValue b) =>
               (b -> Value -> Value -> TopLevel Value)
            -> Value
toValueCase prim =
  VLambda $ \b -> return $
  VLambda $ \v1 -> return $
  VLambda $ \v2 ->
  prim (fromValue b) v1 v2
