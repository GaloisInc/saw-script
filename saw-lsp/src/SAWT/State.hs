{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module SAWT.State where

import Control.Exception (SomeException, try)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State (MonadState (..), StateT (..), evalStateT, execStateT, gets)
import Data.AIG.CompactGraph qualified as AIG
import Data.IORef (IORef, atomicModifyIORef', newIORef)
import SAWScript.Interpreter qualified as SAW
import SAWScript.Options (Options (..), Verbosity (..), printOutVia)
import SAWScript.Options qualified as SAW
import SAWScript.Value qualified as SAW

newtype SAWT m a = SAWT {unSAWT :: StateT SAWEnv m a}
  deriving
    ( Applicative,
      Functor,
      Monad,
      MonadIO,
      MonadState SAWEnv
    )

runSAWT :: MonadIO m => SAWT m a -> SAWEnv -> m (a, SAWEnv)
runSAWT (SAWT sawAction) = runStateT sawAction

evalSAWT :: MonadIO m => SAWT m a -> SAWEnv -> m a
evalSAWT (SAWT sawAction) = evalStateT sawAction

execSAWT :: MonadIO m => SAWT m a -> SAWEnv -> m SAWEnv
execSAWT (SAWT sawAction) = execStateT sawAction

data SAWEnv = SAWEnv
  { seTopLevelRO :: SAW.TopLevelRO,
    seTopLevelRW :: SAW.TopLevelRW,
    seOutput :: IORef [String]
  }

newSAWEnv :: MonadIO m => m SAWEnv
newSAWEnv =
  do
    outRef <- liftIO (newIORef mempty)
    let options = SAW.defaultOptions {printOutFn = capture outRef}
    (ctx, ro, rw) <- liftIO (SAW.buildTopLevelEnv (SAW.AIGProxy AIG.compactProxy) options)
    pure (SAWEnv {seTopLevelRO = ro, seTopLevelRW = rw, seOutput = outRef})
  where
    capture :: IORef [String] -> Verbosity -> String -> IO ()
    capture outRef = printOutVia (\s -> atomicModifyIORef outRef (s :)) False Info

liftTopLevel :: (MonadIO m, SAW.IsValue a) => SAW.TopLevel a -> SAWT m (SAW.Value, [String])
liftTopLevel action =
  do
    SAWEnv {..} <- get
    (value, newRW) <- liftIO (SAW.runTopLevel action seTopLevelRO seTopLevelRW)
    output <- flushOutput
    let env' = SAWEnv {seTopLevelRW = newRW, ..}
    put env'
    pure (value, filter (not . null) output)

tryLiftTopLevel :: (MonadIO m, SAW.IsValue a) => SAW.TopLevel a -> SAWT m (Either String SAW.Value, [String])
tryLiftTopLevel action =
  do
    SAWEnv {..} <- get
    result <- liftIO (try (SAW.runTopLevel action seTopLevelRO seTopLevelRW))
    output <- flushOutput
    case result of
      Left (e :: SomeException) -> pure (Left (show e), output)
      Right (value, newRW) ->
        do
          let env' = SAWEnv {seTopLevelRW = newRW, ..}
          put env'
          pure (Right value, output)

flushOutput :: MonadIO m => SAWT m [String]
flushOutput =
  do
    outRef <- gets seOutput
    liftIO (atomicModifyIORef' outRef (mempty,))

atomicModifyIORef :: IORef t -> (t -> t) -> IO ()
atomicModifyIORef ref f = atomicModifyIORef' ref (\x -> (f x, ()))
