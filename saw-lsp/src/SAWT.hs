{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module SAWT where

import Control.Monad.Catch (MonadCatch, MonadThrow)
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.IO.Unlift (MonadUnliftIO)
import Control.Monad.Reader (MonadReader (..), ReaderT (..), asks, void)
import Control.Monad.State (MonadState (..))
import Control.Monad.Trans (MonadTrans (..))
import Data.AIG.CompactGraph qualified as AIG
import Data.IORef (IORef, modifyIORef, newIORef, readIORef, writeIORef)
import SAWScript.AST qualified as SAW
import SAWScript.Interpreter qualified as SAW
import SAWScript.Lexer (lexSAW)
import SAWScript.Options (Options (..), Verbosity (..), printOutVia)
import SAWScript.Options qualified as SAW
import SAWScript.Parser (parseStmt, parseStmtSemi)
import SAWScript.Proof qualified as SAW
import SAWScript.Value qualified as SAW

data SAWEnv = SAWEnv
  { seTopLevelRO :: SAW.TopLevelRO,
    seTopLevelRW :: SAW.TopLevelRW,
    seProofState :: Maybe SAW.ProofState,
    seOutput :: IORef [String]
  }

newtype SAWT m a = SAWT {unSAWT :: ReaderT (IORef SAWEnv) m a}
  deriving
    ( Applicative,
      Functor,
      Monad,
      MonadIO,
      MonadUnliftIO,
      MonadTrans,
      MonadThrow,
      MonadCatch
    )

runSAWT :: MonadIO m => SAWT m a -> SAWEnv -> m a
runSAWT (SAWT rdr) env =
  do
    envRef <- liftIO $ newIORef env
    runReaderT rdr envRef

runSAWTDefault :: MonadIO m => SAWT m a -> m a
runSAWTDefault action =
  do
    env <- defaultSAWEnv
    runSAWT action env

defaultSAWEnv :: MonadIO m => m SAWEnv
defaultSAWEnv =
  do
    seOutput <- liftIO $ newIORef mempty
    let options = SAW.defaultOptions {printOutFn = printOutVia (captureOutput seOutput) False Info}
    (ctx, ro, rw) <- liftIO $ SAW.buildTopLevelEnv (SAW.AIGProxy AIG.compactProxy) options
    pure (SAWEnv {seTopLevelRO = ro, seTopLevelRW = rw, seProofState = Nothing, seOutput = seOutput})

emptySAWEnv :: MonadIO m => SAWT m ()
emptySAWEnv = SAWT $ ReaderT $ \ref -> liftIO defaultSAWEnv >>= liftIO . writeIORef ref

captureOutput :: IORef [String] -> String -> IO ()
captureOutput ref s = modifyIORef ref (s :)

flushOutput :: MonadIO m => SAWT m [String]
flushOutput =
  do
    ref <- asks seOutput
    ss <- liftIO $ readIORef ref
    liftIO $ writeIORef ref mempty
    pure ss

instance MonadIO m => MonadReader SAWEnv (SAWT m) where
  ask =
    SAWT $
      ReaderT $
        \ref -> liftIO (readIORef ref)
  local update (SAWT rdr) =
    SAWT $
      ReaderT $
        \ref ->
          do
            original <- liftIO (readIORef ref)
            liftIO (modifyIORef ref update)
            res <- runReaderT rdr ref
            liftIO (writeIORef ref original)
            pure res

instance MonadIO m => MonadState SAWEnv (SAWT m) where
  get =
    SAWT $
      ReaderT $
        \ref -> liftIO (readIORef ref)
  put sawEnv =
    SAWT $
      ReaderT $
        \ref -> liftIO (writeIORef ref sawEnv)

liftTopLevel :: (MonadIO m, SAW.IsValue a) => SAW.TopLevel a -> SAWT m SAW.Value
liftTopLevel action =
  do
    SAWEnv {..} <- get
    (value, newRW) <- liftIO (SAW.runTopLevel action seTopLevelRO seTopLevelRW)
    let env' = SAWEnv {seTopLevelRW = newRW, ..}
    put env'
    pure value

withTopLevel :: (MonadIO m, SAW.IsValue a) => SAW.TopLevel a -> (SAWEnv -> m b) -> SAWT m b
withTopLevel action onResult =
  do
    SAWEnv {..} <- get
    (value, newRW) <- liftIO (SAW.runTopLevel action seTopLevelRO seTopLevelRW)
    let env' = SAWEnv {seTopLevelRW = newRW, ..}
    put env'
    lift (onResult env')

getLastResult :: MonadIO m => SAWT m String
getLastResult =
  do
    SAWEnv {..} <- ask
    undefined

runSAWStmt :: MonadIO m => SAW.Stmt -> SAWT m ()
runSAWStmt stmt = void (liftTopLevel (SAW.interpretStmt False stmt))

runSAWText :: MonadIO m => String -> SAWT m ()
runSAWText str =
  do
    let tokens = lexSAW "<lsp>" str
    case parseStmtSemi tokens of
      Left err -> liftIO (print err)
      Right stmt -> runSAWStmt stmt

sample :: IO [String]
sample = runSAWTDefault sawAction
  where
    sawAction =
      do
        runSAWStmt stmt
        flushOutput
    stmtText = "3"
    stmt =
      case parseStmt (lexSAW "" stmtText) of
        Left err -> error (show err)
        Right s -> s