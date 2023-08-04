{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SAWT where

import Control.Monad.Catch (MonadCatch, MonadThrow, SomeException, try)
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.IO.Unlift (MonadUnliftIO)
import Control.Monad.Reader (MonadReader (..), ReaderT (..), void)
import Control.Monad.State (MonadState (..), gets, modify)
import Control.Monad.Trans (MonadTrans (..))
import Data.AIG.CompactGraph qualified as AIG
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HMap
import Data.IORef (IORef, atomicModifyIORef', atomicWriteIORef, newIORef, readIORef)
import SAWScript.AST qualified as SAW
import SAWScript.Interpreter qualified as SAW
import SAWScript.Options (Options (..), Verbosity (..), printOutVia)
import SAWScript.Options qualified as SAW
import SAWScript.Value qualified as SAW
import Util.Stack as Stack

atomicModifyIORef :: IORef t -> (t -> t) -> IO ()
atomicModifyIORef ref f = atomicModifyIORef' ref (\x -> (f x, ()))

-------------------------------------------------------------------------------
-- Monad/interfaces

-- | A monad transformer to include `SAW` functionality in a transformer stack.
newtype SAWT m a = SAWT {unSAWT :: ReaderT (IORef SAWState) m a}
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

instance MonadIO m => MonadReader SAWState (SAWT m) where
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
            liftIO (atomicModifyIORef ref update)
            res <- runReaderT rdr ref
            liftIO (atomicWriteIORef ref original)
            pure res

instance MonadIO m => MonadState SAWState (SAWT m) where
  get =
    SAWT $
      ReaderT $
        \ref -> liftIO (readIORef ref)
  put sawEnv =
    SAWT $
      ReaderT $
        \ref -> liftIO (atomicWriteIORef ref sawEnv)

-------------------------------------------------------------------------------
-- Running

-- | Run a SAW action with the given environment
runSAWT :: MonadIO m => SAWT m a -> SAWState -> m a
runSAWT (SAWT rdr) sState =
  do
    sawStateRef <- liftIO (newIORef sState)
    runReaderT rdr sawStateRef

-- | Run a SAW action with the given environment reference
runSAWT' :: MonadIO m => SAWT m a -> IORef SAWState -> m a
runSAWT' (SAWT rdr) = runReaderT rdr

-- | Run a SAW action with a default environment (at the moment, the environment
-- specified by `defaultSAWEnv`)
runSAWTDefault :: MonadIO m => SAWT m a -> m a
runSAWTDefault action =
  do
    sState <- newSAWState
    runSAWT action sState

-------------------------------------------------------------------------------
-- Accessing/modifying

getRef :: MonadIO m => SAWT m (IORef SAWState)
getRef = SAWT (ReaderT pure)

getRO :: MonadIO m => SAWT m SAW.TopLevelRO
getRO = gets (seTopLevelRO . ssSAWEnv)

getRW :: MonadIO m => SAWT m SAW.TopLevelRW
getRW = gets (seTopLevelRW . ssSAWEnv)

getContext :: MonadIO m => SAWT m Context
getContext = gets ssContext

setContext :: MonadIO m => Context -> SAWT m ()
setContext ctx = modify (\SAWState {..} -> SAWState {ssContext = ctx, ..})

getCheckpoints :: MonadIO m => SAWT m Checkpoints
getCheckpoints = gets ssCheckpoints

setCheckpoints :: MonadIO m => Checkpoints -> SAWT m ()
setCheckpoints checks = modify (\SAWState {..} -> SAWState {ssCheckpoints = checks, ..})

-- | Empty the buffer containing SAW's printed output since inception or since
-- the last call to `flushOutput`
flushOutput :: MonadIO m => SAWT m [String]
flushOutput =
  do
    outputRef <- gets ssOutput
    output <- liftIO (readIORef outputRef)
    liftIO (atomicWriteIORef outputRef mempty)
    pure output

-------------------------------------------------------------------------------
-- Our state/environment

-- | A broader notion of state than SAW admits, this structure includes
-- information that allows for tracking an evaluation context and for creating
-- and restoring checkpoints associated with those contexts.
data SAWState = SAWState
  { ssSAWEnv :: SAWEnv,
    ssContext :: Context,
    ssCheckpoints :: Checkpoints,
    ssOutput :: IORef [String] -- where does this belong? I need it to initialize `printOutVia`, which is currently populated in `newSAWEnv`
  }

-- | Make an empty SAW state
newSAWState :: MonadIO m => m SAWState
newSAWState = newSAWStateWithCheckpoints mempty

-- | Make an empty SAW state, initialized with preexisting checkpoints
newSAWStateWithCheckpoints :: MonadIO m => Checkpoints -> m SAWState
newSAWStateWithCheckpoints checkpoints =
  do
    ssOutput <- liftIO $ newIORef mempty
    env <- newSAWEnv ssOutput
    pure
      SAWState
        { ssSAWEnv = env,
          ssContext = emptyStack,
          ssCheckpoints = checkpoints,
          ssOutput = ssOutput
        }

-------------------------------------------------------------------------------
-- SAW's state/environment

-- | Packages the environments that a `TopLevel` action reads/writes.
data SAWEnv = SAWEnv
  { seTopLevelRO :: SAW.TopLevelRO,
    seTopLevelRW :: SAW.TopLevelRW
    -- seProofState :: Maybe SAW.ProofState
  }

-- | A default environment for SAW, derived from SAW's own notion of a default
-- environment, but that captures printed output in an `IORef` buffer we control
newSAWEnv :: MonadIO m => IORef [String] -> m SAWEnv
newSAWEnv outputRef =
  do
    let options = SAW.defaultOptions {printOutFn = printOutVia captureOutput False Info}
    (ctx, ro, rw) <- liftIO $ SAW.buildTopLevelEnv (SAW.AIGProxy AIG.compactProxy) options
    pure (SAWEnv {seTopLevelRO = ro, seTopLevelRW = rw})
  where
    captureOutput :: String -> IO ()
    captureOutput s = atomicModifyIORef outputRef (s :)

-- | Replace the existing `SAWState` with an empty state.
nukeSAWEnv :: MonadIO m => SAWT m ()
nukeSAWEnv = SAWT $ ReaderT $ \ref ->
  do
    emptyState <- newSAWState
    liftIO (atomicWriteIORef ref emptyState)

-- | Replace the existing `SAWState` with an empty state, but maintain the
-- existing cache of checkpoints.
resetSAWEnv :: MonadIO m => SAWT m ()
resetSAWEnv = SAWT $ ReaderT $ \ref ->
  do
    SAWState {..} <- liftIO (readIORef ref)
    mostlyEmptyState <- newSAWStateWithCheckpoints ssCheckpoints
    liftIO (atomicWriteIORef ref mostlyEmptyState)

-------------------------------------------------------------------------------
-- Context

type Context = Stack SAW.Stmt

mkContext :: [SAW.Stmt] -> Context
mkContext = Stack.fromList

emptyContext :: Context
emptyContext = emptyStack

addStmtToContext :: SAW.Stmt -> Context -> Context
addStmtToContext = push

updateContext :: MonadIO m => SAW.Stmt -> SAWT m ()
updateContext stmt =
  do
    ctx <- getContext
    setContext (push stmt ctx)

-------------------------------------------------------------------------------
-- Checkpoint(s)

data Checkpoint = Checkpoint
  { ckEnv :: SAW.TopLevelCheckpoint,
    ckVal :: SAW.Value,
    ckOutput :: Maybe String
  }

type Checkpoints = HashMap Context Checkpoint

-- addCheckpoint :: Context -> Checkpoint -> Checkpoints -> Checkpoints
-- addCheckpoint = HMap.insert

findCheckpoint :: Checkpoints -> Context -> Maybe Checkpoint
findCheckpoint = flip HMap.lookup

findCheckpointM :: MonadIO m => SAWT m (Maybe Checkpoint)
findCheckpointM = HMap.lookup <$> getContext <*> getCheckpoints

createCheckpoint :: MonadIO m => SAW.Value -> Maybe String -> SAWT m Checkpoint
createCheckpoint ckVal ckOutput =
  do
    rw <- getRW
    ckEnv <- liftIO (SAW.makeCheckpoint rw)
    pure Checkpoint {..}

-- | Remember a checkpoint with the current context
rememberCheckpoint :: MonadIO m => Checkpoint -> SAWT m ()
rememberCheckpoint checkpoint =
  do
    checks <- getCheckpoints
    ctx <- getContext
    setCheckpoints (HMap.insert ctx checkpoint checks)

addCheckpoint :: MonadIO m => SAW.Value -> Maybe String -> SAWT m ()
addCheckpoint val outM = createCheckpoint val outM >>= rememberCheckpoint

restoreCheckpoint :: MonadIO m => Checkpoint -> SAWT m ()
restoreCheckpoint Checkpoint {..} = void (liftTopLevel (SAW.restoreCheckpoint ckEnv))

-------------------------------------------------------------------------------

-- runSAWScript :: MonadIO m => NonEmpty SAW.Stmt -> SAWT m (SAW.Value, Maybe String)
-- runSAWScript stmts =
--   do
--     drainSAWEnv
--     let ctx = Stack.fromList stmts
--     ckM <- local (\SAWState {..} -> SAWState {ssContext = ctx, ..}) lookupSAWCheckpoint
--     case ckM of
--       Nothing ->
--         let (prefix, final) = (NE.init stmts, NE.last stmts)
--          in mapM_ runSAWStmt prefix >> runSAWStmt final
--       Just ck@Checkpoint {..} -> restoreSAWCheckpoint ck >> pure (ckVal, ckOutput)

-------------------------------------------------------------------------------

-- -- | Interpret a SAW statement in a SAWT context. Cache a checkpoint that allows
-- -- returning to the resultant environment. Returns whether or not the resultant
-- -- environment came from a cached checkpoint (i.e., was executing the statement
-- -- a cache hit).
-- runStmtCheckpoint :: MonadIO m => SAW.Stmt -> SAWT m Bool
-- runStmtCheckpoint = runStmtWith True

-- -- | Interpret a SAW statement in a SAWT context. Returns whether or not the
-- -- resultant environment came from a cached checkpoint (i.e., was executing the
-- -- statement a cache hit).
-- runStmt :: MonadIO m => SAW.Stmt -> SAWT m Bool
-- runStmt = runStmtWith False

-- runStmtWith :: MonadIO m => Bool -> SAW.Stmt -> SAWT m Bool
-- runStmtWith checkpointAfter stmt =
--   do
--     modify (\SAWState {..} -> SAWState {ssContext = push stmt ssContext, ..})
--     (context, checkpoints) <- gets (\SAWState {..} -> (ssContext, ssCheckpoints))
--     liftIO (hPrint stderr (hash context))
--     hit <- case checkpoints HMap.!? context of
--       Just checkpoint -> liftTopLevel (SAW.restoreCheckpoint checkpoint) >> pure True
--       Nothing -> liftTopLevel (SAW.interpretStmt False stmt) >> pure False
--     when checkpointAfter makeCheckpoint
--     pure hit

-- runStmt' :: MonadIO m => Bool -> Bool -> SAW.Stmt -> SAWT m Bool
-- runStmt' tryRestore makeCheckpoint stmt =
--   do

-------------------------------------------------------------------------------
-- TopLevel

-- | Execute a `TopLevel` action to produce a `Value`
liftTopLevel :: (MonadIO m, SAW.IsValue a) => SAW.TopLevel a -> SAWT m SAW.Value
liftTopLevel action =
  do
    SAWState {ssSAWEnv = SAWEnv {..}, ..} <- get
    (value, newRW) <- liftIO (SAW.runTopLevel action seTopLevelRO seTopLevelRW)
    let state' = SAWState {ssSAWEnv = SAWEnv {seTopLevelRW = newRW, ..}, ..}
    put state'
    pure value

tryLiftTopLevel :: (MonadIO m, SAW.IsValue a) => SAW.TopLevel a -> SAWT m (Either String SAW.Value)
tryLiftTopLevel action =
  do
    SAWState {ssSAWEnv = SAWEnv {..}, ..} <- get
    result <- liftIO (try (SAW.runTopLevel action seTopLevelRO seTopLevelRW))
    case result of
      Left (e :: SomeException) -> pure (Left (show e))
      Right (value, newRW) ->
        do
          let state' = SAWState {ssSAWEnv = SAWEnv {seTopLevelRW = newRW, ..}, ..}
          put state'
          pure (Right value)

-- withTopLevel :: (MonadIO m, SAW.IsValue a) => SAW.TopLevel a -> (SAWState -> m b) -> SAWT m b
-- withTopLevel action onResult =
--   do
--     SAWState {ssSAWEnv = SAWEnv {..}, ..} <- get
--     (value, newRW) <- liftIO (SAW.runTopLevel action seTopLevelRO seTopLevelRW)
--     let state' = SAWState {ssSAWEnv = SAWEnv {seTopLevelRW = newRW, ..}, ..}
--     put state'
--     lift (onResult state')
