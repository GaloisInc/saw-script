{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module SAWT where

import Control.Monad (when)
import Control.Monad.Catch (MonadCatch, MonadThrow)
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.IO.Unlift (MonadUnliftIO)
import Control.Monad.Reader (MonadReader (..), ReaderT (..), asks, void)
import Control.Monad.State (MonadState (..), gets, modify)
import Control.Monad.Trans (MonadTrans (..))
import Data.AIG.CompactGraph qualified as AIG
import Data.Bits
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HMap
import Data.Hashable
import Data.IORef (IORef, modifyIORef, newIORef, readIORef, writeIORef)
import SAWScript.AST qualified as SAW
import SAWScript.Interpreter qualified as SAW
import SAWScript.Lexer (lexSAW)
import SAWScript.Options (Options (..), Verbosity (..), printOutVia)
import SAWScript.Options qualified as SAW
import SAWScript.Parser (parseStmt, parseStmtSemi)
import SAWScript.Proof qualified as SAW
import SAWScript.Value qualified as SAW
import System.IO
import Text.Printf (printf)

type Checkpoints = HashMap (Stack SAW.Stmt) SAW.TopLevelCheckpoint

-- | A broader notion of state than SAW admits, this structure includes
-- information that allows for tracking an evaluation context and for creating
-- and restoring checkpoints associated with those contexts.
data SAWState = SAWState
  { ssSAWEnv :: SAWEnv,
    ssCurrentContext :: Stack SAW.Stmt,
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
          ssCurrentContext = emptyStack,
          ssCheckpoints = checkpoints,
          ssOutput = ssOutput
        }

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
    captureOutput s = modifyIORef outputRef (s :)

-- | Replace the existing `SAWState` with an empty state.
nukeSAWEnv :: MonadIO m => SAWT m ()
nukeSAWEnv = SAWT $ ReaderT $ \ref ->
  do
    emptyState <- newSAWState
    liftIO (writeIORef ref emptyState)

-- | Replace the existing `SAWState` with an empty state, but maintain the
-- existing cache of checkpoints.
drainSAWEnv :: MonadIO m => SAWT m ()
drainSAWEnv = SAWT $ ReaderT $ \ref ->
  do
    SAWState {..} <- liftIO (readIORef ref)
    mostlyEmptyState <- newSAWStateWithCheckpoints ssCheckpoints
    liftIO (writeIORef ref mostlyEmptyState)

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

-- instance MonadIO m => MonadReader SAWState (SAWT m) where
--   ask =
--     SAWT $
--       ReaderT $
--         \ref -> liftIO (readIORef ref)
--   local update (SAWT rdr) =
--     SAWT $
--       ReaderT $
--         \ref ->
--           do
--             original <- liftIO (readIORef ref)
--             liftIO (modifyIORef ref update)
--             res <- runReaderT rdr ref
--             liftIO (writeIORef ref original)
--             pure res

instance MonadIO m => MonadState SAWState (SAWT m) where
  get =
    SAWT $
      ReaderT $
        \ref -> liftIO (readIORef ref)
  put sawEnv =
    SAWT $
      ReaderT $
        \ref -> liftIO (writeIORef ref sawEnv)

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

getRO :: MonadIO m => SAWT m SAW.TopLevelRO
getRO = gets (seTopLevelRO . ssSAWEnv)

getRW :: MonadIO m => SAWT m SAW.TopLevelRW
getRW = gets (seTopLevelRW . ssSAWEnv)

makeCheckpoint :: MonadIO m => SAWT m ()
makeCheckpoint =
  do
    rw <- getRW
    checkpoint <- liftIO (SAW.makeCheckpoint rw)
    modify (\SAWState {..} -> SAWState {ssCheckpoints = HMap.insert ssCurrentContext checkpoint ssCheckpoints, ..})
    size <- gets (\SAWState {..} -> length ssCheckpoints)
    liftIO $
      hPutStrLn stderr $
        unlines
          [ "made checkpoint",
            "currently holding " <> show size <> " checkpoints"
          ]

-- | Empty the buffer containing SAW's printed output since inception or since
-- the last call to `flushOutput`
flushOutput :: MonadIO m => SAWT m [String]
flushOutput =
  do
    outputRef <- gets ssOutput
    output <- liftIO (readIORef outputRef)
    liftIO (writeIORef outputRef mempty)
    pure output

-------------------------------------------------------------------------------

-- | Interpret a SAW statement in a SAWT context. Cache a checkpoint that allows
-- returning to the resultant environment. Returns whether or not the resultant
-- environment came from a cached checkpoint (i.e., was executing the statement
-- a cache hit).
runStmtCheckpoint :: MonadIO m => SAW.Stmt -> SAWT m Bool
runStmtCheckpoint = runStmtWith True

-- | Interpret a SAW statement in a SAWT context. Returns whether or not the
-- resultant environment came from a cached checkpoint (i.e., was executing the
-- statement a cache hit).
runStmt :: MonadIO m => SAW.Stmt -> SAWT m Bool
runStmt = runStmtWith False

runStmtWith :: MonadIO m => Bool -> SAW.Stmt -> SAWT m Bool
runStmtWith checkpointAfter stmt =
  do
    modify (\SAWState {..} -> SAWState {ssCurrentContext = push stmt ssCurrentContext, ..})
    (context, checkpoints) <- gets (\SAWState {..} -> (ssCurrentContext, ssCheckpoints))
    liftIO (hPrint stderr (hash context))
    hit <- case checkpoints HMap.!? context of
      Just checkpoint -> liftTopLevel (SAW.restoreCheckpoint checkpoint) >> pure True
      Nothing -> liftTopLevel (SAW.interpretStmt False stmt) >> pure False
    when checkpointAfter makeCheckpoint
    pure hit

-------------------------------------------------------------------------------

data Stack a = Stack {stackElems :: [a], stackHash :: Int}
  deriving (Eq)

instance Show a => Show (Stack a) where
  show Stack {..} =
    printf "Stack {stackElems = %s, stackHash = %x}" (show stackElems) stackHash

instance Eq a => Hashable (Stack a) where
  hashWithSalt salt Stack {..} = salt `hashWithSalt` stackHash
  hash Stack {..} = stackHash

push :: Hashable a => a -> Stack a -> Stack a
push x Stack {..} =
  Stack
    { stackElems = x : stackElems,
      stackHash = stackHash `xor` hash x
    }

pop :: Hashable a => Stack a -> Maybe (a, Stack a)
pop Stack {..} =
  case stackElems of
    [] -> Nothing
    (x : xs) -> Just (x, Stack {stackElems = xs, stackHash = stackHash `xor` hash x})

emptyStack :: Stack a
emptyStack = Stack {stackElems = mempty, stackHash = 0xdeadbeef}

fromList :: Hashable a => [a] -> Stack a
fromList = foldr push emptyStack

-------------------------------------------------------------------------------

undo :: MonadIO m => SAWT m ()
undo = undefined

-- | Execute a `TopLevel` action to produce a `Value`
--
-- TODO: we should probably promote this result into `Either` by catching
-- whatever exceptions may get thrown
liftTopLevel :: (MonadIO m, SAW.IsValue a) => SAW.TopLevel a -> SAWT m SAW.Value
liftTopLevel action =
  do
    SAWState {ssSAWEnv = SAWEnv {..}, ..} <- get
    (value, newRW) <- liftIO (SAW.runTopLevel action seTopLevelRO seTopLevelRW)
    let state' = SAWState {ssSAWEnv = SAWEnv {seTopLevelRW = newRW, ..}, ..}
    put state'
    pure value

-- withTopLevel :: (MonadIO m, SAW.IsValue a) => SAW.TopLevel a -> (SAWState -> m b) -> SAWT m b
-- withTopLevel action onResult =
--   do
--     SAWState {ssSAWEnv = SAWEnv {..}, ..} <- get
--     (value, newRW) <- liftIO (SAW.runTopLevel action seTopLevelRO seTopLevelRW)
--     let state' = SAWState {ssSAWEnv = SAWEnv {seTopLevelRW = newRW, ..}, ..}
--     put state'
--     lift (onResult state')

runSAWText :: MonadIO m => String -> SAWT m ()
runSAWText str =
  do
    let tokens = lexSAW "<lsp>" str
    case parseStmtSemi tokens of
      Left err -> liftIO (print err)
      Right stmt -> void (runStmt stmt)

sample :: IO [String]
sample = runSAWTDefault sawAction
  where
    sawAction =
      do
        runStmt stmt
        flushOutput
    stmtText = "3"
    stmt =
      case parseStmt (lexSAW "" stmtText) of
        Left err -> error (show err)
        Right s -> s
