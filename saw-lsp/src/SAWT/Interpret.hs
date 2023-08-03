module SAWT.Interpret where

import Control.Monad.IO.Class (MonadIO)
import Data.Bool (bool)
import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty ((:|)))
import Data.List.NonEmpty qualified as NE
import FList (FList (prefix), after, fingers)
import SAWScript.AST (Stmt)
import SAWScript.Interpreter qualified as SAW
import SAWScript.Value qualified as SAW
import SAWT
  ( Checkpoint (..),
    Checkpoints,
    SAWT,
    addCheckpoint,
    findCheckpoint,
    flushOutput,
    getCheckpoints,
    getContext,
    liftTopLevel,
    resetSAWEnv,
    restoreCheckpoint,
    tryLiftTopLevel,
    updateContext,
  )

-------------------------------------------------------------------------------
-- Interpretation of statement blocks

-- | Always executed in an empty environment.
--
-- Before executing a script, this function tries to find the largest prefix of
-- the script that's already been executed, and if it finds one, it will restore
-- the associated checkpoint and continue from there. If it doesn't find one, it
-- will revert to executing all statements individually.
--
-- Caching behavior can be "aggressive", in which case checkpoints are created
-- after every statement is (newly) executed, or not, in which case a checkpoint
-- is only created after the last statement in the script is executed.
interpretSAWScript ::
  MonadIO m =>
  -- | Cache aggressively?
  Bool ->
  NonEmpty Stmt ->
  SAWT m (Int, SAW.Value, Maybe String)
interpretSAWScript cacheAggressively (stmt :| stmts) =
  do
    resetSAWEnv
    checks <- getCheckpoints
    let interp =
          if cacheAggressively
            then interpretCacheSAWStmts
            else interpretSAWStmts
    case mostEfficientSplit checks (stmt : stmts) of
      Nothing ->
        do
          interp (stmt :| stmts)
      Just (ck@Checkpoint {..}, rest) ->
        do
          restoreCheckpoint ck
          let reused = length (stmt :| stmts) - length rest
          case rest of
            [] -> pure (reused, ckVal, ckOutput)
            (s : ss) ->
              do
                (hits, val, outM) <- interp (s :| ss)
                pure (reused + hits, val, outM)

-- | Cache once at the end
interpretSAWStmts :: MonadIO m => NonEmpty Stmt -> SAWT m (Int, SAW.Value, Maybe String)
interpretSAWStmts stmts =
  do
    results <- traverse interpretSAWStmt stmts
    let (val, outM) = NE.last results
    addCheckpoint val outM
    pure (0, val, outM)

-- | Cache everything along the way
interpretCacheSAWStmts :: MonadIO m => NonEmpty Stmt -> SAWT m (Int, SAW.Value, Maybe String)
interpretCacheSAWStmts stmts =
  do
    results <- traverse interpretSAWStmtCache stmts
    let hits = sum (NE.map (\(b, _, _) -> bool 0 1 b) results)
        (_, val, outM) = NE.last results
    pure (hits, val, outM)

mostEfficientSplit :: Checkpoints -> [Stmt] -> Maybe (Checkpoint, [Stmt])
mostEfficientSplit checks stmts = go (orderedSplits stmts)
  where
    go splits =
      case splits of
        [] -> Nothing
        (flist : ss) ->
          let context = prefix flist
           in case findCheckpoint checks context of
                Just ck -> Just (ck, after flist)
                Nothing -> go ss

-- | All contexts that the list of statements admit, ordered largest first
orderedSplits :: [Stmt] -> [FList Stmt]
orderedSplits = reverse . fingers

-------------------------------------------------------------------------------
-- Interpretation of single statements

-- | Interpret a SAW statement to obtain its `Value` and printed output, if any.
-- If the statement has already been executed in the current context, use the
-- stored result of that execution intsead of interpreting the statement anew,
-- and reset the context. Afterwards, create a checkpoint for having executed
-- this statement in the preexisting context.
interpretSAWStmtCache :: MonadIO m => Stmt -> SAWT m (Bool, SAW.Value, Maybe String)
interpretSAWStmtCache = interpretSAWStmt' True

-- | Interpret a SAW statement to obtain its `Value` and its printed output, if
-- any. Doesn't capture SAW failure. Doesn't cache.
interpretSAWStmt :: MonadIO m => Stmt -> SAWT m (SAW.Value, Maybe String)
interpretSAWStmt stmt =
  do
    (_, val, outM) <- interpretSAWStmt' False stmt
    pure (val, outM)

interpretSAWStmt' :: MonadIO m => Bool -> Stmt -> SAWT m (Bool, SAW.Value, Maybe String)
interpretSAWStmt' useCache stmt =
  do
    updateContext stmt
    context <- getContext
    checkpoints <- getCheckpoints
    case (useCache, findCheckpoint checkpoints context) of
      (False, _) -> interpret >>= miss
      (True, Nothing) -> interpret >>= miss
      (True, Just ck@Checkpoint {..}) ->
        restoreCheckpoint ck >> pure (True, ckVal, ckOutput)
  where
    miss (val, outM)
      | useCache = addCheckpoint val outM >> pure (False, val, outM)
      | otherwise = pure (False, val, outM)
    interpret =
      do
        val <- liftTopLevel (SAW.interpretStmt False stmt)
        output <- flushOutput
        case output of
          [] -> pure (val, Nothing)
          _ -> pure (val, Just (intercalate "\n" output))

-- | Interpret a SAW statement to obtain its `Value` and its printed output, if
-- any, or fail with a message if SAW failed.
tryInterpretSAWStmt ::
  MonadIO m =>
  Stmt ->
  SAWT m (Either String (SAW.Value, Maybe String))
tryInterpretSAWStmt stmt =
  do
    valE <- tryLiftTopLevel (SAW.interpretStmt False stmt)
    case valE of
      Left err -> pure (Left err)
      Right val ->
        do
          outputLines <- flushOutput
          case outputLines of
            [] -> pure (Right (val, Nothing))
            _ -> pure (Right (val, Just (intercalate "\n" outputLines)))
