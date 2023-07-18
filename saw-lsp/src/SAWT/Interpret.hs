{-# LANGUAGE TupleSections #-}

module SAWT.Interpret where

import Control.Applicative (Applicative (liftA2))
import Control.Monad (unless)
import Control.Monad.IO.Class (MonadIO)
import Data.Bifunctor
import Data.Bool (bool)
import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty ((:|)))
import Data.List.NonEmpty qualified as NE
import FList (FList, after, before, fingers)
import SAWScript.AST (Stmt)
import SAWScript.Interpreter qualified as SAW
import SAWScript.Lexer qualified as SAW
import SAWScript.Parser qualified as SAW
import SAWScript.Value qualified as SAW
import SAWT
  ( Checkpoint (..),
    Checkpoints,
    SAWT,
    addStmtToContext,
    findCheckpoint,
    flushOutput,
    getCheckpoints,
    getContext,
    liftTopLevel,
    makeCheckpoint,
    mkContext,
    rememberCheckpoint,
    resetSAWEnv,
    restoreCheckpoint,
    setContext,
    tryLiftTopLevel,
  )

-------------------------------------------------------------------------------
-- Interpretation of statement blocks

-- | Always executed in an empty environment
interpretCacheSAWScript ::
  MonadIO m =>
  NonEmpty Stmt ->
  SAWT m (Int, SAW.Value, Maybe String)
interpretCacheSAWScript (stmt :| stmts) =
  do
    resetSAWEnv
    checks <- getCheckpoints
    case mostEfficientSplit checks (stmt : stmts) of
      Nothing ->
        do
          (hits, val, outM) <- interpretCacheSAWStmts (stmt :| stmts)
          makeCheckpoint val outM >>= rememberCheckpoint
          pure (0, val, outM)
      Just (ck@Checkpoint {..}, rest) ->
        do
          restoreCheckpoint ck
          let used = length (stmt :| stmts) - length rest
          case rest of
            [] -> pure (used, ckVal, ckOutput)
            (s : ss) ->
              do
                (val, outM) <- interpretSAWStmts (s :| ss)
                makeCheckpoint val outM >>= rememberCheckpoint
                pure (used, val, outM)

interpretSAWStmts :: MonadIO m => NonEmpty Stmt -> SAWT m (SAW.Value, Maybe String)
interpretSAWStmts stmts = NE.last <$> traverse interpretSAWStmt stmts

interpretCacheSAWStmts :: MonadIO m => NonEmpty Stmt -> SAWT m (Int, SAW.Value, Maybe String)
interpretCacheSAWStmts stmts =
  do
    results <- traverse interpretCacheSAWStmt stmts
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
          let context = mkContext (before flist)
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
-- and reset the context.
interpretCacheSAWStmt :: MonadIO m => Stmt -> SAWT m (Bool, SAW.Value, Maybe String)
interpretCacheSAWStmt stmt =
  do
    ctx <- getContext
    let ctx' = addStmtToContext stmt ctx
    checks <- getCheckpoints
    (hit, val, outM) <- case findCheckpoint checks ctx' of
      Nothing -> uncurry (False,,) <$> interpretSAWStmt stmt
      Just ck@Checkpoint {..} ->
        do
          restoreCheckpoint ck
          pure (True, ckVal, ckOutput)
    setContext ctx'
    unless hit (makeCheckpoint val outM >>= rememberCheckpoint)
    pure (hit, val, outM)

-- | Interpret a SAW statement to obtain its `Value` and its printed output, if
-- any. Doesn't capture SAW failure.
interpretSAWStmt :: MonadIO m => Stmt -> SAWT m (SAW.Value, Maybe String)
interpretSAWStmt stmt =
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
