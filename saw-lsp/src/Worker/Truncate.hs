{-# LANGUAGE BlockArguments #-}

module Worker.Truncate (Position (..), truncateScript) where

import Data.Maybe (mapMaybe)
import Message (Position (..))
import SAWScript.AST (Expr (..), Located (..), Pattern (..), Stmt (..))
import SAWScript.Position (Pos (..), getPos)

-- | At the given `Position`, which we assume to be within an expression
-- containing a list of statements, insert a call to `print_goal` and a call to
-- `admit`, and truncate the rest of the statements in the block, as well as the
-- rest of the statements provided.
truncateScript :: Position -> String -> [Stmt] -> [Stmt]
truncateScript (Position l c) note stmts =
  let mark = Position (l + 1) (c + 1)
      mkVar v = Var (Located v "" Unknown)
      mkBind = StmtBind Unknown (PWild Nothing) Nothing
      printGoal = mkBind (mkVar "print_goal")
      admit = mkBind (Application (mkVar "admit") (String note))
   in truncateScriptWith [printGoal, admit] mark stmts

-- | At the given `Position`, which we assume to be within an expression
-- containing a list of statements, insert `additions` and truncate the rest of
-- the statements in the block, as well as the rest of the statements provided.
truncateScriptWith :: [Stmt] -> Position -> [Stmt] -> [Stmt]
truncateScriptWith additions mark = mapMaybe (truncateBindStmtWith additions mark)

-- | If `mark` describes a point in the middle of `stmt`, try to truncate
-- statements within the expression `stmt` contains.
truncateBindStmtWith :: [Stmt] -> Position -> Stmt -> Maybe Stmt
truncateBindStmtWith additions mark stmt
  | pos `endsBefore` mark = Just stmt
  | pos `startsAfter` mark = Nothing
  | otherwise =
      case stmt of
        StmtBind posn pat ty e -> StmtBind posn pat ty <$> truncateLExprWith additions mark e
        -- TODO: this could be triggered if a user defines a block statement
        -- using an introduction form other than bind (i.e. `<-`), which is
        -- possible
        _ -> undefined
  where
    pos = getPos stmt

-- | If `mark` describes a point in the middle of `expr`, try to truncate
-- statements inside `expr`.
truncateLExprWith :: [Stmt] -> Position -> Expr -> Maybe Expr
truncateLExprWith additions mark expr =
  case expr of
    LExpr pos e
      | pos `endsBefore` mark -> Just expr
      | pos `startsAfter` mark -> Nothing
      | otherwise -> LExpr pos <$> truncateOverlappingExprWith additions mark e
    _ -> Nothing

-- Assuming `mark` describes a point in the middle of `expr`, if `expr` is of a
-- form that contains a set of statements (e.g. arrays and blocks), truncate the
-- statements following `mark` within that set. If not, leave the expression
-- alone.
truncateOverlappingExprWith :: [Stmt] -> Position -> Expr -> Maybe Expr
truncateOverlappingExprWith additions mark expr =
  case expr of
    Bool _ -> Just expr
    String _ -> Just expr
    Int _ -> Just expr
    Code _ -> Just expr
    CType _ -> Just expr
    Array es -> Just (Array (mapMaybe goExpr es)) -- TODO
    Block ss -> Just (Block (mapMaybe goStmt ss <> additions))
    Tuple es -> Just expr -- TODO
    Record binds -> Just expr
    Index a i -> Just expr
    Lookup e n -> Just expr
    TLookup e i -> Just expr
    Var _ -> Just expr
    Function pat e -> Just expr
    Application e1 e2 -> Application <$> goExpr e1 <*> goExpr e2
    Let d e -> Just expr
    TSig e ty -> Just expr
    IfThenElse c t f -> Just expr
    LExpr p e -> truncateLExprWith additions mark expr
  where
    goExpr = truncateOverlappingExprWith additions mark
    goStmt = truncateBindStmtWith additions mark

-- | Does the `Pos` start after the `Position`?
startsAfter :: Pos -> Position -> Bool
startsAfter reference Position {..} =
  case reference of
    Range _ refStartLine refStartCol _ _ ->
      case refStartLine `compare` line of
        LT -> False
        EQ -> refStartCol >= character
        GT -> True
    _ -> False

-- | Does the `Pos` end before the `Position`?
endsBefore :: Pos -> Position -> Bool
endsBefore pos Position {..} =
  case pos of
    Range _ _ _ refEndLine refEndCol ->
      case refEndLine `compare` line of
        LT -> True
        EQ -> refEndCol <= character
        GT -> False
    _ -> False
