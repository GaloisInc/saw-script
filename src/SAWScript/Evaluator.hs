module SAWScript.Evaluator where

import SAWScript.AST

evaluate :: Expr -> Expr
evaluate = id