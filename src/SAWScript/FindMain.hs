
module SAWScript.FindMain where

import SAWScript.Compiler
import SAWScript.AST

import Control.Monad

-- errMsgs

noMainErr :: Err a
noMainErr = fail "No main function defined."

multiMainErr :: Err b
multiMainErr = fail "Multiple main functions defined."

-- | Takes a list of TopStmts, separates out any main blocks, failing if there is not exactly one.
findMain :: Compiler [TopStmt MPType] (Module MPType)
findMain = compiler "FindMain" $ \input ->
  case separate sepMain input of
  ([],_)    -> noMainErr
  ([mn],ts) -> return $ Module { declarations = ts, mainBlock = mn }
  _ -> multiMainErr

-- | Takes a TopStmt and possibly returns two lists, the first a list of all the main blocks found in the module,
--   the second a list of the other, non-main bindings from a TopBind statement that contains a main binding.
sepMain :: TopStmt MPType -> Maybe (Expr MPType)
sepMain ts = case ts of
  TopBind "main" e -> Just e
  _            -> Nothing

-- |Partition that produces what results it can as it traverses the list
separate :: (a -> Maybe b) -> [a] -> ([b],[a])
separate f = foldr
  (\a (y,n) -> case f a of
     Just b  -> (b:y,n)
     Nothing -> (y,a:n))
  ([],[])

