
module SAWScript.FindMain where

import SAWScript.Compiler
import SAWScript.AST

import Control.Monad

-- errMsgs

noMainErr :: Err a
noMainErr = fail "No main function defined."

multiMainErr :: Show a => Int -> [a] -> Err b
multiMainErr n xs = fail ("Multiple main functions defined: " ++ show n ++ " " ++ show xs)

-- | Takes a list of TopStmts, separates out any main blocks, failing if there is not exactly one.
findMain :: Compiler [TopStmt MPType] (Module MPType)
findMain = compiler "FindMain" $ \input ->
  case partitionMaybe sepMain input of
  ([],_) -> noMainErr
  (res:restBinds,ts)
    | null restBinds -> case res of
        ([],_) -> noMainErr
        (mb:restBs,binds)
          | null restBs -> return $ Module { declarations = TopLet binds : ts, mainBlock = mb }
          | otherwise -> multiMainErr 1 (mb:restBs)
    | otherwise -> multiMainErr 2 (res:restBinds)

-- | Takes a TopStmt and possibly returns two lists, the first a list of all the main blocks found in the module,
--   the second a list of the other, non-main bindings from a TopLet statement that contains a main binding.
sepMain :: TopStmt MPType -> Maybe ([[BlockStmt MPType]],[(Name,Expr MPType)])
sepMain ts = case ts of
  TopLet binds -> let ts = partitionMaybe isMain binds in guard (not $ null $ fst ts) >> return ts
  _            -> Nothing

-- | Takes a binding pair and returns a main block if the binding is of the appropriate form, Nothing otherwise.
isMain :: (Name,Expr MPType) -> Maybe [BlockStmt MPType]
isMain (n,e) = case (n,e) of
  ("main",Block bs _) -> Just bs
  _                   -> Nothing

-- |Partition that produces what results it can as it traverses the list
partitionMaybe :: (a -> Maybe b) -> [a] -> ([b],[a])
partitionMaybe f = foldr
  (\a (y,n) -> case f a of
     Just b  -> (b:y,n)
     Nothing -> (y,a:n))
  ([],[])

