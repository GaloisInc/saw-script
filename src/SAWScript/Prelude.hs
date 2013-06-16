module SAWScript.Prelude where

import SAWScript.AST hiding (Name)
import SAWScript.MGU

import qualified Data.Map as M

preludeEnv :: [(Name, Schema)]
preludeEnv =
  [ ("return", Forall ["a"]
               (tFun (boundVar "a") (topLevel (boundVar "a")))
    )
  , ("print", Forall ["a"]
               (tFun (boundVar "a") (topLevel tUnit))
    )
  ]
  where topLevel = tBlock (tContext TopLevel)
        boundVar = TyVar . BoundVar

preludeEnvRenamer :: Env Name
preludeEnvRenamer = M.fromList $ map (\(n,_) -> (n,n)) preludeEnv

