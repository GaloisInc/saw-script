module SAWScript.Prelude where

import SAWScript.AST hiding (Name)
import SAWScript.MGU

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
