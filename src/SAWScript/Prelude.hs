{-# LANGUAGE TemplateHaskell #-}
module SAWScript.Prelude where

import SAWScript.AST hiding (Name)
import SAWScript.MGU

import Verifier.SAW.ParserUtils hiding (ModuleName, preludeName)
import Verifier.SAW.Prelude

import qualified Data.Map as M
import Language.Haskell.TH.Syntax hiding (Name)

$(runDecWriter $ do
  let prelName = returnQ $ VarE (mkName "preludeModule")
  preludeExp <- defineImport prelName preludeModule
  prelude <- defineModuleFromFile
               [ preludeExp ]
               "ssPreludeModule"
               "prelude/prelude.sawcore"
  declareSharedModuleFns "SAWScriptPrelude" (decVal prelude)
 )

preludeName :: ModuleName
preludeName = ModuleName [] "Prelude"


preludeEnv :: [(ResolvedName, Schema)]
preludeEnv = map qualify $
  [ ("return", Forall ["m", "a"]
               (tFun (boundVar "a") (tBlock (boundVar "m") (boundVar "a")))
    )
  , ("print", Forall ["a"]
               (tFun (boundVar "a") (topLevel (tTuple [])))
    )
  ]
  where topLevel = tBlock (tContext TopLevel)
        boundVar = TyVar . BoundVar
        qualify (n, ty) = (TopLevelName preludeName n, ty)
