{-# LANGUAGE TemplateHaskell #-}
module SAWScript.Prelude where

import SAWScript.AST hiding (Name)
import SAWScript.MGU

import Verifier.SAW.ParserUtils hiding (ModuleName)
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

preludeNames :: [String]
preludeNames = map fst preludeEnv
