{- The REPL takes in a single statement at a time; however, most of the
compiler operates at the module granularity.  This module bridges that gap by
providing machinery to lift single statements to the module level. -}

module SAWScript.REPL.GenerateModule ( scratchpad
                                     , replFileName
                                     ) where

import Data.Map (Map)
import qualified Data.Map as Map

import SAWScript.AST (ModuleName,
                      Module(..), ValidModule)

scratchpad :: Map ModuleName ValidModule -> Module
scratchpad modsInScope =
  Module { moduleName = replModuleName
         , moduleExprEnv = [] -- no expressions yet
         , modulePrimEnv = Map.empty -- no 'Prim's in the REPL
         , moduleDependencies = modsInScope
         , moduleCryDeps = []
         }

-- The name of the REPL, as it should be reported in error messages
replFileName :: String
replFileName = "<stdin>"

-- The name of the REPL as a 'ModuleName'
replModuleName :: ModuleName
replModuleName = replFileName
