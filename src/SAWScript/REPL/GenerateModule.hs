{- The REPL takes in a single statement at a time; however, most of the
compiler operates at the module granularity.  This module bridges that gap by
providing machinery to lift single statements to the module level. -}

module SAWScript.REPL.GenerateModule ( wrapBStmt
                                     , scratchpad
                                     , replFileName
                                     , replModuleName
                                     ) where

import Data.Map (Map)
import qualified Data.Map as Map

import SAWScript.AST (ModuleName(ModuleName),
                      Module(..), ValidModule,
                      Expr(Block),
                      BlockStmt,
                      RawT,
                      Name)

wrapBStmt :: Map ModuleName ValidModule
             -> Name
             -> BlockStmt refT RawT
             -> Module refT RawT typeT
wrapBStmt modsInScope stmtName stmt =
  (scratchpad modsInScope) {
    {- The expression environment simply maps @it@ to the statement. Statements
    aren't expressions, so I wrap it up in a block (with an unspecified return
    type). -}
    moduleExprEnv = Map.singleton stmtName (Block [stmt] Nothing) }

scratchpad :: Map ModuleName ValidModule -> Module refT exprT typeT
scratchpad modsInScope =
  Module { moduleName = replModuleName
         , moduleExprEnv = Map.empty -- no expressions yet
         , modulePrimEnv = Map.empty -- no 'Prim's in the REPL
         , moduleTypeEnv = Map.empty -- no type synonyms in the REPL
         , moduleDependencies = modsInScope }

-- The name of the REPL, as it should be reported in error messages
replFileName :: String
replFileName = "<stdin>"

-- The name of the REPL as a 'ModuleName'
replModuleName :: ModuleName
replModuleName = ModuleName [] replFileName
