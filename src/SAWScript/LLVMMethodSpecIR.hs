{- |
Module      : SAWScript.LLVMMethodSpecIR
Description : Provides typechecked representation for LLVM function
              specifications and function for creating it from AST
              representation.
Maintainer  : atomb
Stability   : provisional
-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SAWScript.LLVMMethodSpecIR
  ( -- * MethodSpec record
    LLVMMethodSpecIR
  , specName
  , specPos
  , specCodebase
  , specBackend
  , specSolverStats
  , specFunction
  , specBehavior
  , specAssumptions
  , specAddBehaviorCommand
  , specAddVarDecl
  , specAddLogicAssignment
  , specAddAssumption
  , specGetLogicAssignment
  , specLLVMExprNames
  , initLLVMMethodSpec
    -- * Method behavior.
  , BehaviorSpec
  -- , bsLoc
  , bsExprs
  , bsPtrExprs
  , bsExprDecls
  , bsAssumptions
  , BehaviorCommand(..)
  , bsCommands
  ) where

-- Imports {{{1

import Data.Map (Map)
import qualified Data.Map as Map
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import qualified Verifier.LLVM.Codebase as LSS
import Verifier.LLVM.Backend
import Verifier.LLVM.Backend.SAW

import SAWScript.LLVMExpr
import SAWScript.Prover.SolverStats
import SAWScript.Utils

-- BehaviorSpec {{{1

-- | Postconditions used for implementing behavior specification. All
-- LogicExprs in behavior commands need to be extracted with
-- useLogicExpr, in a specific shared context, before they can be
-- used.
data BehaviorCommand
     -- | Assign an LLVM variables the value given by the mixed expression.
   = Ensure Bool Pos LLVMExpr MixedExpr
     -- | Modify an LLVM variables to an arbitrary expression.
     -- integral type or array.
   | Modify LLVMExpr LLVMActualType
     -- | Allocate a new memory region of the given type and store it in
     -- the location named.
   | Allocate LLVMExpr LLVMActualType
     -- | Specifies return value for a function.
   | Return MixedExpr
     -- | Specifies an arbitrary return value for a function.
   | ReturnArbitrary LLVMActualType

data BehaviorSpec = BS {
         -- | Program counter for spec.
         -- bsLoc :: LSS.SymBlockID
         -- | Declared LLVM expressions, with types and maybe initial values.
         bsExprDecls :: Map LLVMExpr (LLVMActualType, Maybe LogicExpr)
         -- | Assumptions for this behavior.
       , bsAssumptions :: [LogicExpr]
         -- | Commands to execute in reverse order.
       , bsReversedCommands :: [BehaviorCommand]
       }

-- | Returns list of all LLVM expressions that are not pointers.
bsExprs :: BehaviorSpec -> [LLVMExpr]
bsExprs bs = Map.keys (bsExprDecls bs)

-- | Returns list of all LLVM expressions that are pointers.
bsPtrExprs :: BehaviorSpec -> [LLVMExpr]
bsPtrExprs bs = filter isPtrLLVMExpr (bsExprs bs)

-- Command utilities {{{2

-- | Return commands in behavior in order they appeared in spec.
bsCommands :: BehaviorSpec -> [BehaviorCommand]
bsCommands = reverse . bsReversedCommands

bsAddCommand :: BehaviorCommand -> BehaviorSpec -> BehaviorSpec
bsAddCommand bc bs =
  bs { bsReversedCommands = bc : bsReversedCommands bs }

bsAddAssumption :: LogicExpr -> BehaviorSpec -> BehaviorSpec
bsAddAssumption a bs =
  bs { bsAssumptions = a : bsAssumptions bs }

type Backend = SAWBackend

initLLVMMethodSpec :: Pos
                   -> SBE Backend
                   -> LSS.Codebase Backend
                   -> LSS.Symbol
                   -> LLVMMethodSpecIR
initLLVMMethodSpec pos sbe cb defname =
  let initBS = BS { -- bsLoc = LSS.sdEntry def
                    bsExprDecls = Map.empty
                  , bsAssumptions = []
                  , bsReversedCommands = []
                  }
      initMS = MSIR { specPos = pos
                    , specCodebase = cb
                    , specBackend = sbe
                    , specFunction = defname
                    , specLLVMExprNames = Map.empty
                    , specBehavior = initBS
                    , specSolverStats = mempty
                    }
  in initMS

-- MethodSpecIR {{{1

data LLVMMethodSpecIR = MSIR {
    specPos :: Pos
    -- | Codebase containing function to verify.
  , specCodebase :: LSS.Codebase Backend
    -- | Backend of symbolic simulator
  , specBackend :: SBE Backend
    -- | Name of function to verify.
  , specFunction :: LSS.Symbol -- TODO: is this necessary?
    -- | Mapping from user-visible LLVM state names to LLVMExprs
  , specLLVMExprNames :: Map String (LLVMActualType, LLVMExpr)
    -- | Behavior specification for method.
  , specBehavior :: BehaviorSpec
    -- | Statistics about the solver that proved this spec
  , specSolverStats :: SolverStats
  }

-- | Return user printable name of method spec (currently the class +
-- method name).
specName :: LLVMMethodSpecIR -> Doc
specName = LSS.ppSymbol . specFunction

specAssumptions :: LLVMMethodSpecIR -> [LogicExpr]
specAssumptions = bsAssumptions . specBehavior

specAddVarDecl :: Pos -> String -> LLVMExpr -> LLVMActualType
               -> LLVMMethodSpecIR -> LLVMMethodSpecIR
specAddVarDecl _pos name expr lt ms = ms { specBehavior = bs'
                                        , specLLVMExprNames = ns' }
  where bs = specBehavior ms
        bs' = bs { bsExprDecls =
                     Map.insert expr (lt, Nothing) (bsExprDecls bs)
                 }
        ns' = Map.insert name (lt, expr) (specLLVMExprNames ms)

-- TODO: fix up error handling for this function
specAddLogicAssignment :: Pos -> LLVMExpr -> LogicExpr
                       -> LLVMMethodSpecIR -> LLVMMethodSpecIR
specAddLogicAssignment _pos expr t ms = ms { specBehavior = bs' }
  where bs = specBehavior ms
        eds = bsExprDecls bs
        eds' = case Map.lookup expr eds of
                 Just (at, Nothing) -> Map.insert expr (at, Just t) eds
                 Just (_, Just _) ->
                   error $ "assignment already given for " ++ show expr
                 Nothing ->
                   error $ "assignment for undeclared variable " ++ show expr
        bs' = bs { bsExprDecls = eds' }

specGetLogicAssignment :: LLVMMethodSpecIR -> LLVMExpr -> Maybe LogicExpr
specGetLogicAssignment ms expr =
  case Map.lookup expr (bsExprDecls (specBehavior ms)) of
    Just (_, Nothing) -> Nothing
    Just (_, t) -> t
    Nothing -> Nothing

specAddBehaviorCommand :: BehaviorCommand
                       -> LLVMMethodSpecIR -> LLVMMethodSpecIR
specAddBehaviorCommand bc ms =
  ms { specBehavior = bsAddCommand bc (specBehavior ms) }

specAddAssumption :: LogicExpr
                  -> LLVMMethodSpecIR -> LLVMMethodSpecIR
specAddAssumption a ms =
  ms { specBehavior = bsAddAssumption a (specBehavior ms) }
