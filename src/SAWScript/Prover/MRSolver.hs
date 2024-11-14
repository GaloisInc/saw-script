{- |
Module      : SAWScript.Prover.MRSolver
Description : The SAW monadic-recursive solver (Mr. Solver)
Copyright   : Galois, Inc. 2022
License     : BSD3
Maintainer  : westbrook@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWScript.Prover.MRSolver
  (askMRSolver, refinementTerm, 
   MRFailure(..), showMRFailure, showMRFailureNoCtx,
   RefinesS(..), asRefinesS,
   FunAssump(..), FunAssumpRHS(..), asFunAssump,
   Refnset, emptyRefnset, addFunAssump,
   MREnv(..), emptyMREnv, mrEnvSetDebugLevel,
   asProjAll, isSpecFunType) where

import SAWScript.Prover.MRSolver.Term
import SAWScript.Prover.MRSolver.Evidence
import SAWScript.Prover.MRSolver.Monad
import SAWScript.Prover.MRSolver.Solver
