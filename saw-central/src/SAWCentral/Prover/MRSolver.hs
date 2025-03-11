{- |
Module      : SAWCentral.Prover.MRSolver
Description : The SAW monadic-recursive solver (Mr. Solver)
Copyright   : Galois, Inc. 2022
License     : BSD3
Maintainer  : westbrook@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCentral.Prover.MRSolver
  (askMRSolver, refinementTerm, 
   MRFailure(..), showMRFailure, showMRFailureNoCtx,
   RefinesS(..), asRefinesS,
   FunAssump(..), FunAssumpRHS(..), asFunAssump,
   Refnset, emptyRefnset, addFunAssump,
   MREnv(..), emptyMREnv, mrEnvSetDebugLevel,
   asProjAll, isSpecFunType) where

import SAWCentral.MRSolver.Term
import SAWCentral.MRSolver.Evidence
import SAWCentral.MRSolver.Monad
import SAWCentral.MRSolver.Solver
