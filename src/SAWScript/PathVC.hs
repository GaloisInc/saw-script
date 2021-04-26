{- |
Module      : SAWScript.PathVC
Description : Assumptions and assertions for symbolic execution paths.
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}
module SAWScript.PathVC where

import Control.Monad.State
import Prettyprinter

import Verifier.SAW.SharedTerm
import Verifier.SAW.Term.Pretty (SawDoc)

import SAWScript.VerificationCheck

-- | Describes the verification result arising from one symbolic execution path.
data PathVC l = PathVC {
          pvcStartLoc :: l
        , pvcEndLoc :: Maybe l
          -- | Assumptions on inputs.
        , pvcAssumptions :: Term
          -- | Static errors found in path.
        , pvcStaticErrors :: [SawDoc]
          -- | What to verify for this result.
        , pvcChecks :: [VerificationCheck]
        }

ppPathVC :: PathVC l -> SawDoc
ppPathVC pvc =
  nest 2 $
  vcat [ pretty "Path VC:"
       , nest 2 $
         vcat [ pretty "Assumptions:"
              , ppTerm defaultPPOpts (pvcAssumptions pvc)
              ]
       , nest 2 $ vcat $
         pretty "Static errors:" :
         pvcStaticErrors pvc
       , nest 2 $ vcat $
         pretty "Checks:" :
         map ppCheck (pvcChecks pvc)
       ]

type PathVCGenerator l m = StateT (PathVC l) m

-- | Add verification condition to list.
pvcgAssertEq :: (Monad m) =>
                String -> Term -> Term
             -> PathVCGenerator l m ()
pvcgAssertEq name jv sv  =
  modify $ \pvc -> pvc { pvcChecks = EqualityCheck name jv sv : pvcChecks pvc }

pvcgAssert :: (Monad m) =>
              String -> Term -> PathVCGenerator l m ()
pvcgAssert nm v =
  modify $ \pvc -> pvc { pvcChecks = AssertionCheck nm v : pvcChecks pvc }

pvcgFail :: Monad m =>
            SawDoc -> PathVCGenerator l m ()
pvcgFail msg =
  modify $ \pvc -> pvc { pvcStaticErrors = msg : pvcStaticErrors pvc }

