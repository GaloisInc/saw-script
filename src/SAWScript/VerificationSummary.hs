{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts #-}

{- |
Module      : SAWScript.VerificationSummary
Description : Summaries of verification for human consumption.
License     : BSD3
Maintainer  : atomb
-}

module SAWScript.VerificationSummary
  ( computeVerificationSummary
  , jsonVerificationSummary
  , prettyVerificationSummary
  ) where

import Control.Lens ((^.))
import qualified Data.Set as Set
import Data.String
import Prettyprinter
import Data.Aeson (encode, (.=), Value(..), object)
import qualified Data.ByteString.Lazy.UTF8 as BLU

import qualified Lang.Crucible.JVM as CJ
import SAWScript.Crucible.Common.MethodSpec
import qualified SAWScript.Crucible.Common.MethodSpec as CMS
import qualified SAWScript.Crucible.LLVM.MethodSpecIR as CMSLLVM
import qualified SAWScript.Crucible.JVM.MethodSpecIR as CMSJVM
import SAWScript.Proof
import SAWScript.Prover.SolverStats
import qualified Verifier.SAW.Term.Pretty as PP
import What4.ProgramLoc (ProgramLoc(plSourceLoc))

type JVMTheorem =  CMS.CrucibleMethodSpecIR CJ.JVM
type LLVMTheorem = CMSLLVM.SomeLLVM CMS.CrucibleMethodSpecIR

data VerificationSummary =
  VerificationSummary
  { vsJVMMethodSpecs :: [JVMTheorem]
  , vsLLVMMethodSpecs :: [LLVMTheorem]
  , vsTheorems :: [Theorem]
  }

vsVerifSolvers :: VerificationSummary -> Set.Set String
vsVerifSolvers vs =
  Set.unions $
  map (\ms -> solverStatsSolvers (ms ^. csSolverStats)) (vsJVMMethodSpecs vs) ++
  map (\(CMSLLVM.SomeLLVM ms) -> solverStatsSolvers (ms ^. csSolverStats)) (vsLLVMMethodSpecs vs)

vsTheoremSolvers :: VerificationSummary -> Set.Set String
vsTheoremSolvers = Set.unions . map getSolvers . vsTheorems
  where getSolvers thm = solverStatsSolvers (thmStats thm)

vsAllSolvers :: VerificationSummary -> Set.Set String
vsAllSolvers vs = Set.union (vsVerifSolvers vs) (vsTheoremSolvers vs)

computeVerificationSummary :: [JVMTheorem] -> [LLVMTheorem] -> [Theorem] -> VerificationSummary
computeVerificationSummary = VerificationSummary

-- TODO: we could make things instances of a ToJSON typeclass instead of using the two methods below.
msToJSON :: forall ext . Pretty (MethodId ext) => CMS.CrucibleMethodSpecIR ext -> Value
msToJSON cms = object [
    ("type" .= ("method" :: String))
    , ("method" .= (show $ pretty $ cms ^. csMethod))
    , ("loc" .= (show $ pretty $ plSourceLoc $ cms ^. csLoc))
    , ("status" .= (statusString $ cms ^. csSolverStats))
    , ("specification" .= ("unknown" :: String)) -- TODO
  ]

thmToJSON :: Theorem -> Value
thmToJSON thm = object [
    ("type" .= ("property" :: String))
    , ("loc" .= ("unknown" :: String)) -- TODO: Theorem has no attached location information
    , ("status" .= (statusString $ thmStats thm))
    , ("term" .= (show $ ppProp PP.defaultPPOpts $ thmProp thm))
  ]

statusString :: SolverStats -> String
statusString stats = if ((Set.null s) || (Set.member "ADMITTED" s)) then "assumed" else "verified"
  where s = solverStatsSolvers stats

jsonVerificationSummary :: VerificationSummary -> String
jsonVerificationSummary (VerificationSummary jspecs lspecs thms) =
  BLU.toString $ encode vals where
    vals = foldr (++) [] [jvals, lvals, thmvals]
    jvals = msToJSON <$> jspecs
    lvals = (\(CMSLLVM.SomeLLVM ls) -> msToJSON ls) <$> lspecs -- TODO: why is the type annotation required here?
    thmvals = thmToJSON <$> thms

prettyVerificationSummary :: VerificationSummary -> String
prettyVerificationSummary vs@(VerificationSummary jspecs lspecs thms) =
  show $ vsep
  [ prettyJVMSpecs jspecs
  , prettyLLVMSpecs lspecs
  , prettyTheorems thms
  , prettySolvers (Set.toList (vsAllSolvers vs))
  ] where
      section nm = "#" <+> nm
      item txt = "*" <+> txt
      code txt = vsep ["~~~~", txt, "~~~~"]
      subitem = indent 4 . item
      sectionWithItems _ _ [] = mempty
      sectionWithItems nm prt items =
        vsep [section nm, "", vsep (map prt items)]
      verifStatus s = if Set.null (solverStatsSolvers (s ^. CMS.csSolverStats))
                      then "assumed"
                      else "verified"
      -- TODO: ultimately the goal is for the following to summarize all
      -- preconditions made by this verification, but we need to extract
      -- a bunch more information for that to be meaningful.
      {-
      condStatus s = (if null (s ^. (CMS.csPreState . CMS.csConditions))
                      then "without"
                      else "with") <+> "conditions"
                      -}
      prettyJVMSpecs ss =
        sectionWithItems "JVM Methods Analyzed" prettyJVMSpec ss
      prettyJVMSpec s =
        vsep [ item (fromString (s ^. CMSJVM.csMethodName))
             -- , subitem (condStatus s)
             , subitem (verifStatus s)
             ]
      prettyLLVMSpecs ss =
        sectionWithItems "LLVM Functions Analyzed" prettyLLVMSpec ss
      prettyLLVMSpec (CMSLLVM.SomeLLVM s) =
        vsep [ item (fromString (s ^. CMSLLVM.csName))
             -- , subitem (condStatus s)
             , subitem (verifStatus s)
             ]
      prettyTheorems ts =
        sectionWithItems "Theorems Proved or Assumed" (item . prettyTheorem) ts
      prettyTheorem t =
        vsep [ if Set.null (solverStatsSolvers (thmStats t))
               then "Axiom:"
               else "Theorem:"
             , code (indent 2 (ppProp PP.defaultPPOpts (thmProp t)))
             , ""
             ]
      prettySolvers ss =
        sectionWithItems "Solvers Used" (item . fromString) ss
