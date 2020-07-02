{-# LANGUAGE OverloadedStrings #-}
{- |
Module      : SAWScript.VerificationSummary
Description : Summaries of verification for human consumption.
License     : BSD3
Maintainer  : atomb
-}

module SAWScript.VerificationSummary where

import Control.Lens
import qualified Data.Set as Set
import Data.String
import qualified Data.Text.Lazy as Text
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text

import qualified Lang.Crucible.JVM as CJ
import SAWScript.Crucible.Common.MethodSpec
import qualified SAWScript.Crucible.Common.MethodSpec as CMS
import qualified SAWScript.Crucible.LLVM.MethodSpecIR as CMSLLVM
import qualified SAWScript.Crucible.JVM.MethodSpecIR as CMSJVM
import SAWScript.Proof
import SAWScript.Prover.SolverStats

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
  where getSolvers (Theorem _ ss) = solverStatsSolvers ss

vsAllSolvers :: VerificationSummary -> Set.Set String
vsAllSolvers vs = Set.union (vsVerifSolvers vs) (vsTheoremSolvers vs)

computeVerificationSummary :: [JVMTheorem] -> [LLVMTheorem] -> [Theorem] -> VerificationSummary
computeVerificationSummary = VerificationSummary

prettyVerificationSummary :: VerificationSummary -> Text.Text
prettyVerificationSummary vs@(VerificationSummary jspecs lspecs thms) =
  renderLazy . layoutPretty defaultLayoutOptions $
  vsep
  [ prettyJVMSpecs jspecs
  , prettyLLVMSpecs lspecs
  , prettyTheorems thms
  , prettySolvers (map fromString (Set.toList (vsAllSolvers vs)))
  ] where
      section n = "#" <+> n
      item txt = "*" <+> txt
      subitem txt = indent 4 . item
      sectionWithItems _ _ [] = mempty
      sectionWithItems nm prt items =
        vsep [section nm, "", vsep (map prt items), ""]
      prettyJVMSpecs ss =
        sectionWithItems "JVM Methods Analyzed" prettyJVMSpec ss
      prettyJVMSpec s =
          vsep [ fromString (s ^. CMSJVM.csMethodName)
               , subitem "TODO"
               ]
      prettyLLVMSpecs ss =
        sectionWithItems "LLVM Functions Analyzed" prettyLLVMSpec ss
      prettyLLVMSpec (CMSLLVM.SomeLLVM s) =
          vsep [ item (fromString (s ^. CMSLLVM.csName))
               , subitem "TODO"
               ]
      prettyTheorems ts =
        sectionWithItems "Theorems Asserted" prettyTheorem ts
      prettyTheorem t = "TODO"
      prettySolvers ss =
        sectionWithItems "Solvers Used" item ss
