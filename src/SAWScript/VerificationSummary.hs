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
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.String
import Prettyprinter
import Data.Aeson (encode, (.=), Value(..), object, toJSON)
import Data.Aeson.Key (Key)
import qualified Data.ByteString.Lazy.UTF8 as BLU
import Data.Parameterized.Nonce

import qualified Lang.Crucible.JVM as CJ
import SAWCentral.Crucible.Common.MethodSpec
import qualified SAWCentral.Crucible.Common.MethodSpec as CMS
import qualified SAWCentral.Crucible.LLVM.MethodSpecIR as CMSLLVM
import qualified SAWCentral.Crucible.JVM.MethodSpecIR as CMSJVM
import SAWScript.Proof
import SAWCentral.Prover.SolverStats
import qualified Verifier.SAW.Term.Pretty as PP
import Verifier.SAW.Name (SAWNamingEnv)
import What4.ProgramLoc (ProgramLoc(..))
import What4.FunctionName

type JVMTheorem =  CMS.ProvedSpec CJ.JVM
type LLVMTheorem = CMSLLVM.SomeLLVM CMS.ProvedSpec

data VerificationSummary =
  VerificationSummary
  { vsJVMMethodSpecs :: [JVMTheorem]
  , vsLLVMMethodSpecs :: [LLVMTheorem]
  , vsTheorems :: [Theorem]
  }

vsVerifSolvers :: VerificationSummary -> Set.Set String
vsVerifSolvers vs =
  Set.unions $
  map (\ms -> solverStatsSolvers (ms ^. psSolverStats)) (vsJVMMethodSpecs vs) ++
  map (\(CMSLLVM.SomeLLVM ms) -> solverStatsSolvers (ms ^. psSolverStats)) (vsLLVMMethodSpecs vs)

vsTheoremSolvers :: VerificationSummary -> Set.Set String
vsTheoremSolvers = Set.unions . map getSolvers . vsTheorems
  where getSolvers thm = solverStatsSolvers (thmStats thm)

vsAllSolvers :: VerificationSummary -> Set.Set String
vsAllSolvers vs = Set.union (vsVerifSolvers vs) (vsTheoremSolvers vs)

computeVerificationSummary :: TheoremDB -> [JVMTheorem] -> [LLVMTheorem] -> [Theorem] -> VerificationSummary
computeVerificationSummary db js ls thms =
  let roots = mconcat (
                [ vcDeps vc | j <- js, vc <- j^.psVCStats ] ++
                [ vcDeps vc | CMSLLVM.SomeLLVM l <- ls, vc <- l^.psVCStats ] ++
                [ Set.singleton (thmNonce t) | t <- thms ])
      thms' = Map.elems (reachableTheorems db roots)
  in  VerificationSummary js ls thms'

-- TODO: we could make things instances of a ToJSON typeclass instead of using the two methods below.
msToJSON :: forall ext . Pretty (MethodId ext) => CMS.ProvedSpec ext -> Value
msToJSON cms = object [
    ("type" .= ("method" :: String))
    , ("id" .= (indexValue $ cms ^. psSpecIdent))
    , ("method" .= (show $ pretty $ cms ^. psSpec.csMethod))
    , ("loc" .= (show $ pretty $ plSourceLoc $ cms ^. psSpec.csLoc))
    , ("status" .= case cms ^. psProofMethod of
                     SpecAdmitted -> "assumed" :: String
                     SpecProved   -> "verified")
--    , ("specification" .= ("unknown" :: String)) -- TODO
    , ("dependencies" .= toJSON (map indexValue (Set.toList (cms ^. psSpecDeps))))
    , ("vcs"          .= toJSON (map vcToJSON (cms ^. psVCStats)))
    , ("elapsedtime"  .= toJSON (cms ^. psElapsedTime))
    ]

vcToJSON :: CMS.VCStats -> Value
vcToJSON vc = object ([
  ("type"  .= ("vc" :: String))
  , ("id"  .= indexValue (vcIdent vc))
  , ("loc" .= show (conditionLoc (vcMetadata vc)))
  , ("reason" .= conditionType (vcMetadata vc))
  , ("elapsedtime" .= toJSON (vcElapsedTime vc))
  , ("dependencies" .= toJSON (map indexValue (Set.toList (vcDeps vc))))
  , ("tags" .= toJSON (Set.toList (conditionTags (vcMetadata vc))))
  ] ++ theoremStatus (vcThmSummary vc)
  )

thmToJSON :: Theorem -> Value
thmToJSON thm = object ([
    ("type" .= ("property" :: String))
    , ("id" .= (indexValue $ thmNonce thm))
    , ("loc" .= (show $ thmLocation thm))
    , ("reason" .= (thmReason thm))
    , ("dependencies" .= toJSON (map indexValue (Set.toList (thmDepends thm))))
    , ("elapsedtime"  .= toJSON (thmElapsedTime thm))
  ] ++ theoremStatus (thmSummary thm)
    ++ case thmProgramLoc thm of
         Nothing -> []
         Just ploc -> [("ploc" .= plocToJSON ploc)]
  )

theoremStatus :: TheoremSummary -> [(Key,Value)]
theoremStatus summary = case summary of
      ProvedTheorem stats ->
        [ ("status"  .= ("verified" :: String))
        , ("provers" .= toJSON (Set.toList (solverStatsSolvers stats)))
        ]
      TestedTheorem n ->
        [ ("status"   .= ("tested" :: String))
        , ("numtests" .= toJSON n)
        ]
      AdmittedTheorem msg ->
        [ ("status"   .= ("assumed" :: String))
        , ("admitmsg" .= msg)
        ]

--    , ("term" .= (show $ ppProp PP.defaultPPOpts $ thmProp thm))

plocToJSON :: ProgramLoc -> Value
plocToJSON ploc = object
  [ "function" .= toJSON (functionName (plFunction ploc))
  , "loc"      .= show (plSourceLoc ploc)
  ]


jsonVerificationSummary :: VerificationSummary -> String
jsonVerificationSummary (VerificationSummary jspecs lspecs thms) =
  BLU.toString $ encode vals where
    vals = foldr (++) [] [jvals, lvals, thmvals]
    jvals = msToJSON <$> jspecs
    lvals = (\(CMSLLVM.SomeLLVM ls) -> msToJSON ls) <$> lspecs -- TODO: why is the type annotation required here?
    thmvals = thmToJSON <$> thms

prettyVerificationSummary :: PP.PPOpts -> SAWNamingEnv -> VerificationSummary -> String
prettyVerificationSummary ppOpts nenv vs@(VerificationSummary jspecs lspecs thms) =
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
      verifStatus s = case s ^. CMS.psProofMethod of
                        CMS.SpecAdmitted -> "assumed"
                        CMS.SpecProved   -> "verified"
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
        vsep [ item (fromString (s ^. CMS.psSpec.CMSJVM.csMethodName))
             -- , subitem (condStatus s)
             , subitem (verifStatus s)
             ]
      prettyLLVMSpecs ss =
        sectionWithItems "LLVM Functions Analyzed" prettyLLVMSpec ss
      prettyLLVMSpec (CMSLLVM.SomeLLVM s) =
        vsep [ item (fromString (s ^. CMS.psSpec.CMSLLVM.csName))
             -- , subitem (condStatus s)
             , subitem (verifStatus s)
             ]
      prettyTheorems ts =
        sectionWithItems "Theorems Proved or Assumed" (item . prettyTheorem) ts
      prettyTheorem t =
        vsep [ case thmSummary t of
                 ProvedTheorem{}   -> "Theorem:"
                 TestedTheorem n   -> "Theorem (randomly tested on" <+> viaShow n <+> "samples):"
                 AdmittedTheorem{} -> "Axiom:"
             , code (indent 2 (ppProp ppOpts nenv (thmProp t)))
             , ""
             ]
      prettySolvers ss =
        sectionWithItems "Solvers Used" (item . fromString) ss
