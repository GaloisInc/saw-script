{- |
Module      : SAWCentral.Provers.Rewrite
Description : Useful rewrites.
Maintainer  : GaloisInc
Stability   : provisional
-}

{-# LANGUAGE OverloadedStrings #-}

module SAWCentral.Prover.Rewrite (basic_ss) where

import SAWCore.Module (lookupVarIndexInMap, ResolvedName(..))
import SAWCore.Name (nameIndex)
import SAWCore.QualName (QualName)
import SAWCore.Rewriter
         ( Simpset, emptySimpset, addRules, RewriteRule
         , scEqsRewriteRules, scDefRewriteRules
         , addConvs
         )
import SAWCore.Conversion
import SAWCore.SharedTerm (SharedContext, scGetModuleMap, scResolveQualName)

basic_ss :: SharedContext -> IO (Simpset a)
basic_ss sc =
  do rs1 <- concat <$> traverse (defRewrites sc) defs
     rs2 <- scEqsRewriteRules sc eqs
     return $ addConvs procs (addRules (rs1 ++ rs2) emptySimpset)
     where
       eqs =
         [ "Prelude.unsafeCoerce_same"
         , "Prelude.headRecord_RecordValue"
         , "Prelude.tailRecord_RecordValue"
         , "Prelude.PairValue_fst_snd"
         , "Prelude.PairValue_fst_Unit"
         , "Prelude.RecordValue_head_tail"
         , "Prelude.RecordValue_head_Empty"
         , "Prelude.not_not"
         , "Prelude.true_implies"
         , "Prelude.implies__eq"
         , "Prelude.and_True1"
         , "Prelude.and_False1"
         , "Prelude.and_True2"
         , "Prelude.and_False2"
         , "Prelude.and_idem"
         , "Prelude.or_True1"
         , "Prelude.or_False1"
         , "Prelude.or_True2"
         , "Prelude.or_False2"
         , "Prelude.or_idem"
         , "Prelude.not_True"
         , "Prelude.not_False"
         , "Prelude.not_or"
         , "Prelude.not_and"
         , "Prelude.ite_true"
         , "Prelude.ite_false"
         , "Prelude.ite_not"
         , "Prelude.ite_nest1"
         , "Prelude.ite_nest2"
         , "Prelude.ite_fold_not"
         , "Prelude.ite_eq"
         , "Prelude.ite_true"
         , "Prelude.ite_false"
         , "Prelude.or_triv1"
         , "Prelude.and_triv1"
         , "Prelude.or_triv2"
         , "Prelude.and_triv2"
         , "Prelude.bvAddZeroL"
         , "Prelude.bvAddZeroR"
         , "Prelude.bveq_sameL"
         , "Prelude.bveq_sameR"
         , "Prelude.bveq_same2"
         , "Prelude.bvEq_refl"
         , "Prelude.bvNat_bvToNat"
         ]
       defs = ["Cryptol.seq", "Cryptol.ecEq", "Cryptol.ecNotEq"]
       procs = bvConversions ++ natConversions ++ vecConversions


defRewrites :: SharedContext -> QualName -> IO [RewriteRule a]
defRewrites sc qn =
  do mname <- scResolveQualName sc qn
     case mname of
       Nothing -> pure []
       Just nm ->
         do mm <- scGetModuleMap sc
            case lookupVarIndexInMap (nameIndex nm) mm of
              Just (ResolvedDef def) -> scDefRewriteRules sc def
              _ -> pure []
