{- |
Module      : SAWScript.Provers.Rewrite
Description : Useful rewrites.
Maintainer  : GaloisInc
Stability   : provisional
-}

module SAWScript.Prover.Rewrite where

import Verifier.SAW.Rewriter
         ( Simpset, emptySimpset, addRules, RewriteRule
         , rewriteSharedTerm
         , scEqsRewriteRules, scDefRewriteRules
         , addConvs
         )
import Verifier.SAW.Term.Functor(preludeName, mkIdent, Ident, mkModuleName)
import Verifier.SAW.Conversion
import Verifier.SAW.SharedTerm(Term,SharedContext,scFindDef)

rewriteEqs :: SharedContext -> Term -> IO Term
rewriteEqs sc t =
  do let eqs = map (mkIdent preludeName)
                [ "eq_Bool", "eq_Nat", "eq_bitvector", "eq_VecBool"
                , "eq_VecVec" ]
     rs <- scEqsRewriteRules sc eqs
     ss <- addRules rs <$> basic_ss sc
     t' <- rewriteSharedTerm sc ss t
     return t'

basic_ss :: SharedContext -> IO Simpset
basic_ss sc =
  do rs1 <- concat <$> traverse (defRewrites sc) defs
     rs2 <- scEqsRewriteRules sc eqs
     return $ addConvs procs (addRules (rs1 ++ rs2) emptySimpset)
     where
       eqs = map (mkIdent preludeName)
         [ "unsafeCoerce_same"
         , "not_not"
         , "true_implies"
         , "implies__eq"
         , "and_True1"
         , "and_False1"
         , "and_True2"
         , "and_False2"
         , "and_idem"
         , "or_True1"
         , "or_False1"
         , "or_True2"
         , "or_False2"
         , "or_idem"
         , "not_True"
         , "not_False"
         , "not_or"
         , "not_and"
         , "ite_true"
         , "ite_false"
         , "ite_not"
         , "ite_nest1"
         , "ite_nest2"
         , "ite_fold_not"
         , "ite_eq"
         , "ite_true"
         , "ite_false"
         , "or_triv1"
         , "and_triv1"
         , "or_triv2"
         , "and_triv2"
         , "eq_refl"
         , "bvAddZeroL"
         , "bvAddZeroR"
         , "bveq_sameL"
         , "bveq_sameR"
         , "bveq_same2"
         , "bvNat_bvToNat"
         ]
       defs = map (mkIdent (mkModuleName ["Cryptol"])) ["seq", "ecEq", "ecNotEq"]
       procs = [tupleConversion, recordConversion] ++
               bvConversions ++ natConversions ++ vecConversions



defRewrites :: SharedContext -> Ident -> IO [RewriteRule]
defRewrites sc ident =
  scFindDef sc ident >>= \maybe_def ->
  case maybe_def of
    Nothing -> return []
    Just def -> scDefRewriteRules sc def
