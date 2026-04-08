theory Tests
  imports Negate_Proofs And_Proofs Or_Proofs XOR_Proofs Bit_Proofs Comparisons_Proofs
          Sequences_Proofs Comprehension_Proofs RecordDecls_Proofs Words_Proofs OOB_Proofs
          Recursion_Proofs TypeArith_Proofs Quickcheck_Tests "isabelle/tac_prove0"
          "isabelle/Nested"
begin

lemma "tac_prove0.goal x y z"
  unfolding tac_prove0.goal_def
  by auto

end