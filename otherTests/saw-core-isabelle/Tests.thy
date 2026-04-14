theory Tests
  imports Negate_Proofs And_Proofs Or_Proofs XOR_Proofs Bit_Proofs Comparisons_Proofs
          Sequences_Proofs Comprehension_Proofs RecordDecls_Proofs Words_Proofs OOB_Proofs
          Recursion_Proofs TypeArith_Proofs Quickcheck_Tests "isabelle/tac_prove0" "isabelle/Enums"
          "isabelle/Nested" "isabelle/Names"
begin

lemma "tac_prove0.goal x y z"
  unfolding tac_prove0.goal_def
  by auto

lemma "Enums.myEnum_eq_valid a b c x y"
  unfolding Enums.myEnum_eq_valid_def Enums.myEnum_eq_def
  by (auto split: Enums.MyEnum.splits)

lemma "Enums.opt_valid a b x y"
  unfolding Enums.opt_valid_def
  by (auto split: option.splits)

end