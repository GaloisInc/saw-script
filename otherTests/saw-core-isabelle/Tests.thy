theory Tests
  imports Negate_Proofs And_Proofs Or_Proofs XOR_Proofs Bit_Proofs Comparisons_Proofs
          Sequences_Proofs Comprehension_Proofs RecordDecls_Proofs Words_Proofs OOB_Proofs
          Recursion_Proofs TypeArith_Proofs Quickcheck_Tests "isabelle/tac_prove0" "isabelle/Enums"
          "isabelle/Nested" "isabelle/Names" "isabelle/Enums" "isabelle/Foreign" "isabelle/Inf"
          "isabelle/ArithMap"
begin

lemma "\<And>x y z. tac_prove0.goal x y z"
  unfolding tac_prove0.goal_def
  by auto

lemma "\<And>a b c x y. Enums.myEnum_eq_valid a b c x y"
  unfolding Enums.myEnum_eq_valid_def Enums.myEnum_eq_def
  by (auto split: Enums.MyEnum.splits)

lemma "\<And>a b x y. Enums.opt_valid a b x y"
  unfolding Enums.opt_valid_def
  by (auto split: option.splits)

lemma "\<And>n x y. ArithMap.map2_plus n x y"
  unfolding ArithMap.map2_plus_def ArithMap.map2_def
  apply simp
  apply transfer'
  by auto

lemma "\<And>n x y. ArithMap.map2_times n x y"
  unfolding ArithMap.map2_times_def ArithMap.map2_def
  apply simp
  apply transfer'
  by auto

lemma "\<And>n x y. ArithMap.map2_minus n x y"
  unfolding ArithMap.map2_minus_def ArithMap.map2_def
  apply simp
  apply transfer'
  by auto

lemma "\<And>n x. ArithMap.map_uminus n x"
  unfolding ArithMap.map_uminus_def
  apply simp
  apply transfer'
  by auto

end