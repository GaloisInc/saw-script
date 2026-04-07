theory Bit_Proofs
imports "./isabelle/Bit"
begin

context includes cryptol_syntax begin

lemmas test_defs =
  implies_truth_table_def
  conj_truth_table_def
  disj_truth_table_def

lemma "implies_truth_table"
  unfolding test_defs
  by simp


lemma "conj_truth_table"
  unfolding test_defs
  by simp

lemma "disj_truth_table"
  unfolding test_defs
  by simp

end
end