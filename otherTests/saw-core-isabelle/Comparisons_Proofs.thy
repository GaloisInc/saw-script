theory Comparisons_Proofs
imports "./isabelle/Comparisons"
begin

context includes cryptol_syntax begin

lemmas test_defs =
  eq_bit_table_def
  eq_logic_def
  eq_valid_def
  eq_words_len_mismatch_def
  lt_bit_def
  lt_logic_def
  lt_valid_def
  neq_valid_def
  comparison_idents_def
  signed_comparison_idents_def
  min_max_idents_def

lemma "eq_bit_table"
  unfolding test_defs
  by simp


lemma "eq_logic`{'a::coercible_atom} x x"
  unfolding test_defs
  by simp

lemma "eq_valid`{'a::coercible_atom} x y"
  unfolding test_defs
  by simp

lemma "eq_valid`{Bit} x y"
  unfolding test_defs
  by simp

lemma "eq_valid`{[8]} x y"
  unfolding test_defs
  by simp

lemma "eq_valid`{[0]} x y"
  unfolding test_defs
  by simp

lemma "eq_valid`{[8][16]} x y"
  unfolding test_defs
  by simp

lemma "LEN('a) = LEN('b) \<Longrightarrow> eq_words_len_mismatch`{'a,'b} x y"
  unfolding test_defs
  by simp

lemma "lt_bit"
  unfolding test_defs
  by simp

lemma "lt_valid`{'a::{ord,coercible_atom}} x y"
  unfolding test_defs
  by simp

lemma "neq_valid`{'a::coercible_atom} x y"
  unfolding test_defs
  by simp

lemma comparison_idents: "comparison_idents`{'a::{linorder,coercible_atom}} x y"
  unfolding test_defs
  by fastforce

lemma "comparison_idents`{[32]} x y"
  by (rule comparison_idents)

lemma "comparison_idents`{Bit} x y"
  by (rule comparison_idents)

lemma "comparison_idents`{Integer} x y"
  by (rule comparison_idents)

lemma "comparison_idents`{[32][8]} x y"
  by (rule comparison_idents)

lemma "signed_comparison_idents`{['a]} x y"
  unfolding test_defs
  by fastforce

lemma "min_max_idents`{'a::{linorder,coercible_atom}} x y"
  unfolding test_defs
  by (simp add: min_le_iff_disj)

end
end