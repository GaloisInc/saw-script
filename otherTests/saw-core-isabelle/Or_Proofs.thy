theory Or_Proofs
imports "./isabelle/Or"
begin

context includes cryptol_syntax begin

lemmas test_defs =
  or_logic_def
  or_valid_def
  or_valid_Bit_def
  or_valid_seq_def
  or_valid_word_def
  or_valid_seq_seq_word_def
  or_truth_table_def
  or_word_lit_def


lemma "or_valid_Bit x y"
  unfolding test_defs
  by simp

lemma "or_valid_seq`{'a,'b::{logic,coercible_atom}} x y"
  unfolding test_defs
  by simp

lemma "or_valid_seq_seq_word x y"
  unfolding test_defs
  by simp

lemma "or_valid_word`{32} x y"
  unfolding test_defs
  by simp

lemma "or_truth_table"
  unfolding test_defs
  by simp

lemma "or_word_lit"
  unfolding test_defs
  by simp

end

end