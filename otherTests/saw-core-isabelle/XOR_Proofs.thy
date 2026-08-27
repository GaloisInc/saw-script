theory XOR_Proofs
imports "./isabelle/XOR"
begin

context includes cryptol_syntax begin

lemmas test_defs =
  xor_logic_def
  xor_valid_def
  xor_valid_Bit_def
  xor_valid_seq_def
  xor_valid_word_def
  xor_valid_seq_seq_word_def
  xor_truth_table_def
  xor_word_lit_def


lemma "xor_valid_Bit x y"
  unfolding test_defs
  by simp

lemma "xor_valid_seq`{'a,'b::{logic,coercible_atom}} x y"
  unfolding test_defs
  by simp

lemma "xor_valid_seq_seq_word x y"
  unfolding test_defs
  by simp

lemma "xor_valid_word`{32} x y"
  unfolding test_defs
  by simp

lemma "xor_truth_table"
  unfolding test_defs
  by simp

lemma "xor_word_lit"
  unfolding test_defs
  by simp

end

end