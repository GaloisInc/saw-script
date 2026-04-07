theory And_Proofs
imports "./isabelle/And"
begin

context includes cryptol_syntax begin

lemmas test_defs =
  and_logic_def
  and_valid_def
  and_valid_Bit_def
  and_valid_seq_def
  and_valid_word_def
  and_valid_seq_seq_word_def
  and_True_False_def
  and_True_True_def
  and_word_lit_def


lemma "and_valid_Bit x y"
  unfolding test_defs
  by simp

lemma and_valid_seq: "and_valid_seq`{'a,'b::{logic,coercible_atom}} x y"
  unfolding test_defs
  by simp

lemma "and_valid_seq_seq_word x y"
  unfolding test_defs
  by simp

lemma "and_valid_word`{32} x y"
  unfolding test_defs
  by simp

lemma "and_True_False"
  unfolding test_defs
  by simp

lemma "and_True_True"
  unfolding test_defs
  by simp

lemma "and_word_lit"
  unfolding test_defs
  by simp

end

end