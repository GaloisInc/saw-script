theory Negate_Proofs
imports "./isabelle/Negate"
begin

context includes cryptol_syntax begin

lemmas test_defs = 
  negate_logic_def
  negate_valid_def
  negate_valid_bit_def
  negate_valid_seq_def
  negate_valid_word_def
  negate_valid_seq_seq_word_def
  negate_true_is_false_def
  negate_word_lit_def


lemma "negate_valid_bit x"
  unfolding test_defs
  by simp

lemma negate_valid_seq: "negate_valid_seq`{'a,'b::{logic,coercible_atom}} x"
  unfolding test_defs
  by simp

lemma "negate_valid_seq_seq_word x"
  unfolding negate_valid_seq_seq_word_def
  by (rule negate_valid_seq)

lemma "negate_valid_word`{32} x"
  unfolding test_defs
  by simp

lemma "negate_true_is_false"
  unfolding test_defs
  by simp

lemma "negate_word_lit"
  unfolding test_defs
  by simp

end

end