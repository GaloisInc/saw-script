theory Words_Proofs
  imports "isabelle/Words"
begin

context includes cryptol_syntax begin

lemma "carry_valid`{'n} x y"
  unfolding carry_valid_def
  by (simp add: carry_seq_def2)

lemma "LEN('n) \<ge> 1 \<Longrightarrow> scarry_valid`{'n} x y"
  unfolding scarry_valid_def
  by (simp add: scarry_seq_def2)

lemma "LEN('n) \<ge> 1 \<Longrightarrow> sborrow_valid`{'n} x y"
  unfolding sborrow_valid_def
  by (simp add: sborrow_seq_def2)

end

end