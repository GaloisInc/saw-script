theory TypeSyn_Proofs
imports TypeSyn
begin

context includes cryptol_syntax begin

lemma "seq_noop`{'n} x = x"
  unfolding seq_noop_def
  by simp

end

end